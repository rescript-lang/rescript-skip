/**
 * Reanalyze DCE Harness - Dis-aggregation Pattern
 * 
 * Demonstrates reactive dead code elimination with:
 * - Server: Receives complete file data, dis-aggregates into fine-grained fragments
 * - Client: Receives small deltas (only changed fragments), computes liveness
 * 
 * Input: Single collection `files` with complete file data
 *   files["main.res"] = { decls: [...], refs: [...], annotations: [...] }
 * 
 * Output: Disaggregated `fragments` resource with composite keys
 *   ("main.res", "decls") → [...]
 *   ("main.res", "refs") → [...]
 *   ("main.res", "annotations") → [...]
 * 
 * When a file changes, Skip only sends deltas for fragments that changed.
 * 
 * Run with: node examples/ReanalyzeDCEHarness.res.js
 */

// ============================================================================
// Server Module
// ============================================================================

module Server = {
  @module("./ReanalyzeDCEService.js")
  external service: SkipruntimeCore.skipService = "service"

  let defaultOpts: SkipruntimeServer.runOptions = {
    streaming_port: 18091,
    control_port: 18090,
    platform: Some(#wasm),
    no_cors: None,
  }

  let start = (opts: SkipruntimeServer.runOptions) =>
    SkipruntimeServer.Natural.runService(service, ~options=opts)

  let stop = (server: SkipruntimeServer.skipServer) =>
    SkipruntimeServer.Natural.close(server)
}

// ============================================================================
// Client Module
// ============================================================================

module Client = {
  let localhost = "127.0.0.1"

  let makeBroker = (opts: SkipruntimeServer.runOptions) =>
    SkipruntimeHelpers.make(
      Some({
        host: localhost,
        streaming_port: opts.streaming_port,
        control_port: opts.control_port,
        secured: None,
      }),
      None,
    )

  // Complete file data type
  type fileData = {
    decls: array<string>,
    refs: array<(string, string)>,
    annotations: array<(string, string)>,
    optArgCalls: array<(string, string, array<string>)>, // (caller, fn, passed_args)
  }

  // Send complete file data
  let updateFile = (broker, filename: string, data: fileData) => {
    // Convert to JSON matching the TypeScript FileData type
    let jsonData = JSON.Object(Dict.fromArray([
      ("decls", JSON.Array(data.decls->Array.map(d => JSON.String(d)))),
      ("refs", JSON.Array(data.refs->Array.map(((target, source)) => 
        JSON.Array([JSON.String(target), JSON.String(source)])
      ))),
      ("annotations", JSON.Array(data.annotations->Array.map(((pos, annot)) =>
        JSON.Array([JSON.String(pos), JSON.String(annot)])
      ))),
      ("optArgCalls", JSON.Array(data.optArgCalls->Array.map(((caller, fn, passed)) =>
        JSON.Array([JSON.String(caller), JSON.String(fn), JSON.Array(passed->Array.map(a => JSON.String(a)))])
      ))),
    ]))
    SkipruntimeHelpers.update(broker, "files", [
      (JSON.String(filename), [jsonData])
    ])
  }

  // Delete a file
  let deleteFile = (broker, filename: string) => {
    SkipruntimeHelpers.update(broker, "files", [
      (JSON.String(filename), [])  // Empty values = delete
    ])
  }

  let getStreamUrl = async (opts: SkipruntimeServer.runOptions, broker, resource) => {
    let uuid = await SkipruntimeHelpers.getStreamUUID(broker, resource, None)
    `http://${localhost}:${opts.streaming_port->Int.toString}/v1/streams/${uuid}`
  }
}

// ============================================================================
// Layer 2: Client-side Liveness Computation using ClientReducer + SkipruntimeFixpoint
// ============================================================================

module ClientDCE = {
  // Optional arg call: (caller, fn, passed_args)
  type optArgCall = {caller: string, fn: string, passed: array<string>}

  // Reducers for incremental aggregation
  let declsReducer: ClientReducer.SetReducer.t<string> = ClientReducer.SetReducer.make()
  let refsReducer: ClientReducer.SetReducer.t<(string, string)> = ClientReducer.SetReducer.make()
  let annotReducer: ClientReducer.MapReducer.t<string, string> = ClientReducer.MapReducer.make()
  let optArgCallsReducer: ClientReducer.ArrayReducer.t<optArgCall> = ClientReducer.ArrayReducer.make()

  type state = {
    // Fixpoint
    mutable fixpoint: SkipruntimeFixpoint.t,
    mutable subscription: option<SkipruntimeCore.sseSubscription>,
    // Track current base and step for incremental updates
    mutable currentBase: Set.t<string>,
    mutable currentStep: Set.t<string>,  // Set of "source→target" strings
    // Optional args tracking: fn → arg → Set<callers who passed this arg>
    // This tracks provenance so we can remove args when callers become dead
    mutable usedArgsWithProvenance: Map.t<string, Map.t<string, Set.t<string>>>,
    // Index: caller → array of optArgCalls from that caller
    mutable optArgCallsByCaller: Map.t<string, array<optArgCall>>,
  }

  let state: state = {
    fixpoint: SkipruntimeFixpoint.make(~base=[]),
    subscription: None,
    currentBase: Set.make(),
    currentStep: Set.make(),
    usedArgsWithProvenance: Map.make(),
    optArgCallsByCaller: Map.make(),
  }

  // Count SSE updates and fixpoint updates
  let sseUpdateCount = ref(0)
  let updateCount = ref(0)
  let totalUpdateTimeMs = ref(0.0)
  let isInitialized = ref(false)

  // Helper to encode edge as string for Set membership
  let edgeKey = (source, target) => `${source}→${target}`
  let parseEdge = (key: string): option<(string, string)> => {
    switch key->String.split("→") {
    | [source, target] => Some((source, target))
    | _ => None
    }
  }

  // Accessors for aggregated data (from reducers)
  let getAllDecls = () => declsReducer->ClientReducer.SetReducer.currentSet
  let getAllRefs = () => refsReducer->ClientReducer.SetReducer.currentSet
  let getAllAnnotations = () => annotReducer->ClientReducer.MapReducer.currentMap
  let getAllOptArgCalls = () => optArgCallsReducer->ClientReducer.ArrayReducer.currentArray

  // Build refsByTarget index from refs set
  let getRefsByTarget = (): Map.t<string, Set.t<string>> => {
    let result: Map.t<string, Set.t<string>> = Map.make()
    getAllRefs()->Set.forEach(((target, source)) => {
      switch result->Map.get(target) {
      | Some(sources) => sources->Set.add(source)->ignore
      | None =>
        let sources = Set.make()
        sources->Set.add(source)->ignore
        result->Map.set(target, sources)->ignore
      }
    })
    result
  }

  // Rebuild optArgCallsByCaller index from all opt arg calls
  let rebuildOptArgCallsByCaller = () => {
    state.optArgCallsByCaller = Map.make()
    getAllOptArgCalls()->Array.forEach(call => {
      let existing = state.optArgCallsByCaller->Map.get(call.caller)->Option.getOr([])
      state.optArgCallsByCaller->Map.set(call.caller, existing->Array.concat([call]))->ignore
    })
  }

  // Add args to usedArgsWithProvenance when a caller becomes live
  let addCallerToUsedArgs = (caller: string) => {
    switch state.optArgCallsByCaller->Map.get(caller) {
    | Some(calls) =>
      calls->Array.forEach(({fn, passed, caller: c}) => {
        passed->Array.forEach(arg => {
          // Get or create fn map
          let fnMap = switch state.usedArgsWithProvenance->Map.get(fn) {
          | Some(m) => m
          | None =>
            let m = Map.make()
            state.usedArgsWithProvenance->Map.set(fn, m)->ignore
            m
          }
          // Get or create arg set
          let callers = switch fnMap->Map.get(arg) {
          | Some(s) => s
          | None =>
            let s = Set.make()
            fnMap->Map.set(arg, s)->ignore
            s
          }
          callers->Set.add(c)->ignore
        })
      })
    | None => ()
    }
  }

  // Remove args from usedArgsWithProvenance when a caller becomes dead
  let removeCallerFromUsedArgs = (caller: string) => {
    switch state.optArgCallsByCaller->Map.get(caller) {
    | Some(calls) =>
      calls->Array.forEach(({fn, passed, caller: c}) => {
        passed->Array.forEach(arg => {
          switch state.usedArgsWithProvenance->Map.get(fn) {
          | Some(fnMap) =>
            switch fnMap->Map.get(arg) {
            | Some(callers) => 
              callers->Set.delete(c)->ignore
              // If no callers left for this arg, could remove the entry
            | None => ()
            }
          | None => ()
          }
        })
      })
    | None => ()
    }
  }

  // Get used args for a function (only from live callers)
  let getUsedArgs = (fn: string): Set.t<string> => {
    let result = Set.make()
    switch state.usedArgsWithProvenance->Map.get(fn) {
    | Some(fnMap) =>
      fnMap->Map.entries->Iterator.forEach(entry => {
        let (arg, callers) = entry
        if callers->Set.size > 0 {
          result->Set.add(arg)->ignore
        }
      })
    | None => ()
    }
    result
  }

  // Compute what the base SHOULD be (without modifying fixpoint)
  let computeDesiredBase = () => {
    let base = Set.make()
    let allAnnotations = getAllAnnotations()
    let allDecls = getAllDecls()
    let refsByTarget = getRefsByTarget()
    
    // @live annotations
    allAnnotations->Map.entries->Iterator.forEach(entry => {
      let (pos, annot) = entry
      if annot == "live" {
        base->Set.add(pos)->ignore
      }
    })
    
    // External refs (refs where source is not in allDecls)
    refsByTarget->Map.entries->Iterator.forEach(entry => {
      let (target, sources) = entry
      let hasExternalRef = ref(false)
      sources->Set.forEach(src => {
        if !(allDecls->Set.has(src)) {
          hasExternalRef := true
        }
      })
      if hasExternalRef.contents {
        base->Set.add(target)->ignore
      }
    })
    
    base
  }

  // Compute what the step edges SHOULD be (without modifying fixpoint)
  let computeDesiredStep = () => {
    let step = Set.make()
    let allAnnotations = getAllAnnotations()
    let refsByTarget = getRefsByTarget()
    
    refsByTarget->Map.entries->Iterator.forEach(entry => {
      let (target, sources) = entry
      sources->Set.forEach(source => {
        let isBlocked = allAnnotations->Map.get(source) == Some("dead")
        if !isBlocked {
          step->Set.add(edgeKey(source, target))->ignore
        }
      })
    })
    
    step
  }

  // Compute set difference: elements in a but not in b
  let setDiff = (a: Set.t<string>, b: Set.t<string>): array<string> => {
    let result = []
    a->Set.forEach(x => {
      if !(b->Set.has(x)) {
        result->Array.push(x)->ignore
      }
    })
    result
  }

  // Update fixpoint incrementally
  // Note: Reducers have already been updated, so aggregates are current
  let updateFixpointIncremental = () => {
    updateCount := updateCount.contents + 1
    let startTime = Date.now()
    
    // Rebuild optArgCallsByCaller index (TODO: make this incremental too)
    rebuildOptArgCallsByCaller()
    
    let desiredBase = computeDesiredBase()
    let desiredStep = computeDesiredStep()
    
    // Compute diffs
    let addedToBase = setDiff(desiredBase, state.currentBase)
    let removedFromBase = setDiff(state.currentBase, desiredBase)
    let addedStepKeys = setDiff(desiredStep, state.currentStep)
    let removedStepKeys = setDiff(state.currentStep, desiredStep)
    
    // Convert step keys back to tuples
    let addedToStep = addedStepKeys->Array.filterMap(parseEdge)
    let removedToStep = removedStepKeys->Array.filterMap(parseEdge)
    
    // Apply changes
    let changes = state.fixpoint->SkipruntimeFixpoint.applyChanges(
      ~addedToBase,
      ~removedFromBase,
      ~addedToStep,
      ~removedToStep,
    )
    
    // Update optional args incrementally based on fixpoint changes
    changes.removed->Array.forEach(removeCallerFromUsedArgs)
    changes.added->Array.forEach(addCallerToUsedArgs)
    
    // Update tracking
    state.currentBase = desiredBase
    state.currentStep = desiredStep
    
    let endTime = Date.now()
    let durationMs = endTime -. startTime
    totalUpdateTimeMs := totalUpdateTimeMs.contents +. durationMs
    
    Console.log(`    [INCREMENTAL #${updateCount.contents->Int.toString}] ${durationMs->Float.toString}ms - ` ++
      `Δbase: +${addedToBase->Array.length->Int.toString}/-${removedFromBase->Array.length->Int.toString}, ` ++
      `Δstep: +${addedToStep->Array.length->Int.toString}/-${removedToStep->Array.length->Int.toString}, ` ++
      `Δfixpoint: +${changes.added->Array.length->Int.toString}/-${changes.removed->Array.length->Int.toString}`)
  }

  // Initial setup (first SSE message)
  // Note: Reducers have already been updated, so aggregates are current
  let initializeFixpoint = () => {
    updateCount := updateCount.contents + 1
    let startTime = Date.now()
    
    // Build optArgCallsByCaller index
    rebuildOptArgCallsByCaller()
    
    let desiredBase = computeDesiredBase()
    let desiredStep = computeDesiredStep()
    
    // Create fixpoint with initial base
    state.fixpoint = SkipruntimeFixpoint.make(~base=desiredBase->Set.values->Iterator.toArray)
    
    // Add all step edges
    let edgeCount = ref(0)
    desiredStep->Set.forEach(key => {
      switch parseEdge(key) {
      | Some((source, target)) =>
        state.fixpoint->SkipruntimeFixpoint.addToStep(~source, ~target)->ignore
        edgeCount := edgeCount.contents + 1
      | None => ()
      }
    })
    
    // Initialize optional args from all live elements
    state.usedArgsWithProvenance = Map.make()
    state.fixpoint->SkipruntimeFixpoint.current->Array.forEach(addCallerToUsedArgs)
    
    // Update tracking
    state.currentBase = desiredBase
    state.currentStep = desiredStep
    isInitialized := true
    
    let endTime = Date.now()
    let durationMs = endTime -. startTime
    totalUpdateTimeMs := totalUpdateTimeMs.contents +. durationMs
    
    let numSources = declsReducer.contributions->Map.size
    let numDecls = getAllDecls()->Set.size
    
    Console.log(`    [INIT #${updateCount.contents->Int.toString}] ${durationMs->Float.toString}ms - ` ++
      `${numSources->Int.toString} files, ` ++
      `${numDecls->Int.toString} decls, ` ++
      `${desiredBase->Set.size->Int.toString} base, ` ++
      `${edgeCount.contents->Int.toString} edges`)
  }

  // Smart update: initialize on first call, incremental thereafter
  let updateFixpoint = () => {
    if isInitialized.contents {
      updateFixpointIncremental()
    } else {
      initializeFixpoint()
    }
  }

  // Handle SSE data from fragments resource
  // Uses reducers for incremental aggregation
  let handleFragmentsData = (data: JSON.t) => {
    sseUpdateCount := sseUpdateCount.contents + 1
    let dataStr = JSON.stringify(data)
    Console.log(`[SSE #${sseUpdateCount.contents->Int.toString}] fragments: ${dataStr->String.length->Int.toString} bytes`)
    
    switch data {
    | JSON.Array(entries) =>
      Console.log(`  → ${entries->Array.length->Int.toString} fragment updates`)
      
      entries->Array.forEach(entry => {
        // Each entry is [[filename, fragmentType], [value]]
        switch entry {
        | JSON.Array([JSON.Array([JSON.String(filename), JSON.String(fragmentType)]), JSON.Array(values)]) =>
          Console.log(`  → file="${filename}", fragment="${fragmentType}"`)

          // Handle deletion (empty values) or update
          switch (fragmentType, values[0]) {
          | ("decls", valueOpt) =>
            let newDecls = switch valueOpt {
            | Some(JSON.Array(decls)) =>
              Console.log(`    → ${decls->Array.length->Int.toString} decls`)
              decls->Array.filterMap(d => {
                switch d {
                | JSON.String(s) => Some(s)
                | _ => None
                }
              })
            | _ => 
              Console.log(`    → DELETED`)
              []
            }
            let delta = declsReducer->ClientReducer.SetReducer.setContributionArray(
              ~source=filename,
              ~values=newDecls,
            )
            if delta.added->Array.length > 0 || delta.removed->Array.length > 0 {
              Console.log(`    Δagg: +${delta.added->Array.length->Int.toString}/-${delta.removed->Array.length->Int.toString}`)
            }
            
          | ("refs", valueOpt) =>
            let newRefs = switch valueOpt {
            | Some(JSON.Array(refs)) =>
              Console.log(`    → ${refs->Array.length->Int.toString} refs`)
              refs->Array.filterMap(r => {
                switch r {
                | JSON.Array([JSON.String(target), JSON.String(source)]) => Some((target, source))
                | _ => None
                }
              })
            | _ =>
              Console.log(`    → DELETED`)
              []
            }
            let delta = refsReducer->ClientReducer.SetReducer.setContributionArray(
              ~source=filename,
              ~values=newRefs,
            )
            if delta.added->Array.length > 0 || delta.removed->Array.length > 0 {
              Console.log(`    Δagg: +${delta.added->Array.length->Int.toString}/-${delta.removed->Array.length->Int.toString}`)
            }
            
          | ("annotations", valueOpt) =>
            let newAnnots: Map.t<string, string> = Map.make()
            switch valueOpt {
            | Some(JSON.Array(annots)) =>
              Console.log(`    → ${annots->Array.length->Int.toString} annotations`)
              annots->Array.forEach(a => {
                switch a {
                | JSON.Array([JSON.String(pos), JSON.String(annot)]) =>
                  newAnnots->Map.set(pos, annot)->ignore
                | _ => ()
                }
              })
            | _ =>
              Console.log(`    → DELETED`)
            }
            let delta = annotReducer->ClientReducer.MapReducer.setContribution(
              ~source=filename,
              ~values=newAnnots,
            )
            if delta.added->Array.length > 0 || delta.removed->Array.length > 0 {
              Console.log(`    Δagg: +${delta.added->Array.length->Int.toString}/-${delta.removed->Array.length->Int.toString}`)
            }
            
          | ("optArgCalls", valueOpt) =>
            let newCalls = switch valueOpt {
            | Some(JSON.Array(calls)) =>
              Console.log(`    → ${calls->Array.length->Int.toString} optArgCalls`)
              calls->Array.filterMap(c => {
                switch c {
                | JSON.Array([JSON.String(caller), JSON.String(fn), JSON.Array(passed)]) =>
                  let passedArgs = passed->Array.filterMap(a => {
                    switch a {
                    | JSON.String(s) => Some(s)
                    | _ => None
                    }
                  })
                  Some({caller, fn, passed: passedArgs})
                | _ => None
                }
              })
            | _ =>
              Console.log(`    → DELETED`)
              []
            }
            let delta = optArgCallsReducer->ClientReducer.ArrayReducer.setContribution(
              ~source=filename,
              ~values=newCalls,
            )
            if delta.added->Array.length > 0 || delta.removed->Array.length > 0 {
              Console.log(`    Δagg: +${delta.added->Array.length->Int.toString}/-${delta.removed->Array.length->Int.toString}`)
            }
            
          | _ => ()
          }
        | _ => ()
        }
      })
      
      updateFixpoint()
    | _ => ()
    }
  }

  let subscribe = (fragmentsUrl: string) => {
    let sub = SkipruntimeCore.subscribeSSE(fragmentsUrl, handleFragmentsData)
    state.subscription = Some(sub)
  }

  let close = () => {
    switch state.subscription {
    | Some(sub) => sub.close()
    | None => ()
    }
    state.subscription = None
  }

  let getLiveSet = (): array<string> => {
    state.fixpoint->SkipruntimeFixpoint.current
  }

  let getDeadSet = (): array<string> => {
    let live = Set.fromArray(getLiveSet())
    let dead = []
    getAllDecls()->Set.forEach(decl => {
      if !(live->Set.has(decl)) {
        dead->Array.push(decl)->ignore
      }
    })
    dead
  }

  // Optional args report type
  type optArgsReport = {used: array<string>, unused: array<string>}

  // Get optional args analysis for a function
  // declaredArgs would come from function signatures (simplified here)
  let getOptionalArgsReport = (fn: string, declaredArgs: array<string>): optArgsReport => {
    let usedSet = getUsedArgs(fn)
    let used = []
    let unused = []
    declaredArgs->Array.forEach(arg => {
      if usedSet->Set.has(arg) {
        used->Array.push(arg)->ignore
      } else {
        unused->Array.push(arg)->ignore
      }
    })
    {used, unused}
  }
}

// ============================================================================
// Helper
// ============================================================================

let delay = ms => {
  Promise.make((resolve, _reject) => {
    let _ = setTimeout(() => resolve(), ms)
  })
}

let logArray = (label, arr) =>
  Console.log(label ++ ": [" ++ arr->Array.toSorted(String.compare)->Array.join(", ") ++ "]")

// ============================================================================
// Main
// ============================================================================

let run = async () => {
  Console.log("===========================================")
  Console.log("Reanalyze DCE Harness - Dis-aggregation Pattern")
  Console.log("===========================================")
  Console.log("")
  Console.log("Server: Receives complete file data → dis-aggregates into fragments")
  Console.log("Client: Receives small deltas → computes liveness locally")
  Console.log("")
  Console.log("When only annotations change, only the annotations fragment is sent!")
  Console.log("")

  let server = await Server.start(Server.defaultOpts)
  Console.log("Server started on ports 18090/18091")

  let broker = Client.makeBroker(Server.defaultOpts)

  // Subscribe to the fragments resource
  let fragmentsUrl = await Client.getStreamUrl(Server.defaultOpts, broker, "fragments")
  Console.log(`Subscribing to fragments resource via SSE...`)
  ClientDCE.subscribe(fragmentsUrl)

  await delay(500)

  // Phase 1: Initial state (from server's initialData)
  Console.log("")
  Console.log("--- Phase 1: Initial State ---")
  Console.log("  main.res: decls=[main, unused_in_main], refs=[[utils,main],[api,main]], @live=main")
  Console.log("           optArgCalls: main calls utils(~format)")
  Console.log("  utils.res: decls=[utils, helpers, dead_util], refs=[[helpers,utils]]")
  Console.log("           (utils has optional args: ~format, ~locale, ~timezone)")
  Console.log("  api.res: decls=[api, db, logger], refs=[[db,api],[logger,api]], @dead=api")
  Console.log("           optArgCalls: api calls utils(~format, ~locale) - BUT API IS DEAD!")
  Console.log("")
  
  logArray("Live set", ClientDCE.getLiveSet())
  logArray("Dead set", ClientDCE.getDeadSet())
  
  // Show optional args analysis
  let utilsArgs = ClientDCE.getOptionalArgsReport("utils", ["~format", "~locale", "~timezone"])
  Console.log("")
  Console.log("Optional args for 'utils' (only from LIVE callers):")
  logArray("  Used args", utilsArgs.used)
  logArray("  Unused args", utilsArgs.unused)
  Console.log("  (api's call to utils(~format, ~locale) doesn't count - api is dead!)")

  // Phase 2: Add a new file (complete file data in one update)
  Console.log("")
  Console.log("--- Phase 2: Add feature.res (new file) ---")
  Console.log("  Sending complete file data in ONE update:")
  Console.log("  { decls: [feature], refs: [[dead_util, feature]], annotations: [[feature, live]],")
  Console.log("    optArgCalls: feature calls utils(~timezone) }")
  Console.log("")

  await Client.updateFile(broker, "feature.res", {
    decls: ["feature"],
    refs: [("dead_util", "feature")],
    annotations: [("feature", "live")],
    optArgCalls: [("feature", "utils", ["~timezone"])],
  })
  
  await delay(300)

  logArray("Live set", ClientDCE.getLiveSet())
  logArray("Dead set", ClientDCE.getDeadSet())
  
  let utilsArgs2 = ClientDCE.getOptionalArgsReport("utils", ["~format", "~locale", "~timezone"])
  Console.log("Optional args for 'utils':")
  logArray("  Used args", utilsArgs2.used)
  logArray("  Unused args", utilsArgs2.unused)
  Console.log("  (feature's call added ~timezone!)")

  // Phase 3: Update only annotations for api.res (remove @dead)
  Console.log("")
  Console.log("--- Phase 3: Update api.res (remove @dead annotation) ---")
  Console.log("  Sending file with empty annotations:")
  Console.log("  { decls: [api, db, logger], refs: [[db,api],[logger,api]], annotations: [],")
  Console.log("    optArgCalls: api calls utils(~format, ~locale) }")
  Console.log("")
  Console.log("  ⚡ EXPECT: Only 'annotations' fragment delta sent!")
  Console.log("  ⚡ EXPECT: api becomes LIVE → its optArgCalls now count!")
  Console.log("")

  await Client.updateFile(broker, "api.res", {
    decls: ["api", "db", "logger"],
    refs: [("db", "api"), ("logger", "api")],
    annotations: [],  // Remove the @dead annotation
    optArgCalls: [("api", "utils", ["~format", "~locale"])],
  })
  
  await delay(300)

  logArray("Live set", ClientDCE.getLiveSet())
  logArray("Dead set", ClientDCE.getDeadSet())
  
  let utilsArgs3 = ClientDCE.getOptionalArgsReport("utils", ["~format", "~locale", "~timezone"])
  Console.log("Optional args for 'utils':")
  logArray("  Used args", utilsArgs3.used)
  logArray("  Unused args", utilsArgs3.unused)
  Console.log("  (api became live → ~locale now used!)")

  // Phase 4: Update only decls for utils.res
  Console.log("")
  Console.log("--- Phase 4: Update utils.res (add new_helper decl) ---")
  Console.log("  Sending file with new decl:")
  Console.log("  { decls: [utils, helpers, dead_util, new_helper], refs: [[helpers,utils]], annotations: [],")
  Console.log("    optArgCalls: [] }")
  Console.log("")
  Console.log("  ⚡ EXPECT: Only 'decls' fragment delta sent (refs/annotations unchanged)!")
  Console.log("")

  await Client.updateFile(broker, "utils.res", {
    decls: ["utils", "helpers", "dead_util", "new_helper"],
    refs: [("helpers", "utils")],
    annotations: [],
    optArgCalls: [],
  })
  
  await delay(300)

  logArray("Live set", ClientDCE.getLiveSet())
  logArray("Dead set", ClientDCE.getDeadSet())

  // Cleanup
  // Summary
  Console.log("")
  Console.log("===========================================")
  Console.log("SUMMARY: Fixpoint Update Cost")
  Console.log("===========================================")
  Console.log(`Total updates: ${ClientDCE.updateCount.contents->Int.toString}`)
  Console.log(`Total update time: ${ClientDCE.totalUpdateTimeMs.contents->Float.toString}ms`)
  Console.log(`Average per update: ${(ClientDCE.totalUpdateTimeMs.contents /. ClientDCE.updateCount.contents->Int.toFloat)->Float.toString}ms`)
  Console.log("")
  Console.log("✅ Using incremental updates via SkipruntimeFixpoint.applyChanges()")
  Console.log("   Only changed base/step elements are updated!")
  Console.log("")

  ClientDCE.close()
  await Server.stop(server)
  Console.log("Server stopped.")
  Console.log("")
  Console.log("Demo complete!")
}

let () = run()->ignore
