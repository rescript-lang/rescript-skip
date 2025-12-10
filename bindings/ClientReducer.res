/**
 * ClientReducer: Incremental aggregation with provenance tracking
 * 
 * Aggregates values from multiple sources (e.g., files) while tracking
 * which source contributed each value. This enables O(delta) updates
 * when a source's contribution changes.
 * 
 * Supports multiset semantics: the same value can come from multiple sources,
 * and is only removed from the aggregate when all sources remove it.
 */

module SetReducer = {
  /**
   * A reducer that aggregates sets from multiple sources.
   * Uses multiset counting to handle values present in multiple sources.
   */
  type t<'v> = {
    // source -> set of values contributed by that source
    mutable contributions: Map.t<string, Set.t<'v>>,
    // value -> count of sources contributing this value
    mutable counts: Map.t<'v, int>,
    // current aggregate (values with count > 0)
    mutable current: Set.t<'v>,
  }

  type delta<'v> = {
    added: array<'v>,    // Values newly added to aggregate
    removed: array<'v>,  // Values removed from aggregate
  }

  let make = (): t<'v> => {
    contributions: Map.make(),
    counts: Map.make(),
    current: Set.make(),
  }

  /**
   * Set the contribution from a source.
   * Returns the delta: what changed in the aggregate.
   */
  let setContribution = (reducer: t<'v>, ~source: string, ~values: Set.t<'v>): delta<'v> => {
    let oldValues = reducer.contributions->Map.get(source)->Option.getOr(Set.make())
    
    // Compute what this source added/removed
    let sourceAdded = []
    let sourceRemoved = []
    
    // Find values added by this source
    values->Set.forEach(v => {
      if !(oldValues->Set.has(v)) {
        sourceAdded->Array.push(v)->ignore
      }
    })
    
    // Find values removed by this source
    oldValues->Set.forEach(v => {
      if !(values->Set.has(v)) {
        sourceRemoved->Array.push(v)->ignore
      }
    })
    
    // Update contributions
    if values->Set.size == 0 {
      reducer.contributions->Map.delete(source)->ignore
    } else {
      reducer.contributions->Map.set(source, values)->ignore
    }
    
    // Track what changed in the aggregate
    let aggregateAdded = []
    let aggregateRemoved = []
    
    // Process additions: increment count, add to aggregate if count goes 0→1
    sourceAdded->Array.forEach(v => {
      let oldCount = reducer.counts->Map.get(v)->Option.getOr(0)
      let newCount = oldCount + 1
      reducer.counts->Map.set(v, newCount)->ignore
      
      if oldCount == 0 {
        // Value is new to aggregate
        reducer.current->Set.add(v)->ignore
        aggregateAdded->Array.push(v)->ignore
      }
    })
    
    // Process removals: decrement count, remove from aggregate if count goes 1→0
    sourceRemoved->Array.forEach(v => {
      let oldCount = reducer.counts->Map.get(v)->Option.getOr(0)
      let newCount = max(0, oldCount - 1)
      
      if newCount == 0 {
        reducer.counts->Map.delete(v)->ignore
        reducer.current->Set.delete(v)->ignore
        aggregateRemoved->Array.push(v)->ignore
      } else {
        reducer.counts->Map.set(v, newCount)->ignore
      }
    })
    
    {added: aggregateAdded, removed: aggregateRemoved}
  }

  /**
   * Convenience: set contribution from an array
   */
  let setContributionArray = (reducer: t<'v>, ~source: string, ~values: array<'v>): delta<'v> => {
    setContribution(reducer, ~source, ~values=Set.fromArray(values))
  }

  /**
   * Delete a source's contribution entirely
   */
  let deleteSource = (reducer: t<'v>, ~source: string): delta<'v> => {
    setContribution(reducer, ~source, ~values=Set.make())
  }

  /**
   * Get current aggregate as array
   */
  let currentArray = (reducer: t<'v>): array<'v> => {
    reducer.current->Set.values->Iterator.toArray
  }

  /**
   * Get current aggregate as set
   */
  let currentSet = (reducer: t<'v>): Set.t<'v> => {
    reducer.current
  }
}

module MapReducer = {
  /**
   * A reducer that aggregates maps from multiple sources.
   * For overlapping keys, later sources win (last-write-wins).
   * Tracks provenance to enable correct removal.
   */
  type t<'k, 'v> = {
    // source -> map contributed by that source
    mutable contributions: Map.t<string, Map.t<'k, 'v>>,
    // key -> array of (source, value) pairs
    mutable provenance: Map.t<'k, array<(string, 'v)>>,
    // current aggregate
    mutable current: Map.t<'k, 'v>,
  }

  type delta<'k, 'v> = {
    added: array<('k, 'v)>,      // Keys newly added or changed
    removed: array<'k>,          // Keys removed from aggregate
  }

  let make = (): t<'k, 'v> => {
    contributions: Map.make(),
    provenance: Map.make(),
    current: Map.make(),
  }

  /**
   * Set the contribution from a source.
   * Returns the delta: what changed in the aggregate.
   */
  let setContribution = (reducer: t<'k, 'v>, ~source: string, ~values: Map.t<'k, 'v>): delta<'k, 'v> => {
    let oldMap = reducer.contributions->Map.get(source)->Option.getOr(Map.make())
    
    let aggregateAdded = []
    let aggregateRemoved = []
    
    // Remove old contributions from this source
    oldMap->Map.entries->Iterator.forEach(entry => {
      let (key, _) = entry
      switch reducer.provenance->Map.get(key) {
      | Some(sources) =>
        let newSources = sources->Array.filter(((s, _)) => s != source)
        if newSources->Array.length == 0 {
          // No more sources for this key
          reducer.provenance->Map.delete(key)->ignore
          reducer.current->Map.delete(key)->ignore
          aggregateRemoved->Array.push(key)->ignore
        } else {
          reducer.provenance->Map.set(key, newSources)->ignore
          // Update current to last remaining source's value
          let (_, lastValue) = newSources[newSources->Array.length - 1]->Option.getOrThrow
          let oldValue = reducer.current->Map.get(key)
          reducer.current->Map.set(key, lastValue)->ignore
          if oldValue != Some(lastValue) {
            aggregateAdded->Array.push((key, lastValue))->ignore
          }
        }
      | None => ()
      }
    })
    
    // Add new contributions from this source
    values->Map.entries->Iterator.forEach(entry => {
      let (key, value) = entry
      let sources = reducer.provenance->Map.get(key)->Option.getOr([])
      let newSources = sources->Array.concat([(source, value)])
      reducer.provenance->Map.set(key, newSources)->ignore
      
      let oldValue = reducer.current->Map.get(key)
      reducer.current->Map.set(key, value)->ignore
      
      if oldValue != Some(value) {
        // Remove from removed list if we're re-adding
        // (already handled above, but value changed)
        aggregateAdded->Array.push((key, value))->ignore
      }
    })
    
    // Update contributions
    if values->Map.size == 0 {
      reducer.contributions->Map.delete(source)->ignore
    } else {
      reducer.contributions->Map.set(source, values)->ignore
    }
    
    {added: aggregateAdded, removed: aggregateRemoved}
  }

  /**
   * Delete a source's contribution entirely
   */
  let deleteSource = (reducer: t<'k, 'v>, ~source: string): delta<'k, 'v> => {
    setContribution(reducer, ~source, ~values=Map.make())
  }

  /**
   * Get current aggregate
   */
  let currentMap = (reducer: t<'k, 'v>): Map.t<'k, 'v> => {
    reducer.current
  }

  /**
   * Get current value for a key
   */
  let get = (reducer: t<'k, 'v>, key: 'k): option<'v> => {
    reducer.current->Map.get(key)
  }
}

module ArrayReducer = {
  /**
   * A reducer that concatenates arrays from multiple sources.
   * Maintains the full array, tracking which elements came from which source.
   */
  type t<'v> = {
    // source -> array contributed by that source
    mutable contributions: Map.t<string, array<'v>>,
    // current aggregate (concatenation of all sources)
    mutable current: array<'v>,
  }

  type delta<'v> = {
    added: array<'v>,
    removed: array<'v>,
  }

  let make = (): t<'v> => {
    contributions: Map.make(),
    current: [],
  }

  // Recompute current from all contributions
  let recompute = (reducer: t<'v>) => {
    let result = []
    reducer.contributions->Map.values->Iterator.forEach(arr => {
      arr->Array.forEach(v => result->Array.push(v)->ignore)
    })
    reducer.current = result
  }

  /**
   * Set the contribution from a source.
   * Returns the delta: what changed in the aggregate.
   */
  let setContribution = (reducer: t<'v>, ~source: string, ~values: array<'v>): delta<'v> => {
    let oldValues = reducer.contributions->Map.get(source)->Option.getOr([])
    
    // For arrays, we track simple add/remove at source level
    // The aggregate delta is the source delta
    let added = values
    let removed = oldValues
    
    // Update contributions
    if values->Array.length == 0 {
      reducer.contributions->Map.delete(source)->ignore
    } else {
      reducer.contributions->Map.set(source, values)->ignore
    }
    
    recompute(reducer)
    
    {added, removed}
  }

  /**
   * Delete a source's contribution entirely
   */
  let deleteSource = (reducer: t<'v>, ~source: string): delta<'v> => {
    setContribution(reducer, ~source, ~values=[])
  }

  /**
   * Get current aggregate
   */
  let currentArray = (reducer: t<'v>): array<'v> => {
    reducer.current
  }
}

