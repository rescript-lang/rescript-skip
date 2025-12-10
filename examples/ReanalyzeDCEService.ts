/**
 * Reanalyze DCE Service - Dis-aggregation Pattern
 * 
 * This service receives COMPLETE file data and DIS-AGGREGATES it into
 * fine-grained keys so the client receives small deltas.
 * 
 * Input: Single collection `files` with key=filename, value=complete file data
 *   files["main.res"] = { decls: [...], refs: [...], annotations: [...] }
 * 
 * Output: Disaggregated collection with composite keys
 *   ("main.res", "decls") → [...]
 *   ("main.res", "refs") → [...]
 *   ("main.res", "annotations") → [...]
 * 
 * When a file changes, Skip compares each output key's new value to old value
 * and only sends deltas for keys whose values actually changed.
 */
import {
  type Context,
  type EagerCollection,
  type Json,
  type Mapper,
  type Resource,
  type SkipService,
  type Values,
} from "@skipruntime/core";

// ============================================================================
// Types
// ============================================================================

// Complete file data bundled together
type FileData = {
  decls: string[];                      // declarations in this file
  refs: [string, string][];             // [target, source] pairs
  annotations: [string, "live" | "dead"][]; // [position, annotation] pairs
  optArgCalls: [string, string, string[]][]; // [caller, fn, passed_args] - optional arg usage
};

// Fragment key is [filename, fragmentType]
type FragmentKey = [string, string];

// Fragment value - use Json for flexibility
type FragmentValue = Json;

type InputCollections = {
  files: EagerCollection<string, FileData>;
};

type OutputCollections = {
  files: EagerCollection<string, FileData>;
  fragments: EagerCollection<FragmentKey, FragmentValue>;
};

// ============================================================================
// Dis-aggregation Mapper
// ============================================================================

/**
 * FileDisaggregator: Splits complete file data into separate keyed fragments.
 * 
 * Input:  "main.res" → { decls: [...], refs: [...], annotations: [...] }
 * Output: [
 *   [["main.res", "decls"], [...]],
 *   [["main.res", "refs"], [...]],
 *   [["main.res", "annotations"], [...]]
 * ]
 * 
 * This allows Skip to detect which specific fragment changed and send
 * minimal deltas to clients.
 */
class FileDisaggregator implements Mapper<string, FileData, FragmentKey, FragmentValue> {
  mapEntry(
    filename: string,
    values: Values<FileData>,
    _ctx: Context
  ): Iterable<[FragmentKey, FragmentValue]> {
    const file = values.getUnique();
    // Returns [key, value] tuples - one input produces four outputs
    return [
      [[filename, "decls"], file.decls as Json],
      [[filename, "refs"], file.refs as Json],
      [[filename, "annotations"], file.annotations as Json],
      [[filename, "optArgCalls"], file.optArgCalls as Json],
    ];
  }
}

// ============================================================================
// Resources
// ============================================================================

/**
 * Raw files resource - exposes the input collection directly
 */
class FilesResource implements Resource<OutputCollections> {
  instantiate(collections: OutputCollections): EagerCollection<string, FileData> {
    return collections.files;
  }
}

/**
 * Fragments resource - exposes the disaggregated data
 * 
 * Clients subscribe to this and receive deltas like:
 *   key=["api.res", "annotations"] changed → new value
 */
class FragmentsResource implements Resource<OutputCollections> {
  instantiate(collections: OutputCollections): EagerCollection<FragmentKey, FragmentValue> {
    return collections.fragments;
  }
}

// ============================================================================
// Service Definition
// ============================================================================

export const service: SkipService<InputCollections, OutputCollections> = {
  initialData: {
    files: [
      ["main.res", [{
        decls: ["main", "unused_in_main"],
        refs: [["utils", "main"], ["api", "main"]],
        annotations: [["main", "live"]],
        optArgCalls: [
          // main calls utils with ~format arg
          ["main", "utils", ["~format"]],
        ],
      }]],
      ["utils.res", [{
        // utils has optional args: ~format, ~locale, ~timezone
        decls: ["utils", "helpers", "dead_util"],
        refs: [["helpers", "utils"]],
        annotations: [],
        optArgCalls: [],
      }]],
      ["api.res", [{
        decls: ["api", "db", "logger"],
        refs: [["db", "api"], ["logger", "api"]],
        annotations: [["api", "dead"]],
        optArgCalls: [
          // api calls utils with ~format and ~locale (but api is @dead!)
          ["api", "utils", ["~format", "~locale"]],
        ],
      }]],
    ],
  },
  resources: {
    files: FilesResource,
    fragments: FragmentsResource,
  },
  createGraph: (inputs: InputCollections): OutputCollections => {
    // Disaggregate files into fragments
    const fragments = inputs.files.map(FileDisaggregator);
    return {
      files: inputs.files,
      fragments,
    };
  },
};
