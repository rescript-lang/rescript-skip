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
class FileDisaggregator {
    mapEntry(filename, values, _ctx) {
        const file = values.getUnique();
        // Returns [key, value] tuples - one input produces four outputs
        return [
            [[filename, "decls"], file.decls],
            [[filename, "refs"], file.refs],
            [[filename, "annotations"], file.annotations],
            [[filename, "optArgCalls"], file.optArgCalls],
        ];
    }
}
// ============================================================================
// Resources
// ============================================================================
/**
 * Raw files resource - exposes the input collection directly
 */
class FilesResource {
    instantiate(collections) {
        return collections.files;
    }
}
/**
 * Fragments resource - exposes the disaggregated data
 *
 * Clients subscribe to this and receive deltas like:
 *   key=["api.res", "annotations"] changed → new value
 */
class FragmentsResource {
    instantiate(collections) {
        return collections.fragments;
    }
}
// ============================================================================
// Service Definition
// ============================================================================
export const service = {
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
    createGraph: (inputs) => {
        // Disaggregate files into fragments
        const fragments = inputs.files.map(FileDisaggregator);
        return {
            files: inputs.files,
            fragments,
        };
    },
};
