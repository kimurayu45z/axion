/// The Axion prelude sources, loaded from stdlib/ at compile time.
pub const PRELUDE_FFI: &str = include_str!("../../../stdlib/ffi.ax");
pub const PRELUDE_NUMBER: &str = include_str!("../../../stdlib/number.ax");
pub const PRELUDE_OPTION: &str = include_str!("../../../stdlib/option.ax");
pub const PRELUDE_RESULT: &str = include_str!("../../../stdlib/result.ax");
pub const PRELUDE_ITER: &str = include_str!("../../../stdlib/iter.ax");
pub const PRELUDE_RANGE: &str = include_str!("../../../stdlib/range.ax");
pub const PRELUDE_MATH: &str = include_str!("../../../stdlib/math.ax");
pub const PRELUDE_STR: &str = include_str!("../../../stdlib/str.ax");
pub const PRELUDE_STRING: &str = include_str!("../../../stdlib/string.ax");
pub const PRELUDE_ARRAY: &str = include_str!("../../../stdlib/array.ax");
pub const PRELUDE_IO: &str = include_str!("../../../stdlib/io.ax");
pub const PRELUDE_LOG: &str = include_str!("../../../stdlib/log.ax");

/// Collection module sources (included in prelude for resolution, but not auto-imported).
pub const COLLECTION_HASHMAP: &str = include_str!("../../../stdlib/collection/hashmap.ax");
pub const COLLECTION_HASHSET: &str = include_str!("../../../stdlib/collection/hashset.ax");
pub const COLLECTION_BTREEMAP: &str = include_str!("../../../stdlib/collection/btreemap.ax");
pub const COLLECTION_BTREESET: &str = include_str!("../../../stdlib/collection/btreeset.ax");

/// A boundary marker for one stdlib file within the combined prelude source.
#[derive(Debug, Clone)]
pub struct StdFileBoundary {
    /// The module name (e.g. "math", "option", "collection").
    pub name: String,
    /// Byte offset where this file starts in the combined source.
    pub start: usize,
    /// Byte offset where this file ends in the combined source.
    pub end: usize,
    /// Whether symbols from this module are auto-imported into every user module.
    /// If false, symbols are only available via explicit `use std.<module>.*` imports.
    pub auto_import: bool,
}

/// A separately-parsed stdlib module (not part of the prelude source at all).
#[derive(Debug, Clone)]
pub struct StdAuxModule {
    pub name: String,
    pub source: &'static str,
}

/// Get the combined prelude source (without user source).
pub fn prelude_source() -> String {
    prelude_source_with_boundaries().0
}

/// Get the combined prelude source together with per-file byte boundaries.
///
/// Returns `(combined_source, boundaries)` where each boundary records which
/// stdlib file occupies which byte range in the combined source.
///
/// Includes ALL modules (auto-import and non-auto-import). The `auto_import`
/// flag on each boundary controls whether symbols are injected automatically.
pub fn prelude_source_with_boundaries() -> (String, Vec<StdFileBoundary>) {
    // (name, source, auto_import)
    let files: &[(&str, &str, bool)] = &[
        ("ffi", PRELUDE_FFI, true),
        ("number", PRELUDE_NUMBER, true),
        ("option", PRELUDE_OPTION, true),
        ("result", PRELUDE_RESULT, true),
        ("iter", PRELUDE_ITER, true),
        ("range", PRELUDE_RANGE, true),
        ("math", PRELUDE_MATH, true),
        ("str", PRELUDE_STR, true),
        ("string", PRELUDE_STRING, true),
        ("array", PRELUDE_ARRAY, true),
        ("collection", COLLECTION_HASHMAP, false),
        ("collection", COLLECTION_HASHSET, false),
        ("collection", COLLECTION_BTREEMAP, false),
        ("collection", COLLECTION_BTREESET, false),
    ];

    let mut combined = String::new();
    let mut boundaries = Vec::new();

    for (i, (name, src, auto_import)) in files.iter().enumerate() {
        let start = combined.len();
        combined.push_str(src);
        if i + 1 < files.len() {
            combined.push('\n');
        }
        let end = combined.len();
        boundaries.push(StdFileBoundary {
            name: name.to_string(),
            start,
            end,
            auto_import: *auto_import,
        });
    }

    (combined, boundaries)
}

/// Returns stdlib modules that are NOT part of the prelude source at all.
/// These are parsed separately and available only via explicit `use std.<module>.*`.
pub fn aux_std_modules() -> Vec<StdAuxModule> {
    vec![
        StdAuxModule { name: "io".to_string(), source: PRELUDE_IO },
        StdAuxModule { name: "log".to_string(), source: PRELUDE_LOG },
    ]
}

/// Prepend the prelude to user source (auto-import modules only).
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let combined = format!(
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        PRELUDE_FFI, PRELUDE_NUMBER, PRELUDE_OPTION, PRELUDE_RESULT,
        PRELUDE_ITER, PRELUDE_RANGE, PRELUDE_MATH, PRELUDE_STR,
        PRELUDE_STRING, PRELUDE_ARRAY, user_source
    );
    let prelude_lines = PRELUDE_FFI.lines().count()
        + PRELUDE_NUMBER.lines().count()
        + PRELUDE_OPTION.lines().count()
        + PRELUDE_RESULT.lines().count()
        + PRELUDE_ITER.lines().count()
        + PRELUDE_RANGE.lines().count()
        + PRELUDE_MATH.lines().count()
        + PRELUDE_STR.lines().count()
        + PRELUDE_STRING.lines().count()
        + PRELUDE_ARRAY.lines().count()
        + 10;
    (combined, prelude_lines)
}

/// Prepend the prelude AND collection sources to user source.
/// Used by tests that need HashMap/HashSet/BTreeMap/BTreeSet.
pub fn with_prelude_and_collections(user_source: &str) -> (String, usize) {
    let combined = format!(
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        PRELUDE_FFI, PRELUDE_NUMBER, PRELUDE_OPTION, PRELUDE_RESULT,
        PRELUDE_ITER, PRELUDE_RANGE, PRELUDE_MATH, PRELUDE_STR,
        PRELUDE_STRING, PRELUDE_ARRAY,
        COLLECTION_HASHMAP, COLLECTION_HASHSET,
        COLLECTION_BTREEMAP, COLLECTION_BTREESET,
        user_source
    );
    let prelude_lines = PRELUDE_FFI.lines().count()
        + PRELUDE_NUMBER.lines().count()
        + PRELUDE_OPTION.lines().count()
        + PRELUDE_RESULT.lines().count()
        + PRELUDE_ITER.lines().count()
        + PRELUDE_RANGE.lines().count()
        + PRELUDE_MATH.lines().count()
        + PRELUDE_STR.lines().count()
        + PRELUDE_STRING.lines().count()
        + PRELUDE_ARRAY.lines().count()
        + COLLECTION_HASHMAP.lines().count()
        + COLLECTION_HASHSET.lines().count()
        + COLLECTION_BTREEMAP.lines().count()
        + COLLECTION_BTREESET.lines().count()
        + 14;
    (combined, prelude_lines)
}
