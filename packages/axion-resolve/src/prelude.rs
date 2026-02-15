/// The Axion prelude sources, loaded from stdlib/ at compile time.
pub const PRELUDE_FFI: &str = include_str!("../../../stdlib/ffi.ax");
pub const PRELUDE_NUMBER: &str = include_str!("../../../stdlib/number.ax");
pub const PRELUDE_OPTION: &str = include_str!("../../../stdlib/option.ax");
pub const PRELUDE_RESULT: &str = include_str!("../../../stdlib/result.ax");
pub const PRELUDE_ITER: &str = include_str!("../../../stdlib/iter.ax");
pub const PRELUDE_RANGE: &str = include_str!("../../../stdlib/range.ax");
pub const PRELUDE_MATH: &str = include_str!("../../../stdlib/math.ax");
pub const PRELUDE_STRING: &str = include_str!("../../../stdlib/string.ax");
pub const PRELUDE_ARRAY: &str = include_str!("../../../stdlib/array.ax");
pub const PRELUDE_HASHMAP: &str = include_str!("../../../stdlib/hashmap.ax");

/// A boundary marker for one stdlib file within the combined prelude source.
#[derive(Debug, Clone)]
pub struct StdFileBoundary {
    /// The module name (e.g. "math", "option").
    pub name: String,
    /// Byte offset where this file starts in the combined source.
    pub start: usize,
    /// Byte offset where this file ends in the combined source.
    pub end: usize,
}

/// Get the combined prelude source (without user source).
pub fn prelude_source() -> String {
    prelude_source_with_boundaries().0
}

/// Get the combined prelude source together with per-file byte boundaries.
///
/// Returns `(combined_source, boundaries)` where each boundary records which
/// stdlib file occupies which byte range in the combined source.
pub fn prelude_source_with_boundaries() -> (String, Vec<StdFileBoundary>) {
    let files: &[(&str, &str)] = &[
        ("ffi", PRELUDE_FFI),
        ("number", PRELUDE_NUMBER),
        ("option", PRELUDE_OPTION),
        ("result", PRELUDE_RESULT),
        ("iter", PRELUDE_ITER),
        ("range", PRELUDE_RANGE),
        ("math", PRELUDE_MATH),
        ("string", PRELUDE_STRING),
        ("array", PRELUDE_ARRAY),
        ("hashmap", PRELUDE_HASHMAP),
    ];

    let mut combined = String::new();
    let mut boundaries = Vec::new();

    for (i, (name, src)) in files.iter().enumerate() {
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
        });
    }

    (combined, boundaries)
}

/// Prepend the prelude to user source.
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let combined = format!(
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        PRELUDE_FFI, PRELUDE_NUMBER, PRELUDE_OPTION, PRELUDE_RESULT, PRELUDE_ITER, PRELUDE_RANGE, PRELUDE_MATH, PRELUDE_STRING, PRELUDE_ARRAY, PRELUDE_HASHMAP, user_source
    );
    let prelude_lines = PRELUDE_FFI.lines().count()
        + PRELUDE_NUMBER.lines().count()
        + PRELUDE_OPTION.lines().count()
        + PRELUDE_RESULT.lines().count()
        + PRELUDE_ITER.lines().count()
        + PRELUDE_RANGE.lines().count()
        + PRELUDE_MATH.lines().count()
        + PRELUDE_STRING.lines().count()
        + PRELUDE_ARRAY.lines().count()
        + PRELUDE_HASHMAP.lines().count()
        + 10;
    (combined, prelude_lines)
}
