/// The Axion prelude sources, loaded from stdlib/ at compile time.
pub const PRELUDE_NUMBER: &str = include_str!("../../../stdlib/number.ax");
pub const PRELUDE_OPTION: &str = include_str!("../../../stdlib/option.ax");
pub const PRELUDE_RESULT: &str = include_str!("../../../stdlib/result.ax");
pub const PRELUDE_ITER: &str = include_str!("../../../stdlib/iter.ax");
pub const PRELUDE_RANGE: &str = include_str!("../../../stdlib/range.ax");
pub const PRELUDE_MATH: &str = include_str!("../../../stdlib/math.ax");
pub const PRELUDE_STRING: &str = include_str!("../../../stdlib/string.ax");
pub const PRELUDE_ARRAY: &str = include_str!("../../../stdlib/array.ax");

/// Prepend the prelude to user source.
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let combined = format!(
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        PRELUDE_NUMBER, PRELUDE_OPTION, PRELUDE_RESULT, PRELUDE_ITER, PRELUDE_RANGE, PRELUDE_MATH, PRELUDE_STRING, PRELUDE_ARRAY, user_source
    );
    let prelude_lines = PRELUDE_NUMBER.lines().count()
        + PRELUDE_OPTION.lines().count()
        + PRELUDE_RESULT.lines().count()
        + PRELUDE_ITER.lines().count()
        + PRELUDE_RANGE.lines().count()
        + PRELUDE_MATH.lines().count()
        + PRELUDE_STRING.lines().count()
        + PRELUDE_ARRAY.lines().count()
        + 8;
    (combined, prelude_lines)
}
