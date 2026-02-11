/// The Axion prelude sources, loaded from stdlib/ at compile time.
pub const PRELUDE_OPTION: &str = include_str!("../../../stdlib/option.ax");
pub const PRELUDE_RESULT: &str = include_str!("../../../stdlib/result.ax");
pub const PRELUDE_MATH: &str = include_str!("../../../stdlib/math.ax");

/// Prepend the prelude to user source.
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let combined = format!("{}\n{}\n{}\n{}", PRELUDE_OPTION, PRELUDE_RESULT, PRELUDE_MATH, user_source);
    let prelude_lines = PRELUDE_OPTION.lines().count()
        + PRELUDE_RESULT.lines().count()
        + PRELUDE_MATH.lines().count()
        + 3;
    (combined, prelude_lines)
}
