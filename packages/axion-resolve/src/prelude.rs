/// The Axion prelude source, prepended to every compilation unit.
pub const PRELUDE_SOURCE: &str = r#"pub enum Option[T]
    Some(value: T)
    None

pub enum Result[T, E]
    Ok(value: T)
    Err(error: E)

fn abs(x: i64) -> i64
    if x < 0
        0 - x
    else
        x

fn min(a: i64, b: i64) -> i64
    if a < b
        a
    else
        b

fn max(a: i64, b: i64) -> i64
    if a > b
        a
    else
        b
"#;

/// Prepend the prelude to user source.
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let prelude_lines = PRELUDE_SOURCE.lines().count();
    let combined = format!("{}\n{}", PRELUDE_SOURCE, user_source);
    (combined, prelude_lines + 1) // +1 for separator newline
}
