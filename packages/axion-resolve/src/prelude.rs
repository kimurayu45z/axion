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

fn clamp(x: i64, lo: i64, hi: i64) -> i64
    if x < lo
        lo
    else
        if x > hi
            hi
        else
            x

fn sign(x: i64) -> i64
    if x > 0
        1
    else
        if x < 0
            0 - 1
        else
            0

fn unwrap_or[T](opt: Option[T], default: T) -> T
    match opt
        Option[T].Some(v) => v
        Option[T].None => default

fn map_option[T, U](opt: Option[T], f: Fn(T) -> U) -> Option[U]
    match opt
        Option[T].Some(v) => Option[U].Some(f(v))
        Option[T].None => Option[U].None

fn unwrap_or_ok[T, E](res: Result[T, E], default: T) -> T
    match res
        Result[T, E].Ok(v) => v
        Result[T, E].Err(_) => default

fn map_result[T, U, E](res: Result[T, E], f: Fn(T) -> U) -> Result[U, E]
    match res
        Result[T, E].Ok(v) => Result[U, E].Ok(f(v))
        Result[T, E].Err(e) => Result[U, E].Err(e)

fn is_some[T](opt: Option[T]) -> i64
    match opt
        Option[T].Some(_) => 1
        Option[T].None => 0

fn is_none[T](opt: Option[T]) -> i64
    match opt
        Option[T].Some(_) => 0
        Option[T].None => 1

fn is_ok[T, E](res: Result[T, E]) -> i64
    match res
        Result[T, E].Ok(_) => 1
        Result[T, E].Err(_) => 0

fn is_err[T, E](res: Result[T, E]) -> i64
    match res
        Result[T, E].Ok(_) => 0
        Result[T, E].Err(_) => 1
"#;

/// Prepend the prelude to user source.
/// Returns (combined_source, prelude_line_count).
pub fn with_prelude(user_source: &str) -> (String, usize) {
    let prelude_lines = PRELUDE_SOURCE.lines().count();
    let combined = format!("{}\n{}", PRELUDE_SOURCE, user_source);
    (combined, prelude_lines + 1) // +1 for separator newline
}
