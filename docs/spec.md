# Axion Language Specification v0.1

**A Programming Language Designed for AI-First Code Generation**

Draft — 2026-02-07

---

## 0. Design Philosophy

Axion（アクシオン）は、LLM による自動コード生成を第一級の設計目標とするシステムプログラミング言語である。以下の原則に従う：

1. **Deterministic Surface（決定論的表層）** — 同一の意図に対して、文法的に正しい書き方が唯一つだけ存在する
2. **Zero-Cost Abstraction（ゼロコスト抽象化）** — ランタイムコストを伴わない抽象化を保証する
3. **Compiler-Owned Complexity（コンパイラが複雑性を引き受ける）** — メモリ管理・ライフタイム・リージョンの推論はコンパイラの責務とする
4. **Typed Effects（型付きエフェクト）** — すべての副作用を型システムで追跡する
5. **Machine-Readable Diagnostics（機械可読診断）** — エラー・警告を構造化データとして出力する

---

## 1. Lexical Structure

### 1.1 Source Encoding

- ソースファイルは UTF-8 のみ
- 拡張子: `.ax`
- BOM 禁止

### 1.2 Keywords（予約語）

以下の 28 語のみを予約語とする。拡張予約語は存在しない。

```
fn  let  mut  type  struct  enum  trait  impl
match  if  else  for  in  return  break  continue
use  mod  pub  self  Self  true  false  with
where  as  const  test
```

### 1.3 Identifiers

```
identifier     = [a-z_][a-z0-9_]*        // 値・関数・変数
type_ident     = [A-Z][A-Za-z0-9]*       // 型・トレイト
module_ident   = [a-z][a-z0-9_]*         // モジュール
```

- `snake_case` を値に、`PascalCase` を型に強制（コンパイルエラー）
- `_` は Rust と同様に「未使用バインディング」を表す特別な識別子（パターン内でのワイルドカード、代入先としての破棄）

**組み込みプリミティブ型**はすべて小文字（Rust と同様）：
`bool`, `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128`,
`f16`, `f32`, `f64`, `bf16`, `str`, `char`, `never`, `usize`
これらは `type_ident` ルールの例外であり、予約された型名として扱われる。
単位型は空タプル `{}` で表現する（`unit` キーワードは存在しない）。

### 1.4 Layout Rule（レイアウトルール）

- インデントベース（Haskell 方式）
- インデント幅は **4 スペース固定**（タブ禁止、他のスペース数はコンパイルエラー）
- セミコロン不要
- 行継続は末尾の演算子で暗黙に決定される

```
// 正しい
let result = long_expression
    + another_expression

// コンパイルエラー: 演算子が行頭
let result = long_expression
+ another_expression
```

### 1.5 Comments

```
// 行コメント（唯一のコメント形式）

/// ドキュメントコメント（構造化メタデータ付き）
/// @param x 入力テンソル
/// @returns 正規化されたテンソル
/// @effect IO
/// @complexity O(n)
/// @example
///   let y = normalize(tensor![1.0, 2.0, 3.0])
```

- ブロックコメント `/* */` は存在しない（ネスト問題を排除）
- ドキュメントコメントはセマンティックタグ付き（コンパイラが検証）

---

## 2. Type System

### 2.1 Primitive Types

| Type | Size | Description |
|------|------|-------------|
| `bool` | 1 byte | `true` / `false` |
| `i8`, `i16`, `i32`, `i64`, `i128` | N/8 bytes | 符号付き整数 |
| `u8`, `u16`, `u32`, `u64`, `u128` | N/8 bytes | 符号なし整数 |
| `f16`, `f32`, `f64` | N/8 bytes | IEEE 754 浮動小数点 |
| `bf16` | 2 bytes | Brain floating point |
| `str` | fat pointer | UTF-8 文字列（不変） |
| `char` | 4 bytes | Unicode scalar value |
| `{}` | 0 bytes | 単位型（空タプル） |
| `never` | 0 bytes | ボトム型（到達不能） |

- **暗黙の型変換は一切存在しない**（`i32` → `i64` も明示的）
- 数値リテラルは接尾辞で型を決定: `42_i32`, `3.14_f64`
- 接尾辞省略時のデフォルト: 整数 → `i64`, 浮動小数点 → `f64`

### 2.2 Compound Types

```
// タプル（波括弧で囲む）
type Point = {f64, f64}

// タプルリテラル
let origin = {0.0, 0.0}
let unit_val = {}              // 空タプル = 単位型

// 配列（固定長、スタック確保）
type Matrix = Array[f64, 3, 3]

// スライス（ファットポインタ）
type Slice = Span[f64]

// ベクタ（ヒープ確保、可変長）
type Items = Vec[f64]

// マップ（順序保証ハッシュマップ）— リテラルは #{ key => value }
type Config = Map[str, Value]
let headers = #{"Content-Type" => "application/json", "Accept" => "*/*"}

// セット — リテラルは #{ value, ... }
type Ids = Set[i64]
let primes = #{2, 3, 5, 7, 11}

// オプション
type MaybeInt = Option[i64]    // Some(x) | None

// 結果
type ParseResult = Result[Ast, ParseError]  // Ok(x) | Err(e)
```

### 2.3 Struct（構造体）

```
struct User
    name: str
    age: u32
    email: str

// 構築 — #{ } でフィールドを指定
let user = User #{name: "Alice", age: 30, email: "alice@example.com"}

// 複数行
let user = User #{
    name: "Alice",
    age: 30,
    email: "alice@example.com",
}
```

- フィールドはデフォルトで不変・private
- `pub` で公開、`mut` で可変を明示

```
struct Counter
    pub mut count: i64
    max_count: i64
```

### 2.4 Enum（代数的データ型）

```
enum Shape
    Circle(radius: f64)
    Rect(width: f64, height: f64)
    Point

// パターンマッチは網羅性を強制
fn area(shape: Shape) -> f64
    match shape
        Shape.Circle(r) => f64.pi() * r * r
        Shape.Rect(w, h) => w * h
        Shape.Point => 0.0
```

- すべての `match` は網羅的でなければならない（ワイルドカード `_` で省略可）
- ネストしたパターンマッチを許可

### 2.5 Generics（ジェネリクス）

```
fn first[T](items: Vec[T]) -> Option[T]
    if items.is_empty()
        None
    else
        Some(items.get(0))
```

- Monomorphization により実行時コストゼロ
- 型パラメータは `[T]` で囲む（`<T>` ではない — `<` / `>` の比較演算子との曖昧性を排除）

### 2.6 Trait（トレイト）

```
trait Hashable
    fn hash(self) -> u64

trait Printable
    fn to_str(self) -> str

// 実装
impl Hashable for User
    fn hash(self) -> u64
        hash.combine(self.name.hash(), self.age.hash())

// トレイト境界
fn lookup[K: Hashable + Eq, V](table: Map[K, V], key: K) -> Option[V]
    table.get(key)
```

- トレイトは Rust と同様のコヒーレンスルールに従う
- **デフォルト実装を許可**するが、ダイアモンド継承は禁止
- `dyn Trait` による動的ディスパッチも可能（vtable ベース）

### 2.7 Type Aliases & Newtypes

```
// エイリアス（同一型、コンパイル時に消える）
type UserId = i64

// Newtype（別の型として扱われる、ゼロコスト）
type Email = newtype str
    fn validate(s: str) -> Result[Email, ValidationError]
        if s.contains("@")
            Ok(Email(s))
        else
            Err(ValidationError.invalid_format("email"))
```

---

## 3. Memory Model

### 3.1 Design Principle

Axion のメモリモデルは **Region-Based Memory Management（リージョンベースメモリ管理）** を採用する。Rust のライフタイムアノテーションに相当するものをプログラマが記述する必要はない。コンパイラが以下を自動的に推論する：

1. 各値がどのリージョン（メモリ領域）に属するか
2. いつそのリージョンを解放できるか
3. 値の move / copy / borrow をどのように行うか

### 3.2 Value Semantics（値セマンティクス）

```
// デフォルトは所有権の移動（move）
let a = Vec.from([1, 2, 3])
let b = a                  // a は move される
// a.len()                 // コンパイルエラー: a は既に move 済み

// Copy トレイトを実装する型は暗黙にコピー
let x: i64 = 42
let y = x                  // copy（x は引き続き有効）
```

### 3.3 Borrowing（自動借用）

ライフタイムアノテーションは不要。コンパイラが自動で解決する。

```
fn first_word(text: str) -> str
    // コンパイラが text への借用を推論
    // ライフタイムは呼び出し元のスコープから自動決定
    text.split(" ").first().unwrap_or("")

fn process(items: Vec[Item]) -> Summary
    // items は不変借用として渡される（コンパイラ判断）
    let total = items.iter().map(|x| x.value).sum()
    Summary #{total, count: items.len()}
```

**コンパイラの推論アルゴリズム：**

1. 関数シグネチャから入出力の所有権関係を制約として抽出
2. 関数本体の使用パターンからリージョン制約を生成
3. 制約充足ソルバ（HM ベース拡張）でリージョンを割り当て
4. 解が一意でない場合はコンパイルエラー（曖昧性排除）

### 3.4 Mutable References（可変参照）

```
fn increment(mut counter: Counter)
    counter.count = counter.count + 1

// 排他的可変性の保証（Rust と同等）
let mut c = Counter #{count: 0, max_count: 100}
increment(mut c)        // `mut` を呼び出し側でも明示（意図の明確化）
```

- 可変参照と不変参照の同時存在はコンパイルエラー
- `mut` キーワードは定義側と使用側の両方に必要（AI が副作用の有無を明確に認識できる）

### 3.5 Arena Allocator（アリーナアロケータ）

パフォーマンスクリティカルなコードのためのエスケープハッチ：

```
fn build_tree(data: Vec[Node]) -> Tree with Alloc
    let arena = Arena.new(capacity: 1_mb)
    // arena 内のすべての割り当ては一括解放される
    arena.scope(|a|
        let root = a.alloc(Node.root())
        for item in data
            root.add_child(a.alloc(item))
        Tree #{root}
    )
```

---

## 4. Effect System

### 4.1 Overview

Axion は Algebraic Effect System を採用する。すべての副作用は型シグネチャの `with` 節で宣言される。

### 4.2 Built-in Effects

| Effect | Description |
|--------|-------------|
| `IO` | ファイル・ネットワーク・標準入出力 |
| `Async` | 非同期操作 |
| `State[T]` | 可変状態 |
| `Error[E]` | 回復可能なエラー |
| `Alloc` | ヒープアロケーション |
| `Unsafe` | 安全性保証を緩和する操作 |
| `Random` | 乱数生成 |
| `Clock` | 現在時刻の取得 |
| `Log` | ロギング |

### 4.3 Effect Declaration

```
// 副作用のない純粋関数（デフォルト）
fn add(a: i64, b: i64) -> i64
    a + b

// IO エフェクト付き
fn read_config(path: str) -> Result[Config, IoError] with IO
    let content = fs.read_to_str(path)
    toml.parse(content)

// 複数エフェクト
fn fetch_and_store(url: str) -> Result[{}, AppError] with IO, Async, Log
    log.info("Fetching: {url}")
    let data = http.get(url).await
    fs.write("cache.json", data.to_json())
```

### 4.4 Effect Propagation（エフェクト伝播）

```
// エフェクトは呼び出し元に自動伝播する
fn process_all(urls: Vec[str]) -> Result[Vec[Data], AppError] with IO, Async, Log
    urls.map(|url| fetch_and_store(url))    // fetch_and_store のエフェクトがここに伝播

// 純粋関数から副作用関数を呼ぶとコンパイルエラー
fn bad_pure(x: i64) -> i64
    log.info("x = {x}")    // CE: effect `Log` not declared in signature
    x + 1
```

### 4.5 Effect Handlers（エフェクトハンドラ）

テスト時にエフェクトをモックに差し替え可能：

```
// 本番コード
fn app_main() -> Result[{}, AppError] with IO, Async, Log
    let config = read_config("app.toml")
    let data = fetch_and_store(config.data_url)
    process(data)

// テストコード — IO をモックに差し替え
test "app processes data correctly"
    let mock_fs = MockFs.with_files(
        "app.toml" => "data_url = \"http://test.local/data\""
    )
    let mock_http = MockHttp.with_responses(
        "http://test.local/data" => "{\"items\": [1, 2, 3]}"
    )
    handle app_main()
        IO => mock_io(mock_fs, mock_http)
        Log => discard
```

---

## 5. Functions

### 5.1 Function Declaration

```
fn function_name(param1: Type1, param2: Type2) -> ReturnType
    body_expression
```

- 最後の式が戻り値（`return` は早期リターンのみに使用）
- 戻り値 `{}` の場合、`-> {}` は省略可
- **オーバーロードは禁止**（名前から関数が一意に決定される）

### 5.2 Named Arguments & Default Values

```
fn create_server(host: str = "0.0.0.0", port: u16 = 8080, workers: u32 = 4) -> Server with IO
    Server.bind(host, port, workers)

// 呼び出し — 名前付き引数は順不同
let srv = create_server(port: 3000, workers: 8)
```

- 位置引数と名前付き引数の混在は**禁止**（2引数以下は位置引数、3引数以上は名前付き必須）

### 5.3 Closures（クロージャ）

```
let double = |x: i64| x * 2

// 型推論が効く文脈では型省略可
let nums = vec![1, 2, 3].map(|x| x * 2)

// 複数行クロージャ
let process = |item: Item|
    let normalized = item.normalize()
    normalized.validate()
```

### 5.4 Pipeline Operator（パイプライン演算子）

```
// メソッドチェーンの代替 — データフローが左→右で一貫
let result = raw_data
    |> parse
    |> validate
    |> transform(config: default_config())
    |> serialize
```

---

## 6. Control Flow

### 6.1 Conditional（条件分岐）

```
// if は式（値を返す）
let category = if score >= 90
    "excellent"
else if score >= 70
    "good"
else
    "needs improvement"
```

- **三項演算子は存在しない**（`if` 式で代替）
- `else` なしの `if` は `{}` を返す

### 6.2 Pattern Matching（パターンマッチ）

```
fn describe(value: Value) -> str
    match value
        Value.Int(n) if n > 0 => "positive integer: {n}"
        Value.Int(0) => "zero"
        Value.Int(n) => "negative integer: {n}"
        Value.Str(s) if s.is_empty() => "empty string"
        Value.Str(s) => "string: {s}"
        Value.List([]) => "empty list"
        Value.List([first, ..rest]) => "list starting with {first}"
```

- 網羅性チェックは必須（非網羅的 match はコンパイルエラー）
- ガード条件 `if` を許可
- ネスト・OR パターン `A | B =>` を許可

### 6.3 Loops（ループ）

```
// for-in が唯一のループ構文
for item in collection
    process(item)

// インデックス付き
for {index, item} in collection.enumerate()
    log.debug("{index}: {item}")

// レンジ
for i in 0..100
    compute(i)

// while 相当（for + iterator）
for _ in iter.repeat_while(|| condition())
    do_work()

// 無限ループ
for _ in iter.forever()
    if should_stop()
        break
    tick()
```

- `while` / `loop` は**存在しない** — `for` + イテレータに統一
- `break` は値を返せる:
```
let found = for x in items
    if x.matches()
        break x
```

### 6.4 Early Return & Error Propagation

```
fn parse_config(path: str) -> Result[Config, AppError] with IO
    // `?` で早期リターン（Rust と同様）
    let content = fs.read_to_str(path)?
    let parsed = toml.parse(content)?
    Ok(Config.from(parsed))
```

---

## 7. Module System

### 7.1 File-Based Modules

```
// ディレクトリ構造がそのままモジュール階層
// src/
//   main.ax          → mod main
//   config.ax        → mod config
//   net/
//     http.ax        → mod net.http
//     tcp.ax         → mod net.tcp
```

- 1 ファイル = 1 モジュール（例外なし）
- `mod.ax` のようなバレルファイルは存在しない
- モジュール名はファイル名から自動決定

### 7.2 Imports

```
use std.collections.Map
use std.io.{File, BufReader}
use crate.config.AppConfig
```

- **ワイルドカードインポート `use std.io.*` は禁止**（名前空間汚染を防止）
- **循環インポートはコンパイルエラー**

### 7.3 Visibility

```
// デフォルトはモジュール内 private
fn internal_helper() -> i64
    42

// pub で公開
pub fn public_api(input: str) -> Result[Output, ApiError]
    let x = internal_helper()
    process(input, x)
```

- `pub` と private の2段階のみ（`pub(crate)` 等の中間は存在しない）

---

## 8. Tensor Types（テンソル型）

### 8.1 Shaped Tensors（形状付きテンソル）

AI/ML ワークロードのためのファーストクラスサポート：

```
// 型パラメータ: Tensor[Element, Shape]
type Image = Tensor[f32, [BatchSize, 3, 224, 224]]
type Features = Tensor[f32, [BatchSize, 512]]

fn conv_block(input: Tensor[f32, [B, 3, H, W]]) -> Tensor[f32, [B, 64, H, W]]
    input
        |> conv2d(in_ch: 3, out_ch: 64, kernel: 3, padding: 1)
        |> batch_norm(64)
        |> relu
```

### 8.2 Dimension Variables（次元変数）

```
fn matmul[M, K, N](
    a: Tensor[f32, [M, K]],
    b: Tensor[f32, [K, N]]
) -> Tensor[f32, [M, N]]
    intrinsic.matmul(a, b)

// コンパイル時に次元チェック
let weights = Tensor.randn([784, 256])    // Tensor[f32, [784, 256]]
let input = Tensor.randn([32, 784])       // Tensor[f32, [32, 784]]
let output = matmul(input, weights)       // Tensor[f32, [32, 256]] ✓

let bad_weights = Tensor.randn([128, 10])
// matmul(input, bad_weights)  // CE: dimension mismatch: K=784 vs K=128
```

### 8.3 Dynamic Dimensions

```
// `?` で動的次元を許可（コンパイル時チェックをスキップ）
fn flexible_forward(input: Tensor[f32, [?, ?]]) -> Tensor[f32, [?, 10]]
    input.linear(input.shape(1), 10)
```

---

## 9. Concurrency

### 9.1 Structured Concurrency（構造化並行性）

```
fn fetch_all(urls: Vec[str]) -> Vec[Result[Response, HttpError]] with IO, Async
    // すべてのタスクが完了するまでスコープを抜けない
    async.scope(|s|
        urls.map(|url|
            s.spawn(|| http.get(url))
        ).collect_results()
    )
```

- **非構造化 spawn は存在しない** — すべての並行処理はスコープ付き
- データレースはコンパイル時に排除

### 9.2 Channels

```
fn producer_consumer() with Async
    let {tx, rx} = channel.bounded[i64](capacity: 100)

    async.scope(|s|
        s.spawn(||
            for i in 0..1000
                tx.send(i)
        )
        s.spawn(||
            for value in rx
                process(value)
        )
    )
```

### 9.3 Atomic & Lock-Free

```
// アトミック型は標準ライブラリで提供
let counter = Atomic[i64].new(0)
counter.fetch_add(1, ordering: Relaxed)

// 明示的ロック（必要な場合のみ）
let shared = Mutex.new(Vec[i64].new())
shared.lock(|data|
    data.push(42)
)
```

---

## 10. Error Handling

### 10.1 Result Type（唯一のエラー表現）

```
enum Result[T, E]
    Ok(T)
    Err(E)
```

- **例外（exceptions）は存在しない**
- パニックは回復不能エラー専用（例: out of memory）
- `?` 演算子でエラー伝播

### 10.2 Error Types

```
enum AppError
    NotFound(resource: str)
    Permission(action: str, reason: str)
    Validation(field: str, message: str)
    Internal(source: Box[dyn Error])

// トレイト実装で自動変換
impl From[IoError] for AppError
    fn from(err: IoError) -> AppError
        AppError.Internal(source: Box.new(err))
```

### 10.3 Error Context（エラーコンテキスト）

```
fn load_user(id: UserId) -> Result[User, AppError] with IO
    let data = fs.read_to_str("users/{id}.json")
        .context("failed to read user file for id={id}")?
    let user = json.parse[User](data)
        .context("failed to parse user data for id={id}")?
    Ok(user)
```

---

## 11. Testing

### 11.1 Unit Tests

```
test "addition works"
    assert 1 + 1 == 2

test "user creation validates email"
    let result = User.new(name: "Alice", age: 30, email: "invalid")
    assert result.is_err()
    assert result.unwrap_err() == ValidationError.invalid_format("email")
```

- `test` はファーストクラスキーワード
- テストは同一ファイル内に定義（別ファイルにテストを分離しない）

### 11.2 Property-Based Tests（プロパティベーステスト）

```
test property "sort is idempotent" for (xs: Vec[i64])
    assert xs.sort() == xs.sort().sort()

test property "serialize then deserialize is identity" for (user: User)
    let json = user.to_json()
    let restored = User.from_json(json).unwrap()
    assert restored == user

test property "map preserves length" for (xs: Vec[i64], f: Fn(i64) -> i64)
    assert xs.map(f).len() == xs.len()
```

- `Arbitrary` トレイトを実装した型に対して自動的にランダム入力を生成
- 失敗時はシュリンクされた最小反例を報告

### 11.3 Snapshot Tests

```
test snapshot "config serialization"
    let config = Config.default()
    assert_snapshot config.to_toml()
    // 初回実行時にスナップショットファイルを生成
    // 2回目以降は差分を検出
```

### 11.4 Benchmark Tests

```
test bench "matrix multiplication 1000x1000"
    let a = Tensor.randn([1000, 1000])
    let b = Tensor.randn([1000, 1000])
    bench.iter(||
        matmul(a, b)
    )
```

---

## 12. Compiler Architecture

### 12.1 Compilation Pipeline

```
Source (.ax)
  → Lexer (UTF-8 → Tokens)
  → Parser (Tokens → CST)
  → Desugaring (CST → AST)
  → Name Resolution (AST → Resolved AST)
  → Type Inference (Resolved AST → Typed AST)
  → Effect Checking (Typed AST → Effect-Annotated AST)
  → Region Inference (Effect-Annotated AST → Region-Annotated AST)
  → Borrow Checking (Region-Annotated AST → Verified AST)
  → Monomorphization (Verified AST → Specialized AST)
  → MIR Generation (Specialized AST → MIR)
  → Optimization Passes (MIR → Optimized MIR)
  → Code Generation (Optimized MIR → LLVM IR → Machine Code)
```

### 12.2 Structured Error Output

すべてのコンパイラ診断は JSON で出力可能：

```json
{
  "diagnostics": [
    {
      "severity": "error",
      "code": "E0301",
      "category": "type_mismatch",
      "message": "expected Tensor[f32, [32, 256]], found Tensor[f32, [32, 128]]",
      "primary_span": {
        "file": "src/model.ax",
        "line": 42,
        "col": 12,
        "end_line": 42,
        "end_col": 35
      },
      "labels": [
        {
          "span": { "line": 42, "col": 12 },
          "message": "this expression has type Tensor[f32, [32, 128]]"
        },
        {
          "span": { "line": 38, "col": 5 },
          "message": "expected Tensor[f32, [32, 256]] because of this"
        }
      ],
      "fix_suggestions": [
        {
          "message": "dimension K mismatch: the second matrix has 128 columns but 256 are required",
          "edits": [
            {
              "file": "src/model.ax",
              "line": 40,
              "old_text": "Tensor.randn([128, 10])",
              "new_text": "Tensor.randn([256, 10])"
            }
          ]
        }
      ],
      "related": [
        {
          "message": "function signature requires K=256",
          "span": { "file": "src/model.ax", "line": 35 }
        }
      ]
    }
  ]
}
```

### 12.3 Incremental Compilation

- ファイル単位の依存グラフによる差分コンパイル
- 型チェックはモジュールのインターフェース（シグネチャ）が変わらない限りスキップ
- 目標: 単一ファイル変更後の再チェック < 100ms

### 12.4 Deterministic Builds

- 同一ソースからは常にバイト単位で同一のバイナリが生成される
- タイムスタンプ・ランダムシード・パス情報はバイナリに埋め込まない

---

## 13. Standard Library Overview

### 13.1 Core Modules

| Module | Description |
|--------|-------------|
| `std.io` | ファイル・ストリーム I/O |
| `std.net` | TCP, UDP, HTTP |
| `std.collections` | Vec, Map, Set, Deque, BTreeMap |
| `std.math` | 数学関数 |
| `std.str` | 文字列操作 |
| `std.fmt` | フォーマッティング |
| `std.json` | JSON パーサ / シリアライザ |
| `std.toml` | TOML パーサ |
| `std.csv` | CSV パーサ |
| `std.crypto` | ハッシュ・暗号化 |
| `std.time` | 日時操作 |
| `std.regex` | 正規表現 |
| `std.async` | 非同期ランタイム |
| `std.test` | テストフレームワーク |

### 13.2 Tensor Modules

| Module | Description |
|--------|-------------|
| `std.tensor` | テンソル基本操作 |
| `std.tensor.linalg` | 線形代数 |
| `std.tensor.nn` | ニューラルネットワークレイヤ |
| `std.tensor.optim` | 最適化アルゴリズム |
| `std.tensor.data` | データローダ |

---

## 14. Package Manager: `axpkg`

### 14.1 Manifest File (`axion.toml`)

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2026"

[dependencies]
http_client = "2.1.0"
json_schema = "1.0.0"

[dev_dependencies]
mock_server = "0.5.0"
```

### 14.2 Lockfile

- `axion.lock` によるリプロダクシブルビルド
- ハッシュベースの依存検証

### 14.3 Commands

```bash
axpkg new my_project      # プロジェクト作成
axpkg build               # ビルド
axpkg test                # テスト実行
axpkg bench               # ベンチマーク
axpkg check               # 型チェックのみ（高速）
axpkg fmt                 # フォーマット（正規形に変換）
axpkg doc                 # ドキュメント生成
axpkg publish             # パッケージ公開
```

---

## 15. Interoperability

### 15.1 C FFI

```
extern "C"
    fn malloc(size: usize) -> Ptr[{}]
    fn free(ptr: Ptr[{}])
    fn strlen(s: Ptr[u8]) -> usize
```

- `extern "C"` ブロックで C 関数を宣言
- エフェクト `Unsafe` が必要

### 15.2 WASM Target

```bash
axpkg build --target wasm32
```

- WebAssembly をファーストクラスターゲットとしてサポート
- `wasm-bindgen` 相当の自動バインディング生成

---

## 16. AI Toolchain Integration

### 16.1 Machine-Readable Interface

```bash
# 構造化診断の出力
axpkg check --output-format json

# 型情報のダンプ
axpkg types --output-format json --file src/model.ax

# 自動修正候補の出力
axpkg fix --dry-run --output-format json

# コード補完候補（LSP の JSON-RPC を直接利用）
axpkg complete --file src/model.ax --line 42 --col 12
```

### 16.2 Canonical Form Guarantee

```bash
# ソースコードを正規形に変換（冪等）
axpkg fmt

# 正規形でない場合はエラー（CI 用）
axpkg fmt --check
```

正規形の保証：

- インデント: 4 スペース（固定）
- import 順: std → external → crate（アルファベット順）
- 関数内の宣言順: types → constants → functions
- 空行: 関数間は 1 行、セクション間は 2 行
- 末尾改行: あり（1 行のみ）

### 16.3 AST Normalization

同一のセマンティクスを持つコードは、AST レベルで同一の表現に正規化される：

```
// 以下はすべて同一の AST に正規化される

// 入力 A
if x > 0
    do_something()

// 入力 B（コメント除去・空白正規化後に A と同一）
if x>0
    do_something( )

// → 正規化後は常に A の形
```

### 16.4 Verification Pipeline for AI-Generated Code

```bash
# AI が生成したコードを検証するワンコマンド
axpkg verify src/generated.ax

# 実行内容:
# 1. axpkg fmt --check       (正規形チェック)
# 2. axpkg check             (型チェック + エフェクトチェック)
# 3. axpkg test              (全テスト実行)
# 4. axpkg test --property   (プロパティテスト)
# 5. axpkg audit             (依存関係の脆弱性チェック)
```

---

## 17. Complete Example

以下に、Axion の主要機能を使用した完全なプログラム例を示す。

```
// src/main.ax
// HTTP API サーバーの実装例

use std.net.http.{Server, Request, Response, Status}
use std.json
use std.collections.Map
use crate.models.{User, UserId}
use crate.store.UserStore

// --- Types ---

enum ApiError
    NotFound(resource: str)
    BadRequest(message: str)
    Internal(source: Box[dyn Error])

impl ApiError
    fn to_response(self) -> Response
        match self
            ApiError.NotFound(r) => Response.json(
                status: Status.NotFound
                body: json!(#{"error" => "not found", "resource" => r})
            )
            ApiError.BadRequest(m) => Response.json(
                status: Status.BadRequest
                body: json!(#{"error" => "bad request", "message" => m})
            )
            ApiError.Internal(_) => Response.json(
                status: Status.InternalServerError
                body: json!(#{"error" => "internal server error"})
            )

// --- Handlers ---

fn get_user(store: UserStore, id: UserId) -> Result[Response, ApiError] with IO
    let user = store.find(id)
        .ok_or(ApiError.NotFound("user/{id}"))?
    Ok(Response.json(status: Status.Ok, body: user.to_json()))

fn create_user(store: UserStore, req: Request) -> Result[Response, ApiError] with IO
    let body = req.json[User]()
        .map_err(|e| ApiError.BadRequest(e.to_str()))?
    let user = store.insert(body)?
    Ok(Response.json(status: Status.Created, body: user.to_json()))

fn router(store: UserStore, req: Request) -> Response with IO
    let result = match {req.method, req.path.segments()}
        {"GET",  ["users", id]} => get_user(store, UserId(id.parse_i64()?))
        {"POST", ["users"]}     => create_user(store, req)
        _ => Err(ApiError.NotFound(req.path))

    match result
        Ok(response) => response
        Err(error) => error.to_response()

// --- Entry Point ---

fn main() -> Result[{}, AppError] with IO, Async, Log
    let config = Config.from_env()?
    let store = UserStore.connect(config.database_url)?

    log.info("Starting server on {config.host}:{config.port}")

    let server = Server.bind(
        host: config.host
        port: config.port
        workers: config.workers
    )

    server.run(|req| router(store, req))


// --- Tests ---

test "GET /users/:id returns user"
    let store = UserStore.mock(users: vec![
        User #{id: UserId(1), name: "Alice", email: "alice@test.com"}
    ])
    let req = Request.get("/users/1")
    let resp = router(store, req)
    assert resp.status == Status.Ok

test "GET /users/:id returns 404 for missing user"
    let store = UserStore.mock(users: vec![])
    let req = Request.get("/users/999")
    let resp = router(store, req)
    assert resp.status == Status.NotFound

test "POST /users creates user"
    let store = UserStore.mock(users: vec![])
    let req = Request.post("/users")
        .json(json!(#{"name" => "Bob", "email" => "bob@test.com"}))
    let resp = router(store, req)
    assert resp.status == Status.Created

test property "round-trip serialization" for (user: User)
    let json = user.to_json()
    let restored = User.from_json(json).unwrap()
    assert restored == user
```

---

## Appendix A: Comparison with Existing Languages

| Feature | Axion | Rust | Go | Zig | Haskell |
|---------|-------|------|----|-----|---------|
| Memory Management | Region inference (auto) | Ownership + lifetimes | GC | Manual + allocators | GC |
| Zero-Cost Abstraction | ✓ | ✓ | ✗ | ✓ | Partial |
| Effect System | Algebraic effects | ✗ | ✗ | ✗ | Monads |
| Shaped Tensors | Built-in | Library | ✗ | Library | Library |
| Canonical Form | Enforced | rustfmt (optional) | gofmt | zig fmt | ✗ |
| Structured Errors | JSON native | Text | Text | Text | Text |
| Property Testing | Built-in | Library | Library | Library | QuickCheck |
| Overloading | Forbidden | Forbidden | Forbidden | ✗ | Typeclasses |
| Exceptions | None | None (panic) | ✗ | Error union | Exceptions |
| Null | None (Option) | None (Option) | nil | Optional | Maybe |
| Learning Curve (Human) | Medium | Hard | Easy | Medium | Hard |
| Learning Curve (AI) | **Easy** | Hard | Easy | Medium | Medium |

---

## Appendix B: Reserved Error Codes

| Range | Category |
|-------|----------|
| E0001–E0099 | Syntax errors |
| E0100–E0199 | Name resolution errors |
| E0200–E0299 | Type errors |
| E0300–E0399 | Dimension/shape errors |
| E0400–E0499 | Effect errors |
| E0500–E0599 | Region/borrow errors |
| E0600–E0699 | Module system errors |
| E0700–E0799 | Pattern match errors |
| E0800–E0899 | Concurrency errors |
| W0001–W0999 | Warnings |

---

## Appendix C: Grammar (EBNF Excerpt)

```ebnf
program        = { top_level_item } ;
top_level_item = function_def | struct_def | enum_def | trait_def
               | impl_block | type_alias | use_decl | test_def ;

function_def   = ["pub"] "fn" IDENT type_params? "(" params ")"
                 ["->" type] [effect_clause] NEWLINE INDENT body DEDENT ;

effect_clause  = "with" effect { "," effect } ;
effect         = TYPE_IDENT [type_args] ;

type           = primitive_type
               | TYPE_IDENT [type_args]
               | "{" [type { "," type }] "}"
               | "Fn" "(" [type { "," type }] ")" "->" type ;

primitive_type = "bool" | "i8" | "i16" | "i32" | "i64" | "i128"
               | "u8" | "u16" | "u32" | "u64" | "u128"
               | "f16" | "f32" | "f64" | "bf16"
               | "str" | "char" | "never" | "usize" ;

type_args      = "[" type { "," type } "]" ;
type_params    = "[" type_param { "," type_param } "]" ;
type_param     = TYPE_IDENT [":" trait_bound { "+" trait_bound }] ;

struct_def     = ["pub"] "struct" TYPE_IDENT type_params?
                 NEWLINE INDENT { field_def NEWLINE } DEDENT ;
struct_literal = TYPE_IDENT "#{" { IDENT ":" expr "," } "}" ;

map_literal    = "#{" { expr "=>" expr "," } "}" ;
set_literal    = "#{" { expr "," } "}" ;
tuple_literal  = "{" [ expr { "," expr } ] "}" ;

enum_def       = ["pub"] "enum" TYPE_IDENT type_params?
                 NEWLINE INDENT { variant_def NEWLINE } DEDENT ;

test_def       = "test" [test_modifier] STRING_LIT [for_clause]
                 NEWLINE INDENT body DEDENT ;
test_modifier  = "property" | "snapshot" | "bench" ;
```

---

*End of Specification*
