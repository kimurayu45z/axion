# Axion Language Specification v0.1

**A Programming Language Designed for AI-First Code Generation**

Draft — 2026-02-07

---

## 0. Design Philosophy

Axion（アクシオン）は、LLM による自動コード生成を第一級の設計目標とするシステムプログラミング言語である。以下の原則に従う：

1. **Deterministic Surface（決定論的表層）** — 同一の意図に対して、文法的に正しい書き方が唯一つだけ存在する
2. **Zero-Cost Abstraction（ゼロコスト抽象化）** — ランタイムコストを伴わない抽象化を保証する
3. **Compiler-Owned Complexity（コンパイラが複雑性を引き受ける）** — ライフタイム・リージョンの推論はコンパイラの責務とする。関数パラメータの所有権モード（borrow / move）のみプログラマが宣言する
4. **Typed Effects（型付きエフェクト）** — すべての副作用を型システムで追跡する
5. **Machine-Readable Diagnostics（機械可読診断）** — エラー・警告を構造化データとして出力する

---

## 1. Lexical Structure

### 1.1 Source Encoding

- ソースファイルは UTF-8 のみ
- 拡張子: `.ax`
- BOM 禁止

### 1.2 Keywords（予約語）

以下の 35 語のみを予約語とする。拡張予約語は存在しない。

```
fn  let  mut  move  type  struct  enum  interface
match  if  else  while  for  in  return  break  continue
use  mod  pkg  pub  self  Self  true  false  with
where  as  const  dim  dyn  extern  handle  assert  test
```

### 1.3 Identifiers

```
identifier     = [a-z_][a-z0-9_]*        // 値・関数・変数
type_ident     = [A-Z][A-Za-z0-9]*       // 型・インターフェース
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
///   let y = normalize(Tensor.from([1.0, 2.0, 3.0]))
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
| `str` | unsized | UTF-8 文字列スライス型（通常 `&str` として使用、Rust の `str` と同様） |
| `char` | 4 bytes | Unicode scalar value |
| `{}` | 0 bytes | 単位型（空タプル） |
| `never` | 0 bytes | ボトム型（到達不能） |

- **暗黙の型変換は一切存在しない**（`i32` → `i64` も明示的）
- 数値リテラルは接尾辞で型を決定: `42_i32`, `3.14_f64`
- 接尾辞省略時のデフォルト: 整数 → `i64`, 浮動小数点 → `f64`

**文字列リテラル：**

```
"hello"              // String（所有文字列）
&"hello"             // &str（静的文字列スライス、Rust の &'static str 相当）
"Hello, {name}"      // String（文字列補間、{} 内の式を埋め込む）
```

- `""` は `String` 型を返す。コンパイラはリテラル文字列のヒープ割り当てを最適化できる
- `&""` は `&str` 型を返す（静的データへの参照）
- 文字列補間は `{}` 内に式を記述し、`Printable` インターフェースの `to_string()` が呼ばれる

**Copy セマンティクス：**

- **プリミティブ型のみが Copy**（`bool`, 整数型, 浮動小数点型, `char`, `usize`）
- ユーザー定義型に Copy を実装することは**不可能**
- プリミティブ以外の型のコピーが必要な場合は `.clone()` を明示的に呼ぶ

### 2.2 Compound Types

```
// タプル（波括弧で囲む）
type Point = {f64, f64}

// タプルリテラル
let origin = {0.0, 0.0}
let unit_val = {}              // 空タプル = 単位型

// 所有文字列（ヒープ確保、可変長、UTF-8）
type Name = String

// 文字列スライス（ファットポインタ、他の所有者の文字列データを参照）
type Label = &str

// 配列（固定長、スタック確保）
type Matrix = FixedArray[f64][3, 3]

// スライス（ファットポインタ、他の所有者の連続データを参照）
type Slice = &[f64]

// ベクタ（ヒープ確保、可変長）
type Items = Array[f64]

// マップ（順序保証ハッシュマップ）— リテラルは #{ key => value }
type Config = Map[String, Value]
let headers = #{"Content-Type" => "application/json", "Accept" => "*/*"}

// セット — リテラルは #{ value, ... }
type Ids = Set[i64]
let primes = #{2, 3, 5, 7, 11}

// オプション
type MaybeInt = Option[i64]    // Some(x) | None

// 結果
type ParseResult = Result[Ast, ParseError]  // Ok(x) | Err(e)

// ヒープ確保のスマートポインタ（単一所有権）
type Boxed = Box[dyn Printable]
```

### 2.3 Struct（構造体）

```
struct User
    name: String
    age: u32
    email: String

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
fn first[T: Copy](items: Array[T]) -> Option[T]
    if items.is_empty()
        None
    else
        Some(items.get(0))

fn take_first[T](move mut items: Array[T]) -> Option[T]
    if items.is_empty()
        None
    else
        Some(items.remove(0))
```

- Monomorphization により実行時コストゼロ
- 型パラメータは `[T]` で囲む（`<T>` ではない — `<` / `>` の比較演算子との曖昧性を排除）

### 2.6 Methods & Interfaces（メソッドとインターフェース）

#### メソッド定義

メソッドは `fn@[ReceiverType]` 構文で定義する。`self` が暗黙的に使える。

```
// borrow（デフォルト）
fn@[User] display_name() -> &str
    self.name.as_str()

// mut borrow
fn@[mut User] rename(new_name: String)
    self.name = new_name

// move（消費）
fn@[move User] into_name() -> String
    self.name
```

構文の分解：

```
fn @[ReceiverType] name [TypeParams] (params) -> ReturnType
│   │                    │            │
│   │                    │            └─ 引数
│   │                    └─ 型パラメータ（ジェネリクス）
│   └─ レシーバー（所有権モード付き）
└─ 関数キーワード
```

呼び出し側：

```
let mut user = User #{name: "Alice", age: 30, email: "alice@example.com"}
user.display_name()         // borrow — user はまだ使える
user.rename("Bob")          // mut borrow — user.name が変更される
let name = user.into_name() // move — user はここで死ぬ
// user.age                  // CE: user was moved
```

ジェネリックメソッド：

```
fn@[Array[T]] print_all[T: Printable]()
    for item in self
        log.info(item.to_string())
```

- メソッドは定義元の型と**同じパッケージ内**でのみ定義可能

#### コンストラクタ（静的メソッド）

**戻り値が `Self` を含む場合のみ**、`fn Type.name()` 構文で静的メソッドを定義できる。

```
fn User.new(name: String, age: u32, email: String) -> Self
    Self #{name, age, email}

fn User.from_json(json: Json) -> Result[Self, ParseError]
    let name = json.get(&"name")?.as_string()?
    let age = json.get(&"age")?.as_u32()?
    let email = json.get(&"email")?.as_string()?
    Ok(Self #{name, age, email})

// fn User.helper() -> i64    // CE: static method must return Self
```

#### Interface（ダックタイピング）

```
interface Hashable
    fn hash() -> u64

interface Printable
    fn to_string() -> String
```

型が interface を満たすかは**構造的に判定**される（Go と同様）。明示的な宣言は不要。

```
// User は hash() -> u64 を持つので、自動的に Hashable を満たす
fn@[User] hash() -> u64
    hash.combine(self.name.hash(), self.age.hash())

fn@[User] to_string() -> String
    "{self.name} (age {self.age})"
```

所有権モードが必要な interface メソッド：

```
interface MutableCollection
    fn@[mut] clear()           // mut 必須
    fn len() -> usize          // borrow（デフォルト）

interface Consumable
    fn@[move] consume() -> Data  // move 必須
```

#### `impl Interface for Type`（コンパイル時検証）

型が interface を満たすかは構造的に判定されるが、**明示的にコンパイル時検証**することもできる。Go の `var _ Interface = Type{}` に相当する機能。

```
impl Printable for Point
```

ジェネリック型の場合：

```
impl[T] Printable for Array[T]
```

`impl Interface for Type` は以下を検証する：
- **Duck-typed interface**: 必要なメソッドがすべて存在すること
- **Marker interface**: `interface_impls` レジストリに登録されていること

不満足の場合はコンパイルエラーとなる。メソッド定義やシンボル登録は行わない（純粋なアサーション）。

#### Interface 境界（静的ディスパッチ）

```
fn lookup[K: Hashable + Eq, V](table: Map[K, V], key: K) -> Option[V]
    table.get(key)
```

- Monomorphization による静的ディスパッチ（ゼロコスト）

#### 動的ディスパッチ

```
fn print_all(items: Array[dyn Printable])
    for item in items
        log.info(item.to_string())
```

- `dyn Interface` で vtable ベースの動的ディスパッチ

### 2.7 Type Aliases & Newtypes

```
// エイリアス（同一型、コンパイル時に消える）
type UserId = i64

// Newtype（別の型として扱われる、ゼロコスト）
type Email = newtype String

fn Email.validate(s: &str) -> Result[Self, ValidationError]
    if s.contains(&"@")
        Ok(Self(String.from(s)))
    else
        Err(ValidationError.invalid_format(&"email"))
```

---

## 3. Memory Model

### 3.1 Design Principle

Axion のメモリモデルは **Region-Based Memory Management（リージョンベースメモリ管理）** を採用する。Rust のライフタイムアノテーションに相当するものをプログラマが記述する必要はない。

ただし、**関数パラメータの所有権モード**はプログラマが宣言する。これにより、コンパイラの推論が決定論的になり、AI にとっても人間にとっても意図が明確になる。

### 3.2 Ownership Modes（所有権モード）

関数パラメータには以下の修飾子を指定できる。修飾子なしの場合は不変借用がデフォルトとなる。

| 修飾子 | 所有権 | 可変性 | 呼び出し後の元変数 |
|--------|--------|--------|-------------------|
| (なし) | 借用 | 不変 | 使える |
| `mut` | 借用 | 可変 | 使える（変更が反映） |
| `move` | 移動 | 不変 | 使えない |
| `move mut` | 移動 | 可変 | 使えない |

所有権と可変性は完全に直交する。

**参照型（`&` 付き型）について：** 型構文中の `&` はスライス・ビュー型を示す。パラメータの借用修飾子とは別の概念である。

```
// & は型構文で「所有しないビュー」を表す
&str             // 文字列スライス（Rust の &str と同様）
&[T]             // スライス（旧 Span[T] を置き換え）

// パラメータの所有権は修飾子で決まる（& は使わない）
fn sum(items: Array[i64]) -> i64           // borrow（デフォルト）
fn consume(move items: Array[i64]) -> i64  // move
fn get_slice(items: Array[i64]) -> &[i64]  // 戻り値がスライス型
```

構造体フィールドに `&` 付き型を持たせた場合、そのフィールドはライフタイム制約を持つ（詳細は 3.8 節）。

コンパイラが自動推論するのは以下のみ：

1. 各値がどのリージョン（メモリ領域）に属するか
2. いつそのリージョンを解放できるか
3. 参照のライフタイム（呼び出し元のスコープから自動決定）

### 3.3 Default Borrow（デフォルト借用）

関数パラメータは**デフォルトで不変借用**として渡される。

```
fn process(items: Array[Item]) -> Summary
    // items は不変借用 — 読み取りのみ可能
    let total = items.iter().map(|x| x.value).sum()
    Summary #{total: total, count: items.len()}

// 呼び出し側
let items = Array.from([item1, item2, item3])
let summary = process(items)    // borrow — items はまだ使える
items.len()                      // OK
```

プリミティブ型（Copy 型）は、借用の代わりに暗黙にコピーされる（ゼロコスト抽象化の維持）。

### 3.4 Mutable Borrow（可変借用）

`mut` 修飾子で可変借用を宣言する。変更は呼び出し元に反映される。

```
fn append(mut items: Array[Item])
    items.push(Item.default())

// 呼び出し側 — mut を明示
let mut items = Array.from([item1, item2])
append(mut items)        // mut borrow — items に変更が反映
assert items.len() == 3  // OK: push が反映されている
```

- 可変借用と不変借用の同時存在はコンパイルエラー（排他的可変性、Rust と同等）
- `mut` は定義側と呼び出し側の**両方に必要**（AI が副作用の有無を明確に認識できる）

### 3.5 Move（所有権の移動）

`move` 修飾子で所有権の移動を宣言する。呼び出し後、元の変数は使用不可。

```
fn consume(move items: Array[Item]) -> Array[Item]
    items.push(Item.default())
    items

// 呼び出し側 — move を明示
let items = Array.from([item1, item2])
let new_items = consume(move items)  // move — items はここで死ぬ
// items.len()                        // CE: items was moved
```

`move mut` で移動 + 可変を宣言できる：

```
fn transform(move mut items: Array[Item]) -> Array[Item]
    items.sort()
    items.dedup()
    items
```

**`move` を使うべき場面：**

- 所有権を奪って別のコンテナに格納する場合
- 値を消費して新しい値を返す場合
- 呼び出し元でその値が不要になった場合

### 3.6 Call-Site Annotation（呼び出し側アノテーション）

`mut` と `move` は呼び出し側にも明示する。コードを読むだけで所有権の流れが完全にわかる。

```
let mut items = Array.from([1, 2, 3])

process(items)              // borrow — items はまだ使える
append(mut items)           // mut borrow — items に変更が反映
let result = consume(move items)  // move — items はここで死ぬ
// items.len()              // CE: items was moved
```

呼び出し側の修飾子が定義側と一致しない場合はコンパイルエラー：

```
fn read_only(data: Array[i64]) -> i64
    data.iter().sum()

read_only(move data)        // CE: function expects borrow, got move
read_only(mut data)         // CE: function expects immutable borrow, got mut
```

### 3.7 Value Semantics（値セマンティクス）

代入時のデフォルトは**所有権の移動（move）**。これは関数パラメータのデフォルト（borrow）とは異なる。

```
// 代入は move
let a = Array.from([1, 2, 3])
let b = a                  // a は move される
// a.len()                 // CE: a は既に move 済み

// プリミティブ型（Copy 型）は暗黙にコピー
let x: i64 = 42
let y = x                  // copy（x は引き続き有効）
```

**注意：** 代入のデフォルトが move、パラメータのデフォルトが borrow という非対称性は意図的な設計である。代入は「値の所有権を移す」意図が明確であり、関数呼び出しは「値を一時的に使う」意図が一般的であるため。

### 3.8 Region Inference（リージョン推論）

コンパイラは参照のライフタイムを自動推論する。プログラマがライフタイムアノテーションを書く必要はない。

```
fn first_word(text: &str) -> &str
    // コンパイラが戻り値のライフタイムを text のスコープから自動決定
    text.split(" ").first().unwrap_or("")

// 呼び出し側
let greeting = "hello world"
let word = first_word(greeting)  // word のライフタイムは greeting に紐づく
```

**コンパイラの推論アルゴリズム：**

1. 関数パラメータの所有権モード（borrow / move）からリージョン制約を生成
2. 戻り値の型から出力リージョンを決定
3. 関数本体のローカル変数にスコープベースのリージョンを割り当て
4. 制約充足ソルバでリージョンの包含関係を解決

パラメータの所有権をプログラマが宣言するため、推論の入力が明確になり、**解が一意に定まらないケースが大幅に減少する**。曖昧なケースが残る場合のみコンパイルエラーとなる。

#### 3.8.1 Field-Level Lifetime Tracking（フィールドごとライフタイム追跡）

構造体が参照型フィールドを持つ場合、コンパイラは**フィールドごとに独立したライフタイム**を追跡する。

```
struct View
    name: String     // 所有型 → ライフタイム制約なし
    data: &[i64]     // 参照型 → ライフタイム制約あり
    label: &str      // 参照型 → ライフタイム制約あり
```

コンパイラは構築時に各参照フィールドの出自を記録する：

```
let nums = Array.from([1, 2, 3])
let text = "hello"

let view = View #{
    name: String.from("view1"),
    data: nums.as_slice(),    // data → nums から借用
    label: text,              // label → text から借用
}

view.name.len()       // OK: 所有型、常にアクセス可
view.data.sum()       // OK: nums が生きている
view.label.len()      // OK: text が生きている
```

フィールドの参照元が死んだ場合、そのフィールドのみが使用不可になる：

```
drop(move text)       // drop: 組み込み関数 fn drop[T](move val: T)
view.data.sum()       // OK: nums はまだ生きている
// view.label.len()   // CE: label's source (text) was dropped
```

#### 3.8.2 Destructuring for Lifetime Separation（分解によるライフタイム分離）

構造体を分解すると、各フィールドが独立した変数として独立したライフタイムを持つ：

```
let view = View #{name: String.from("v"), data: a.as_slice(), label: b}

// 分解 → 各フィールドが独立
let {name, data, label} = view

// data と label は完全に独立したライフタイムを持つ
process_slice(data)     // a が生きていればOK
process_str(label)      // b が生きていればOK
```

#### 3.8.3 Function Boundary Rule（関数境界ルール）

構造体を丸ごと関数に渡す場合、**すべての参照フィールドの参照元が生きている必要がある**（保守的ルール）：

```
fn process_view(view: View) -> i64
    view.data.sum()     // data しか使っていないが...

// 呼び出し側 — すべての参照フィールドが生きていないとダメ
process_view(view)      // nums と text の両方が生きている必要がある
```

これはシグネチャだけでインターフェースが決定され、関数本体を変更しても呼び出し側が壊れないことを保証する。精度が必要なら分解して必要なフィールドだけ渡す：

```
let {data, ..} = view
process_slice(data)     // nums だけ生きていればOK
```

#### 3.8.4 Active Type（Active 型）

`T@{field1, field2, ...}` は、構造体の一部の参照フィールドだけが有効であることを型レベルで表現する組み込み構文である：

```
struct Connection
    reader: &[u8]       // 参照
    writer: &[u8]       // 参照
    config: Config       // 所有

fn read_next(conn: Connection@{reader}) -> Result[Packet, Error]
    conn.reader.parse()     // OK: reader は active
    conn.config.timeout     // OK: 所有フィールドは常にアクセス可
    // conn.writer           // CE: `writer` is not active in Connection@{reader}
```

**アクセスルール：**

| フィールドの種類 | `@{}` に含まれる | `@{}` に含まれない |
|----------------|------------------|-------------------|
| 所有型（`String`, `Array` 等） | 常にアクセス可 | 常にアクセス可 |
| 参照型（`&[T]`, `&str` 等） | アクセス可 | コンパイルエラー |

呼び出し側は、指定された参照フィールドの参照元だけが生きていればよい：

```
let conn = Connection #{
    reader: read_buf.as_slice(),
    writer: write_buf.as_slice(),
    config: config,
}

drop(move write_buf)
// full_process(conn)                 // CE: writer's source was dropped
read_next(conn)                       // OK: reader の参照元だけ生きていればいい
```

修飾子なし（`conn: Connection`）は全参照フィールドを active とする糖衣構文：

```
// この2つは等価
fn process(conn: Connection)
fn process(conn: Connection@{reader, writer})
```

#### 3.8.5 Closure Capture Lifetime（クロージャのキャプチャライフタイム）

クロージャがキャプチャする変数のライフタイムは、キャプチャ方法に依存する：

```
// borrow キャプチャ（デフォルト）— クロージャのライフタイムはキャプチャ元に紐づく
let data = Array.from([1, 2, 3])
let sum_fn = || data.iter().sum()    // data を借用キャプチャ
sum_fn()                              // OK: data が生きている

// クロージャを返す場合、borrow キャプチャだとスコープ外になる
fn make_filter(prefix: &str) -> Fn(&str) -> bool
    |s| s.starts_with(prefix)
    // CE: closure outlives borrowed `prefix`

// 修正: move でキャプチャ元の所有権をクロージャに移す
fn make_filter(move prefix: String) -> Fn(&str) -> bool
    |s| s.starts_with(prefix)    // OK: prefix はクロージャが所有
```

### 3.9 Arena Allocator（アリーナアロケータ）

パフォーマンスクリティカルなコードのためのエスケープハッチ：

```
fn build_tree(data: Array[Node]) -> Tree with Alloc
    let arena = Arena.new(1_mb)
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
| `Alloc` | ヒープアロケーション |
| `Unsafe` | 安全性保証を緩和する操作 |
| `Random` | 乱数生成 |
| `Clock` | 現在時刻の取得 |

**エフェクト追跡の対象外：**

- **ロギング** — `log.info(...)` 等はエフェクト宣言なしで任意の関数から呼び出せる。`log` モジュールは import 不要で常に利用可能（prelude）。ロギングは観測目的の副作用であり、プログラムのセマンティクスに影響しないため特例とする
- **エラー** — 回復可能なエラーは `Result[T, E]` 型 + `?` 演算子で表現する。エフェクトとしては扱わない

### 4.3 Effect Declaration

```
// 副作用のない純粋関数（デフォルト）
fn add(a: i64, b: i64) -> i64
    a + b

// IO エフェクト付き
fn read_config(path: &str) -> Result[Config, IoError] with IO
    let content = fs.read_to_str(path)
    toml.parse(content)

// 複数エフェクト
fn fetch_and_store(url: &str) -> Result[{}, AppError] with IO, Async
    log.info("Fetching: {url}")
    let data = http.get(url).await
    fs.write("cache.json", data.to_json())
```

### 4.4 Effect Propagation（エフェクト伝播）

```
// エフェクトは呼び出し元に自動伝播する
fn process_all(urls: Array[String]) -> Result[Array[Data], AppError] with IO, Async
    urls.map(|url| fetch_and_store(url))    // fetch_and_store のエフェクトがここに伝播

// 純粋関数から副作用関数を呼ぶとコンパイルエラー
fn bad_pure(x: i64) -> i64
    fs.write("log.txt", "x = {x}")    // CE: effect `IO` not declared in signature
    x + 1
```

### 4.5 Effect Handlers（エフェクトハンドラ）

テスト時にエフェクトをモックに差し替え可能：

```
// 本番コード
fn app_main() -> Result[{}, AppError] with IO, Async
    let config = read_config(&"app.toml")
    let data = fetch_and_store(config.data_url.as_str())
    process(data)

// テストコード — IO をモックに差し替え
test "app processes data correctly"
    let mock_fs = MockFs.with_files(
        &"app.toml" => &"data_url = \"http://test.local/data\""
    )
    let mock_http = MockHttp.with_responses(
        &"http://test.local/data" => &"{\"items\": [1, 2, 3]}"
    )
    handle app_main()
        IO => mock_io(mock_fs, mock_http)
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

### 5.2 Closures（クロージャ）

```
let double = |x: i64| x * 2

// 型推論が効く文脈では型省略可
let nums = Array.from([1, 2, 3]).map(|x| x * 2)

// 複数行クロージャ
let process = |item: Item|
    let normalized = item.normalize()
    normalized.validate()
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
fn describe(value: Value) -> String
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

**借用値に対するパターンマッチ：** 関数パラメータがデフォルト借用の場合、パターンマッチで束縛される変数も借用になる。Copy 型のフィールドは自動的にコピーされる。

```
fn describe_shape(shape: Shape) -> String
    match shape                      // shape は borrow（デフォルト）
        Shape.Circle(r) =>          // r: f64 は Copy → コピー
            "circle with radius {r}"
        Shape.Rect(w, h) =>         // w, h: f64 は Copy → コピー
            "rect {w}x{h}"
        Shape.Point => "point"

fn get_user_name(user: User) -> &str
    match user                       // user は borrow
        User #{name, ..} =>         // name: &String（借用）
            name.as_str()            // &String から &str を返す
```

### 6.3 Loops（ループ）

```
// for-in — コレクションの反復
for item in collection
    process(item)

// インデックス付き
for {index, item} in collection.enumerate()
    log.debug("{index}: {item}")

// レンジ
for i in 0..100
    compute(i)

// while — 条件付きループ
while buf.remaining() > 0
    process_chunk(buf)

// 無限ループ（while true）
while true
    if should_stop()
        break
    tick()
```

- ループ構文は `for` と `while` の2種類のみ
- `loop` キーワードは存在しない（`while true` で代替）
- `break` は値を返せる:
```
let found = for x in items
    if x.matches()
        break x
```

### 6.4 Early Return & Error Propagation

```
fn parse_config(path: &str) -> Result[Config, AppError] with IO
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
use pkg.config.AppConfig
```

- **ワイルドカードインポート `use std.io.*` は禁止**（名前空間汚染を防止）
- **循環インポートはコンパイルエラー**

### 7.3 Visibility

```
// デフォルトはモジュール内 private
fn internal_helper() -> i64
    42

// pub で公開
pub fn public_api(input: &str) -> Result[Output, ApiError]
    let x = internal_helper()
    process(input, x)
```

- `pub` — 外部に公開
- `pub(pkg)` — パッケージ内のみ公開（他パッケージからはアクセス不可）
- (なし) — モジュール内 private

---

## 8. Const Generics & Dimension Types

### 8.1 Const Generics（コンパイル時定数パラメータ）

`const` パラメータはコンパイル時に値が確定する定数。モノモーフィゼーションにより定数ごとに特殊化されたコードが生成される。

```
// 固定長バッファ
struct FixedBuf[T, const N: usize]
    data: FixedArray[T][N]

fn FixedBuf.new[T, const N: usize]() -> Self
    Self #{data: FixedArray.zeroed()}

// 使用
let buf = FixedBuf[u8, 1024].new()    // N=1024 でモノモーフィゼーション
```

`const` パラメータの用途：固定長配列、ビット幅、バッファサイズなど **メモリレイアウトに影響する** コンパイル時定数。

### 8.2 Dimension Types（次元型システム）

`dim` パラメータはシンボリックな次元変数。値は**実行時に決定**されるが、変数間の**関係性はコンパイル時に検証**される。

```
fn matmul[dim M, dim K, dim N](
    a: Tensor[f32][M, K],
    b: Tensor[f32][K, N]
) -> Tensor[f32][M, N]
```

`const` との決定的な違い：

| | `const` | `dim` |
|--|---------|-------|
| 値の決定時期 | コンパイル時 | **実行時** |
| コード生成 | 定数ごとにモノモーフィゼーション | **1つのコード**（次元は実行時パラメータ） |
| チェック対象 | 値そのもの | **変数間の関係**（等価性・算術） |
| 用途 | メモリレイアウト、バッファサイズ | テンソル形状、行列次元 |

### 8.3 Dimension Checking（次元チェック）

コンパイラはユニフィケーションベースの制約解決で次元の整合性を検証する。

```
let data = load_csv(&"train.csv")       // Tensor[f32][?N, 784] — N は実行時に決定
let weights = Tensor.randn(784, 256)    // Tensor[f32][784, 256]

let output = matmul(data, weights)
// コンパイラの推論:
//   K = 784 (data の2次元目) = 784 (weights の1次元目) ✓
//   M = ?N（不明だがそのまま伝播）
//   結果: Tensor[f32][?N, 256]

let bad = Tensor.randn(128, 10)
// matmul(data, bad)   // CE: dimension mismatch: K=784 (from data) vs K=128 (from bad)
```

次元の3段階：

| 表記 | 意味 | チェック |
|------|------|---------|
| `784` | 具体値 | コンパイル時に値の一致を検証 |
| `dim K` | シンボリック変数 | コンパイル時に等価性・算術関係を検証 |
| `?` | ワイルドカード | 実行時チェックにフォールバック |

### 8.4 Dimension Arithmetic（次元算術）

`dim` 変数はコンパイル時算術の対象になる：

```
fn reshape[dim M, dim N](
    t: Tensor[f32][M * N]
) -> Tensor[f32][M, N]

fn flatten[dim M, dim N](
    t: Tensor[f32][M, N]
) -> Tensor[f32][M * N]

// コンパイラが M * N の関係を追跡
let a = Tensor.randn(3, 4)          // Tensor[f32][3, 4]
let flat = flatten(a)                // Tensor[f32][12]
let b = reshape[3, 4](flat)         // Tensor[f32][3, 4] ✓
// let c = reshape[2, 5](flat)      // CE: 2*5=10 ≠ 12
```

### 8.5 Tensor Library（ライブラリ分離）

言語が提供するのは `const` / `dim` パラメータと次元チェックの仕組みのみ。`Tensor` 型の実装はライブラリが担う。

```
// std.tensor（標準ライブラリ）
// Tensor 型定義、基本演算、CPU バックエンド

// 外部ライブラリ（例）
// tensor_gpu: CUDA / Metal バックエンド
// tensor_autograd: 自動微分
// tensor_nn: ニューラルネットワークレイヤ
```

使用例：

```
use std.tensor.Tensor
use tensor_nn.{linear, conv2d, batch_norm, relu}

fn conv_block[dim B, dim H, dim W](
    input: Tensor[f32][B, 3, H, W]
) -> Tensor[f32][B, 64, H, W]
    input
```

---

## 9. Concurrency

### 9.1 Structured Concurrency（構造化並行性）

```
fn fetch_all(urls: Array[String]) -> Array[Result[Response, HttpError]] with IO, Async
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
    let {tx, rx} = channel.bounded[i64](100)

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
counter.fetch_add(1, Relaxed)

// 明示的ロック（必要な場合のみ）
let shared = Mutex.new(Array[i64].new())
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
    NotFound(resource: String)
    Permission(action: String, reason: String)
    Validation(field: String, message: String)
    Internal(source: Box[dyn Error])

// ? 演算子のエラー変換は Type.from() コンストラクタを利用
fn AppError.from(err: IoError) -> Self
    Self.Internal(source: Box.new(err))
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
    let result = User.new("Alice", 30, "invalid")
    assert result.is_err()
    assert result.unwrap_err() == ValidationError.invalid_format(&"email")
```

- `test` はファーストクラスキーワード
- テストは同一ファイル内に定義（別ファイルにテストを分離しない）

### 11.2 Property-Based Tests（プロパティベーステスト）

```
test property "sort is idempotent" for (xs: Array[i64])
    assert xs.sort() == xs.sort().sort()

test property "serialize then deserialize is identity" for (user: User)
    let json = user.to_json()
    let restored = User.from_json(json).unwrap()
    assert restored == user

test property "map preserves length" for (xs: Array[i64], f: Fn(i64) -> i64)
    assert xs.map(f).len() == xs.len()
```

- `Arbitrary` インターフェースを実装した型に対して自動的にランダム入力を生成
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
      "message": "expected Tensor[f32][32, 256], found Tensor[f32][32, 128]",
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
          "message": "this expression has type Tensor[f32][32, 128]"
        },
        {
          "span": { "line": 38, "col": 5 },
          "message": "expected Tensor[f32][32, 256] because of this"
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
| `std.collections` | Array, Map, Set, Deque, BTreeMap |
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

### 13.2 Tensor Ecosystem（外部ライブラリ）

テンソル関連は標準ライブラリではなく外部ライブラリとして提供される。言語は `dim` パラメータと次元チェックの仕組みのみを提供する。

| Package | Description |
|---------|-------------|
| `tensor` | テンソル基本操作、CPU バックエンド |
| `tensor_gpu` | CUDA / Metal バックエンド |
| `tensor_nn` | ニューラルネットワークレイヤ |
| `tensor_optim` | 最適化アルゴリズム |
| `tensor_data` | データローダ |

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
- `Ptr[T]` は FFI 専用の生ポインタ型。`Unsafe` コンテキストでのみ使用可能

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
- import 順: std → external → pkg（アルファベット順）
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
use pkg.models.{User, UserId}
use pkg.store.UserStore

// --- Types ---

enum ApiError
    NotFound(resource: String)
    BadRequest(message: String)
    Internal(source: Box[dyn Error])

fn@[ApiError] to_response() -> Response
    match self
        ApiError.NotFound(r) => Response.json(
            Status.NotFound,
            Json.from(#{"error" => "not found", "resource" => r})
        )
        ApiError.BadRequest(m) => Response.json(
            Status.BadRequest,
            Json.from(#{"error" => "bad request", "message" => m})
        )
        ApiError.Internal(_) => Response.json(
            Status.InternalServerError,
            Json.from(#{"error" => "internal server error"})
        )

// --- Handlers ---

fn get_user(store: UserStore, id: UserId) -> Result[Response, ApiError] with IO
    let user = store.find(id)
        .ok_or(ApiError.NotFound("user/{id}"))?
    Ok(Response.json(Status.Ok, user.to_json()))

fn create_user(store: UserStore, move req: Request) -> Result[Response, ApiError] with IO
    let body = req.json[User]()
        .map_err(|e| ApiError.BadRequest(e.to_str()))?
    let user = store.insert(body)?
    Ok(Response.json(Status.Created, user.to_json()))

fn router(store: UserStore, move req: Request) -> Response with IO
    let result = match {req.method, req.path.segments()}
        {"GET",  ["users", id]} => get_user(store, UserId(id.parse_i64()?))
        {"POST", ["users"]}     => create_user(store, move req)
        _ => Err(ApiError.NotFound(req.path))

    match result
        Ok(response) => response
        Err(error) => error.to_response()

// --- Entry Point ---

fn main() -> Result[{}, AppError] with IO, Async
    let config = Config.from_env()?
    let store = UserStore.connect(config.database_url.as_str())?

    log.info("Starting server on {config.host}:{config.port}")

    let server = Server.bind(config.host.as_str(), config.port, config.workers)

    server.run(|req| router(store, move req))


// --- Tests ---

test "GET /users/:id returns user"
    let store = UserStore.mock(Array.from([
        User #{id: UserId(1), name: "Alice", email: "alice@test.com"}
    ]))
    let req = Request.get(&"/users/1")
    let resp = router(store, move req)
    assert resp.status == Status.Ok

test "GET /users/:id returns 404 for missing user"
    let store = UserStore.mock(Array.new())
    let req = Request.get(&"/users/999")
    let resp = router(store, move req)
    assert resp.status == Status.NotFound

test "POST /users creates user"
    let store = UserStore.mock(Array.new())
    let req = Request.post(&"/users")
        .json(#{"name" => "Bob", "email" => "bob@test.com"})
    let resp = router(store, move req)
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
| Memory Management | Default borrow + explicit move + region inference | Ownership + lifetimes | GC | Manual + allocators | GC |
| Zero-Cost Abstraction | ✓ | ✓ | ✗ | ✓ | Partial |
| Effect System | Algebraic effects | ✗ | ✗ | ✗ | Monads |
| Shaped Tensors | `dim` checking (lang) + Library | Library | ✗ | Library | Library |
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
top_level_item = function_def | method_def | constructor_def
               | struct_def | enum_def | interface_def
               | impl_for_def
               | type_alias | use_decl | test_def ;

// 通常の関数
function_def   = ["pub"] "fn" IDENT type_params? "(" params ")"
                 ["->" type] [effect_clause] NEWLINE INDENT body DEDENT ;

// インスタンスメソッド: fn@[mut Type] name[T: Bound](params) -> Return
method_def     = ["pub"] "fn" "@" "[" receiver "]" IDENT type_params?
                 "(" params ")" ["->" type] [effect_clause]
                 NEWLINE INDENT body DEDENT ;
receiver       = [ "mut" | "move" ] type ;

// コンストラクタ: fn Type.name(params) -> Self（Self を含む戻り値のみ）
constructor_def = ["pub"] "fn" TYPE_IDENT "." IDENT "(" params ")"
                  "->" self_type [effect_clause]
                  NEWLINE INDENT body DEDENT ;
self_type      = "Self" | TYPE_IDENT "[" "Self" { "," type } "]" ;

param          = param_modifier IDENT ":" type ;
param_modifier = [ "move" ] [ "mut" ] ;

effect_clause  = "with" effect { "," effect } ;
effect         = TYPE_IDENT [type_args] ;

type           = primitive_type
               | TYPE_IDENT [type_args] [dim_args]
               | "{" [type { "," type }] "}"
               | "Fn" "(" [type { "," type }] ")" "->" type
               | "&" "[" type "]"
               | "&" "str"
               | TYPE_IDENT "@" "{" IDENT { "," IDENT } "}"
               | "dyn" TYPE_IDENT ;

primitive_type = "bool" | "i8" | "i16" | "i32" | "i64" | "i128"
               | "u8" | "u16" | "u32" | "u64" | "u128"
               | "f16" | "f32" | "f64" | "bf16"
               | "str" | "char" | "never" | "usize" ;

type_args      = "[" type { "," type } "]" ;
dim_args       = "[" dim_expr { "," dim_expr } "]" ;
dim_expr       = INT_LITERAL | IDENT | dim_expr ("*" | "+" | "-") dim_expr | "?" ;
type_params    = "[" type_param { "," type_param } "]" ;
type_param     = TYPE_IDENT [":" iface_bound { "+" iface_bound }]
               | "const" IDENT ":" type
               | "dim" IDENT ;
iface_bound    = TYPE_IDENT [type_args] ;

struct_def     = ["pub"] "struct" TYPE_IDENT type_params?
                 NEWLINE INDENT { field_def NEWLINE } DEDENT ;
struct_literal = TYPE_IDENT "#{" { IDENT ":" expr "," } "}" ;

map_literal    = "#{" { expr "=>" expr "," } "}" ;
set_literal    = "#{" { expr "," } "}" ;
tuple_literal  = "{" [ expr { "," expr } ] "}" ;

enum_def       = ["pub"] "enum" TYPE_IDENT type_params?
                 NEWLINE INDENT { variant_def NEWLINE } DEDENT ;

// Interface（ダックタイピング）
interface_def  = ["pub"] "interface" TYPE_IDENT type_params?
                 NEWLINE INDENT { iface_method NEWLINE } DEDENT ;
iface_method   = "fn" ["@" "[" ("mut" | "move") "]"] IDENT
                 "(" params ")" ["->" type] ;

// impl Interface for Type（コンパイル時インターフェース検証）
impl_for_def   = "impl" type_params? TYPE_IDENT [type_args] "for" type ;

test_def       = "test" [test_modifier] STRING_LIT [for_clause]
                 NEWLINE INDENT body DEDENT ;
test_modifier  = "property" | "snapshot" | "bench" ;
for_clause     = "for" "(" param { "," param } ")" ;
```

---

*End of Specification*
