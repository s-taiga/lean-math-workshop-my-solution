/-
このファイルでは群・部分群の定義と基本性質を見る。

# 目次
- Section 1. 群の定義と基本性質
- Section 2. 部分群の定義と基本性質
-/
import Mathlib.Tactic
import Mathlib.Data.SetLike.Basic
namespace Tutorial

section Section1
/-
# 1 群の定義と基本性質
数学的には、群とは以下のような情報をまとめたものと思える。
1. 台集合`G`
2. `G`上の二項演算`- * - : G × G → G`
3. 単位元`1 ∈ G`
4. 各元`a ∈ G`に`a⁻¹ ∈ G`を対応させる操作`(-)⁻¹ : G → G`
5. これらが、結合則や単位元や逆元についての条件を満たす
このチュートリアルでは*乗法的記法*のみを用いる。

これをLeanでは以下のように表す。
-/
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_inv_left : ∀ a : G, mul (inv a) a = one

/-
1. `G : Type`は`G`が集合であることを表すと思ってよい。
2. `mul : G → G → G`は二項演算（mul = multiplication）。
Leanで`→`は右結合的、つまり`mul : G → (G → G)`、つまり`mul`とは「`G`の元を与えたら「`G`から`G`への写像」を返すような写像」である。
人によっては`Hom(G, Hom(G, G))`と書くと分かりやすいかもしれない。
よって`mul`は二項演算と思える（`a`と`b`の結果は`mul a b`）。
このようにLeanでは`X × Y → Z`の代わりに`X → Y → Z`を使うことが多い。
3. `one : G`とは`G`の単位元のこと。
`G`の元を表すときは `∈`でなく `a : G`のように表すことに注意。
4. `inv : G → G`は`a`に対してその逆元（となるべきもの）を返す写像

ここまでが構造であって、普通の数学ではその後は公理であるが、Leanでは公理（が成り立つという事実）も一緒に群という一つの構造だと思う。
5. `mul_assoc`, `one_mul`, `mul_inv_left`が何を表すかはみれば分かるだろう。

見て分かる通り、今回は*左単位元と左逆元のみ*を要請としているが、群の公理はこれで十分である。
実際、後で*これが右単位元・右逆元であることを示して*いく。
-/

/-
例えばℤは足し算について群であることは次のように表現、証明できる。
（このチュートリアルで群は乗法的にかかれているので注意）
-/
example : Group ℤ where
  mul := fun x y ↦ x + y
  one := 0
  inv := fun x ↦ - x
  mul_assoc := by
    intro a b c
    ring
  one_mul := by
    intro a
    ring
  mul_inv_left := by
    intro a
    ring

-- 環`A`の可逆元全体`Aˣ`は積について群になる
variable [Ring A]

example : Group Aˣ where
  mul := fun a b ↦ a * b
  one := 1
  inv := fun a ↦ a⁻¹
  mul_assoc := by
    intro a b c
    ring_nf
    exact mul_assoc a b c
  one_mul := by
    intro a
    ring_nf
    exact one_mul a
  mul_inv_left := by
    intro a
    ring_nf
    exact mul_left_inv a

--以下この節では`G`を群とする。
variable [Group G]
/-
いちいち`G`の演算を`mul a b`等と書いていたのでは大変なので、
`*`と`1`と`⁻¹` (`\inv` または `\-` または `\-1`) が使えるようにするためのおまじない。
-/
instance : Mul G := ⟨Group.mul⟩
instance : One G := ⟨Group.one⟩
instance : Inv G := ⟨Group.inv⟩

-- 定義から出てくるものを、使えるよう名付けておく

/-- 群の積は結合的である。 -/
theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) := Group.mul_assoc a b c
-- `a * b * c`はLeanでは`(a * b) * c`のこと。
-- `(a * b) * c`と書いてもよい。

/-- `1`は左単位元。 -/
@[simp]
theorem one_mul (a : G) : 1 * a = a := Group.one_mul a

/-- `a⁻¹`は`a`の左逆元。 -/
@[simp]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 := Group.mul_inv_left a

/-
上に出てきた`@[simp]`について。
これは「左辺を簡単にすると右辺になる」形の定理につけておく。
すると次のように`simp` tacticがこれらを使えるようになる。
-/
example (a b : G) : (a * b)⁻¹ * (a * b) = 1 := by
  -- `simp`を使ってみよう。すると
  -- 自動的に`inv_mul_self`が使われて証明が終わる。
  -- `simp?`にすると使われた定理が分かる。
  exact inv_mul_self (a * b)

-- 後々のためにもう1つ`simp`を追加。証明中でも`simp`を積極的に使おう。
@[simp]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  calc
    a⁻¹ * (a * b) = (a⁻¹ * a) * b := by
      rw [← mul_assoc]
    _ = 1 * b := by
      rw [inv_mul_self]
    _ = b := by
      rw [one_mul]

/-
まずは`1`が右単位元でもあることを見ていきたい。
そのため次の補題を使う。
-/
/-- 等しいかどうかは左から元をかけてチェックできる。 -/
theorem mul_left_cancel (a : G) {x y : G} : a * x = a * y → x = y := by
  -- ヒント: `intro h`してから上のように`calc`で変形しよう
  -- （`calc`を使わず`rw`のみの縛りプレイでも可能）
  intro h
  calc x
    _ = 1 * x := by rw [one_mul]
    _ = (a⁻¹ * a) * x := by rw [inv_mul_self]
    _ = a⁻¹ * (a * x) := by rw [mul_assoc]
    _ = a⁻¹ * (a * y) := by rw [h]
    _ = (a⁻¹ * a) * y := by rw [← mul_assoc]
    _ = 1 * y := by rw [← inv_mul_self]
    _ = y := by rw [one_mul]

/-- `1`は右単位元でもある。 -/
@[simp]
theorem mul_one (a : G) : a * 1 = a := by
  /-
  ヒント: `mul_left_cancel`の`a`として`foo`を使いたいときは、
  `apply mul_left_cancel (a := foo)`または、単に
  `apply mul_left_cancel foo`とする。
  `foo`として何を使えばいいだろうか？
  その後は積極的に`simp`を使おう。
  -/
  apply mul_left_cancel (a := a⁻¹)
  calc a⁻¹ * (a * 1)
    _ = (a⁻¹ * a) * 1 := by rw [mul_assoc]
    _ = 1 * 1 := by rw [inv_mul_self]
    _ = 1 := by rw [one_mul]
    _ = a⁻¹ * a := by rw [inv_mul_self]

-- `a⁻¹`が`a`の右逆元でもあること
@[simp]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_left_cancel (a := a⁻¹)
  calc a⁻¹ * (a * a⁻¹)
    _ = (a⁻¹ * a) * a⁻¹ := by rw [mul_assoc]
    _ = 1 * a⁻¹ := by rw [inv_mul_self]
    _ = a⁻¹ := by rw [one_mul]
    _ = a⁻¹ * 1 := by rw [mul_one]

-- いろいろ便利なので練習も兼ねて`simp`を追加。
@[simp]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  rw [mul_inv_self]
  exact one_mul b

@[simp]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc]
  rw [mul_inv_self]
  exact mul_one a

@[simp]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc]
  rw [inv_mul_self]
  exact mul_one a

/-- 等しいかどうかは右から元をかけてチェックできる。 -/
theorem mul_right_cancel (a : G) {x y : G} : x * a = y * a → x = y := by
  intro h
  calc x
    _ = x * 1 := by rw [mul_one]
    _ = x * (a * a⁻¹) := by rw [mul_inv_self]
    _ = x * a * a⁻¹ := by rw [mul_assoc]
    _ = y * a * a⁻¹ := by rw [h]
    _ = y * (a * a⁻¹) := by rw [mul_assoc]
    _ = y * 1 := by rw [mul_inv_self]
    _ = y := by rw [mul_one]

/-- 左逆元の一意性 -/
theorem inv_eq_of_mul_eq_one_left {a x : G} : x * a = 1 → a⁻¹ = x := by
  intro h
  apply mul_right_cancel (a := a)
  rw [inv_mul_self]
  exact id (Eq.symm h)

-- その変種。後で便利かも。
theorem eq_inv_of_mul_eq_one_left {a x : G} : x * a = 1 → x = a⁻¹ :=
  fun h ↦ (inv_eq_of_mul_eq_one_left h).symm

@[simp]
theorem inv_one : (1 : G)⁻¹ = 1 := by
  apply inv_eq_of_mul_eq_one_left
  exact one_mul 1

@[simp]
theorem inv_inv {a : G} : a⁻¹⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_left
  exact mul_inv_self a

/-- 積の逆元は逆元をひっくり返した積。 -/
@[simp]
theorem mul_inv_rev {a b : G} : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  rw [← mul_assoc]
  rw [mul_assoc b⁻¹ a⁻¹ a]
  rw [inv_mul_self]
  rw [mul_one]
  exact inv_mul_self b

theorem mul_inv_eq_iff_eq_mul {a b c : G} : a * b⁻¹ = c ↔ a = c * b := by
  -- ヒント: `constructor`でゴールを分けよう
  constructor
  case mp =>
    intro h
    apply mul_right_cancel (a := b⁻¹)
    rw [mul_assoc c b b⁻¹]
    rw [mul_inv_self]
    rw [mul_one]
    exact h
  case mpr =>
    intro h
    apply mul_right_cancel (a := b)
    rw [mul_assoc a]
    rw [inv_mul_self]
    rw [mul_one]
    exact h

theorem mul_inv_eq_one {a b : G} : a * b⁻¹ = 1 ↔ a = b := by
  nth_rewrite 2 [← one_mul b]
  exact mul_inv_eq_iff_eq_mul

theorem inv_mul_eq_one {a b : G} : a⁻¹ * b = 1 ↔ a = b := by
  constructor
  case mp =>
    intro h
    apply mul_left_cancel (a := a⁻¹)
    rw [inv_mul_self]
    exact id (Eq.symm h)
  case mpr =>
    intro h
    rw [h]
    exact inv_mul_self b

end Section1


section Section2
/-
# 2. 部分群
群`G`の部分群とは、単位元を含み積と逆元で閉じた`G`の部分集合である。
これは以下のように定式化できる。
-/
structure Subgroup (G) [Group G] where
  carrier : Set G
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier
/-
- 群`G`に対して、`Set G`とは`G`の部分集合の集合と思ってよい。
- `carrier`とは部分群の台集合
- その他は部分群の公理

*Leanでの部分集合の扱いについて*
全体集合`X`の部分集合`A : Set X`については、
`x : X`が`A`に属することは、`x : A`でなく`x ∈ A`と書く。
上で`1 ∈ carrier`等書いているのはそのため。

*上級者向け、飛ばしてください*
集合`X`について`Set X`とは実は`X → Prop`のことで、
`A : Set X`とは「`X`の元が与えられたら、それが`A`に属するかどうかという命題を返す写像`A : G → Prop`のこと」
ようするに`{x : X | xについての条件 }`という部分集合の作り方の、
`xについての条件`のところを取り出したのが`A`である。
`x : X`がこの条件`A`を満たす、つまり`A x`のことを、
数学の慣習と合うように`x ∈ A`と書いている。
（`x ∈ A`の定義は実は`A x`なので、上で`carrier 1`とか書いてもエラーは出ない。）
このような実装をしているのは、`X`の元`x`の型は唯一つのみであって、
同時に`x : X`かつ`x : A`であることはありえない、という型理論の要請からきている。
-/

-- 以下この節では`G`を群、`H`をその部分群とする
variable [Group G] {H : Subgroup G}

/-
部分群とは「台集合と、ある公理たちが成り立つという事実との組」なので、
本来は`a ∈ H`とは書けず`a ∈ H.carrier`と書かなければならない。
それは面倒なので以下のおまじないにより`a ∈ H`と書ける。
-/
instance : SetLike (Subgroup G) G where
  coe H := H.carrier
  coe_injective' H₁ H₂ _ := by cases H₁; cases H₂; congr

namespace Subgroup

-- 定義からすぐ分かること

@[simp]
theorem one_mem : 1 ∈ H := H.one_mem'

theorem mul_mem {a b : G} : a ∈ H → b ∈ H → a * b ∈ H := H.mul_mem'

theorem inv_mem {a : G} : a ∈ H → a⁻¹ ∈ H := H.inv_mem'

theorem inv_mem_iff {a : G} : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor
  case mp =>
    nth_rewrite 2 [← inv_inv (a := a)]
    exact H.inv_mem'
  case mpr =>
    exact H.inv_mem'    

/-
部分群が等しいとは`∈`が同値なとき。
このような補題を`ext`マークつけておくと、
部分群が等しいことを示すとき`ext` tacticで使えるようになる。
-/
@[ext]
theorem ext {H K : Subgroup G} : (∀ x : G, x ∈ H ↔ x ∈ K) → H = K := SetLike.ext

end Subgroup

-- 最後にいくつか典型的な部分群を構成してこのファイルは終わり。

/-- 群`G`の中心、つまり全ての元と可換な元全体のなす部分群。 -/
def center (G) [Group G] : Subgroup G where
  carrier := { a : G | ∀ x : G, a * x = x * a}
  -- この部分集合が部分群の公理を満たすことを示そう。
  one_mem' := by
    intros a
    rw [one_mul, mul_one]
  mul_mem' := by
    intros a b ha hb ab
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := by
    intros a ha b
    rw [← inv_inv (a := b), ← mul_inv_rev, ← ha, mul_inv_rev]

/-
下の`centrizer`と`noramlizer`は少し面倒で難しい。
以降では使わないので*最初は飛ばして*、時間が余ったら解いてみることをおすすめします。
-/
variable (H)
/-- 部分群`H`の中心化群。 -/
def Subgroup.centralizer : Subgroup G where
  carrier := { a : G | ∀ x ∈ H, a * x = x * a }
  one_mem' := by
    intro a _
    rw [one_mul, mul_one]
  mul_mem' := by
    /- ヒント
    `ha : ∀ x, x ∈ H → a * x = x * a`と`hx : x ∈ H`があったら、
    `ha x hx`や`ha _ hx`で、`a * x = x * a`という等式が取り出せる。
    -/
    intro a b ha hb ab hab
    rw [mul_assoc, hb ab hab, ← mul_assoc, ha ab hab, mul_assoc]
  inv_mem' := by
    intro a ha b hb
    have hb_inv := Subgroup.inv_mem hb
    rw [← inv_inv (a := b), ← mul_inv_rev, ← ha b⁻¹ hb_inv, mul_inv_rev]

/- 役立つかもしれないヒント
`x * y * z * a * b`を`x * (y * z) * a * b`に変えたいときは、
`rw [mul_assoc x]`など、`mul_assoc`に適切な引数を渡せばよい。
（`mul_assoc a b c : a * b * c = a * (b * c)`だった。）
例えばこの場合は、`rw [mul_assoc _ _ z]`など、
引数を適当に省略して`_`とすることもできる。
こうすると、`?₁ * ?₂ * z`を探して`?₁ * (?₂ * z)`にしてくれる。
式変形が多い場合は`calc`を使うと混乱しないかもしれない。
もしくは冷静に紙に書きながら考えると、
短く証明できるかもしれない。
-/

/-- 部分群`H`の正規化群。 -/
def Subgroup.normalizer : Subgroup G where
  carrier := { a : G | ∀ x, x ∈ H ↔ a * x * a⁻¹ ∈ H }
  one_mem' := by
    intro a
    constructor
    case mp =>
      intro ha
      rw [one_mul, inv_one, mul_one]
      exact ha
    case mpr =>
      intro h1a1
      rw [← mul_one (a := a), ← inv_one, ← one_mul (a := a * 1⁻¹), ← mul_assoc]
      exact h1a1
  mul_mem' := by
    intro a b ha hb ab
    constructor
    case mp =>
      intro hab
      rw [mul_inv_rev, ← mul_assoc _ b⁻¹, mul_assoc a, mul_assoc a, ← ha, ← hb]
      exact hab
    case mpr =>
      intro hababab_inv
      rw [hb, ha, ← mul_assoc a, ← mul_assoc a, mul_assoc _ b⁻¹, ← mul_inv_rev]
      exact hababab_inv
  inv_mem' := by
    intro a ha b
    constructor
    case mp =>
      intro hb
      rw [ha, ← mul_assoc a, ← mul_assoc a, mul_inv_self, one_mul, mul_assoc, inv_mul_self, mul_one]
      exact hb
    case mpr =>
      intro haba
      rw [← mul_one (a := b), ← inv_mul_self (a := a⁻¹), ← mul_assoc, ← one_mul (a := b * a⁻¹⁻¹ * a⁻¹), ← mul_inv_self (a := a)]
      rw [mul_assoc a, ← mul_assoc a⁻¹, ← mul_assoc a, ← mul_assoc a⁻¹, ← ha]
      exact haba

end Section2

end Tutorial
