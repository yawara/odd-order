/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsMonomialSetup

/-!
# Isaacs Problem 6A.2 — 奇数位数の非可換 Frobenius complement (書籍 p. 184)

**主張**: 位数 43 の体 `F` の乗法群で `α` の位数を 7, `ε` の位数を 3 とし,
`GL(3, 43)` の中で
`a = diag(α, α⁴, α²)`, `b = ![[0,1,0],[0,0,1],[ε,0,0]]`
とおくと `A = ⟨a, b⟩` は**非巡回で位数 63**, その `43³` 位のベクトル空間 `V` への自然な作用は
**Frobenius**。書籍の Note: これは**奇数位数の非可換群が Frobenius complement になりうる**
ことを示す例。

⚠ **一般化**: 証明は「位数 7 の `α` と位数 3 の `ε` をもつ体」でそのまま通るので,
本ファイルでは一般の体 `F` で述べる (書籍の `F = 𝔽₄₃` はその特殊化; 43 での存在は
`exists_orderOf_eq_seven_zmod_fortyThree` / `exists_orderOf_eq_three_zmod_fortyThree`)。

## 内容

**行列の関係式**: `matA α = diag(α, α⁴, α²)` / `matB ε = ![[0,1,0],[0,0,1],[ε,0,0]]` /
`matA_pow_seven` (`a⁷ = 1`) / `matB_pow_three` (**`b³ = ε · 1`** はスカラー) /
`matB_pow_nine` (`b⁹ = 1`) / `matA_mul_matB` (**`a · b = b · a²`**, 書籍 hint の
「`b` は `⟨a⟩` を正規化」の実内容 — 実際 `b⁻¹ a b = a²`, `b a b⁻¹ = a⁴`)。

**群構造**: `uA` / `uB` (`GL(3,F)` の元) / `orderOf_uA = 7` / `orderOf_uB = 9` /
`uB_mem_normalizer` / `grpA` (= `A`) / **`card_grpA` (`|A| = 63`)** /
**`not_isCyclic_grpA`**。

**Frobenius 性**: 正規形 `exists_pow_mul_pow_of_mem_grpA` (`A` の元は `aⁱ bʲ`) と
立方計算 `cube_uA_pow_mul_uB` (`(aⁱb)³ = b³`) / `cube_uA_pow_mul_uB_sq`
(`(aⁱb²)³ = b⁶`) から **`isFrobeniusAction_grpA`**。⭐ 書籍 hint の「素数位数の元に
還元」も Sylow も要らない (下記 `### Frobenius 性` 節参照)。

**書籍の場合 `F = 𝔽₄₃`**: `exists_odd_order_nonabelian_frobenius_complement`。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.2: `GL(3,43)` の奇数位数非可換 Frobenius complement (p. 184) -/

variable {F : Type*} [Field F]

/-- 書籍 6A.2 の `a = diag(α, α⁴, α²)`。 -/
def matA (α : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![α, α ^ 4, α ^ 2]

/-- 書籍 6A.2 の `b = ![[0,1,0],[0,0,1],[ε,0,0]]`。 -/
def matB (ε : F) : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; ε, 0, 0]

theorem matA_pow (α : F) (n : ℕ) :
    matA α ^ n = Matrix.diagonal ![α ^ n, (α ^ 4) ^ n, (α ^ 2) ^ n] := by
  rw [matA, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem matA_apply_diag (α : F) (i : Fin 3) :
    matA α i i = ![α, α ^ 4, α ^ 2] i := Matrix.diagonal_apply_eq _ i

theorem matA_pow_seven {α : F} (hα : α ^ 7 = 1) : matA α ^ 7 = 1 := by
  have hk : ∀ k : ℕ, (α ^ k) ^ 7 = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, hα, one_pow]
  rw [matA_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact hα
  · exact hk 4
  · exact hk 2

/-- `b³` はスカラー行列 `ε · 1`。 -/
theorem matB_pow_three (ε : F) : matB ε ^ 3 = ε • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB, Matrix.mul_apply, Fin.sum_univ_three]

theorem matB_pow_nine {ε : F} (hε : ε ^ 3 = 1) : matB ε ^ 9 = 1 := by
  have h : matB ε ^ 9 = (matB ε ^ 3) ^ 3 := by rw [← pow_mul]
  rw [h, matB_pow_three, smul_pow, one_pow, hε, one_smul]

/-- **`a · b = b · a²`** — `b` は `⟨a⟩` を正規化し `b⁻¹ a b = a²`。 -/
theorem matA_mul_matB {α : F} (hα : α ^ 7 = 1) (ε : F) :
    matA α * matB ε = matB ε * matA α ^ 2 := by
  have h8 : (α ^ 4) ^ 2 = α := by
    have h : (α ^ 4) ^ 2 = α ^ 7 * α := by ring
    rw [h, hα, one_mul]
  have h4 : (α ^ 2) ^ 2 = α ^ 4 := by ring
  rw [matA_pow, matA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB, Matrix.mul_apply, Matrix.diagonal_apply, h8, h4, mul_comm]

/-! ### `GL(3, F)` の元としての `a`, `b` と `A = ⟨a, b⟩` -/

variable {α ε : F}

/-- 書籍 6A.2 の `a ∈ GL(3, F)` (逆元は `a⁶`)。 -/
def uA (hα : orderOf α = 7) : (Matrix (Fin 3) (Fin 3) F)ˣ where
  val := matA α
  inv := matA α ^ 6
  val_inv := by
    have h : matA α * matA α ^ 6 = matA α ^ 7 := (pow_succ' (matA α) 6).symm
    rw [h, matA_pow_seven (hα ▸ pow_orderOf_eq_one α)]
  inv_val := by
    have h : matA α ^ 6 * matA α = matA α ^ 7 := (pow_succ (matA α) 6).symm
    rw [h, matA_pow_seven (hα ▸ pow_orderOf_eq_one α)]

/-- 書籍 6A.2 の `b ∈ GL(3, F)` (逆元は `b⁸`)。 -/
def uB (hε : orderOf ε = 3) : (Matrix (Fin 3) (Fin 3) F)ˣ where
  val := matB ε
  inv := matB ε ^ 8
  val_inv := by
    have h : matB ε * matB ε ^ 8 = matB ε ^ 9 := (pow_succ' (matB ε) 8).symm
    rw [h, matB_pow_nine (hε ▸ pow_orderOf_eq_one ε)]
  inv_val := by
    have h : matB ε ^ 8 * matB ε = matB ε ^ 9 := (pow_succ (matB ε) 8).symm
    rw [h, matB_pow_nine (hε ▸ pow_orderOf_eq_one ε)]

@[simp] theorem uA_val (hα : orderOf α = 7) :
    ((uA hα : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = matA α := rfl

@[simp] theorem uB_val (hε : orderOf ε = 3) :
    ((uB hε : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = matB ε := rfl

theorem uA_pow_seven (hα : orderOf α = 7) : uA hα ^ 7 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, uA_val, Units.val_one]
  exact matA_pow_seven (hα ▸ pow_orderOf_eq_one α)

theorem uB_pow_nine (hε : orderOf ε = 3) : uB hε ^ 9 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, uB_val, Units.val_one]
  exact matB_pow_nine (hε ▸ pow_orderOf_eq_one ε)

theorem orderOf_uA (hα : orderOf α = 7) : orderOf (uA hα) = 7 := by
  have hne : uA hα ≠ 1 := by
    intro h
    have h1 : matA α = 1 := by rw [← uA_val hα, h, Units.val_one]
    have : α = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [matA, Matrix.diagonal_apply, Matrix.one_apply] using this
    rw [this, orderOf_one] at hα
    omega
  have hdvd : orderOf (uA hα) ∣ 7 := orderOf_dvd_of_pow_eq_one (uA_pow_seven hα)
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h7
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h7

theorem orderOf_uB (hε : orderOf ε = 3) : orderOf (uB hε) = 9 := by
  have hne : uB hε ^ 3 ≠ 1 := by
    intro h
    have h1 : matB ε ^ 3 = 1 := by
      rw [← uB_val hε, ← Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [matB_pow_three] at h1
    have : ε = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.one_apply] using this
    rw [this, orderOf_one] at hε
    omega
  have hdvd : orderOf (uB hε) ∣ 9 := orderOf_dvd_of_pow_eq_one (uB_pow_nine hε)
  have hmem : orderOf (uB hε) ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [h]; norm_num)) hne
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [h])) hne
  · exact h

/-- **`a · b = b · a²`** (単元版)。 -/
theorem uA_mul_uB (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    uA hα * uB hε = uB hε * uA hα ^ 2 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, uA_val, uB_val]
  exact matA_mul_matB (hα ▸ pow_orderOf_eq_one α) ε

/-- `b⁻¹ a b = a²`。 -/
theorem uB_inv_mul_uA_mul_uB (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    (uB hε)⁻¹ * uA hα * uB hε = uA hα ^ 2 := by
  have h := uA_mul_uB hα hε
  calc (uB hε)⁻¹ * uA hα * uB hε = (uB hε)⁻¹ * (uA hα * uB hε) := by group
    _ = (uB hε)⁻¹ * (uB hε * uA hα ^ 2) := by rw [h]
    _ = uA hα ^ 2 := by group

/-- `b a b⁻¹ = a⁴` (`a⁸ = a` と `b a² b⁻¹ = a` から)。 -/
theorem uB_mul_uA_mul_uB_inv (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    uB hε * uA hα * (uB hε)⁻¹ = uA hα ^ 4 := by
  have h2 : uB hε * uA hα ^ 2 * (uB hε)⁻¹ = uA hα := by
    have h := uA_mul_uB hα hε
    calc uB hε * uA hα ^ 2 * (uB hε)⁻¹ = (uB hε * uA hα ^ 2) * (uB hε)⁻¹ := by group
      _ = (uA hα * uB hε) * (uB hε)⁻¹ := by rw [h]
      _ = uA hα := by group
  have h8 : uA hα ^ 8 = uA hα := by
    have h : uA hα ^ 8 = uA hα ^ 7 * uA hα := by rw [← pow_succ]
    rw [h, uA_pow_seven hα, one_mul]
  calc uB hε * uA hα * (uB hε)⁻¹
      = uB hε * uA hα ^ 8 * (uB hε)⁻¹ := by rw [h8]
    _ = (uB hε * uA hα ^ 2 * (uB hε)⁻¹) ^ 4 := by rw [conj_pow, ← pow_mul]
    _ = uA hα ^ 4 := by rw [h2]

/-- 書籍 6A.2 の `A = ⟨a, b⟩ ≤ GL(3, F)`。 -/
def grpA (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    Subgroup ((Matrix (Fin 3) (Fin 3) F)ˣ) :=
  Subgroup.closure {uA hα, uB hε}

theorem grpA_eq_sup (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    grpA hα hε = Subgroup.zpowers (uA hα) ⊔ Subgroup.zpowers (uB hε) := by
  rw [grpA, show ({uA hα, uB hε} : Set ((Matrix (Fin 3) (Fin 3) F)ˣ))
      = {uA hα} ∪ {uB hε} from rfl,
    Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

/-- `b` は `⟨a⟩` を正規化する。 -/
theorem uB_mem_normalizer (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    uB hε ∈ Subgroup.normalizer (Subgroup.zpowers (uA hα)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨4 * n, ?_⟩
    rw [zpow_mul, show ((uA hα) ^ (4 : ℤ)) = ((uA hα) ^ (4 : ℕ)) by norm_cast,
      ← uB_mul_uA_mul_uB_inv hα hε, conj_zpow]
  · rintro ⟨n, hn⟩
    refine ⟨2 * n, ?_⟩
    have hstep : ((uB hε)⁻¹ * uA hα * ((uB hε)⁻¹)⁻¹) ^ n
        = (uB hε)⁻¹ * (uA hα ^ n) * ((uB hε)⁻¹)⁻¹ := conj_zpow
    rw [inv_inv] at hstep
    rw [uB_inv_mul_uA_mul_uB hα hε] at hstep
    rw [zpow_mul, show ((uA hα) ^ (2 : ℤ)) = ((uA hα) ^ (2 : ℕ)) by norm_cast, hstep, hn]
    group

/-! ### `|A| = 63` と非巡回性 -/

/-- **Isaacs Problem 6A.2 (前半)**: `A = ⟨a, b⟩` の位数は `63 = 7 · 9`。 -/
theorem card_grpA [Finite F] (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    Nat.card ↥(grpA hα hε) = 63 := by
  rw [grpA_eq_sup, card_sup_of_le_normalizer_of_coprime
    (Subgroup.zpowers_le.mpr (uB_mem_normalizer hα hε)) ?_]
  · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_uA, orderOf_uB]
  · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_uA, orderOf_uB]
    decide

/-- **Isaacs Problem 6A.2 (前半)**: `A = ⟨a, b⟩` は**非巡回** (`b⁻¹ a b = a² ≠ a`)。 -/
theorem not_isCyclic_grpA (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    ¬ IsCyclic ↥(grpA hα hε) := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcomm : ∀ x y : ↥(grpA hα hε), x * y = y * x := by
    intro x y
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← zpow_add, ← zpow_add, add_comm]
  have hAmem : uA hα ∈ grpA hα hε := Subgroup.subset_closure (by simp)
  have hBmem : uB hε ∈ grpA hα hε := Subgroup.subset_closure (by simp)
  have h := hcomm ⟨uA hα, hAmem⟩ ⟨uB hε, hBmem⟩
  have hcomm' : uA hα * uB hε = uB hε * uA hα := congrArg Subtype.val h
  have hsq : uB hε * uA hα = uB hε * uA hα ^ 2 := by
    rw [← hcomm', uA_mul_uB hα hε]
  have hone : uA hα = 1 := by
    have := mul_left_cancel hsq
    calc uA hα = uA hα ^ 2 * (uA hα)⁻¹ := by group
      _ = uA hα * (uA hα)⁻¹ := by rw [← this]
      _ = 1 := by group
  have hord := orderOf_uA hα
  rw [hone, orderOf_one] at hord
  omega

/-! ### Frobenius 性

書籍 hint は「素数位数の元 `t` について `C_V(t) = 1` を見れば十分」だが, **正規形
`x = aⁱ bʲ` を使うと素数位数への還元も Sylow も要らない**:

* `3 ∣ j` のとき `bʲ = εᵐ · 1` (スカラー) なので `x = diag(εᵐαⁱ, εᵐα⁴ⁱ, εᵐα²ⁱ)`。
  非零ベクトルを固定するなら対角成分のどれかが `1`, ところが `⟨ε⟩ ⊓ ⟨α⟩ = 1` ゆえ
  `εᵐ = 1` かつ `α^{kⁱ} = 1` となり `x = 1`。
* `3 ∤ j` のとき **`x³` は非単位スカラー** (`aⁱ` の寄与は `1 + 4^j + 4^{2j} ≡ 0 (mod 7)` で
  消え, `b^{3j} = ε^j · 1` が残る) — スカラーは非零ベクトルを固定しない。
-/

/-- **正規形**: `A = ⟨a, b⟩` の元はすべて `aⁱ bʲ` (`i j : ℕ`) の形。 -/
theorem exists_pow_mul_pow_of_mem_grpA [Finite F] (hα : orderOf α = 7) (hε : orderOf ε = 3)
    {x : (Matrix (Fin 3) (Fin 3) F)ˣ} (hx : x ∈ grpA hα hε) :
    ∃ i j : ℕ, x = uA hα ^ i * uB hε ^ j :=
  exists_pow_mul_pow_of_mem_closure_pair (uB_mem_normalizer hα hε) hx

/-- `b aⁱ b⁻¹ = a^{4i}`。 -/
theorem uB_mul_uA_pow_mul_uB_inv (hα : orderOf α = 7) (hε : orderOf ε = 3) (i : ℕ) :
    uB hε * uA hα ^ i * (uB hε)⁻¹ = uA hα ^ (4 * i) := by
  rw [← conj_pow, uB_mul_uA_mul_uB_inv hα hε, ← pow_mul]

/-- `b aⁱ = a^{4i} b`。 -/
theorem uB_mul_uA_pow (hα : orderOf α = 7) (hε : orderOf ε = 3) (i : ℕ) :
    uB hε * uA hα ^ i = uA hα ^ (4 * i) * uB hε := by
  rw [← uB_mul_uA_pow_mul_uB_inv hα hε i]
  group

/-- `b² aⁱ = a^{16i} b²`。 -/
theorem uB_sq_mul_uA_pow (hα : orderOf α = 7) (hε : orderOf ε = 3) (i : ℕ) :
    uB hε ^ 2 * uA hα ^ i = uA hα ^ (16 * i) * uB hε ^ 2 := by
  have h : uB hε ^ 2 * uA hα ^ i = uB hε * (uB hε * uA hα ^ i) := by
    rw [pow_two, mul_assoc]
  rw [h, uB_mul_uA_pow hα hε i]
  have h2 : uB hε * (uA hα ^ (4 * i) * uB hε) = (uB hε * uA hα ^ (4 * i)) * uB hε := by
    rw [mul_assoc]
  rw [h2, uB_mul_uA_pow hα hε (4 * i), show 4 * (4 * i) = 16 * i by ring, pow_two, mul_assoc]

theorem uA_pow_mul_seven (hα : orderOf α = 7) (k : ℕ) : uA hα ^ (7 * k) = 1 := by
  rw [pow_mul, uA_pow_seven hα, one_pow]

/-- `(aⁱ b)³ = b³` — `aⁱ` の寄与 `1 + 4 + 16 = 21 ≡ 0 (mod 7)` が消える。 -/
theorem cube_uA_pow_mul_uB (hα : orderOf α = 7) (hε : orderOf ε = 3) (i : ℕ) :
    (uA hα ^ i * uB hε) ^ 3 = uB hε ^ 3 := by
  have h21 : uA hα ^ (21 * i) = 1 := by
    rw [show 21 * i = 7 * (3 * i) by ring]
    exact uA_pow_mul_seven hα _
  have expand : (uA hα ^ i * uB hε) ^ 3
      = uA hα ^ i * (uB hε * uA hα ^ i) * (uB hε * uA hα ^ i) * uB hε := by
    rw [pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  rw [expand, uB_mul_uA_pow hα hε i]
  have step : uA hα ^ i * (uA hα ^ (4 * i) * uB hε) * (uA hα ^ (4 * i) * uB hε) * uB hε
      = uA hα ^ i * uA hα ^ (4 * i) * (uB hε * uA hα ^ (4 * i)) * (uB hε * uB hε) := by
    simp only [mul_assoc]
  rw [step, uB_mul_uA_pow hα hε (4 * i)]
  have final : uA hα ^ i * uA hα ^ (4 * i) * (uA hα ^ (4 * (4 * i)) * uB hε) * (uB hε * uB hε)
      = uA hα ^ (21 * i) * uB hε ^ 3 := by
    rw [show (21 : ℕ) * i = i + 4 * i + 4 * (4 * i) by ring, pow_add, pow_add,
      pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  rw [final, h21, one_mul]

/-- `(aⁱ b²)³ = b⁶` — `aⁱ` の寄与 `1 + 16 + 256 = 273 = 39·7 ≡ 0 (mod 7)` が消える。 -/
theorem cube_uA_pow_mul_uB_sq (hα : orderOf α = 7) (hε : orderOf ε = 3) (i : ℕ) :
    (uA hα ^ i * uB hε ^ 2) ^ 3 = uB hε ^ 6 := by
  have h273 : uA hα ^ (273 * i) = 1 := by
    rw [show 273 * i = 7 * (39 * i) by ring]
    exact uA_pow_mul_seven hα _
  have expand : (uA hα ^ i * uB hε ^ 2) ^ 3
      = uA hα ^ i * (uB hε ^ 2 * uA hα ^ i) * (uB hε ^ 2 * uA hα ^ i) * uB hε ^ 2 := by
    rw [pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  rw [expand, uB_sq_mul_uA_pow hα hε i]
  have step : uA hα ^ i * (uA hα ^ (16 * i) * uB hε ^ 2) * (uA hα ^ (16 * i) * uB hε ^ 2)
        * uB hε ^ 2
      = uA hα ^ i * uA hα ^ (16 * i) * (uB hε ^ 2 * uA hα ^ (16 * i))
        * (uB hε ^ 2 * uB hε ^ 2) := by
    simp only [mul_assoc]
  rw [step, uB_sq_mul_uA_pow hα hε (16 * i)]
  have final : uA hα ^ i * uA hα ^ (16 * i) * (uA hα ^ (16 * (16 * i)) * uB hε ^ 2)
        * (uB hε ^ 2 * uB hε ^ 2)
      = uA hα ^ (273 * i) * uB hε ^ 6 := by
    rw [show (273 : ℕ) * i = i + 16 * i + 16 * (16 * i) by ring, pow_add, pow_add,
      show (6 : ℕ) = 2 + 2 + 2 by norm_num, pow_add, pow_add]
    simp only [mul_assoc]
  rw [final, h273, one_mul]

/-! ### 不動点の解析 -/

/-- `⟨ε⟩ ⊓ ⟨α⟩ = 1` の元形: `c³ = 1` かつ `c⁷ = 1` なら `c = 1`。 -/
theorem eq_one_of_pow_three_pow_seven {c : F} (h3 : c ^ 3 = 1) (h7 : c ^ 7 = 1) : c = 1 := by
  have hd : orderOf c ∣ Nat.gcd 3 7 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h7)
  rw [show Nat.gcd 3 7 = 1 by norm_num] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem uB_pow_three_val (hε : orderOf ε = 3) :
    ((uB hε ^ 3 : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F)
      = ε • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [Units.val_pow_eq_pow_val, uB_val, matB_pow_three]

/-- `b³ = ε · 1` はスカラーゆえ `GL(3,F)` の中心に入る。 -/
theorem uB_pow_three_commute (hε : orderOf ε = 3) (y : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    Commute (uB hε ^ 3) y := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, uB_pow_three_val hε, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one]

/-- **Isaacs Problem 6A.2 (後半)** ⭐: `A = ⟨a, b⟩` の位数 `|F|³` のベクトル空間 `V = F³` への
自然な作用は **Frobenius**。 -/
theorem isFrobeniusAction_grpA [Finite F] (hα : orderOf α = 7) (hε : orderOf ε = 3) :
    IsFrobeniusAction ↥(grpA hα hε) (Multiplicative (Fin 3 → F)) := by
  intro x hxne w hwne hfix
  -- ベクトルと行列に翻訳
  set v : Fin 3 → F := Multiplicative.toAdd w with hvdef
  have hvne : v ≠ 0 := by
    intro h
    exact hwne (Multiplicative.toAdd.injective (by rw [← hvdef, h]; rfl))
  set X : (Matrix (Fin 3) (Fin 3) F)ˣ := (x : (Matrix (Fin 3) (Fin 3) F)ˣ) with hXdef
  have hsmul : X • v = v := congrArg Multiplicative.toAdd hfix
  have hfixv : (X : Matrix (Fin 3) (Fin 3) F).mulVec v = v := hsmul
  have hα7 : α ^ 7 = 1 := hα ▸ pow_orderOf_eq_one α
  have hε3 : ε ^ 3 = 1 := hε ▸ pow_orderOf_eq_one ε
  have hεne : ε ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hε
    omega
  -- `7 ∤ c` なら `α^{ci} = 1 ⟹ αⁱ = 1`
  have key : ∀ c i : ℕ, Nat.Coprime 7 c → α ^ (c * i) = 1 → α ^ i = 1 := by
    intro c i hc h
    have h7 : (7 : ℕ) ∣ c * i := hα ▸ orderOf_dvd_of_pow_eq_one h
    obtain ⟨t, rfl⟩ := hc.dvd_of_dvd_mul_left (by rwa [mul_comm] at h7)
    rw [pow_mul, hα7, one_pow]
  -- 正規形 `X = aⁱ bʲ` と `j = 3m + r`
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_grpA hα hε x.2
  obtain ⟨m, r, hr, hjmr⟩ : ∃ m r, r < 3 ∧ j = 3 * m + r :=
    ⟨j / 3, j % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 3).symm⟩
  set Z : (Matrix (Fin 3) (Fin 3) F)ˣ := uB hε ^ 3 with hZdef
  have hZ3 : Z ^ 3 = 1 := by
    rw [hZdef, ← pow_mul]
    exact uB_pow_nine hε
  have hZval : ∀ k : ℕ, ((Z ^ k : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F)
      = ε ^ k • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro k
    rw [Units.val_pow_eq_pow_val, hZdef, uB_pow_three_val hε, smul_pow, one_pow]
  have hcomm : Commute (Z ^ m) (uA hα ^ i) := (uB_pow_three_commute hε (uA hα ^ i)).pow_left m
  have hXform : X = Z ^ m * (uA hα ^ i * uB hε ^ r) := by
    rw [hXdef, hij, hjmr, pow_add, pow_mul, ← hZdef, ← mul_assoc, ← hcomm.eq, mul_assoc]
  -- `3 ∤ r` のときに使う: `X³ = (aⁱ bʳ)³`
  have hX3 : X ^ 3 = (uA hα ^ i * uB hε ^ r) ^ 3 := by
    have hc2 : Commute (Z ^ m) (uA hα ^ i * uB hε ^ r) :=
      (uB_pow_three_commute hε (uA hα ^ i * uB hε ^ r)).pow_left m
    rw [hXform, hc2.mul_pow, ← pow_mul, mul_comm m 3, pow_mul, hZ3, one_pow, one_mul]
  -- `X` が `v` を固定するなら `X³` も固定する
  have hfix3 : (X ^ 3 : (Matrix (Fin 3) (Fin 3) F)ˣ) • v = v := by
    rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, hsmul, hsmul, hsmul]
  interval_cases r
  · -- `r = 0`: `X` は対角行列 `diag(εᵐαⁱ, εᵐα⁴ⁱ, εᵐα²ⁱ)`
    rw [pow_zero, mul_one, hcomm.eq] at hXform
    have hXval : (X : Matrix (Fin 3) (Fin 3) F)
        = Matrix.diagonal (fun k => ![α ^ i, (α ^ 4) ^ i, (α ^ 2) ^ i] k * ε ^ m) := by
      rw [hXform, Units.val_mul, Units.val_pow_eq_pow_val, uA_val, matA_pow, hZval,
        diagonal_mul_scalar]
    rw [hXval] at hfixv
    obtain ⟨k, hk⟩ := exists_diagonal_eq_one_of_mulVec_eq hvne hfixv
    have hgen : ∀ c : ℕ, ((α ^ c) ^ i) ^ 7 = 1 := fun c => by
      rw [← pow_mul, ← pow_mul, show c * (i * 7) = 7 * (c * i) by ring, pow_mul, hα7, one_pow]
    have hgen0 : (α ^ i) ^ 7 = 1 := by
      rw [← pow_mul, show i * 7 = 7 * i by ring, pow_mul, hα7, one_pow]
    have hd7 : ![α ^ i, (α ^ 4) ^ i, (α ^ 2) ^ i] k ^ 7 = 1 := by
      fin_cases k
      · exact hgen0
      · exact hgen 4
      · exact hgen 2
    -- `εᵐ` は `3` 乗でも `7` 乗でも `1` ⟹ `εᵐ = 1`
    have hεm : ε ^ m = 1 := by
      refine eq_one_of_pow_three_pow_seven ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hε3, one_pow]
      · have h7 : (![α ^ i, (α ^ 4) ^ i, (α ^ 2) ^ i] k * ε ^ m) ^ 7 = 1 := by
          rw [hk, one_pow]
        rw [mul_pow, hd7, one_mul] at h7
        exact h7
    have hdk : ![α ^ i, (α ^ 4) ^ i, (α ^ 2) ^ i] k = 1 := by
      rw [hεm, mul_one] at hk; exact hk
    have hai7 : α ^ i = 1 := by
      fin_cases k
      · exact hdk
      · exact key 4 i (by norm_num) (by rw [pow_mul]; exact hdk)
      · exact key 2 i (by norm_num) (by rw [pow_mul]; exact hdk)
    have hgen2 : ∀ c : ℕ, (α ^ c) ^ i = 1 := fun c => by
      rw [← pow_mul, mul_comm, pow_mul, hai7, one_pow]
    have hai : uA hα ^ i = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, uA_val, matA_pow, Units.val_one, ← Matrix.diagonal_one]
      congr 1
      funext p
      fin_cases p
      · exact hai7
      · exact hgen2 4
      · exact hgen2 2
    have hzm : Z ^ m = 1 := by
      refine Units.ext ?_
      rw [hZval, hεm, one_smul, Units.val_one]
    have hXone : X = 1 := by rw [hXform, hzm, hai, mul_one]
    exact hxne (Subtype.ext hXone)
  · -- `r = 1`: `X³ = b³ = ε · 1` は非単位スカラー
    have hZ1 : (Z : Matrix (Fin 3) (Fin 3) F) = ε • 1 := by
      rw [hZdef, uB_pow_three_val hε]
    rw [pow_one, cube_uA_pow_mul_uB hα hε, ← hZdef] at hX3
    rw [hX3] at hfix3
    exact scalar_mulVec_ne_of_ne_one hεne hvne (by rw [← hZ1]; exact hfix3)
  · -- `r = 2`: `X³ = b⁶ = ε² · 1` は非単位スカラー
    have hZ2 : uB hε ^ 6 = Z ^ 2 := by rw [hZdef, ← pow_mul]
    rw [cube_uA_pow_mul_uB_sq hα hε, hZ2] at hX3
    rw [hX3] at hfix3
    have hε2ne : ε ^ 2 ≠ 1 := by
      intro h
      have hd : orderOf ε ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rw [hε] at hd
      omega
    exact scalar_mulVec_ne_of_ne_one hε2ne hvne (by rw [← hZval 2]; exact hfix3)

/-! ### 書籍の場合 `F = 𝔽₄₃` -/

instance : Fact (Nat.Prime 43) := ⟨by norm_num⟩

/-- `𝔽₄₃` の乗法群に位数 7 の元がある (`-2 = 41`; `(-2)⁷ = -128 = 1 - 3·43`)。 -/
theorem exists_orderOf_eq_seven_zmod_fortyThree : ∃ α : ZMod 43, orderOf α = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ⟨41, orderOf_eq_prime (by decide) (by decide)⟩

/-- `𝔽₄₃` の乗法群に位数 3 の元がある (`6`; `6³ = 216 = 1 + 5·43`)。 -/
theorem exists_orderOf_eq_three_zmod_fortyThree : ∃ ε : ZMod 43, orderOf ε = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨6, orderOf_eq_prime (by decide) (by decide)⟩

/-- ベクトル空間 `V = 𝔽₄₃³` の位数は `43³` (書籍の「位数 `43³` のベクトル空間」)。 -/
theorem card_fin_three_zmod_fortyThree : Nat.card (Fin 3 → ZMod 43) = 43 ^ 3 := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- **Isaacs Problem 6A.2** (p. 184) ⭐ 書籍の主張そのもの: `GL(3, 43)` には**位数 63 の
非巡回部分群**で, 位数 `43³` のベクトル空間への自然な作用が **Frobenius** なものがある。

書籍の Note: これは**奇数位数の非可換群が Frobenius complement になりうる**ことを示す例。 -/
theorem exists_odd_order_nonabelian_frobenius_complement :
    ∃ A : Subgroup ((Matrix (Fin 3) (Fin 3) (ZMod 43))ˣ),
      Nat.card ↥A = 63 ∧ ¬ IsCyclic ↥A ∧
        IsFrobeniusAction ↥A (Multiplicative (Fin 3 → ZMod 43)) := by
  obtain ⟨α, hα⟩ := exists_orderOf_eq_seven_zmod_fortyThree
  obtain ⟨ε, hε⟩ := exists_orderOf_eq_three_zmod_fortyThree
  exact ⟨grpA hα hε, card_grpA hα hε, not_isCyclic_grpA hα hε, isFrobeniusAction_grpA hα hε⟩

end

end OddOrder.Isaacs.Ch06
