/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.ProblemsOrder120
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6A

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

## この節の内容 (第 1 段: 行列の関係式)

* `matA` / `matB` — 書籍の `a`, `b`。
* `matA_pow` — `a^n = diag(αⁿ, α⁴ⁿ, α²ⁿ)`。
* `matA_pow_seven` — `a⁷ = 1`。
* `matB_pow_three` — `b³ = ε • 1` (スカラー), したがって `matB_pow_nine`: `b⁹ = 1`。
* `matA_mul_matB` — **`a · b = b · a²`** (`b` は `⟨a⟩` を正規化し `b⁻¹ a b = a²`)。
-/

namespace OddOrder.Isaacs.Ch06

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

/-- `S ≤ N_G(N)` かつ位数が互いに素なら `|N ⊔ S| = |N| · |S|`。

`Ch01.card_sup_of_normal_of_coprime` (Problem 1C.4 の helper) の「`N` が `G` で正規」という
仮定を「`S` が `N` を正規化する」に緩めた版 (`N ⊔ S` の中に降りて適用する)。 -/
theorem card_sup_of_le_normalizer_of_coprime {G : Type*} [Group G] [Finite G]
    {N S : Subgroup G} (hnorm : S ≤ Subgroup.normalizer N)
    (h : Nat.Coprime (Nat.card ↥N) (Nat.card ↥S)) :
    Nat.card ↥(N ⊔ S) = Nat.card ↥N * Nat.card ↥S := by
  have hNL : N ≤ N ⊔ S := le_sup_left
  have hSL : S ≤ N ⊔ S := le_sup_right
  haveI hnormal : (N.subgroupOf (N ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr (sup_le Subgroup.le_normalizer hnorm)
  have hcN : Nat.card ↥(N.subgroupOf (N ⊔ S)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hcS : Nat.card ↥(S.subgroupOf (N ⊔ S)) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hsup : N.subgroupOf (N ⊔ S) ⊔ S.subgroupOf (N ⊔ S) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNL hSL, Subgroup.subgroupOf_self]
  have hres := Ch01.card_sup_of_normal_of_coprime (N := N.subgroupOf (N ⊔ S))
    (S := S.subgroupOf (N ⊔ S)) hnormal (by rw [hcN, hcS]; exact h)
  rw [hsup, Subgroup.card_top, hcN, hcS] at hres
  exact hres

instance finiteMatrixUnits {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    [Finite R] : Finite (Matrix n n R)ˣ :=
  Finite.of_injective _ Units.val_injective

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

end

end OddOrder.Isaacs.Ch06
