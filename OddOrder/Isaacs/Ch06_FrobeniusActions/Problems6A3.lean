/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsMonomialSetup

/-!
# Isaacs Problem 6A.3 — 位数 `5²·11` の非巡回 Frobenius complement (書籍 p. 185)

**主張**: 位数 `5²·11 = 275` の**非巡回**群で, ある非自明な群への **Frobenius 作用**を
もつものが存在する。書籍 hint: 適当な素数 `p` について `GL(5, p)` の中で考えよ。

**構成** (6A.2 の `n = 3, q = 7` を `n = 5, q = 11` にしたもの): `α` の位数を 11,
`ε` の位数を 5 とし (`3` は `11` を法として位数 5 なので `3ᵏ mod 11 = 1, 3, 9, 5, 4`)

* `a = diag(α, α³, α⁹, α⁵, α⁴)` (位数 11)
* `b = ![[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1],[ε,0,0,0,0]]` (位数 25,
  `b⁵ = ε · 1` はスカラー)
* `a b = b a⁴`, すなわち `b a b⁻¹ = a³`

とおくと `A = ⟨a, b⟩` は位数 `11 · 25 = 275` の非可換 (ゆえに非巡回) 群で,
`F⁵` への自然な作用は **Frobenius**。

体としては `55 ∣ p - 1` が要る。最小の素数は **`p = 331`** (`331 - 1 = 330 = 2·3·5·11`) で,
`α = 74`, `ε = 64` が使える。

⚠ **一般化**: 証明は「位数 11 の `α` と位数 5 の `ε` をもつ体」でそのまま通るので,
一般の体 `F` で述べる (`p = 331` はその特殊化)。共通部分は
`OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsMonomialSetup` に括り出してある。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.3: 位数 `5²·11` の非巡回 Frobenius complement (p. 185) -/

variable {F : Type*} [Field F]

/-- 書籍 6A.3 の `a = diag(α, α³, α⁹, α⁵, α⁴)` (指数は `3ᵏ mod 11`)。 -/
def matA5 (α : F) : Matrix (Fin 5) (Fin 5) F :=
  Matrix.diagonal ![α, α ^ 3, α ^ 9, α ^ 5, α ^ 4]

/-- 書籍 6A.3 の `b` (巡回シフトの隅に `ε`)。 -/
def matB5 (ε : F) : Matrix (Fin 5) (Fin 5) F :=
  !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; ε, 0, 0, 0, 0]

theorem matA5_pow (α : F) (n : ℕ) :
    matA5 α ^ n
      = Matrix.diagonal ![α ^ n, (α ^ 3) ^ n, (α ^ 9) ^ n, (α ^ 5) ^ n, (α ^ 4) ^ n] := by
  rw [matA5, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem matA5_pow_eleven {α : F} (hα : α ^ 11 = 1) : matA5 α ^ 11 = 1 := by
  have hk : ∀ k : ℕ, (α ^ k) ^ 11 = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, hα, one_pow]
  rw [matA5_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact hα
  · exact hk 3
  · exact hk 9
  · exact hk 5
  · exact hk 4

/-- `b²` を明示的に計算しておく (`b⁵` を段階的に出すため)。 -/
theorem matB5_sq (ε : F) :
    matB5 ε ^ 2
      = !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; ε, 0, 0, 0, 0; 0, ε, 0, 0, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB5, Matrix.mul_apply, Fin.sum_univ_five]

theorem matB5_pow_four (ε : F) :
    matB5 ε ^ 4
      = !![0, 0, 0, 0, 1; ε, 0, 0, 0, 0; 0, ε, 0, 0, 0; 0, 0, ε, 0, 0; 0, 0, 0, ε, 0] := by
  have h : matB5 ε ^ 4 = (matB5 ε ^ 2) * (matB5 ε ^ 2) := by rw [← pow_add]
  rw [h, matB5_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five]

/-- `b⁵` はスカラー行列 `ε · 1`。 -/
theorem matB5_pow_five (ε : F) : matB5 ε ^ 5 = ε • (1 : Matrix (Fin 5) (Fin 5) F) := by
  have h : matB5 ε ^ 5 = (matB5 ε ^ 4) * matB5 ε := by rw [← pow_succ]
  rw [h, matB5_pow_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB5, Matrix.mul_apply, Fin.sum_univ_five]

theorem matB5_pow_twentyfive {ε : F} (hε : ε ^ 5 = 1) : matB5 ε ^ 25 = 1 := by
  have h : matB5 ε ^ 25 = (matB5 ε ^ 5) ^ 5 := by rw [← pow_mul]
  rw [h, matB5_pow_five, smul_pow, one_pow, hε, one_smul]

/-- **`a · b = b · a⁴`** — `b` は `⟨a⟩` を正規化し `b a b⁻¹ = a³`。 -/
theorem matA5_mul_matB5 {α : F} (hα : α ^ 11 = 1) (ε : F) :
    matA5 α * matB5 ε = matB5 ε * matA5 α ^ 4 := by
  have e1 : (α ^ 3) ^ 4 = α := by
    have h : (α ^ 3) ^ 4 = α ^ 11 * α := by ring
    rw [h, hα, one_mul]
  have e2 : (α ^ 9) ^ 4 = α ^ 3 := by
    have h : (α ^ 9) ^ 4 = (α ^ 11) ^ 3 * α ^ 3 := by ring
    rw [h, hα, one_pow, one_mul]
  have e3 : (α ^ 5) ^ 4 = α ^ 9 := by
    have h : (α ^ 5) ^ 4 = α ^ 11 * α ^ 9 := by ring
    rw [h, hα, one_mul]
  have e4 : (α ^ 4) ^ 4 = α ^ 5 := by
    have h : (α ^ 4) ^ 4 = α ^ 11 * α ^ 5 := by ring
    rw [h, hα, one_mul]
  rw [matA5_pow, matA5]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB5, Matrix.mul_apply, Matrix.diagonal_apply, e1, e2, e3, e4, mul_comm]

/-! ### `GL(5, F)` の元としての `a`, `b` と `A = ⟨a, b⟩` -/

variable {α ε : F}

/-- 書籍 6A.3 の `a ∈ GL(5, F)` (逆元は `a¹⁰`)。 -/
def vA (hα : orderOf α = 11) : (Matrix (Fin 5) (Fin 5) F)ˣ where
  val := matA5 α
  inv := matA5 α ^ 10
  val_inv := by
    have h : matA5 α * matA5 α ^ 10 = matA5 α ^ 11 := (pow_succ' (matA5 α) 10).symm
    rw [h, matA5_pow_eleven (hα ▸ pow_orderOf_eq_one α)]
  inv_val := by
    have h : matA5 α ^ 10 * matA5 α = matA5 α ^ 11 := (pow_succ (matA5 α) 10).symm
    rw [h, matA5_pow_eleven (hα ▸ pow_orderOf_eq_one α)]

/-- 書籍 6A.3 の `b ∈ GL(5, F)` (逆元は `b²⁴`)。 -/
def vB (hε : orderOf ε = 5) : (Matrix (Fin 5) (Fin 5) F)ˣ where
  val := matB5 ε
  inv := matB5 ε ^ 24
  val_inv := by
    have h : matB5 ε * matB5 ε ^ 24 = matB5 ε ^ 25 := (pow_succ' (matB5 ε) 24).symm
    rw [h, matB5_pow_twentyfive (hε ▸ pow_orderOf_eq_one ε)]
  inv_val := by
    have h : matB5 ε ^ 24 * matB5 ε = matB5 ε ^ 25 := (pow_succ (matB5 ε) 24).symm
    rw [h, matB5_pow_twentyfive (hε ▸ pow_orderOf_eq_one ε)]

@[simp] theorem vA_val (hα : orderOf α = 11) :
    ((vA hα : (Matrix (Fin 5) (Fin 5) F)ˣ) : Matrix (Fin 5) (Fin 5) F) = matA5 α := rfl

@[simp] theorem vB_val (hε : orderOf ε = 5) :
    ((vB hε : (Matrix (Fin 5) (Fin 5) F)ˣ) : Matrix (Fin 5) (Fin 5) F) = matB5 ε := rfl

theorem vA_pow_eleven (hα : orderOf α = 11) : vA hα ^ 11 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, vA_val, Units.val_one]
  exact matA5_pow_eleven (hα ▸ pow_orderOf_eq_one α)

theorem vB_pow_twentyfive (hε : orderOf ε = 5) : vB hε ^ 25 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, vB_val, Units.val_one]
  exact matB5_pow_twentyfive (hε ▸ pow_orderOf_eq_one ε)

theorem orderOf_vA (hα : orderOf α = 11) : orderOf (vA hα) = 11 := by
  have hne : vA hα ≠ 1 := by
    intro h
    have h1 : matA5 α = 1 := by rw [← vA_val hα, h, Units.val_one]
    have hα1 : α = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [matA5, Matrix.diagonal_apply, Matrix.one_apply] using this
    rw [hα1, orderOf_one] at hα
    omega
  have hdvd : orderOf (vA hα) ∣ 11 := orderOf_dvd_of_pow_eq_one (vA_pow_eleven hα)
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h11
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h11

theorem orderOf_vB (hε : orderOf ε = 5) : orderOf (vB hε) = 25 := by
  have hne : vB hε ^ 5 ≠ 1 := by
    intro h
    have h1 : matB5 ε ^ 5 = 1 := by
      rw [← vB_val hε, ← Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [matB5_pow_five] at h1
    have hε1 : ε = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.one_apply] using this
    rw [hε1, orderOf_one] at hε
    omega
  have hdvd : orderOf (vB hε) ∣ 25 := orderOf_dvd_of_pow_eq_one (vB_pow_twentyfive hε)
  have hmem : orderOf (vB hε) ∈ Nat.divisors 25 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 25 = {1, 5, 25} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [h]; norm_num)) hne
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [h])) hne
  · exact h

/-- **`a · b = b · a⁴`** (単元版)。 -/
theorem vA_mul_vB (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    vA hα * vB hε = vB hε * vA hα ^ 4 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, vA_val, vB_val]
  exact matA5_mul_matB5 (hα ▸ pow_orderOf_eq_one α) ε

/-- **`b a = a³ b`** (`⟨a⟩` の正規化と冪計算の基本形)。 -/
theorem vB_mul_vA (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    vB hε * vA hα = vA hα ^ 3 * vB hε := by
  have h4 : vB hε * vA hα ^ 4 = vA hα * vB hε := (vA_mul_vB hα hε).symm
  have h12 : vA hα ^ 12 = vA hα := by
    have h : vA hα ^ 12 = vA hα ^ 11 * vA hα := by rw [← pow_succ]
    rw [h, vA_pow_eleven hα, one_mul]
  have e : vA hα ^ 12 = vA hα ^ 4 * vA hα ^ 4 * vA hα ^ 4 := by rw [← pow_add, ← pow_add]
  calc vB hε * vA hα = vB hε * vA hα ^ 12 := by rw [h12]
    _ = vB hε * vA hα ^ 4 * vA hα ^ 4 * vA hα ^ 4 := by rw [e]; simp only [mul_assoc]
    _ = vA hα * vB hε * vA hα ^ 4 * vA hα ^ 4 := by rw [h4]
    _ = vA hα * (vB hε * vA hα ^ 4) * vA hα ^ 4 := by simp only [mul_assoc]
    _ = vA hα * (vA hα * vB hε) * vA hα ^ 4 := by rw [h4]
    _ = vA hα * vA hα * (vB hε * vA hα ^ 4) := by simp only [mul_assoc]
    _ = vA hα * vA hα * (vA hα * vB hε) := by rw [h4]
    _ = vA hα ^ 3 * vB hε := by
        rw [show (3 : ℕ) = 1 + 1 + 1 by norm_num, pow_add, pow_add, pow_one]
        simp only [mul_assoc]

/-- 書籍 6A.3 の `A = ⟨a, b⟩ ≤ GL(5, F)`。 -/
def grpA5 (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    Subgroup ((Matrix (Fin 5) (Fin 5) F)ˣ) :=
  Subgroup.closure {vA hα, vB hε}

/-- `b` は `⟨a⟩` を正規化する。 -/
theorem vB_mem_normalizer (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    vB hε ∈ Subgroup.normalizer (Subgroup.zpowers (vA hα)) := by
  have hconj : vB hε * vA hα * (vB hε)⁻¹ = vA hα ^ 3 := by
    rw [vB_mul_vA hα hε]; group
  have hconj2 : (vB hε)⁻¹ * vA hα * vB hε = vA hα ^ 4 := by
    calc (vB hε)⁻¹ * vA hα * vB hε = (vB hε)⁻¹ * (vA hα * vB hε) := by group
      _ = (vB hε)⁻¹ * (vB hε * vA hα ^ 4) := by rw [vA_mul_vB hα hε]
      _ = vA hα ^ 4 := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨3 * n, ?_⟩
    rw [zpow_mul, show ((vA hα) ^ (3 : ℤ)) = ((vA hα) ^ (3 : ℕ)) by norm_cast, ← hconj, conj_zpow]
  · rintro ⟨n, hn⟩
    refine ⟨4 * n, ?_⟩
    have hstep : ((vB hε)⁻¹ * vA hα * ((vB hε)⁻¹)⁻¹) ^ n
        = (vB hε)⁻¹ * (vA hα ^ n) * ((vB hε)⁻¹)⁻¹ := conj_zpow
    rw [inv_inv] at hstep
    rw [hconj2] at hstep
    rw [zpow_mul, show ((vA hα) ^ (4 : ℤ)) = ((vA hα) ^ (4 : ℕ)) by norm_cast, hstep, hn]
    group

/-- **Isaacs Problem 6A.3 (前半)**: `A = ⟨a, b⟩` の位数は `275 = 11 · 25 = 5²·11`。 -/
theorem card_grpA5 [Finite F] (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    Nat.card ↥(grpA5 hα hε) = 5 ^ 2 * 11 := by
  rw [grpA5, card_closure_pair_of_mem_normalizer (vB_mem_normalizer hα hε)
    (by rw [orderOf_vA, orderOf_vB]; decide), orderOf_vA, orderOf_vB]
  norm_num

/-- **Isaacs Problem 6A.3 (前半)**: `A = ⟨a, b⟩` は**非巡回** (`b a b⁻¹ = a³ ≠ a`)。 -/
theorem not_isCyclic_grpA5 (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    ¬ IsCyclic ↥(grpA5 hα hε) := by
  refine not_isCyclic_closure_pair ?_
  intro hcomm
  -- 可換なら `a = a⁴`, ゆえに `a³ = 1` で位数 11 に矛盾
  have h4 : vB hε * vA hα ^ 4 = vB hε * vA hα := by
    rw [← vA_mul_vB hα hε, hcomm]
  have hpow : vA hα ^ 4 = vA hα := mul_left_cancel h4
  have h3 : vA hα ^ 3 = 1 := by
    have h : vA hα ^ 4 = vA hα ^ 3 * vA hα := by rw [← pow_succ]
    rw [h] at hpow
    exact mul_right_cancel (by rw [hpow, one_mul])
  have := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_vA hα] at this
  omega

/-! ### Frobenius 性 -/

theorem vB_pow_five_val (hε : orderOf ε = 5) :
    ((vB hε ^ 5 : (Matrix (Fin 5) (Fin 5) F)ˣ) : Matrix (Fin 5) (Fin 5) F)
      = ε • (1 : Matrix (Fin 5) (Fin 5) F) := by
  rw [Units.val_pow_eq_pow_val, vB_val, matB5_pow_five]

/-- `b⁵ = ε · 1` はスカラーゆえ `GL(5,F)` の中心に入る。 -/
theorem vB_pow_five_commute (hε : orderOf ε = 5) (y : (Matrix (Fin 5) (Fin 5) F)ˣ) :
    Commute (vB hε ^ 5) y := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vB_pow_five_val hε, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one]

/-- `(aⁱ bᵗ)⁵ = b^{5t}` (`t ≥ 1`): `aⁱ` の寄与 `∑_{k<5} (3ᵗ)ᵏ` は `11` の倍数ゆえ消える。 -/
theorem pow_five_vA_pow_mul_vB_pow (hα : orderOf α = 11) (hε : orderOf ε = 5) (i t : ℕ)
    (hsum : (11 : ℕ) ∣ ∑ k ∈ Finset.range 5, (3 ^ t) ^ k) :
    (vA hα ^ i * vB hε ^ t) ^ 5 = vB hε ^ (5 * t) := by
  have hbase : vB hε ^ t * vA hα = vA hα ^ (3 ^ t) * vB hε ^ t := by
    have h := pow_mul_pow_eq_pow_mul_pow (vB_mul_vA hα hε) t 1
    simpa using h
  obtain ⟨c, hc⟩ := hsum
  have hz : vA hα ^ ((∑ k ∈ Finset.range 5, (3 ^ t) ^ k) * i) = 1 := by
    rw [hc, mul_assoc, pow_mul, vA_pow_eleven hα, one_pow]
  rw [pow_mul_pow_pow hbase, hz, one_mul, ← pow_mul, mul_comm t 5]

/-- **Isaacs Problem 6A.3 (後半)** ⭐: `A = ⟨a, b⟩` の `F⁵` への自然な作用は **Frobenius**。 -/
theorem isFrobeniusAction_grpA5 [Finite F] (hα : orderOf α = 11) (hε : orderOf ε = 5) :
    IsFrobeniusAction ↥(grpA5 hα hε) (Multiplicative (Fin 5 → F)) := by
  intro x hxne w hwne hfix
  set v : Fin 5 → F := Multiplicative.toAdd w with hvdef
  have hvne : v ≠ 0 := by
    intro h
    exact hwne (Multiplicative.toAdd.injective (by rw [← hvdef, h]; rfl))
  set X : (Matrix (Fin 5) (Fin 5) F)ˣ := (x : (Matrix (Fin 5) (Fin 5) F)ˣ) with hXdef
  have hsmul : X • v = v := congrArg Multiplicative.toAdd hfix
  have hfixv : (X : Matrix (Fin 5) (Fin 5) F).mulVec v = v := hsmul
  have hα11 : α ^ 11 = 1 := hα ▸ pow_orderOf_eq_one α
  have hε5 : ε ^ 5 = 1 := hε ▸ pow_orderOf_eq_one ε
  -- `11 ∤ c` なら `α^{ci} = 1 ⟹ αⁱ = 1`
  have key : ∀ c i : ℕ, Nat.Coprime 11 c → α ^ (c * i) = 1 → α ^ i = 1 := by
    intro c i hc h
    have h11 : (11 : ℕ) ∣ c * i := hα ▸ orderOf_dvd_of_pow_eq_one h
    obtain ⟨s, rfl⟩ := hc.dvd_of_dvd_mul_left (by rwa [mul_comm] at h11)
    rw [pow_mul, hα11, one_pow]
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_closure_pair (vB_mem_normalizer hα hε) x.2
  obtain ⟨m, t, ht, hjmt⟩ : ∃ m t, t < 5 ∧ j = 5 * m + t :=
    ⟨j / 5, j % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 5).symm⟩
  set Z : (Matrix (Fin 5) (Fin 5) F)ˣ := vB hε ^ 5 with hZdef
  have hZ5 : Z ^ 5 = 1 := by
    rw [hZdef, ← pow_mul]
    exact vB_pow_twentyfive hε
  have hZval : ∀ k : ℕ, ((Z ^ k : (Matrix (Fin 5) (Fin 5) F)ˣ) : Matrix (Fin 5) (Fin 5) F)
      = ε ^ k • (1 : Matrix (Fin 5) (Fin 5) F) := by
    intro k
    rw [Units.val_pow_eq_pow_val, hZdef, vB_pow_five_val hε, smul_pow, one_pow]
  have hcomm : Commute (Z ^ m) (vA hα ^ i) := (vB_pow_five_commute hε (vA hα ^ i)).pow_left m
  have hXform : X = Z ^ m * (vA hα ^ i * vB hε ^ t) := by
    rw [hXdef, hij, hjmt, pow_add, pow_mul, ← hZdef, ← mul_assoc, ← hcomm.eq, mul_assoc]
  by_cases ht0 : t = 0
  · -- `t = 0`: `X` は対角行列 `diag(εᵐα^{cⁱ})`
    subst ht0
    rw [pow_zero, mul_one, hcomm.eq] at hXform
    have hXval : (X : Matrix (Fin 5) (Fin 5) F)
        = Matrix.diagonal (fun k =>
            ![α ^ i, (α ^ 3) ^ i, (α ^ 9) ^ i, (α ^ 5) ^ i, (α ^ 4) ^ i] k * ε ^ m) := by
      rw [hXform, Units.val_mul, Units.val_pow_eq_pow_val, vA_val, matA5_pow, hZval,
        diagonal_mul_scalar]
    rw [hXval] at hfixv
    obtain ⟨k, hk⟩ := exists_diagonal_eq_one_of_mulVec_eq hvne hfixv
    have hgen : ∀ c : ℕ, ((α ^ c) ^ i) ^ 11 = 1 := fun c => by
      rw [← pow_mul, ← pow_mul, show c * (i * 11) = 11 * (c * i) by ring, pow_mul, hα11, one_pow]
    have hgen0 : (α ^ i) ^ 11 = 1 := by
      rw [← pow_mul, show i * 11 = 11 * i by ring, pow_mul, hα11, one_pow]
    have hd11 : ![α ^ i, (α ^ 3) ^ i, (α ^ 9) ^ i, (α ^ 5) ^ i, (α ^ 4) ^ i] k ^ 11 = 1 := by
      fin_cases k
      · exact hgen0
      · exact hgen 3
      · exact hgen 9
      · exact hgen 5
      · exact hgen 4
    have hεm : ε ^ m = 1 := by
      refine eq_one_of_pow_eq_one_of_coprime (m := 5) (n := 11) (by decide) ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hε5, one_pow]
      · have h11 : (![α ^ i, (α ^ 3) ^ i, (α ^ 9) ^ i, (α ^ 5) ^ i, (α ^ 4) ^ i] k * ε ^ m) ^ 11
            = 1 := by rw [hk, one_pow]
        rw [mul_pow, hd11, one_mul] at h11
        exact h11
    have hdk : ![α ^ i, (α ^ 3) ^ i, (α ^ 9) ^ i, (α ^ 5) ^ i, (α ^ 4) ^ i] k = 1 := by
      rw [hεm, mul_one] at hk; exact hk
    have hai11 : α ^ i = 1 := by
      fin_cases k
      · exact hdk
      · exact key 3 i (by decide) (by rw [pow_mul]; exact hdk)
      · exact key 9 i (by decide) (by rw [pow_mul]; exact hdk)
      · exact key 5 i (by decide) (by rw [pow_mul]; exact hdk)
      · exact key 4 i (by decide) (by rw [pow_mul]; exact hdk)
    have hgen2 : ∀ c : ℕ, (α ^ c) ^ i = 1 := fun c => by
      rw [← pow_mul, mul_comm, pow_mul, hai11, one_pow]
    have hai : vA hα ^ i = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, vA_val, matA5_pow, Units.val_one, ← Matrix.diagonal_one]
      congr 1
      funext p
      fin_cases p
      · exact hai11
      · exact hgen2 3
      · exact hgen2 9
      · exact hgen2 5
      · exact hgen2 4
    have hzm : Z ^ m = 1 := by
      refine Units.ext ?_
      rw [hZval, hεm, one_smul, Units.val_one]
    have hXone : X = 1 := by rw [hXform, hzm, hai, mul_one]
    exact hxne (Subtype.ext hXone)
  · -- `t ≠ 0`: `X⁵ = b^{5t} = εᵗ · 1` は非単位スカラー
    have hfix5 : (X ^ 5 : (Matrix (Fin 5) (Fin 5) F)ˣ) • v = v := by
      rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, mul_smul,
        mul_smul, hsmul, hsmul, hsmul, hsmul, hsmul]
    have hc2 : Commute (Z ^ m) (vA hα ^ i * vB hε ^ t) :=
      (vB_pow_five_commute hε (vA hα ^ i * vB hε ^ t)).pow_left m
    have hX5 : X ^ 5 = (vA hα ^ i * vB hε ^ t) ^ 5 := by
      rw [hXform, hc2.mul_pow, ← pow_mul, mul_comm m 5, pow_mul, hZ5, one_pow, one_mul]
    have hsum : (11 : ℕ) ∣ ∑ k ∈ Finset.range 5, (3 ^ t) ^ k := by
      have ht4 : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
      rcases ht4 with rfl | rfl | rfl | rfl <;> norm_num [Finset.sum_range_succ]
    rw [pow_five_vA_pow_mul_vB_pow hα hε i t hsum] at hX5
    have hZt : vB hε ^ (5 * t) = Z ^ t := by rw [hZdef, ← pow_mul]
    rw [hZt] at hX5
    rw [hX5] at hfix5
    have hεt : ε ^ t ≠ 1 := by
      intro h
      have hd : orderOf ε ∣ t := orderOf_dvd_of_pow_eq_one h
      rw [hε] at hd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hd
      omega
    exact scalar_mulVec_ne_of_ne_one hεt hvne (by rw [← hZval t]; exact hfix5)

/-! ### 書籍の場合 `p = 331` (`55 ∣ 330`) -/

instance fact_prime_331 : Fact (Nat.Prime 331) := ⟨by norm_num⟩

/-- `𝔽₃₃₁` の乗法群に位数 11 の元がある (`74`)。 -/
theorem exists_orderOf_eq_eleven_zmod_331 : ∃ α : ZMod 331, orderOf α = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact ⟨74, orderOf_eq_prime (by decide) (by decide)⟩

/-- `𝔽₃₃₁` の乗法群に位数 5 の元がある (`64`)。 -/
theorem exists_orderOf_eq_five_zmod_331 : ∃ ε : ZMod 331, orderOf ε = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨64, orderOf_eq_prime (by decide) (by decide)⟩

/-- **Isaacs Problem 6A.3** (p. 185) ⭐ 書籍の主張そのもの: 位数 `5²·11` の**非巡回**群で
非自明な群 (`𝔽₃₃₁⁵`, 位数 `331⁵`) への **Frobenius 作用**をもつものが存在する。 -/
theorem exists_noncyclic_order_twentyfive_mul_eleven_frobenius :
    ∃ A : Subgroup ((Matrix (Fin 5) (Fin 5) (ZMod 331))ˣ),
      Nat.card ↥A = 5 ^ 2 * 11 ∧ ¬ IsCyclic ↥A ∧
        IsFrobeniusAction ↥A (Multiplicative (Fin 5 → ZMod 331)) := by
  obtain ⟨α, hα⟩ := exists_orderOf_eq_eleven_zmod_331
  obtain ⟨ε, hε⟩ := exists_orderOf_eq_five_zmod_331
  exact ⟨grpA5 hα hε, card_grpA5 hα hε, not_isCyclic_grpA5 hα hε, isFrobeniusAction_grpA5 hα hε⟩

end

end OddOrder.Isaacs.Ch06
