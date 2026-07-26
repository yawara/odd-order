/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionBasics

/-!
# Isaacs Problems 6A — Frobenius 作用の演習 (書籍 pp. 184-186)

## 6A.1 (p. 184)

**主張**: `A ≤ SL(2, p)` の位数が `p` で割れないなら, `A` の位数 `p²` のベクトル空間
`(ZMod p)²` への作用は Frobenius。

**証明**: `1 ≠ a ∈ A` が非零ベクトル `v` を固定したとする。`K := a - 1` は `Kv = 0` ゆえ
`det K = 0`。2 次の行列式を展開すると `det K = det a - tr a + 1 = 2 - tr a` なので **`tr a = 2`**。
このとき `det a = 1` とあわせて成分計算で **`K² = 0`** が出る (固有値が 1 の重根 = 冪単)。
`K² = 0` なら `(1 + K)^n = 1 + n·K` (帰納法) で, 標数 `p` ゆえ `a^p = (1 + K)^p = 1`。
よって `orderOf a ∣ p`, しかし `p ∤ |A|` から `p ∤ orderOf a` なので `orderOf a = 1`, 矛盾。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6A.1: `SL(2,p)` の作用は Frobenius (p. 184) -/

/-! ### 作用の instance

`IsFrobeniusAction` は乗法的に書かれているので, 加群 `V` への線形作用は `Multiplicative V`
への `MulDistribMulAction` に翻訳する。 -/

/-- 加群 `V` への線形作用 (`DistribMulAction`) は, 乗法版 `Multiplicative V` への
`MulDistribMulAction` を与える。 -/
instance multiplicativeMulDistribMulAction {M V : Type*} [Monoid M] [AddMonoid V]
    [DistribMulAction M V] : MulDistribMulAction M (Multiplicative V) where
  smul a x := Multiplicative.ofAdd (a • x.toAdd)
  one_smul x := congrArg Multiplicative.ofAdd (one_smul M x.toAdd)
  mul_smul a b x := congrArg Multiplicative.ofAdd (mul_smul a b x.toAdd)
  smul_mul a x y := congrArg Multiplicative.ofAdd (smul_add a x.toAdd y.toAdd)
  smul_one a := congrArg Multiplicative.ofAdd (smul_zero a)

@[simp]
theorem multiplicative_smul_ofAdd {M V : Type*} [Monoid M] [AddMonoid V] [DistribMulAction M V]
    (a : M) (v : V) : a • (Multiplicative.ofAdd v) = Multiplicative.ofAdd (a • v) := rfl

/-- `SL(n, R)` は `n → R` に `mulVec` で線形に作用する。 -/
instance specialLinearGroupDistribMulAction {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] : DistribMulAction (Matrix.SpecialLinearGroup n R) (n → R) where
  smul a v := (a : Matrix n n R).mulVec v
  one_smul v := by
    change (((1 : Matrix.SpecialLinearGroup n R) : Matrix n n R)).mulVec v = v
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_smul a b v := by
    change (((a * b : Matrix.SpecialLinearGroup n R) : Matrix n n R)).mulVec v
      = (a : Matrix n n R).mulVec ((b : Matrix n n R).mulVec v)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  smul_zero a := by
    change (a : Matrix n n R).mulVec 0 = 0
    exact Matrix.mulVec_zero _
  smul_add a u v := by
    change (a : Matrix n n R).mulVec (u + v)
      = (a : Matrix n n R).mulVec u + (a : Matrix n n R).mulVec v
    exact Matrix.mulVec_add _ _ _

theorem specialLinearGroup_smul_def {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (a : Matrix.SpecialLinearGroup n R) (v : n → R) :
    a • v = (a : Matrix n n R).mulVec v := rfl

/-! ### 冪単性 -/

/-- 環の元 `K` が `K² = 0` なら `(1 + K)^n = 1 + n • K`。 -/
theorem one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] {K : R} (hK : K * K = 0) (n : ℕ) :
    (1 + K) ^ n = 1 + n • K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hK, smul_zero,
      add_zero, succ_nsmul]
    abel

/-- **6A.1 の核**: `SL(2, p)` の元が非零ベクトルを固定するなら, それは冪単で `a^p = 1`。

`Kv = 0` (`K := a - 1`, `v ≠ 0`) から `det K = 0`, 2 次の行列式展開と `det a = 1` から
`tr a = 2`, 成分計算で `K² = 0`, 標数 `p` ゆえ `a^p = (1 + K)^p = 1 + p·K = 1`。 -/
theorem specialLinearGroupTwo_pow_eq_one_of_smul_eq {p : ℕ} [Fact p.Prime]
    (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) {v : Fin 2 → ZMod p} (hv : v ≠ 0)
    (hfix : a • v = v) : a ^ p = 1 := by
  classical
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := (a : Matrix (Fin 2) (Fin 2) (ZMod p)) with hMdef
  set K : Matrix (Fin 2) (Fin 2) (ZMod p) := M - 1 with hKdef
  -- `K v = 0` ⟹ `det K = 0`
  have hKv : K.mulVec v = 0 := by
    rw [hKdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [specialLinearGroup_smul_def] at hfix
    rw [← hMdef] at hfix
    rw [hfix, sub_self]
  have hdetK : K.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hKv⟩
  -- `det a = 1`
  have hdetM : M.det = 1 := a.2
  -- 2 次の展開: `det K = det M - (M 0 0 + M 1 1) + 1`
  have hKentry : ∀ i j, K i j = M i j - (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := by
    intro i j; rw [hKdef]; simp
  have htrace : M 0 0 + M 1 1 = 2 := by
    rw [Matrix.det_fin_two] at hdetK hdetM
    rw [hKentry 0 0, hKentry 0 1, hKentry 1 0, hKentry 1 1] at hdetK
    simp only [Matrix.one_apply_eq] at hdetK
    norm_num at hdetK
    linear_combination hdetM - hdetK
  -- `K² = 0` (`tr = 2`, `det = 1` から成分計算)
  have hKsq : K * K = 0 := by
    have h00 : K 0 0 = M 0 0 - 1 := by rw [hKentry 0 0]; simp
    have h01 : K 0 1 = M 0 1 := by rw [hKentry 0 1]; simp
    have h10 : K 1 0 = M 1 0 := by rw [hKentry 1 0]; simp
    have h11 : K 1 1 = M 1 1 - 1 := by rw [hKentry 1 1]; simp
    rw [Matrix.det_fin_two] at hdetM
    have hentry : ∀ i j : Fin 2, (K * K) i j = K i 0 * K 0 j + K i 1 * K 1 j := by
      intro i j; rw [Matrix.mul_apply, Fin.sum_univ_two]
    have e00 : (K * K) 0 0 = 0 := by
      rw [hentry, h00, h01, h10]
      linear_combination (M 0 0) * htrace - hdetM
    have e01 : (K * K) 0 1 = 0 := by
      rw [hentry, h00, h01, h11]
      linear_combination (M 0 1) * htrace
    have e10 : (K * K) 1 0 = 0 := by
      rw [hentry, h10, h00, h11]
      linear_combination (M 1 0) * htrace
    have e11 : (K * K) 1 1 = 0 := by
      rw [hentry, h10, h01, h11]
      linear_combination (M 1 1) * htrace - hdetM
    ext i j
    rw [Matrix.zero_apply]
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  -- `a^p = 1`
  have hMp : M ^ p = 1 := by
    have hMK : M = 1 + K := by rw [hKdef]; abel
    rw [hMK, one_add_pow_of_sq_eq_zero hKsq]
    have : (p : ℕ) • K = ((p : ZMod p)) • K := (Nat.cast_smul_eq_nsmul _ _ _).symm
    rw [this, ZMod.natCast_self, zero_smul, add_zero]
  ext i j
  have : ((a ^ p : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hMdef, hMp]
  rw [this, Matrix.SpecialLinearGroup.coe_one]

/-- **6A.1 の核 (元の形)**: 位数が `p` で割れない `SL(2, p)` の元は非零ベクトルを固定しない。 -/
theorem specialLinearGroupTwo_eq_one_of_smul_eq {p : ℕ} [Fact p.Prime]
    {a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (ha : ¬ p ∣ orderOf a)
    {v : Fin 2 → ZMod p} (hv : v ≠ 0) (hfix : a • v = v) : a = 1 := by
  have hdvd : orderOf a ∣ p :=
    orderOf_dvd_of_pow_eq_one (specialLinearGroupTwo_pow_eq_one_of_smul_eq a hv hfix)
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (dvd_of_eq hp.symm) ha

/-- **Isaacs Problem 6A.1** (p. 184) ⭐: `A ≤ SL(2, p)` の位数が `p` で割り切れないなら,
`A` の位数 `p²` のベクトル空間 `(ZMod p)²` への自然な作用は **Frobenius**。 -/
theorem isFrobeniusAction_specialLinearGroupTwo {p : ℕ} [Fact p.Prime]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) (hA : ¬ p ∣ Nat.card ↥A) :
    IsFrobeniusAction ↥A (Multiplicative (Fin 2 → ZMod p)) := by
  intro a ha w hw hfix
  refine ha (Subtype.ext ?_)
  have hord : ¬ p ∣ orderOf (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    intro hdvd
    refine hA (hdvd.trans ?_)
    have heq : orderOf (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = orderOf a :=
      orderOf_injective A.subtype (Subgroup.subtype_injective A) a
    rw [heq]
    exact orderOf_dvd_natCard a
  have hwne : (Multiplicative.toAdd w : Fin 2 → ZMod p) ≠ 0 := by
    intro h
    exact hw (Multiplicative.toAdd.injective (by rw [h]; rfl))
  have hfix' : (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) • (Multiplicative.toAdd w)
      = Multiplicative.toAdd w := congrArg Multiplicative.toAdd hfix
  exact specialLinearGroupTwo_eq_one_of_smul_eq hord hwne hfix'

/-- ベクトル空間 `(ZMod p)²` の位数は `p²` (書籍の「位数 `p²` のベクトル空間」)。 -/
theorem card_fin_two_zmod {p : ℕ} [NeZero p] : Nat.card (Fin 2 → ZMod p) = p ^ 2 := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

end

end OddOrder.Isaacs.Ch06
