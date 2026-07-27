/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Isaacs Problem 7A.3 — `GL(n,q)` の Borel 部分群と `N_G(P)` (書籍 p. 209)

**主張** (`G = GL(n,q)`, `P` = 上三角冪単行列のなす Sylow `p`-部分群, `D` = 可逆対角行列):

* (a) `D ≤ N_G(P)`
* (b) `DP` は可逆上三角行列全体
* (c) `G` を**行ベクトルへの右からの掛け算**で作用させると, `P`-不変部分空間は
  `⟨e_{n-k+1}, …, e_n⟩` (各次元 `k` (`1 ≤ k ≤ n`) にちょうど 1 つ)
* (d) `P`-不変部分空間は `N = N_G(P)`-不変でもあり, (c) から `N = DP`

本ファイルはまず**上三角/上三角冪単の部分群**を用意する。鍵は
「上三角行列の積の対角成分は対角成分の積」(`blockTriangular_mul_diag`) で,
これから冪単性が積・逆元で保たれることが従う。

`Matrix.BlockTriangular M id` (`∀ i j, j < i → M i j = 0`) を「上三角」の定義に使う。
-/

namespace OddOrder.Isaacs.Ch07

section /- 7A.3: `GL(n,q)` の上三角部分群 (p. 209) -/

variable {n : ℕ} {F : Type*} [Field F]

/-- **上三角行列の積の対角成分は対角成分の積**。

`(A * B) i i = ∑ k, A i k * B k i` で, `k < i` なら `A i k = 0`, `i < k` なら `B k i = 0`。 -/
theorem blockTriangular_mul_diag {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

/-- **可逆上三角行列のなす部分群** (Borel 部分群 `B = DP`)。 -/
def upperTriangularGL : Subgroup (Matrix.GeneralLinearGroup (Fin n) F) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id}
  mul_mem' := by
    intro A B hA hB
    exact Matrix.BlockTriangular.mul hA hB
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := by
    intro A hA
    haveI : Invertible (A : Matrix (Fin n) (Fin n) F) := A.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular (b := id) hA
    rwa [← Matrix.coe_units_inv] at h

/-- **上三角冪単行列のなす部分群** (`GL(n,q)` の Sylow `p`-部分群)。 -/
def unitriangularGL : Subgroup (Matrix.GeneralLinearGroup (Fin n) F) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id ∧
    ∀ i, (A : Matrix (Fin n) (Fin n) F) i i = 1}
  mul_mem' := by
    intro A B hA hB
    refine ⟨Matrix.BlockTriangular.mul hA.1 hB.1, fun i => ?_⟩
    have hcoe : ((A * B : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F) * B := rfl
    rw [hcoe, blockTriangular_mul_diag hA.1 hB.1 i, hA.2 i, hB.2 i, mul_one]
  one_mem' := ⟨Matrix.blockTriangular_one, fun i => by simp⟩
  inv_mem' := by
    intro A hA
    haveI : Invertible (A : Matrix (Fin n) (Fin n) F) := A.invertible
    have hinvtri : Matrix.BlockTriangular
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) id := by
      have h := Matrix.blockTriangular_inv_of_blockTriangular (b := id) hA.1
      rwa [← Matrix.coe_units_inv] at h
    refine ⟨hinvtri, fun i => ?_⟩
    -- `(A * A⁻¹) i i = A i i * (A⁻¹) i i = 1` から
    have hmul : ((A : Matrix (Fin n) (Fin n) F) *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) i i = 1 := by
      have : ((A * A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) = 1 := by rw [mul_inv_cancel]; rfl
      have hcoe : ((A * A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
      rw [← hcoe, this, Matrix.one_apply_eq]
    rw [blockTriangular_mul_diag hA.1 hinvtri i, hA.2 i, one_mul] at hmul
    exact hmul

theorem unitriangularGL_le_upperTriangularGL :
    (unitriangularGL : Subgroup (Matrix.GeneralLinearGroup (Fin n) F)) ≤ upperTriangularGL :=
  fun _ hA => hA.1

end

end OddOrder.Isaacs.Ch07
