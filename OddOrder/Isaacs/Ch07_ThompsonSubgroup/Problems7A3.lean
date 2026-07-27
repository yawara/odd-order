/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Isaacs Problem 7A.3 — `GL(n,q)` の Borel 部分群と `N_G(P)` (書籍 p. 209)

**主張** (`G = GL(n,q)`, `P` = 上三角冪単行列のなす Sylow `p`-部分群, `D` = 可逆対角行列):

* (a) `D ≤ N_G(P)`
* (b) `DP` は可逆上三角行列全体
* (c) `G` を**行ベクトルへの右からの掛け算**で作用させると, `P`-不変部分空間は
  `⟨e_{n-k+1}, …, e_n⟩` (各次元 `k` (`1 ≤ k ≤ n`) にちょうど 1 つ)
* (d) `P`-不変部分空間は `N = N_G(P)`-不変でもあり, (c) から `N = DP`

鍵は「上三角行列の積の対角成分は対角成分の積」(`blockTriangular_mul_diag`) で,
これから冪単性が積・逆元・共役で保たれることが従う。

`Matrix.BlockTriangular M id` (`∀ i j, j < i → M i j = 0`) を「上三角」の定義に使う。
-/

namespace OddOrder.Isaacs.Ch07

open Pointwise

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

/-- 可逆行列 `A` が上三角なら, その逆行列も上三角。 -/
theorem blockTriangular_coe_inv {A : GL (Fin n) F}
    (hA : Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id) :
    Matrix.BlockTriangular ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) id := by
  haveI : Invertible (A : Matrix (Fin n) (Fin n) F) := A.invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (b := id) hA
  rwa [← Matrix.coe_units_inv] at h

/-- 可逆上三角行列の対角成分と逆行列の対角成分は互いに逆元。

`(A * A⁻¹) i i = A i i * (A⁻¹) i i` (`blockTriangular_mul_diag`) と `A * A⁻¹ = 1` から。 -/
theorem diag_mul_diag_inv {A : GL (Fin n) F}
    (hA : Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id) (i : Fin n) :
    (A : Matrix (Fin n) (Fin n) F) i i *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
  have h1 : (A : Matrix (Fin n) (Fin n) F) *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    have hcoe : ((A * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
    rw [← hcoe, mul_inv_cancel]; rfl
  have h2 := congrFun (congrFun h1 i) i
  rwa [blockTriangular_mul_diag hA (blockTriangular_coe_inv hA) i, Matrix.one_apply_eq] at h2

/-- 可逆上三角行列の対角成分は単元 (体では非零)。 -/
theorem isUnit_diag_of_blockTriangular {A : GL (Fin n) F}
    (hA : Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id) (i : Fin n) :
    IsUnit ((A : Matrix (Fin n) (Fin n) F) i i) :=
  IsUnit.of_mul_eq_one _ (diag_mul_diag_inv hA i)

/-- **可逆上三角行列のなす部分群** (Borel 部分群 `B = DP`)。 -/
def upperTriangularGL : Subgroup (GL (Fin n) F) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id}
  mul_mem' := by
    intro A B hA hB
    exact Matrix.BlockTriangular.mul hA hB
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := blockTriangular_coe_inv

@[simp]
theorem mem_upperTriangularGL {A : GL (Fin n) F} :
    A ∈ (upperTriangularGL : Subgroup (GL (Fin n) F)) ↔
      Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id := Iff.rfl

/-- **上三角冪単行列のなす部分群** (`GL(n,q)` の Sylow `p`-部分群)。 -/
def unitriangularGL : Subgroup (GL (Fin n) F) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id ∧
    ∀ i, (A : Matrix (Fin n) (Fin n) F) i i = 1}
  mul_mem' := by
    intro A B hA hB
    refine ⟨Matrix.BlockTriangular.mul hA.1 hB.1, fun i => ?_⟩
    have hcoe : ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F) * B := rfl
    rw [hcoe, blockTriangular_mul_diag hA.1 hB.1 i, hA.2 i, hB.2 i, mul_one]
  one_mem' := ⟨Matrix.blockTriangular_one, fun i => by simp⟩
  inv_mem' := by
    intro A hA
    refine ⟨blockTriangular_coe_inv hA.1, fun i => ?_⟩
    have hmul := diag_mul_diag_inv hA.1 i
    rwa [hA.2 i, one_mul] at hmul

@[simp]
theorem mem_unitriangularGL {A : GL (Fin n) F} :
    A ∈ (unitriangularGL : Subgroup (GL (Fin n) F)) ↔
      Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id ∧
        ∀ i, (A : Matrix (Fin n) (Fin n) F) i i = 1 := Iff.rfl

theorem unitriangularGL_le_upperTriangularGL :
    (unitriangularGL : Subgroup (GL (Fin n) F)) ≤ upperTriangularGL :=
  fun _ hA => hA.1

/-! ### 対角部分群 `D` と 7A.3(a) -/

/-- 対角行列の積は対角行列 (mathlib に `Matrix.IsDiag.mul` は無い)。 -/
theorem isDiag_mul {A B : Matrix (Fin n) (Fin n) F} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne k i with rfl | hk
  · rw [hB hij, mul_zero]
  · rw [hA (Ne.symm hk), zero_mul]

/-- **可逆対角行列のなす部分群** `D`。 -/
def diagonalGL : Subgroup (GL (Fin n) F) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F).IsDiag}
  mul_mem' := fun hA hB => isDiag_mul hA hB
  one_mem' := Matrix.isDiag_one
  inv_mem' := by
    intro A hA
    have hcoe : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F)⁻¹ := by
      haveI : Invertible (A : Matrix (Fin n) (Fin n) F) := A.invertible
      rw [← Matrix.coe_units_inv]
    obtain ⟨d, hd⟩ : ∃ d, (A : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d :=
      ⟨_, (Matrix.IsDiag.diagonal_diag hA).symm⟩
    change ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag
    rw [hcoe, hd, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _

@[simp]
theorem mem_diagonalGL {A : GL (Fin n) F} :
    A ∈ (diagonalGL : Subgroup (GL (Fin n) F)) ↔
      (A : Matrix (Fin n) (Fin n) F).IsDiag := Iff.rfl

theorem diagonalGL_le_upperTriangularGL :
    (diagonalGL : Subgroup (GL (Fin n) F)) ≤ upperTriangularGL := by
  intro A hA i j h
  have hji : j < i := h
  exact hA hji.ne'

/-- 上三角可逆行列による上三角冪単行列の共役はふたたび上三角冪単。

対角成分は `(A U A⁻¹) i i = A i i * U i i * (A⁻¹) i i = A i i * (A⁻¹) i i = 1`。 -/
theorem conj_mem_unitriangularGL {A U : GL (Fin n) F}
    (hA : A ∈ (upperTriangularGL : Subgroup (GL (Fin n) F)))
    (hU : U ∈ (unitriangularGL : Subgroup (GL (Fin n) F))) :
    A * U * A⁻¹ ∈ (unitriangularGL : Subgroup (GL (Fin n) F)) := by
  have hA' : Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id := hA
  have hAinv := blockTriangular_coe_inv hA'
  have hAU : Matrix.BlockTriangular
      ((A * U : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) id :=
    Matrix.BlockTriangular.mul hA' hU.1
  refine ⟨Matrix.BlockTriangular.mul hAU hAinv, fun i => ?_⟩
  have hcoe : ((A * U * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((A * U : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
  have hcoe' : ((A * U : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) * (U : Matrix (Fin n) (Fin n) F) := rfl
  rw [hcoe, blockTriangular_mul_diag hAU hAinv i, hcoe',
    blockTriangular_mul_diag hA' hU.1 i, hU.2 i, mul_one, diag_mul_diag_inv hA' i]

/-- 上三角可逆行列は上三角冪単部分群を正規化する (`P ⊴ B`)。 -/
theorem upperTriangularGL_le_normalizer :
    (upperTriangularGL : Subgroup (GL (Fin n) F)) ≤
      Subgroup.normalizer (unitriangularGL : Subgroup (GL (Fin n) F)) := by
  intro A hA
  rw [Subgroup.mem_normalizer_iff]
  refine fun U => ⟨fun hU => conj_mem_unitriangularGL hA hU, fun hU => ?_⟩
  have h := conj_mem_unitriangularGL (inv_mem hA) hU
  have heq : A⁻¹ * (A * U * A⁻¹) * A⁻¹⁻¹ = U := by group
  rwa [heq] at h

/-- **Isaacs 7A.3(a)** — 対角部分群 `D` は上三角冪単 Sylow `p`-部分群 `P` を正規化する:
`D ≤ N_G(P)`。 -/
theorem diagonalGL_le_normalizer :
    (diagonalGL : Subgroup (GL (Fin n) F)) ≤
      Subgroup.normalizer (unitriangularGL : Subgroup (GL (Fin n) F)) :=
  le_trans diagonalGL_le_upperTriangularGL upperTriangularGL_le_normalizer

/-! ### 7A.3(b): `DP` = 可逆上三角行列全体 -/

/-- **Isaacs 7A.3(b)** — `DP` は「対角成分が任意の非零元である上三角行列」全体, すなわち
可逆上三角行列 (Borel 部分群) 全体に一致する。

`A` が可逆上三角なら `D := diagonal (fun i => A i i)` は可逆 (各対角成分が単元) で,
`U := D⁻¹ * A` は上三角かつ対角成分がすべて `1`。 -/
theorem diagonalGL_mul_unitriangularGL :
    ((diagonalGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) *
        ((unitriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) =
      ((upperTriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
  ext A
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨D, hD, U, hU, rfl⟩
    exact mul_mem (diagonalGL_le_upperTriangularGL hD) (unitriangularGL_le_upperTriangularGL hU)
  · intro hA
    have hA' : Matrix.BlockTriangular (A : Matrix (Fin n) (Fin n) F) id := hA
    -- `D` = `A` の対角成分からなる可逆対角行列
    have hdiagUnit : IsUnit (Matrix.diagonal (fun i => (A : Matrix (Fin n) (Fin n) F) i i)) :=
      Matrix.isUnit_diagonal.mpr
        (Pi.isUnit_iff.mpr fun i => isUnit_diag_of_blockTriangular hA' i)
    have hDmem : (hdiagUnit.unit : GL (Fin n) F) ∈
        (diagonalGL : Subgroup (GL (Fin n) F)) := by
      change ((hdiagUnit.unit : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag
      rw [hdiagUnit.unit_spec]
      exact Matrix.isDiag_diagonal _
    have hDtri : Matrix.BlockTriangular
        ((hdiagUnit.unit : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) id :=
      diagonalGL_le_upperTriangularGL hDmem
    have hDinvTri := blockTriangular_coe_inv hDtri
    refine ⟨hdiagUnit.unit, hDmem, hdiagUnit.unit⁻¹ * A, ?_, by rw [mul_inv_cancel_left]⟩
    refine ⟨Matrix.BlockTriangular.mul hDinvTri hA', fun i => ?_⟩
    have hcoe : (((hdiagUnit.unit⁻¹ * A : GL (Fin n) F)) :
        Matrix (Fin n) (Fin n) F) =
        (((hdiagUnit.unit⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
          (A : Matrix (Fin n) (Fin n) F) := rfl
    have hDii : ((hdiagUnit.unit : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
        (A : Matrix (Fin n) (Fin n) F) i i := by
      rw [hdiagUnit.unit_spec, Matrix.diagonal_apply_eq]
    rw [hcoe, blockTriangular_mul_diag hDinvTri hA' i, ← hDii, mul_comm,
      diag_mul_diag_inv hDtri i]

/-- **Isaacs 7A.3(b)** (部分群版) — `D ⊔ P` は可逆上三角行列全体。 -/
theorem diagonalGL_sup_unitriangularGL :
    (diagonalGL : Subgroup (GL (Fin n) F)) ⊔ unitriangularGL = upperTriangularGL := by
  refine le_antisymm
    (sup_le diagonalGL_le_upperTriangularGL unitriangularGL_le_upperTriangularGL) fun A hA => ?_
  have hmem : A ∈ ((diagonalGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) *
      ((unitriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
    rw [diagonalGL_mul_unitriangularGL]; exact hA
  rw [Set.mem_mul] at hmem
  obtain ⟨D, hD, U, hU, rfl⟩ := hmem
  exact mul_mem (Subgroup.mem_sup_left hD) (Subgroup.mem_sup_right hU)

end

end OddOrder.Isaacs.Ch07
