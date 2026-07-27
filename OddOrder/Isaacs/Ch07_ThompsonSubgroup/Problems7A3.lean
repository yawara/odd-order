/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

(a)(b) の鍵は「上三角行列の積の対角成分は対角成分の積」(`blockTriangular_mul_diag`) で,
これから冪単性が積・逆元・共役で保たれることが従う。(c) は transvection `1 + c·E_{i,j}` を
`P` の元として使い「非零成分をもつ最小添字」で不変部分空間を捕まえる。(d) は `W ᵥ* A` が
ふたたび `P`-不変で次元が変わらないことと (c) の一意性から従う。

`Matrix.BlockTriangular M id` (`∀ i j, j < i → M i j = 0`) を「上三角」の定義に使う。

⚠ `q` が素数冪であることも `P` が Sylow `p`-部分群であることも使わない — 主張は
**任意の体 `F`** 上で成立する (`|F| = q` は Sylow としての解釈にのみ効く)。
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

/-! ### 7A.3(c): `P`-不変部分空間の分類 -/

/-- 部分群 `H ≤ GL(n,q)` の**行ベクトルへの右からの作用** `v ↦ v ᵥ* A` で不変な部分空間。 -/
def IsRowInvariant (H : Subgroup (GL (Fin n) F)) (W : Submodule F (Fin n → F)) : Prop :=
  ∀ A ∈ H, ∀ v ∈ W, Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) ∈ W

/-- 標準旗の第 `m` 段 `⟨e_m, e_{m+1}, …, e_{n-1}⟩` (0-indexed, 次元 `n - m`)。

`G` は行ベクトルに**右から**作用するので, 上三角行列で不変なのは「**後ろ**の座標が張る」
部分空間の方 (`e_i ᵥ* A` は `A` の第 `i` 行 = `e_i, …, e_{n-1}` の一次結合)。 -/
def rowTail (n : ℕ) (m : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, (i : ℕ) < m → v i = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro u v hu hv i hi
    simp [hu i hi, hv i hi]
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]

@[simp]
theorem mem_rowTail {m : ℕ} {v : Fin n → F} :
    v ∈ rowTail (F := F) n m ↔ ∀ i : Fin n, (i : ℕ) < m → v i = 0 := Iff.rfl

@[simp]
theorem rowTail_zero : rowTail (F := F) n 0 = ⊤ := by
  ext v; simp

@[simp]
theorem rowTail_self : rowTail (F := F) n n = ⊥ := by
  ext v
  simp only [mem_rowTail, Submodule.mem_bot]
  exact ⟨fun h => funext fun i => h i i.isLt, fun h i _ => by rw [h]; rfl⟩

theorem rowTail_antitone {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    rowTail (F := F) n m₂ ≤ rowTail (F := F) n m₁ :=
  fun _ hv i hi => hv i (lt_of_lt_of_le hi h)

/-- **標準旗は `P`-不変** (実際は Borel `B` の作用でも不変)。

`(v ᵥ* A) i = ∑ k, v k * A k i` で, `k < m` なら `v k = 0`, `k ≥ m > i` なら `A k i = 0`。 -/
theorem isRowInvariant_rowTail (m : ℕ) :
    IsRowInvariant (upperTriangularGL : Subgroup (GL (Fin n) F)) (rowTail n m) := by
  intro A hA v hv i hi
  have hsum : Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) i
      = ∑ k, v k * (A : Matrix (Fin n) (Fin n) F) k i := rfl
  rw [hsum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (k : ℕ) m with hk | hk
  · rw [hv k hk, zero_mul]
  · have hik : i < k := by rw [Fin.lt_def]; omega
    rw [hA hik, mul_zero]

/-! #### transvection (`1 + c·E_{i,j}`) -/

/-- transvection `1 + c·E_{i,j}` (`i ≠ j`) を `GL(n,q)` の元として。逆元は `c ↦ -c`。 -/
def transvectionGL {i j : Fin n} (hij : i ≠ j) (c : F) : GL (Fin n) F where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel,
      Matrix.transvection_zero]

@[simp]
theorem coe_transvectionGL {i j : Fin n} (hij : i ≠ j) (c : F) :
    ((transvectionGL hij c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.transvection i j c := rfl

/-- `i < j` なら transvection は上三角冪単。 -/
theorem transvectionGL_mem_unitriangularGL {i j : Fin n} (hij : i < j) (c : F) :
    transvectionGL hij.ne c ∈ (unitriangularGL : Subgroup (GL (Fin n) F)) := by
  refine ⟨fun r s hsr => ?_, fun a => ?_⟩
  · have hrs : s ≠ r := (ne_of_lt hsr)
    have hne : ¬(i = r ∧ j = s) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt_of_gt hsr)
    simp [coe_transvectionGL, Matrix.transvection, Ne.symm hrs, hne]
  · have hne : ¬(i = a ∧ j = a) := by
      rintro ⟨rfl, h⟩
      exact hij.ne' h
    simp [coe_transvectionGL, Matrix.transvection, hne]

/-- `v ᵥ* E_{i,j}(c) = (v i * c) · e_j`。 -/
theorem vecMul_single (v : Fin n → F) (i j : Fin n) (c : F) :
    Matrix.vecMul v (Matrix.single i j c) = Pi.single j (v i * c) := by
  ext k
  have hsum : Matrix.vecMul v (Matrix.single i j c) k
      = ∑ l, v l * Matrix.single i j c l k := rfl
  rw [hsum, Pi.single_apply]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i
      (fun l _ hl => by rw [Matrix.single_apply, if_neg (by rintro ⟨rfl, -⟩; exact hl rfl),
        mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), Matrix.single_apply_same]
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.single_apply, if_neg (by rintro ⟨-, rfl⟩; exact hk rfl), mul_zero]

/-- transvection の行ベクトルへの右作用: `v ᵥ* (1 + c·E_{i,j}) = v + (v i * c) · e_j`。 -/
theorem vecMul_transvectionGL {i j : Fin n} (hij : i ≠ j) (c : F) (v : Fin n → F) :
    Matrix.vecMul v ((transvectionGL hij c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = v + Pi.single j (v i * c) := by
  rw [coe_transvectionGL, Matrix.transvection, Matrix.vecMul_add, Matrix.vecMul_one,
    vecMul_single]

/-! #### 分類定理 -/

/-- `P`-不変部分空間 `W` が `e_{i₀}` 方向に非零成分をもち, かつ `i₀` より前の成分がすべて
消えているなら, `W` は `i₀` 以降の標準基底ベクトルをすべて含む。 -/
theorem single_mem_of_isRowInvariant {W : Submodule F (Fin n → F)}
    (hW : IsRowInvariant (unitriangularGL : Subgroup (GL (Fin n) F)) W)
    {v : Fin n → F} (hv : v ∈ W) {i₀ : Fin n} (hv0 : v i₀ ≠ 0)
    (hlow : ∀ k : Fin n, k < i₀ → v k = 0) :
    ∀ j : Fin n, i₀ ≤ j → ∀ c : F, Pi.single j c ∈ W := by
  classical
  -- Step 1: `i₀ < j` のとき (transvection で `v` を動かして差をとる)
  have hgt : ∀ j : Fin n, i₀ < j → ∀ c : F, Pi.single j c ∈ W := by
    intro j hij c
    have hmem := hW _ (transvectionGL_mem_unitriangularGL hij (1 : F)) v hv
    rw [vecMul_transvectionGL, mul_one] at hmem
    have hsub : Pi.single j (v i₀) ∈ W := by
      simpa using W.sub_mem hmem hv
    have hscale := W.smul_mem (c / v i₀) hsub
    rwa [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ hv0] at hscale
  -- Step 2: `j = i₀` (`v` から `i₀` より後の成分を引き去る)
  have heq0 : ∀ c : F, Pi.single i₀ c ∈ W := by
    have hu : (∑ j ∈ Finset.univ.filter (fun j : Fin n => i₀ < j), Pi.single j (v j)) ∈ W :=
      Submodule.sum_mem _ fun j hj => hgt j (Finset.mem_filter.mp hj).2 _
    have hdiff : v - (∑ j ∈ Finset.univ.filter (fun j : Fin n => i₀ < j), Pi.single j (v j))
        = Pi.single i₀ (v i₀) := by
      funext k
      have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin n => i₀ < j), Pi.single j (v j)) k
          = if i₀ < k then v k else 0 := by
        simp only [Finset.sum_apply, Pi.single_apply]
        rw [Finset.sum_ite_eq (Finset.univ.filter (fun j : Fin n => i₀ < j)) k v]
        simp
      rw [Pi.sub_apply, hsum, Pi.single_apply]
      rcases lt_trichotomy k i₀ with hk | rfl | hk
      · rw [hlow k hk, if_neg (asymm hk), if_neg (ne_of_lt hk), sub_zero]
      · rw [if_neg (lt_irrefl _), if_pos rfl, sub_zero]
      · rw [if_pos hk, if_neg (ne_of_gt hk), sub_self]
    have hmem : Pi.single i₀ (v i₀) ∈ W := hdiff ▸ W.sub_mem hv hu
    intro c
    have hscale := W.smul_mem (c / v i₀) hmem
    rwa [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ hv0] at hscale
  intro j hij c
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact heq0 c
  · exact hgt j hlt c

/-- **Isaacs 7A.3(c)** — `P`-不変部分空間は標準旗 `rowTail n m` (`m ≤ n`) に限る。 -/
theorem exists_eq_rowTail_of_isRowInvariant (W : Submodule F (Fin n → F))
    (hW : IsRowInvariant (unitriangularGL : Subgroup (GL (Fin n) F)) W) :
    ∃ m ≤ n, W = rowTail n m := by
  classical
  set Q : ℕ → Prop := fun k => ∀ v ∈ W, ∀ i : Fin n, (i : ℕ) < k → v i = 0 with hQdef
  have hQ0 : Q 0 := fun _ _ i hi => absurd hi (Nat.not_lt_zero _)
  by_cases hQn : Q n
  · refine ⟨n, le_rfl, ?_⟩
    rw [rowTail_self]
    refine le_antisymm (fun v hv => ?_) bot_le
    exact Submodule.mem_bot F |>.mpr (funext fun i => hQn v hv i i.isLt)
  · -- `Q` が破れる最小の段を取る
    have hex : ∃ k, ¬ Q k := ⟨n, hQn⟩
    have hm0 : ¬ Q (Nat.find hex) := Nat.find_spec hex
    have hm0ne : Nat.find hex ≠ 0 := fun h => hm0 (h ▸ hQ0)
    set m := Nat.find hex - 1 with hmdef
    have hmsucc : m + 1 = Nat.find hex := by omega
    have hQm : Q m := not_not.mp (Nat.find_min hex (by omega))
    have hnotQ : ¬ Q (m + 1) := hmsucc ▸ hm0
    -- `¬ Q (m+1)` から `(i₀ : ℕ) = m` なる非零成分をもつ `v ∈ W` を得る
    obtain ⟨v, hv, i₀, hi₀lt, hv0⟩ : ∃ v ∈ W, ∃ i₀ : Fin n, (i₀ : ℕ) < m + 1 ∧ v i₀ ≠ 0 := by
      simp only [hQdef, not_forall] at hnotQ
      obtain ⟨v, hv, i, hi, hvi⟩ := hnotQ
      exact ⟨v, hv, i, hi, hvi⟩
    have hi₀ : (i₀ : ℕ) = m := by
      by_contra hne
      exact hv0 (hQm v hv i₀ (by omega))
    have hmn : m ≤ n := le_of_lt (hi₀ ▸ i₀.isLt)
    have hlow : ∀ k : Fin n, k < i₀ → v k = 0 := by
      intro k hk
      exact hQm v hv k (by rw [Fin.lt_def] at hk; omega)
    have hsingle := single_mem_of_isRowInvariant hW hv hv0 hlow
    refine ⟨m, hmn, le_antisymm (fun w hw i hi => hQm w hw i hi) fun w hw => ?_⟩
    -- `w ∈ rowTail n m` を標準基底で分解
    have hdecomp : w = ∑ j, Pi.single j (w j) := (Finset.univ_sum_single w).symm
    rw [hdecomp]
    refine Submodule.sum_mem _ fun j _ => ?_
    rcases lt_or_ge (j : ℕ) m with hj | hj
    · rw [hw j hj]
      simp
    · exact hsingle j (by rw [Fin.le_def]; omega) _

/-! #### 次元と一意性 -/

/-- `H ≤ K` なら `K`-不変部分空間は `H`-不変。 -/
theorem IsRowInvariant.mono {H K : Subgroup (GL (Fin n) F)} (hHK : H ≤ K)
    {W : Submodule F (Fin n → F)} (hW : IsRowInvariant K W) : IsRowInvariant H W :=
  fun A hA => hW A (hHK hA)

/-- `m ≤ n` のとき `{i : Fin n // (i : ℕ) < m} ≃ Fin m`。 -/
def finLtEquiv {m : ℕ} (hm : m ≤ n) : {i : Fin n // (i : ℕ) < m} ≃ Fin m where
  toFun i := ⟨i.1, i.2⟩
  invFun j := ⟨⟨j, lt_of_lt_of_le j.2 hm⟩, j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `rowTail n m` は「最初の `m` 座標への射影」の核。 -/
theorem rowTail_eq_ker (m : ℕ) :
    rowTail (F := F) n m =
      LinearMap.ker (LinearMap.funLeft F F
        (Subtype.val : {i : Fin n // (i : ℕ) < m} → Fin n)) := by
  ext v
  simp only [mem_rowTail, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
    Pi.zero_apply, Subtype.forall]

/-- `rowTail n m` の次元は `n - m` (階数・退化次数定理)。 -/
theorem finrank_rowTail {m : ℕ} (hm : m ≤ n) :
    Module.finrank F (rowTail (F := F) n m) = n - m := by
  have hsurj : Function.Surjective
      (LinearMap.funLeft F F (Subtype.val : {i : Fin n // (i : ℕ) < m} → Fin n)) :=
    LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective
  have hcard : Fintype.card {i : Fin n // (i : ℕ) < m} = m := by
    rw [Fintype.card_congr (finLtEquiv hm), Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft F F (Subtype.val : {i : Fin n // (i : ℕ) < m} → Fin n))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_fintype_fun_eq_card, hcard, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hrn
  rw [rowTail_eq_ker]
  omega

/-- **Isaacs 7A.3(c)** — 各次元 `k ≤ n` に対し `P`-不変部分空間はちょうど 1 つ存在する
(すなわち標準旗 `rowTail n (n - k)`)。 -/
theorem existsUnique_isRowInvariant_finrank_eq {k : ℕ} (hk : k ≤ n) :
    ∃! W : Submodule F (Fin n → F),
      IsRowInvariant (unitriangularGL : Subgroup (GL (Fin n) F)) W ∧
        Module.finrank F W = k := by
  refine ⟨rowTail n (n - k), ⟨(isRowInvariant_rowTail (F := F) (n - k)).mono
    unitriangularGL_le_upperTriangularGL, ?_⟩, ?_⟩
  · rw [finrank_rowTail (Nat.sub_le _ _)]
    omega
  · rintro W ⟨hWinv, hWrank⟩
    obtain ⟨m, hmn, rfl⟩ := exists_eq_rowTail_of_isRowInvariant W hWinv
    rw [finrank_rowTail hmn] at hWrank
    have hm : m = n - k := by omega
    rw [hm]

/-! ### 7A.3(d): `N_G(P) = DP` -/

/-- `GL(n,q)` の元 `A` による行ベクトルへの右作用 `v ↦ v ᵥ* A` (線型同型)。 -/
def rowActionEquiv (A : GL (Fin n) F) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (A : Matrix (Fin n) (Fin n) F).vecMulLinear
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).vecMulLinear
    (by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.vecMulLinear_apply,
        LinearMap.id_coe, id_eq]
      rw [Matrix.vecMul_vecMul, A.inv_mul, Matrix.vecMul_one])
    (by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.vecMulLinear_apply,
        LinearMap.id_coe, id_eq]
      rw [Matrix.vecMul_vecMul, A.mul_inv, Matrix.vecMul_one])

@[simp]
theorem rowActionEquiv_apply (A : GL (Fin n) F) (v : Fin n → F) :
    rowActionEquiv A v = Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) := rfl

@[simp]
theorem rowActionEquiv_coe_apply (A : GL (Fin n) F) (v : Fin n → F) :
    ((rowActionEquiv A : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
      (Fin n → F) →ₗ[F] (Fin n → F)) v = Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) := rfl

/-- **`P`-不変部分空間は `N_G(P)`-不変** (Isaacs 7A.3(d) 前半)。

`W` が `P`-不変で `A ∈ N_G(P)` なら, `W ᵥ* A` も `P`-不変 (`(W A) B = (W (A B A⁻¹)) A`) で
次元が等しいので, (c) の一意性から `W ᵥ* A = W`。 -/
theorem rowTail_map_rowActionEquiv (A : GL (Fin n) F)
    (hA : A ∈ Subgroup.normalizer (unitriangularGL : Subgroup (GL (Fin n) F)))
    {m : ℕ} (hm : m ≤ n) :
    (rowTail (F := F) n m).map ((rowActionEquiv A : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
      (Fin n → F) →ₗ[F] (Fin n → F)) = rowTail n m := by
  have hinv : IsRowInvariant (unitriangularGL : Subgroup (GL (Fin n) F))
      ((rowTail (F := F) n m).map
        ((rowActionEquiv A : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
          (Fin n → F) →ₗ[F] (Fin n → F))) := by
    rintro B hB w ⟨v, hv, rfl⟩
    have hconj : A * B * A⁻¹ ∈ (unitriangularGL : Subgroup (GL (Fin n) F)) :=
      (Subgroup.mem_normalizer_iff.mp hA B).mp hB
    refine ⟨Matrix.vecMul v ((A * B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
      isRowInvariant_rowTail m _ (unitriangularGL_le_upperTriangularGL hconj) v hv, ?_⟩
    have hmat : ((A * B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (A : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) := by
      simp
    simp only [rowActionEquiv_coe_apply]
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hmat]
  obtain ⟨m', hm'n, heq⟩ := exists_eq_rowTail_of_isRowInvariant _ hinv
  have hrank : Module.finrank F
      ((rowTail (F := F) n m).map
        ((rowActionEquiv A : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
          (Fin n → F) →ₗ[F] (Fin n → F))) = n - m := by
    rw [LinearEquiv.finrank_map_eq, finrank_rowTail hm]
  rw [heq, finrank_rowTail hm'n] at hrank
  have hmm : m' = m := by omega
  rw [heq, hmm]

/-- **Isaacs 7A.3(d)** — `N_G(P)` は可逆上三角行列全体 (Borel 部分群) に一致する。

`A ∈ N_G(P)` は各標準旗 `rowTail n r` を保つので, `e_r ᵥ* A = A` の第 `r` 行も
`rowTail n r` に入る, すなわち `A r s = 0` (`s < r`)。 -/
theorem normalizer_unitriangularGL_eq :
    Subgroup.normalizer ((unitriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) =
      upperTriangularGL := by
  refine le_antisymm (fun A hA r s hsr => ?_) upperTriangularGL_le_normalizer
  have hrow : Pi.single r (1 : F) ∈ rowTail (F := F) n (r : ℕ) := by
    intro k hk
    exact Pi.single_eq_of_ne (fun h => by rw [h] at hk; omega) 1
  have hmem : Matrix.vecMul (Pi.single r (1 : F)) (A : Matrix (Fin n) (Fin n) F) ∈
      rowTail (F := F) n (r : ℕ) := by
    rw [← rowTail_map_rowActionEquiv A hA (le_of_lt r.isLt)]
    exact ⟨Pi.single r (1 : F), hrow, rfl⟩
  have hzero := hmem s (by rw [Fin.lt_def] at hsr; exact hsr)
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at hzero

/-- **Isaacs 7A.3(d)** (`DP` 形) — `N_G(P) = D ⊔ P`。 -/
theorem normalizer_unitriangularGL_eq_sup :
    Subgroup.normalizer ((unitriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) =
      diagonalGL ⊔ unitriangularGL := by
  rw [normalizer_unitriangularGL_eq, diagonalGL_sup_unitriangularGL]

/-- **Isaacs 7A.3(d)** (集合の積の形) — `N_G(P) = DP`。 -/
theorem normalizer_unitriangularGL_eq_mul :
    ((Subgroup.normalizer ((unitriangularGL : Subgroup (GL (Fin n) F)) :
        Set (GL (Fin n) F))) : Set (GL (Fin n) F)) =
      ((diagonalGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) *
        ((unitriangularGL : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
  rw [normalizer_unitriangularGL_eq, diagonalGL_mul_unitriangularGL]

end

end OddOrder.Isaacs.Ch07
