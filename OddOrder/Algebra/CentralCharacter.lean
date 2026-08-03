/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Ring.Subring.Basic
import OddOrder.Algebra.PiMatrixSimpleModules

/-!
# Central characters of the blocks

A central element of `A` acts on each block of a surjection `π : A ↠ ∏_j M_{n_j}(k)` by a
scalar: its image is central in the matrix algebra, and the centre of a matrix algebra over a
commutative ring consists of the scalar matrices (`Matrix.center_eq_range`).  The resulting map

`ω_i : Z(A) →+* k`

is the **central character** of the `i`-th block.  Two blocks lie in the same *block* of `A` (in
the sense of block theory) exactly when their central characters agree, so this is the entry
point to the block decomposition.

## Main results

* `OddOrder.MatrixModule.exists_scalar_of_mem_center`
* `OddOrder.MatrixModule.centralCharacter`
* `OddOrder.MatrixModule.centralCharacterPi_eq_zero_iff`
* `OddOrder.MatrixModule.SameBlock`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
variable {A : Type*} [Ring A]

/-- **A central element acts on each block by a scalar matrix.** -/
theorem exists_scalar_of_mem_center {π : A →+* ∀ j, Matrix (nn j) (nn j) k}
    (hπ : Function.Surjective π) {z : A} (hz : z ∈ Set.center A) (i : ι) :
    ∃ c : k, π z i = Matrix.scalar (nn i) c := by
  classical
  have hmem : π z i ∈ Set.center (Matrix (nn i) (nn i) k) := by
    rw [Semigroup.mem_center_iff]
    intro M
    obtain ⟨x, hx⟩ := hπ (Pi.single i M)
    have h := congrArg π (Semigroup.mem_center_iff.mp hz x)
    rw [map_mul, map_mul, hx] at h
    simpa using congrFun h i
  rw [Matrix.center_eq_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) [Nonempty (nn i)]

open Classical in
/-- The scalar by which a central element acts on the `i`-th block, read off a diagonal entry. -/
noncomputable def centralScalar (z : A) : k :=
  π z i (Classical.arbitrary (nn i)) (Classical.arbitrary (nn i))

theorem scalar_centralScalar (hπ : Function.Surjective π) {z : A} (hz : z ∈ Set.center A) :
    π z i = Matrix.scalar (nn i) (centralScalar π i z) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hπ hz i
  rw [hc, centralScalar, hc]
  simp

/-- **The central character of the `i`-th block**: a ring homomorphism from the centre of `A` to
the coefficient field. -/
noncomputable def centralCharacter (hπ : Function.Surjective π) :
    Subring.center A →+* k where
  toFun z := centralScalar π i (z : A)
  map_one' := by
    have h1 : π (1 : A) i = 1 := by rw [map_one]; rfl
    simp [centralScalar, h1]
  map_mul' z w := by
    have hzw : π ((z : A) * w) i
        = Matrix.scalar (nn i) (centralScalar π i z) *
          Matrix.scalar (nn i) (centralScalar π i w) := by
      rw [map_mul, Pi.mul_apply, scalar_centralScalar π i hπ z.2,
        scalar_centralScalar π i hπ w.2]
    simp [centralScalar, hzw]
  map_zero' := by simp [centralScalar]
  map_add' z w := by simp [centralScalar]

@[simp]
theorem centralCharacter_apply (hπ : Function.Surjective π) (z : Subring.center A) :
    centralCharacter π i hπ z = centralScalar π i (z : A) := rfl

/-! ### Blocks -/

section Blocks

variable [∀ i, Nonempty (nn i)]

variable (nn) in
/-- The tuple of central characters. -/
noncomputable def centralCharacterPi (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) : Subring.center A →+* (ι → k) :=
  RingHom.pi fun i => centralCharacter π i hπ

/-- **The central characters see exactly `Z(A)` modulo the kernel of the splitting.**  For
`A = kG` the kernel is `J(kG)`, so `Z(kG) ⧸ (Z(kG) ∩ J)` embeds in `∏_i k`; this is what makes
the block decomposition a decomposition of the centre. -/
theorem centralCharacterPi_eq_zero_iff (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) (z : Subring.center A) :
    centralCharacterPi nn π hπ z = 0 ↔ π (z : A) = 0 := by
  constructor
  · intro h
    funext j
    have hj : centralScalar π j (z : A) = 0 := congrFun h j
    rw [scalar_centralScalar π j hπ z.2, hj]
    simp
  · intro h
    funext j
    have hj : π (z : A) j = 0 := by rw [h]; rfl
    simp [centralCharacterPi, RingHom.pi, centralScalar, hj]

variable (nn) in
/-- **Two blocks lie in the same block of `A`** when their central characters agree.  This is
the standard definition of the block partition. -/
def SameBlock (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π) (i j : ι) :
    Prop :=
  centralCharacter π i hπ = centralCharacter π j hπ

theorem sameBlock_equivalence (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) : Equivalence (SameBlock nn π hπ) where
  refl _ := rfl
  symm h := h.symm
  trans h h' := h.trans h'

end Blocks

end OddOrder.MatrixModule
