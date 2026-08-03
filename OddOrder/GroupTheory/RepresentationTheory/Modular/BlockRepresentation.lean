/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import OddOrder.Algebra.PiMatrixSimpleModules

/-!
# The representation carried by a block

The classification of the simple `kG`-modules (`Algebra/PiMatrixSimpleModules`) is phrased in
terms of `Module (kG) M`, whereas Brauer characters (`Modular/BrauerCharacter`) are defined for
`Representation k G V`.  This file is the bridge: given a surjection
`π : kG ↠ ∏_j M_{n_j}(k)`, the `i`-th block carries the representation

`g ↦ (v ↦ π (single g 1) i *ᵥ v)`,

whose module structure is the `blockModule` of the classification.  So the Brauer characters of
these representations are exactly the irreducible ones.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockRepresentation`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {k G ι : Type*} [Field k] [Group G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]

/-- **The representation of `G` on the `i`-th block** of a surjection `kG ↠ ∏_j M_{n_j}(k)`. -/
noncomputable def blockRepresentation
    (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) :
    Representation k G (nn i → k) where
  toFun g := Matrix.mulVecLin (π (single g 1) i)
  map_one' := by
    rw [show (single (1 : G) (1 : k) : MonoidAlgebra k G) = 1 from rfl, map_one]
    simp only [Pi.one_apply, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    rw [show (single (g * h) (1 : k) : MonoidAlgebra k G) = single g 1 * single h 1 by
      rw [single_mul_single, mul_one], map_mul]
    simp only [Pi.mul_apply, Matrix.mulVecLin_mul]
    rfl

@[simp]
theorem blockRepresentation_apply (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι)
    (g : G) (v : nn i → k) :
    blockRepresentation π i g v = π (single g 1) i *ᵥ v := rfl

/-- The representation on a block is the one underlying its module structure. -/
theorem blockRepresentation_apply_eq_smul
    (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) (g : G) (v : nn i → k) :
    letI := MatrixModule.blockModule nn π i
    blockRepresentation π i g v = (single g (1 : k) : MonoidAlgebra k G) • v := rfl

end OddOrder.RepresentationTheory.Modular
