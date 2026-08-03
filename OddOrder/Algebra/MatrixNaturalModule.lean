/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The natural module of a matrix algebra is simple

Brauer's count (`Modular/BrauerCount`) produces the number of matrix *blocks* of `kG ⧸ J(kG)`.
Identifying those blocks with the irreducible `kG`-modules — the uniqueness half of
Artin–Wedderburn — starts from the fact that the column vectors `n → k` form a simple module over
`M_n(k)`.

mathlib has the corresponding statement for endomorphism rings,
`IsSimpleModule (Module.End k V) V`, but no `Module (Matrix n n k) (n → k)` instance (there is no
canonical choice: `n → k` already carries its `k`-module structure).  So the action is installed
here as a *scoped* instance and the simplicity is transported along
`Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k)`.

## Main results

* `OddOrder.MatrixModule.matrixNaturalModule` — the scoped `Module (Matrix n n k) (n → k)`
* `OddOrder.MatrixModule.isSimpleModule_matrix`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

variable (k n) in
/-- `Matrix n n k` as an algebra of endomorphisms of the column vectors. -/
noncomputable def toEndRingHom : Matrix n n k →+* Module.End k (n → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := n)).toRingEquiv.toRingHom

theorem toEndRingHom_apply (M : Matrix n n k) (v : n → k) :
    toEndRingHom k n M v = M *ᵥ v := rfl

/-- **The natural module of a matrix algebra**: column vectors, with `M • v = M *ᵥ v`.

Scoped: `n → k` already carries its `k`-module structure, and mathlib deliberately provides no
`Module (Matrix n n k) (n → k)` instance. -/
noncomputable scoped instance matrixNaturalModule : Module (Matrix n n k) (n → k) :=
  Module.compHom _ (toEndRingHom k n)

@[simp]
theorem matrix_smul_def (M : Matrix n n k) (v : n → k) : M • v = M *ᵥ v := rfl

/-- The identity, viewed as a semilinear equivalence over
`Matrix n n k ≃ Module.End k (n → k)`. -/
noncomputable def toEndSemilinear :
    (n → k) →ₛₗ[toEndRingHom k n] (n → k) where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The column vectors are a simple `M_n(k)`-module.** -/
scoped instance isSimpleModule_matrix [Nonempty n] :
    IsSimpleModule (Matrix n n k) (n → k) := by
  haveI : RingHomSurjective (toEndRingHom k n) :=
    ⟨(Matrix.toLinAlgEquiv' (R := k) (n := n)).surjective⟩
  exact (toEndSemilinear.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
    inferInstance

end OddOrder.MatrixModule
