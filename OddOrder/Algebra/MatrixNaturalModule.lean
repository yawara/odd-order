/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix

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

Conversely a simple Artinian ring has, up to isomorphism, only one simple module
(`IsSimpleRing.isIsotypic`), so `n → k` is *the* simple `M_n(k)`-module.

## Main results

* `OddOrder.MatrixModule.matrixNaturalModule` — the scoped `Module (Matrix n n k) (n → k)`
* `OddOrder.MatrixModule.isSimpleModule_matrix`
* `OddOrder.MatrixModule.linearEquiv_of_isSimpleRing`
* `OddOrder.MatrixModule.linearEquiv_natural_of_isSimpleModule`
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

/-! ### Uniqueness: a simple Artinian ring has only one simple module -/

/-- **Over a simple Artinian ring any two simple modules are isomorphic.**  Both sit inside
`M × N` as simple submodules, and every module over such a ring is isotypic
(`IsSimpleRing.isIsotypic`). -/
theorem linearEquiv_of_isSimpleRing (R : Type*) [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  haveI : IsSimpleModule R (Submodule.fst R M N) :=
    IsSimpleModule.congr (Submodule.fstEquiv R M N)
  haveI : IsSimpleModule R (Submodule.snd R M N) :=
    IsSimpleModule.congr (Submodule.sndEquiv R M N)
  obtain ⟨e⟩ := IsSimpleRing.isIsotypic R (M × N) (Submodule.snd R M N) (Submodule.fst R M N)
  exact ⟨(Submodule.fstEquiv R M N).symm.trans (e.trans (Submodule.sndEquiv R M N))⟩

/-- **Every simple `M_n(k)`-module is the module of column vectors.**  This is the uniqueness
half of Artin–Wedderburn for a single matrix block. -/
theorem linearEquiv_natural_of_isSimpleModule [Nonempty n] (M : Type*) [AddCommGroup M]
    [Module (Matrix n n k) M] [IsSimpleModule (Matrix n n k) M] :
    Nonempty (M ≃ₗ[Matrix n n k] (n → k)) := by
  haveI : IsArtinianRing (Matrix n n k) := isArtinian_of_tower k inferInstance
  exact linearEquiv_of_isSimpleRing _ _ _

end OddOrder.MatrixModule
