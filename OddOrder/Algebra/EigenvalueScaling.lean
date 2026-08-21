/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Conjugating an operator into a scalar multiple of itself shifts its eigenvalues

If an invertible `S` intertwines `T` with `ω • T`, in the sense that

`S (T v) = ω • T (S v)`  for all `v`,

then `S` carries the `ζ`-eigenspace of `T` isomorphically onto the `ω⁻¹ζ`-eigenspace.  In
particular all the eigenvalue multiplicities of `T` are invariant under multiplication by `ω`.

This is the linear-algebra core of the vanishing half of the Brauer–Nesbitt formula
(**Navarro (8.2)**): for an orbit of length `ℓ > 1` of `g` on the cosets `H \\ G`, the induced
module has a block grading, and multiplying the `i`-th block by `ω^i` (for `ω` a primitive
`ℓ`-th root of unity) intertwines the action of `g` with `ω` times itself.  The multiplicities
are then `ω`-invariant, which forces the Brauer character — a multiplicity-weighted sum of
lifted eigenvalues — to vanish.

Nothing here is specific to that application: the statements are about an arbitrary operator on
a vector space over an arbitrary field.

## Main results

* `mem_eigenspace_smul_of_intertwine` — `S` maps the `ζ`-eigenspace into the `ω⁻¹ζ`-eigenspace
* `intertwine_symm` — `S⁻¹` intertwines `T` with `ω⁻¹ • T`
* `map_eigenspace_of_intertwine` — the image is *exactly* the `ω⁻¹ζ`-eigenspace
* `finrank_eigenspace_eq_of_intertwine` — the two eigenspaces have the same dimension
-/

namespace OddOrder.Algebra

open Module Module.End

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- If `S (T v) = ω • T (S v)` for all `v`, then `S` carries `ζ`-eigenvectors of `T` to
`ω⁻¹ζ`-eigenvectors. -/
theorem mem_eigenspace_smul_of_intertwine {T : Module.End F V} {S : V →ₗ[F] V} {ω : F}
    (hω : ω ≠ 0) (h : ∀ v, S (T v) = ω • T (S v)) {ζ : F} {v : V}
    (hv : v ∈ Module.End.eigenspace T ζ) :
    S v ∈ Module.End.eigenspace T (ω⁻¹ * ζ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : S (T v) = ω • T (S v) := h v
  rw [hv, map_smul] at h1
  -- `h1 : ζ • S v = ω • T (S v)`
  have h2 : T (S v) = ω⁻¹ • (ζ • S v) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [h2, smul_smul]

/-- The inverse of an intertwiner intertwines with the inverse scalar. -/
theorem intertwine_symm {T : Module.End F V} {S : V ≃ₗ[F] V} {ω : F} (hω : ω ≠ 0)
    (h : ∀ v, S (T v) = ω • T (S v)) (w : V) :
    S.symm (T w) = ω⁻¹ • T (S.symm w) := by
  have hv := h (S.symm w)
  rw [S.apply_symm_apply] at hv
  -- `hv : S (T (S.symm w)) = ω • T w`
  have : T (S.symm w) = S.symm (ω • T w) := by
    rw [← hv, S.symm_apply_apply]
  rw [this, map_smul, smul_smul, inv_mul_cancel₀ hω, one_smul]

/-- The image of the `ζ`-eigenspace under an intertwiner is exactly the `ω⁻¹ζ`-eigenspace. -/
theorem map_eigenspace_of_intertwine {T : Module.End F V} {S : V ≃ₗ[F] V} {ω : F} (hω : ω ≠ 0)
    (h : ∀ v, S (T v) = ω • T (S v)) (ζ : F) :
    Submodule.map (S : V →ₗ[F] V) (Module.End.eigenspace T ζ)
      = Module.End.eigenspace T (ω⁻¹ * ζ) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_eigenspace_smul_of_intertwine hω h hv
  · intro w hw
    refine ⟨S.symm w, ?_, S.apply_symm_apply w⟩
    -- `S.symm` intertwines with `ω⁻¹`, so it sends the `ω⁻¹ζ`-eigenspace to the `ζ`-one
    have hmem := mem_eigenspace_smul_of_intertwine (T := T) (S := (S.symm : V →ₗ[F] V))
      (ω := ω⁻¹) (inv_ne_zero hω) (intertwine_symm hω h) hw
    rwa [inv_inv, ← mul_assoc, mul_inv_cancel₀ hω, one_mul] at hmem

/-- **Eigenvalue multiplicities are invariant under the intertwining scalar.** -/
theorem finrank_eigenspace_eq_of_intertwine [FiniteDimensional F V] {T : Module.End F V}
    {S : V ≃ₗ[F] V} {ω : F} (hω : ω ≠ 0) (h : ∀ v, S (T v) = ω • T (S v)) (ζ : F) :
    finrank F (Module.End.eigenspace T (ω⁻¹ * ζ)) = finrank F (Module.End.eigenspace T ζ) := by
  rw [← map_eigenspace_of_intertwine hω h ζ]
  exact (Submodule.equivMapOfInjective (S : V →ₗ[F] V) S.injective
    (Module.End.eigenspace T ζ)).symm.finrank_eq

end OddOrder.Algebra
