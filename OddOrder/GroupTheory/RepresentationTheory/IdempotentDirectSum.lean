/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Module

/-!
# Internal direct sum from a complete orthogonal family of idempotent endomorphisms

For Peterfalvi (9.1)'s kernel-FPF count (†), the module `W = [V,U]` decomposes into its
`U`-isotypic components, obtained as the ranges of the **central idempotent projections**
`π_i := (asAlgebraHom ρ) ε_i` of `Z(𝔽̄_p[U])`.  To feed the free-orbit count
(`WielandtCounting.finrank_eq_card_mul_finrank_invariants_of_free`), which wants
`DirectSum.IsInternal A`, we need: a **complete orthogonal family of idempotent endomorphisms**
`π : ι → Module.End R M` gives an internal direct sum `M = ⊕_i range (π i)`.

`isInternal_range_of_completeOrthogonalIdempotents` proves exactly this.  The central idempotents
`{idemBasis φ i}` of `Z(𝔽̄_p[U])` form such a family (`CompleteOrthogonalIdempotents`), and their
images under the algebra map `asAlgebraHom ρ` (which is a ring hom, so preserves the structure by
`CompleteOrthogonalIdempotents.map`) are the projections.
-/

namespace OddOrder.GroupTheory.IdempotentDirectSum

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

open scoped DirectSum

/-- **Internal direct sum from idempotent endomorphisms.**  A complete orthogonal family of
idempotent endomorphisms `π : ι → Module.End R M` (pairwise `π i ∘ π j = 0`, summing to `id`)
decomposes `M = ⊕_i range (π i)` internally. -/
theorem isInternal_range_of_completeOrthogonalIdempotents
    {π : ι → Module.End R M} (hπ : CompleteOrthogonalIdempotents π) :
    DirectSum.IsInternal (fun i => LinearMap.range (π i)) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · -- independence: `π i` fixes `range (π i)` but kills every other range.
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro m hmi hmsup
    -- `π i` is the identity on `range (π i)`.
    obtain ⟨a, rfl⟩ := hmi
    have hfix : π i (π i a) = π i a := by
      have h := DFunLike.congr_fun (hπ.idem i) a
      rwa [Module.End.mul_apply] at h
    -- and `π i` annihilates `⨆ j ≠ i, range (π j)`.
    have hker : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (π j)) ≤ LinearMap.ker (π i) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hπ.ortho (Ne.symm hj)]
      rfl
    have hz : π i (π i a) = 0 := LinearMap.mem_ker.mp (hker hmsup)
    rw [hfix] at hz
    exact hz
  · -- completeness: `m = (∑ π i) m = ∑ (π i m)`, each summand in its range.
    rw [eq_top_iff]
    intro m _
    have hsum : (∑ i, π i m) = m := by rw [← LinearMap.sum_apply, hπ.complete]; rfl
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (π i) m)

end OddOrder.GroupTheory.IdempotentDirectSum
