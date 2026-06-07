/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction

/-!
# Block decomposition of `End V` (BG Prop 2.4(c)/(g))

`OddOrder.GroupTheory.RepresentationTheory` shared module towards the `(g)` step of
**Bender–Glauberman Proposition 2.4**: `dim E_m = ∑ᵢ nᵢ nᵢ₊ₘ` for the conjugation
eigenspaces `E_m`, via the block decomposition `End V = ⊕_{i,t} Hom(Vᵢ, Vₜ)`.

First building block: the reconstruction `∑ᵢ (component i of v) = v` for the internal
eigenspace decomposition `V = ⊕ᵢ Vᵢ` of Prop 2.4(a).
-/

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **Reconstruction of a vector from its eigenspace components.** -/
theorem sum_cyclicEigenspaceFinDecomposition_eq {epsilon : F} {g : Module.End F V} {h : ℕ}
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) (v : V) :
    ∑ i, ((cyclicEigenspaceFinDecomposition hV v i :
      cyclicEigenspaceFinFamily epsilon g h i) : V) = v := by
  classical
  have hcoe : DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h)
      (cyclicEigenspaceFinDecomposition hV v) = v :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h))
      hV).apply_symm_apply v
  conv_rhs => rw [← hcoe, DirectSum.coeLinearMap_eq_dfinsuppSum]
  rw [DFinsupp.sum_eq_sum_fintype _ (fun _ => rfl)]
  simp

/-- **Every endomorphism is the sum of its `(i,t)`-blocks** (BG Prop 2.4(c), spanning half). -/
theorem sum_cyclicHomBlockFinProjection_eq {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h))
    (e : Module.End F V) :
    ∑ p : Fin h × Fin h, ((cyclicHomBlockFinProjection hV p.1 p.2 e : Module.End F V)) = e := by
  classical
  ext v
  have hv : v ∈ ⨆ j, cyclicEigenspaceFinFamily epsilon g h j := by
    rw [hV.submodule_iSup_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem j w hw =>
    rw [LinearMap.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [Finset.sum_congr rfl
        (fun t _ => cyclicHomBlockFinProjection_apply_of_mem_same hV e hw)]
      exact sum_cyclicEigenspaceFinDecomposition_eq hV (e w)
    · intro i _ hi
      exact Finset.sum_eq_zero
        (fun t _ => cyclicHomBlockFinProjection_apply_of_mem_ne hV (Ne.symm hi) e hw)
    · intro hj; exact absurd (mem_univ j) hj
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- The `(i,t)`-blocks span all of `End V` (BG Prop 2.4(c), supremum form). -/
theorem iSup_cyclicHomBlockFin_eq_top {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) :
    ⨆ p : Fin h × Fin h, cyclicHomBlockFin epsilon g p.1 p.2 = ⊤ := by
  rw [eq_top_iff]
  intro e _
  rw [← sum_cyclicHomBlockFinProjection_eq hV e]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.mem_iSup_of_mem p (Submodule.coe_mem _)

open Module in
/-- **The `(i,t)`-blocks form an internal direct sum** `End V = ⊕_{i,t} E_{i,t}` (BG Prop 2.4(c)).
The blocks span (`iSup_cyclicHomBlockFin_eq_top`) and
`∑ dim E_{i,t} = (∑ nᵢ)² = (dim V)² = dim End`, so the coercion `⊕ E_{i,t} → End` is a surjection
between equal-dimensional spaces, hence bijective. -/
theorem isInternal_cyclicHomBlockFin {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) :
    DirectSum.IsInternal (fun p : Fin h × Fin h => cyclicHomBlockFin epsilon g p.1 p.2) := by
  have hsurj : Function.Surjective (DirectSum.coeLinearMap
      (fun p : Fin h × Fin h => cyclicHomBlockFin epsilon g p.1 p.2)) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, iSup_cyclicHomBlockFin_eq_top hV]
  have hsumV : ∑ i, cyclicEigenspaceFinDim epsilon g (i : Fin h) = finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h)) hV).finrank_eq,
      finrank_directSum]
  have hfin : finrank F (DirectSum (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)) = finrank F (Module.End F V) := by
    rw [finrank_directSum]
    simp_rw [finrank_cyclicHomBlockFin hV]
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hsumV, Module.finrank_linearMap]
  haveI : ∀ p : Fin h × Fin h, FiniteDimensional F (cyclicHomBlockFin epsilon g p.1 p.2) :=
    fun _ => inferInstance
  haveI : FiniteDimensional F (DirectSum (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype F (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)).symm
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj, hsurj⟩

end OddOrder.RepresentationTheory
