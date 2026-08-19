/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A simple module lives on one central idempotent

Given a complete orthogonal family of *central* idempotents of `A`, a simple `A`-module is
supported on exactly one of them: that one acts as the identity, the others as zero.  For the
coordinate idempotents of a product ring this is what localises a simple module to one factor
(`PiSimpleModule`); for the block idempotents (`BlockIdempotent`) it is the statement that every
simple module belongs to a unique block.

## Main results

* `OddOrder.exists_unique_smul_eq_self_of_completeOrthogonal`
-/

namespace OddOrder

variable {A : Type*} [Ring A] {κ : Type*} {e : κ → A}
variable {M : Type*} [AddCommGroup M] [Module A M]

variable (e M) in
/-- Multiplication by a central idempotent, as a linear map. -/
def smulCentral (i : κ) (hc : ∀ i, e i ∈ Set.center A) : M →ₗ[A] M where
  toFun s := e i • s
  map_add' _ _ := smul_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply, smul_smul, Semigroup.mem_center_iff.mp (hc i) r]

/-- **On a simple module exactly one member of a complete orthogonal family of central
idempotents acts as the identity** (and the rest act as zero). -/
theorem exists_unique_smul_eq_self_of_completeOrthogonal [Fintype κ]
    (he : CompleteOrthogonalIdempotents e) (hc : ∀ i, e i ∈ Set.center A)
    [IsSimpleModule A M] :
    ∃! i : κ, ∀ s : M, e i • s = s := by
  classical
  have := IsSimpleModule.nontrivial A M
  obtain ⟨s, hs⟩ := exists_ne (0 : M)
  have hsum : ∑ i : κ, e i • s = s := by
    rw [← Finset.sum_smul, he.complete, one_smul]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, e i • s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs (hsum.symm.trans (Finset.sum_eq_zero fun i hi => hcon i hi))
  have hid : ∀ t : M, e i • t = t := by
    have hrange : LinearMap.range (smulCentral e M i hc) = ⊤ := by
      rcases eq_bot_or_eq_top (LinearMap.range (smulCentral e M i hc)) with h | h
      · refine absurd ?_ hi
        have h0 : smulCentral e M i hc = 0 := LinearMap.range_eq_bot.mp h
        calc e i • s = smulCentral e M i hc s := rfl
          _ = 0 := by rw [h0]; simp
      · exact h
    intro t
    obtain ⟨u, hu⟩ := (LinearMap.range_eq_top.mp hrange) t
    have : e i • (e i • u) = e i • u := by rw [smul_smul, he.idem i]
    rw [← hu]
    exact this
  refine ⟨i, hid, fun j hj => ?_⟩
  by_contra hne
  have hzero : e j • s = 0 := by
    rw [← hid s, smul_smul, he.ortho hne, zero_smul]
  exact hs ((hj s).symm.trans hzero)

end OddOrder
