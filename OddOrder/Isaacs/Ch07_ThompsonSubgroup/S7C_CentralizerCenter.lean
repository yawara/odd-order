/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_SylowMaximal

/-!
# Isaacs FGT Ch.7 — Theorem 7.1 Step 5: centralizer of the Sylow center (p. 219)

This leaf proves that the ambient centralizer of the center of the Sylow
`p`-subgroup is exactly that Sylow subgroup in the minimal counterexample.
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section MinimalCounterexampleStepFive

/-- **Isaacs Theorem 7.1, Step 5.**

In a minimal counterexample, `C_G(Z(P)) = P`.  The inclusion `P ≤ C_G(Z(P))`
is immediate from centrality.  Step 4 makes `P` maximal.  The centralizer cannot
be all of `G`, since its assumed normal `p`-complement would then transport to
one in `G`; maximality therefore forces equality. -/
theorem centralizer_center_eq_sylow_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map
          (P : Subgroup G).subtype : Subgroup G) : Set G) =
      (P : Subgroup G) := by
  classical
  have hP_max : IsCoatom (P : Subgroup G) :=
    sylow_isCoatom_of_minimal_counterexample P hHyp ih hG hQuotient
  set Z : Subgroup G :=
    (Subgroup.center (P : Subgroup G)).map
      (P : Subgroup G).subtype with hZ_def
  set C : Subgroup G := Subgroup.centralizer (Z : Set G) with hC_def
  have hP_le_C : (P : Subgroup G) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZ_def] at hz
    obtain ⟨z₀, hz₀_center, rfl⟩ := hz
    have hcomm :=
      (Subgroup.mem_center_iff.mp hz₀_center) ⟨s, hs⟩
    have hcomm_ambient :=
      congrArg (Subgroup.subtype (P : Subgroup G)) hcomm
    simpa [mul_comm] using hcomm_ambient.symm
  have hC_complement :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥C := by
    simpa only [hC_def, hZ_def] using (hHyp P).1
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    let e : ↥C ≃* G :=
      (MulEquiv.subgroupCongr hC_top).trans Subgroup.topEquiv
    exact hG (hasNormalPComplement_of_mulEquiv e hC_complement)
  have hC_eq_P : C = (P : Subgroup G) :=
    (hP_max.le_iff_eq hC_ne_top).mp hP_le_C
  simpa only [hC_def, hZ_def] using hC_eq_P

end MinimalCounterexampleStepFive

end OddOrder.Isaacs.Ch07
