/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_ThompsonPComplement

/-!
# Isaacs FGT Ch.7 — Theorem 7.1 Step 4: the Sylow subgroup is maximal (pp. 218–219)

This leaf continues the minimal-counterexample proof of Thompson's normal
`p`-complement theorem.  Step 2 gives `p`-separability, Step 3 kills
`O_{p'}(G)`, and Hall–Higman then forces every proper overgroup of a Sylow
`p`-subgroup to equal that Sylow subgroup.
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section MinimalCounterexampleStepFour

/-- A finite group whose Sylow `p`-subgroup is the whole group has the trivial
subgroup as a normal `p`-complement. -/
theorem hasNormalPComplement_of_sylow_eq_top
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊤) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine ⟨⊥, inferInstance, fun Q => ?_⟩
  have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
    (Q.is_maximal' P.isPGroup' (by rw [hP]; exact le_top)).symm
  rw [hQP, hP]
  exact Subgroup.isComplement'_bot_top

/-- **Isaacs Theorem 7.1, Step 4.**

In a minimal counterexample, a Sylow `p`-subgroup `P` is maximal in `G`.
For `P ≤ H < G`, the two Thompson local hypotheses descend to `H`, so
minimality supplies a normal `p`-complement `K ◁ H`.  Step 2 makes `G`
`p`-separable and Step 3 gives `O_{p'}(G) = 1`; the Hall–Higman argument then
gives `O_{p'}(H) = 1`.  Since `K` is a normal `p'`-subgroup, `K = 1`, hence
`H` is a `p`-group and Sylow maximality forces `H = P`. -/
theorem sylow_isCoatom_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    IsCoatom (P : Subgroup G) := by
  classical
  have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
    intro hP_top
    exact hG (hasNormalPComplement_of_sylow_eq_top P hP_top)
  letI h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G :=
    isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p G) hQuotient
  have hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ :=
    oPiPrimeCore_eq_bot_of_minimal_counterexample P hHyp ih hG
  rw [isCoatom_iff_ge_of_le]
  refine ⟨hP_ne_top, ?_⟩
  intro H hH_ne_top hPH
  have hOp_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H :=
    (OddOrder.Isaacs.Ch01.opCore_le P).trans hPH
  have hH_oPiPrime :
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ :=
    oPiCorePrime_subgroup_eq_bot_of_opCore_le hOp' hOp_le_H
  have hPsub_p : IsPGroup p ↥((P : Subgroup G).subgroupOf H) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv]
      exact hn)
  have hPsub_index : ¬ p ∣ ((P : Subgroup G).subgroupOf H).index :=
    fun hp => P.not_dvd_index
      (hp.trans (Subgroup.relIndex_dvd_index_of_le hPH))
  let S : Sylow p ↥H := hPsub_p.toSylow hPsub_index
  have hS_coe :
      (S : Subgroup ↥H) = (P : Subgroup G).subgroupOf H :=
    hPsub_p.toSylow_coe hPsub_index
  have hS_map : (S : Subgroup ↥H).map H.subtype = (P : Subgroup G) := by
    rw [hS_coe, Subgroup.map_subgroupOf_eq_of_le hPH]
  have hH_hyp : HasThompsonPComplementHypothesis p ↥H := by
    rw [hasThompsonPComplementHypothesis_iff S]
    apply HasThompsonLocalPComplements.of_subgroup (G := G) H
    rw [hS_map]
    exact hHyp P
  have hH_card : Nat.card ↥H < Nat.card G :=
    Subgroup.card_lt_card_of_ne_top hH_ne_top
  obtain ⟨K, hK_normal, hK_complement⟩ := ih ↥H hH_card hH_hyp
  letI : K.Normal := hK_normal
  have hK_card : Nat.card K = (S : Subgroup ↥H).index :=
    ((hK_complement S).index_eq_card).symm
  have hK_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} K := by
    intro q hq
    rw [hK_card] at hq
    intro hqp
    subst q
    exact S.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)
  have hK_le_core :
      K ≤ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) :=
    hK_pi'.le_oPiCore
  have hK_bot : K = ⊥ := by
    rw [hH_oPiPrime] at hK_le_core
    exact le_bot_iff.mp hK_le_core
  have hS_top : (S : Subgroup ↥H) = ⊤ := by
    have hKS := hK_complement S
    rw [hK_bot] at hKS
    exact Subgroup.isComplement'_bot_left.mp hKS
  have hHP : H ≤ (P : Subgroup G) := by
    rw [← Subgroup.subgroupOf_eq_top, ← hS_coe]
    exact hS_top
  exact hHP

end MinimalCounterexampleStepFour

end OddOrder.Isaacs.Ch07
