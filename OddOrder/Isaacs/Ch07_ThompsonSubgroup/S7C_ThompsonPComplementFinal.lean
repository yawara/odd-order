/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_AbelianQuotientComplement

/-!
# Isaacs FGT Ch.7 — Theorem 7.1 Step 7 and final assembly (pp. 218–219)

This leaf closes Thompson's normal `p`-complement theorem.  Strong induction on
the group order supplies the minimum-counterexample hypothesis used in Steps
1–6.  Step 2 constructs a normal `p`-complement in `G/O_p(G)`; Steps 3, 5, and
6 then provide exactly the reduced hypotheses of the already proved normal-J
closing theorem.
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section ThompsonNormalPComplement

/-- **Isaacs Theorem 7.1** (Thompson normal `p`-complement theorem).

Let `p ≠ 2` and let `P` be a Sylow `p`-subgroup of a finite group `G`.  If
`C_G(Z(P))` and `N_G(J(P))` both have normal `p`-complements, then so does `G`.

The proof converts the hypotheses at `P` to the conjugacy-invariant all-Sylow
form and argues by strong induction on `|G|`.  In a counterexample, Steps 1–2
identify the maximal bad subgroup with `O_p(G)` and construct a normal
`p`-complement in the quotient.  Steps 3, 5, and 6 give `O_{p'}(G) = 1`,
`C_G(Z(P)) = P`, and abelian `2`-subgroups.  Theorem 7.6 then makes `J(P)`
normal, so the assumed complement in its normalizer is a complement in `G`. -/
theorem thompson_normal_p_complement_of_local_hypotheses.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (hCZ : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map
          (P : Subgroup G).subtype : Subgroup G) : Set G)))
    (hNJ : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
        ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  have hHyp : HasThompsonPComplementHypothesis p G := by
    rw [hasThompsonPComplementHypothesis_iff P]
    exact ⟨hCZ, hNJ⟩
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H = n →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H
  suffices hmain : motive (Nat.card G) by
    exact hmain G rfl hHyp
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hH_card hH_hyp
  by_contra hH
  have ih' :
      ∀ (K : Type u) [Group K] [Finite K],
        Nat.card K < Nat.card H →
        HasThompsonPComplementHypothesis p K →
        OddOrder.Isaacs.Ch05.HasNormalPComplement p K := by
    intro K _ _ hK_card hK_hyp
    exact ih (Nat.card K) (by simpa only [hH_card] using hK_card)
      K rfl hK_hyp
  obtain ⟨U, hU_bad, hU_weight_max, hU_card_max⟩ :=
    exists_lexicographically_maximal_badNormalizerPSubgroup hH
  have hU_eq : U = OddOrder.Isaacs.Ch01.opCore p H :=
    maximal_badNormalizer_eq_opCore hH_hyp ih' hU_bad
      hU_weight_max hU_card_max
  subst U
  have hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (H ⧸ OddOrder.Isaacs.Ch01.opCore p H) :=
    maximal_badNormalizer_quotient_hasNormalPComplement ih' hU_bad
      hU_weight_max hU_card_max
  let Q : Sylow p H := default
  have h_pSolvable :
      OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
    isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p H) hQuotient
  have h_oPiPrime_trivial :
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ :=
    oPiPrimeCore_eq_bot_of_minimal_counterexample Q hH_hyp ih' hH
  have h_centralizer_center :
      Subgroup.centralizer
          (((Subgroup.center (Q : Subgroup H)).map
            (Q : Subgroup H).subtype : Subgroup H) : Set H) =
        (Q : Subgroup H) :=
    centralizer_center_eq_sylow_of_minimal_counterexample
      Q hH_hyp ih' hH hQuotient
  have h2abelian :
      ∀ S : Subgroup H, IsPGroup 2 S →
        ∀ x y : ↥S, x * y = y * x :=
    twoSubgroups_commutative_of_minimal_counterexample
      Q hp2 hH_hyp ih' hH hQuotient
  exact hH
    (thompson_normal_p_complement Q hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center (hH_hyp Q).2)

end ThompsonNormalPComplement

end OddOrder.Isaacs.Ch07
