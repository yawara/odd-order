/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeventeenTransfer
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple

/-!
# Peterfalvi Part II, Ch. II: Theorem B

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. II, pp. 108–114.

> **Theorem B.**  In the First Case, the conclusion of Suzuki's Theorem A holds for `G`.

The proof is the dichotomy on hypothesis (B2) (`p ∤ |G^{ab}|`):

* if `p ∣ |G^{ab}|` then `G` is not simple (a simple group is either perfect, and then has
  trivial abelianisation, or abelian, and then has no proper nontrivial subgroup — but the
  First Case provides both `P` of order `p` and an involution), so Ch. I §3 Proposition 2
  (`theoremAConclusion_of_not_simple`) applies;
* if `p ∤ |G^{ab}|` — hypothesis (B2) — then steps (1)–(17) derive a contradiction
  (`false_of_step_seventeen`), so the case is vacuous.
-/

set_option autoImplicit false

open scoped commutatorElement

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- In the First Case, `G` cannot be simple once `p` divides the order of the
abelianisation: a simple group has trivial abelianisation unless it is abelian, and an
abelian simple group has no proper nontrivial subgroup — while `P` (of order `p`, odd)
and the distinguished involution give two such subgroups. -/
theorem not_isSimpleGroup_of_dvd_card_abelianization
    (hB2 : fc.p ∣ Nat.card (Abelianization G)) : ¬ IsSimpleGroup G := by
  intro hsimple
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with hbot | htop
  · -- `G` is abelian, hence `P` is normal and therefore `⊥` or `⊤`
    have hPnormal : fc.P.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        have h1 : ⁅a, b⁆ ∈ commutator G :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      rw [show g * n * g⁻¹ = n * (g * g⁻¹) by rw [← hcomm n g]; group]
      simpa using hn
    rcases hsimple.eq_bot_or_eq_top_of_normal fc.P hPnormal with hPbot | hPtop
    · have := fc.card_P
      rw [hPbot, Subgroup.card_bot] at this
      exact fc.p_prime.one_lt.ne this
    · -- `G = P` has odd order `p`, contradicting the distinguished involution
      have hcard : Nat.card G = fc.p := by
        rw [← fc.card_P, hPtop]
        exact (Subgroup.card_top).symm
      have hord : orderOf fc.toHypothesis.distinguishedInvolution = 2 :=
        orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
          fc.toHypothesis.distinguishedInvolution_ne_one
      have hdvd : 2 ∣ Nat.card G := by
        rw [← hord]
        exact orderOf_dvd_natCard _
      rw [hcard] at hdvd
      exact fc.p_ne_two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two fc.p_prime).mp hdvd).symm
  · -- `G` is perfect, so its abelianisation is trivial
    rw [show Nat.card (Abelianization G) = (commutator G).index from
      (Subgroup.index_eq_card _).symm, htop, Subgroup.index_top] at hB2
    exact fc.p_prime.one_lt.ne' (Nat.dvd_one.mp hB2)

include fc in
/-- **Peterfalvi Part II, Ch. II, Theorem B** (pp. 108–114): in the First Case the
conclusion of Suzuki's Theorem A holds for `G`.

Either `p` divides `|G^{ab}|`, and then `G` is not simple so Ch. I §3 Proposition 2
applies, or hypothesis (B2) holds and steps (1)–(17) are contradictory. -/
theorem theoremB (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nonempty (Hypothesis.TheoremAConclusion G Ω) := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  by_cases hB2 : fc.p ∣ Nat.card (Abelianization G)
  · exact fc.toHypothesis.theoremAConclusion_of_not_simple
      (fc.not_isSimpleGroup_of_dvd_card_abelianization hB2) ind
  · exfalso
    obtain ⟨F, _, ⟨model⟩⟩ :=
      NearFields.rankOne_affine_nearField fc.rankOneQuotient
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨S, hS⟩ : ∃ S : Sylow 3 G,
        fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G) := by
      have hp3 : IsPGroup 3 ↥(fc.sylowThreeNormalizerRSigma model) :=
        IsPGroup.of_card (fc.card_sylowThreeNormalizerRSigma model ind hB2)
      exact hp3.exists_le_sylow
    exact fc.false_of_step_seventeen model ind hB2 S hS

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
