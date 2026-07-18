/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer

/-!
# Peterfalvi Part II, Ch. I §3: Proposition 1(c), centralizer residual

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105–106.

This file contains the target-independent structural clauses of Proposition
1(c).  It starts with the source inference that, once `C_Q(X)` is known to
be a `2`-group, the odd-order direct factor `Q₁` has trivial centralizer
of `X`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

section /- §3 Proposition 1(c) (pp. 105–106) -/

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, first inference.
If `C_Q(X)` is a `2`-group, then `C_{Q₁}(X)=1`.  Here `Q₁` is the
actual normal `2`-complement constructed from the nilpotence of `Q`;
its odd order is coprime to the order of every subgroup of `C_Q(X)`. -/
theorem Q1_inf_centralizer_eq_bot_of_isPGroup (X : Subgroup G)
    (hCQ : IsPGroup 2
      ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G))) :
    hyp.Q1 ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  let C : Subgroup G := hyp.Q ⊓ Subgroup.centralizer (X : Set G)
  let A : Subgroup G := hyp.Q1 ⊓ Subgroup.centralizer (X : Set G)
  have hAC : A ≤ C := inf_le_inf hyp.Q1_le_Q le_rfl
  have hAp : IsPGroup 2 ↥A := by
    have hsub : IsPGroup 2 ↥(A.subgroupOf C) :=
      hCQ.to_subgroup (A.subgroupOf C)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hAC)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
  have hAdvd : Nat.card A ∣ Nat.card hyp.Q1 :=
    Subgroup.card_dvd_of_le inf_le_left
  have hQ1odd : ¬ 2 ∣ Nat.card hyp.Q1 := by
    rw [hyp.card_Q1]
    exact hyp.two_not_dvd_card_Q1Subgroup
  have hnzero : n = 0 := by
    by_contra hn0
    apply hQ1odd
    apply (show 2 ∣ Nat.card A by
      rw [hn]
      exact dvd_pow_self 2 hn0).trans hAdvd
  apply Subgroup.card_eq_one.mp
  rw [hn, hnzero, pow_zero]

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
