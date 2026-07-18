/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands

/-!
# Peterfalvi Appendix III: the actual `K`-action on `Q / Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Higman theorem (d), p. 141, as used in Part II,
Ch. I §3, Lemma 5, p. 107.

This file connects the ambient subgroup `K` from Part II, Ch. I to the
quotient action used in Higman's two-summand theorem.  The action on `Q` is
fixed-point-free, `Q₀` is invariant, and `|K| = |Q₀| - 1`.  Coprime
fixed-point lifting therefore makes the induced action on `Q / Q₀`
fixed-point-free.  Consequently, every invariant subgroup of order `|Q₀|`
is transitive on its nonidentity elements and simple as a `K`-group.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- The action of the ambient subgroup `K` on the actual quotient `Q / Q₀`. -/
noncomputable def conjQByKQuotientQ0 :
    ↥hyp.K →* MulAut (↥hyp.Q ⧸ hyp.Q0.subgroupOf hyp.Q) :=
  quotientMulAutHom hyp.Q0_isInvariant

/-- The orders of `K` and `Q₀` are coprime. -/
theorem card_K_coprime_card_Q0 :
    Nat.Coprime (Nat.card ↥hyp.K)
      (Nat.card ↥(hyp.Q0.subgroupOf hyp.Q)) := by
  apply Suzuki2Groups.card_coprime_of_card_eq_sub_one
  rw [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  exact hyp.card_K_eq_card_Q0_sub_one

/-- The induced action of `K` on `Q / Q₀` is fixed-point-free. -/
theorem conjQByKQuotientQ0_fixed_eq_one :
    ∀ k : ↥hyp.K, k ≠ 1 →
      ∀ q : (↥hyp.Q ⧸ hyp.Q0.subgroupOf hyp.Q),
        hyp.conjQByKQuotientQ0 k q = q → q = 1 := by
  apply Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
    hyp.conjQByK (hyp.Q0.subgroupOf hyp.Q) hyp.Q0_isInvariant
    hyp.card_K_coprime_card_Q0
  intro k hk x hx
  rw [hyp.conjQByK_fixed_eq_one hk hx]
  exact Subgroup.one_mem _

/-- An invariant order-`|Q₀|` subgroup of `Q / Q₀` is transitive under `K`
on its nonidentity elements. -/
theorem quotientQ0_restrict_transitive_of_card_eq
    {U : Subgroup (↥hyp.Q ⧸ hyp.Q0.subgroupOf hyp.Q)}
    (hUinv : IsAInvariant hyp.conjQByKQuotientQ0 U)
    (hcard : Nat.card ↥U = Nat.card ↥hyp.Q0) :
    ∀ a b : U, a ≠ 1 → b ≠ 1 →
      ∃ k : ↥hyp.K, hUinv.restrict k a = b := by
  apply Suzuki2Groups.restrict_transitive_of_fixedPointFree_card
    hyp.conjQByKQuotientQ0 hyp.conjQByKQuotientQ0_fixed_eq_one hUinv
  rw [hcard]
  exact hyp.card_K_eq_card_Q0_sub_one

/-- Every subgroup of an invariant order-`|Q₀|` subgroup which is invariant
under the restricted `K`-action is trivial or the whole subgroup. -/
theorem quotientQ0_invariant_eq_bot_or_top_of_card_eq
    {U : Subgroup (↥hyp.Q ⧸ hyp.Q0.subgroupOf hyp.Q)}
    (hUinv : IsAInvariant hyp.conjQByKQuotientQ0 U)
    (hcard : Nat.card ↥U = Nat.card ↥hyp.Q0)
    {V : Subgroup U} (hVinv : IsAInvariant hUinv.restrict V) :
    V = ⊥ ∨ V = ⊤ := by
  apply Suzuki2Groups.invariant_eq_bot_or_top_of_fixedPointFree_card
    hyp.conjQByKQuotientQ0 hyp.conjQByKQuotientQ0_fixed_eq_one hUinv
  · rw [hcard]
    exact hyp.card_K_eq_card_Q0_sub_one
  · exact hVinv

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
