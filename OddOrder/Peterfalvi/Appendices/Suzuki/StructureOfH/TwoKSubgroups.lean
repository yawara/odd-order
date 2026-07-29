/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.SquareRootFibres
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualCenter
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoSummandSplit

/-!
# The two `K`-subgroups of `S` of order `q²`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 117 (case (3)) and Appendix III, Higman
theorem (d), p. 141.

Case (3) of the Ch. III §1 Proposition works with `K`-subgroups `X`, `Y` of `S`
of order `q²`.  Higman's clause (d) produces them: for a Suzuki `2`-group of
order `q³`, the central quotient `S ⧸ Z(S)` is the direct sum of two invariant
subgroups of order `q` (`center_payload_of_card_eq_cube`), and their preimages
in `S` are `K`-subgroups of order `q²`.

That statement lives in the quotient `↥Q ⧸ Z(↥Q)` with the `IsAInvariant`
vocabulary of Isaacs Ch. 3, while the Proposition's argument is carried out in
`G` with plain subgroups.  This file provides the bridge — `liftCentralQuotient`
and its properties — and packages the resulting pair.

## Main results

* `liftCentralQuotient` — the subgroup of `G` between `Q₀` and `Q` attached to a
  subgroup of `↥Q ⧸ Z(↥Q)`, with its order, its `K`-invariance and injectivity.
* `exists_two_kSubgroups_of_card_cube` — **Higman (d) in `G`-language**: if `Q`
  is a Suzuki `2`-group with `|Q| = |Q₀|³`, there are two distinct `K`-invariant
  subgroups `X ≠ Y` with `Q₀ ≤ X, Y ≤ Q` and `|X| = |Y| = |Q₀|²`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Higman.Suzuki2Groups

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Lifting subgroups of `Q ⧸ Z(Q)` to `G` -/

/-- The subgroup of `G` attached to a subgroup `U` of the central quotient
`↥Q ⧸ Z(↥Q)`: pull back to `↥Q` and push forward to `G`.  It lies between
`Z(Q)` and `Q`. -/
def liftCentralQuotient (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    Subgroup G :=
  (U.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))).map hyp.Q.subtype

variable {hyp}

theorem mem_liftCentralQuotient_iff
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)} {x : G} :
    x ∈ hyp.liftCentralQuotient U ↔
      ∃ hx : x ∈ hyp.Q,
        QuotientGroup.mk' (Subgroup.center ↥hyp.Q) ⟨x, hx⟩ ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem liftCentralQuotient_le_Q
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    hyp.liftCentralQuotient U ≤ hyp.Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- Every lift contains `Q₀`, once the center of `Q` has been identified with
`Q₀`. -/
theorem Q0_le_liftCentralQuotient
    (hZ : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    hyp.Q0 ≤ hyp.liftCentralQuotient U := by
  intro c hc
  refine mem_liftCentralQuotient_iff.mpr ⟨hyp.Q0_le_Q hc, ?_⟩
  have hmem : (⟨c, hyp.Q0_le_Q hc⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q := by
    rw [hZ]
    exact Subgroup.mem_subgroupOf.mpr hc
  have h1 : QuotientGroup.mk' (Subgroup.center ↥hyp.Q)
      (⟨c, hyp.Q0_le_Q hc⟩ : ↥hyp.Q) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmem
  rw [h1]
  exact U.one_mem

/-- The lift multiplies the order by `|Z(Q)|`. -/
theorem card_liftCentralQuotient
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    Nat.card ↥(hyp.liftCentralQuotient U)
      = Nat.card ↥U * Nat.card ↥(Subgroup.center ↥hyp.Q) := by
  classical
  set Z : Subgroup ↥hyp.Q := Subgroup.center ↥hyp.Q with hZdef
  set π := QuotientGroup.mk' Z with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hmapcard : Nat.card ↥(hyp.liftCentralQuotient U)
      = Nat.card ↥(U.comap π) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (U.comap π) hyp.Q.subtype
      (Subgroup.subtype_injective _)).toEquiv).symm
  have hindex : (U.comap π).index = U.index :=
    U.index_comap_of_surjective hπsurj
  have h1 : Nat.card ↥(U.comap π) * U.index = Nat.card ↥hyp.Q := by
    rw [← hindex]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ↥U * U.index = Nat.card (↥hyp.Q ⧸ Z) :=
    Subgroup.card_mul_index _
  have h3 : Nat.card (↥hyp.Q ⧸ Z) * Nat.card ↥Z = Nat.card ↥hyp.Q :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  have hpos : 0 < U.index := Nat.pos_of_ne_zero (by
    intro h
    rw [h, mul_zero] at h2
    exact (Nat.card_pos (α := ↥hyp.Q ⧸ Z)).ne h2)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hmapcard, h1, ← h3, ← h2]
  ring

/-- Distinct subgroups of the central quotient have distinct lifts. -/
theorem liftCentralQuotient_injective :
    Function.Injective hyp.liftCentralQuotient := by
  intro U₁ U₂ h
  have h1 : U₁.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))
      = U₂.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)) :=
    Subgroup.map_injective (Subgroup.subtype_injective hyp.Q) h
  exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _) h1

/-- A `K`-invariant subgroup of the central quotient has `K`-invariant lift,
in the elementwise form the Proposition uses. -/
theorem kInvariant_liftCentralQuotient
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)}
    (hUinv : IsAInvariant
      (IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic hyp.actualKActor.subtype)) U) :
    ∀ k ∈ hyp.K, ∀ y ∈ hyp.liftCentralQuotient U,
      k * y * k⁻¹ ∈ hyp.liftCentralQuotient U := by
  intro k hk y hy
  obtain ⟨hyQ, hyU⟩ := mem_liftCentralQuotient_iff.mp hy
  have hkH : k ∈ hyp.H := hyp.D_le_H (hyp.K_le_D hk)
  have hconjQ : k * y * k⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H k hkH y hyQ
  refine mem_liftCentralQuotient_iff.mpr ⟨hconjQ, ?_⟩
  set a : ↥hyp.actualKActor := ⟨hyp.conjQByK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ with hadef
  have hval : (hyp.actualKActor.subtype a) (⟨y, hyQ⟩ : ↥hyp.Q)
      = (⟨k * y * k⁻¹, hconjQ⟩ : ↥hyp.Q) := rfl
  have := hUinv.smul_mem a hyU
  rwa [IsAInvariant.quotientMulAutHom_apply_mk', hval] at this

variable (hyp)

/-! ## Higman clause (d) in `G`-language -/

/-- **Peterfalvi Appendix III, Higman theorem (d), in the ambient group**
(p. 141), as case (3) of the Ch. III §1 Proposition uses it (p. 117): if `S = Q`
is a Suzuki `2`-group of order `q³` then `S` has two distinct `K`-subgroups of
order `q²`.

`center_payload_of_card_eq_cube` splits `S ⧸ Z(S)` into two complementary
invariant summands of order `q` and identifies `Z(S)` with `Q₀`; the preimages
in `S` are the required subgroups, distinct because the summands are (they are
complementary and both proper). -/
theorem exists_two_kSubgroups_of_card_cube
    (hQsuz : IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3) :
    ∃ X Y : Subgroup G,
      X ≤ hyp.Q ∧ hyp.Q0 ≤ X ∧
        (∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X) ∧
        Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2 ∧
      Y ≤ hyp.Q ∧ hyp.Q0 ≤ Y ∧
        (∀ k ∈ hyp.K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) ∧
        Nat.card ↥Y = Nat.card ↥hyp.Q0 ^ 2 ∧
      X ≠ Y := by
  classical
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg : ActsRegularlyOnInvolutions hyp.actualKActor :=
    hyp.actualKActor_actsRegularlyOnInvolutions
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by rw [hcardQ, hQ0card]
  obtain ⟨-, hZsq, ⟨csplit⟩⟩ :=
    center_payload_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  have hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
    hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hcardlift : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q),
      Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) →
      Nat.card ↥(hyp.liftCentralQuotient U) = Nat.card ↥hyp.Q0 ^ 2 := by
    intro U hU
    rw [card_liftCentralQuotient, hU, hZcard, sq]
  refine ⟨hyp.liftCentralQuotient csplit.left, hyp.liftCentralQuotient csplit.right,
    liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
    kInvariant_liftCentralQuotient csplit.leftInvariant,
    hcardlift _ csplit.leftCard,
    liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
    kInvariant_liftCentralQuotient csplit.rightInvariant,
    hcardlift _ csplit.rightCard, ?_⟩
  intro heq
  have hLR : csplit.left = csplit.right := liftCentralQuotient_injective heq
  have hdisj := csplit.complementary.disjoint
  rw [hLR, disjoint_self] at hdisj
  have hcardR : Nat.card ↥csplit.right = Nat.card ↥(Subgroup.center ↥hyp.Q) :=
    csplit.rightCard
  rw [hdisj, Subgroup.card_bot, hZcard, hQ0card] at hcardR
  rcases Nat.pow_eq_one.mp hcardR.symm with h | h
  · omega
  · exact hm h

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
