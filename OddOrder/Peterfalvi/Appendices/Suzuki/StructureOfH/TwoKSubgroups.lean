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

universe uG uΩ

/-! ## Conjugating a `K`-subgroup by `V` -/

theorem mem_map_conj {G : Type uG} [Group G] {g y : G} {X : Subgroup G} :
    y ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : g⁻¹ * ((MulAut.conj g).toMonoidHom x) * g = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hx']
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_injective {G : Type uG} [Group G] (g : G) :
    Function.Injective fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_injective (MulAut.conj g).injective

namespace Hypothesis

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

/-- **The `K`-subgroups of `S` of order `q²`** — the objects case (3) of the
Ch. III §1 Proposition works with (p. 117). -/
def IsKSubgroupSquare (X : Subgroup G) : Prop :=
  X ≤ hyp.Q ∧ hyp.Q0 ≤ X ∧ (∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X) ∧
    Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2

variable {hyp}

/-- **`V` permutes the `K`-subgroups of `S` of order `q²`.**

`V ≤ D` normalizes `Q` and `Q₀`, and normalizes `K` because `K ⊴ D`
(Ch. I §2 Proposition 2); conjugation preserves cardinality. -/
theorem isKSubgroupSquare_map_conj {g : G} (hg : g ∈ hyp.V) {X : Subgroup G}
    (hX : hyp.IsKSubgroupSquare X) :
    hyp.IsKSubgroupSquare (X.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hXQ, hQ0X, hXinv, hXcard⟩ := hX
  have hgD : g ∈ hyp.D := hyp.V_le_D hg
  have hgiD : g⁻¹ ∈ hyp.D := hyp.D.inv_mem hgD
  have hgH : g ∈ hyp.H := hyp.D_le_H hgD
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y hy
    have := hXQ (mem_map_conj.mp hy)
    have hcj := hyp.Q_normal_in_H g hgH _ this
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group] at hcj
  · intro c hc
    refine mem_map_conj.mpr (hQ0X ?_)
    have := hyp.conj_mem_Q0_of_mem_D hgiD hc
    rwa [show g⁻¹ * c * g⁻¹⁻¹ = g⁻¹ * c * g from by group] at this
  · intro k hk y hy
    refine mem_map_conj.mpr ?_
    have hkK : g⁻¹ * k * g ∈ hyp.K := by
      have hmem : (⟨g⁻¹, hgiD⟩ * ⟨k, hyp.K_le_D hk⟩ * ⟨g⁻¹, hgiD⟩⁻¹ : ↥hyp.D)
          ∈ hyp.K.subgroupOf hyp.D :=
        hyp.K_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr hk) ⟨g⁻¹, hgiD⟩
      have := Subgroup.mem_subgroupOf.mp hmem
      rwa [show ((⟨g⁻¹, hgiD⟩ * ⟨k, hyp.K_le_D hk⟩ * ⟨g⁻¹, hgiD⟩⁻¹ : ↥hyp.D) : G)
          = g⁻¹ * k * g from by push_cast; group] at this
    have hy' := hXinv _ hkK _ (mem_map_conj.mp hy)
    rwa [show (g⁻¹ * k * g) * (g⁻¹ * y * g) * (g⁻¹ * k * g)⁻¹
        = g⁻¹ * (k * y * k⁻¹) * g from by group] at hy'
  · rw [← hXcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective X _
      (MulAut.conj g).injective).toEquiv).symm

/-- **"`P` therefore normalizes `X` and `Y`"** (p. 117, case (3)) when they are
the only two `K`-subgroups of `S` of order `q²`.

`P` has odd order, so it cannot swap a two-element set: if `g` interchanged `X`
and `Y`, then the square root `h` of `g` inside `⟨g⟩` — available because `p` is
odd — would satisfy `X^{h²} = X` either way, contradicting `X^g = Y ≠ X`. -/
theorem map_conj_eq_self_of_unique {g : G} (hg : g ∈ hyp.V) {p : ℕ}
    (hodd : Odd p) (hgp : g ^ p = 1)
    {X Y : Subgroup G} (hX : hyp.IsKSubgroupSquare X) (hne : X ≠ Y)
    (huniq : ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z → Z = X ∨ Z = Y) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  classical
  -- `p` is odd, so `g` is a square inside `⟨g⟩`
  obtain ⟨j, hj⟩ := hodd
  set h : G := g ^ (j + 1) with hhdef
  have hhV : h ∈ hyp.V := hyp.V.pow_mem hg _
  have hsq : h * h = g := by
    rw [hhdef, ← pow_add, show j + 1 + (j + 1) = p + 1 from by omega, pow_succ,
      hgp, one_mul]
  have hcomp : ∀ Z : Subgroup G,
      (Z.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h).toMonoidHom
        = Z.map (MulAut.conj g).toMonoidHom := by
    intro Z
    ext y
    rw [mem_map_conj, mem_map_conj, mem_map_conj]
    rw [show h⁻¹ * (h⁻¹ * y * h) * h = (h * h)⁻¹ * y * (h * h) from by group, hsq]
  by_contra hXg
  have hXgY : X.map (MulAut.conj g).toMonoidHom = Y :=
    (huniq _ (isKSubgroupSquare_map_conj hg hX)).resolve_left hXg
  have hXh := huniq _ (isKSubgroupSquare_map_conj hhV hX)
  rcases hXh with hXhX | hXhY
  · -- `h` fixes `X`, so `g = h²` does too
    have : X.map (MulAut.conj g).toMonoidHom = X := by
      rw [← hcomp, hXhX, hXhX]
    exact hXg this
  · -- `h` sends `X` to `Y`; then `Y^h = X` by injectivity, so `g = h²` fixes `X`
    have hYh : Y.map (MulAut.conj h).toMonoidHom = X := by
      rcases huniq _ (isKSubgroupSquare_map_conj hhV
        (hXhY ▸ isKSubgroupSquare_map_conj hhV hX)) with hh | hh
      · exact hh
      · exact absurd (map_conj_injective h (hXhY.trans hh.symm)) hne
    have : X.map (MulAut.conj g).toMonoidHom = X := by
      rw [← hcomp, hXhY, hYh]
    exact hXg this

/-- **"`P` therefore normalizes `X` and `Y`"** (p. 117, case (3)), elementwise,
for a subgroup `P ≤ V` of prime order: `p` is odd (`prime_ne_two_of_le_V`), so
each of its elements fixes both members of a two-element set of `K`-subgroups. -/
theorem conj_mem_of_unique_of_le_V {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPcard : Nat.card ↥P = p) (hPV : P ≤ hyp.V)
    {X Y : Subgroup G} (hX : hyp.IsKSubgroupSquare X) (hne : X ≠ Y)
    (huniq : ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z → Z = X ∨ Z = Y) :
    ∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X := by
  intro g hg y hy
  have hgp : g ^ p = 1 := by
    have hone := pow_card_eq_one' (G := ↥P) (x := ⟨g, hg⟩)
    rw [hPcard] at hone
    simpa using congrArg (Subtype.val (p := fun z => z ∈ P)) hone
  have hodd : Odd p := hp.odd_of_ne_two (hyp.prime_ne_two_of_le_V hPcard hPV)
  have hfix := map_conj_eq_self_of_unique (hPV hg) hodd hgp hX hne huniq
  have hmem : g * y * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := by
    refine mem_map_conj.mpr ?_
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y from by group]
  rwa [hfix] at hmem

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
      hyp.IsKSubgroupSquare X ∧ hyp.IsKSubgroupSquare Y ∧ X ≠ Y := by
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
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.leftInvariant,
      hcardlift _ csplit.leftCard⟩,
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.rightInvariant,
      hcardlift _ csplit.rightCard⟩, ?_⟩
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
