/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Subgroups of a finite cyclic group are determined by their order

In a finite cyclic group `C`, the subgroup of any given order is unique: two subgroups with the
same cardinality are equal.  The proof identifies an order-`d` subgroup with the kernel of the
`d`-th power map, which is manifestly canonical.

This is a general theorem of finite group theory, with no dependence on any of the three books.
It previously existed as **three verbatim-identical copies** under
`OddOrder/BG/Ch3_MaximalSubgroups/` (one public in `S10_LocalLemmasCore`, two `private` in
`S10_BetaRadicalGlobal` and `S12_Proposition1215`); the docstring of the public copy already
recorded that it ought to be hoisted into a shared helper.

It is consumed by BG §10-§16, by Peterfalvi §10/§16, and by
`OddOrder.GroupTheory.CNGroupStructure` (Gorenstein Theorem 12.1.5).  That last consumer
cannot import `BG`, which is what forced the deduplication (hub ruling, issue 9161).

## Main results

* `OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq` -- equal cardinality implies equality.
-/

namespace OddOrder.GroupTheory

/-- In a finite cyclic group, two subgroups of the same order coincide.

Both subgroups are shown to equal `(powMonoidHom d).ker` for `d` their common order: the
inclusion `≤` holds because every element of an order-`d` subgroup satisfies `g ^ d = 1`, and
the reverse follows by counting, since the kernel has order `gcd d (Nat.card C) = d`. -/
theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} (h : Nat.card H₁ = Nat.card H₂) : H₁ = H₂ := by
  letI : CommGroup C := IsCyclic.commGroup
  have key : ∀ {N : Subgroup C} {d : ℕ},
      Nat.card N = d → N = (powMonoidHom d : C →* C).ker := by
    intro N d hN
    have hN_le : N ≤ (powMonoidHom d : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hN] at this
    have hd_dvd : d ∣ Nat.card C := hN ▸ N.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom d : C →* C).ker = d := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd_dvd]
    exact Subgroup.eq_of_le_of_card_ge hN_le (by rw [hker_card, hN])
  exact (key (d := Nat.card H₁) rfl).trans (key (d := Nat.card H₁) h.symm).symm

/-- In a finite cyclic group, the element of order 2 is unique (if it exists):
`φ(2) = 1` via `IsCyclic.card_orderOf_eq_totient`.

Deduplicated from two verbatim `private` copies (Isaacs Ch05 `Basic` and
Higman `AgemoLayers`; issue 0127 ①). -/
theorem cyclic_eq_of_orderOf_eq_two {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {s t : C} (hs : orderOf s = 2) (ht : orderOf t = 2) : s = t := by
  letI : Fintype C := Fintype.ofFinite C
  classical
  have h2_dvd : (2 : ℕ) ∣ Fintype.card C := by
    rw [← hs]; exact orderOf_dvd_card
  have h_card : Fintype.card {x : C // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient h2_dvd, Nat.totient_two]
  haveI : Subsingleton {x : C // orderOf x = 2} :=
    Fintype.card_le_one_iff_subsingleton.mp h_card.le
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨s, hs⟩ : {x : C // orderOf x = 2}) ⟨t, ht⟩)

/-- In a finite cyclic group, a subgroup of any order dividing `|C|` exists.

Companion to `cyclic_subgroup_eq_of_card_eq`: together they say that a finite cyclic group has
exactly one subgroup of each order dividing `|C|`.  The witness is `(powMonoidHom d).ker`, whose
order is `gcd (Nat.card C) d = d`. -/
theorem exists_subgroup_card_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {d : ℕ} (hd : d ∣ Nat.card C) : ∃ H : Subgroup C, Nat.card H = d := by
  letI : CommGroup C := IsCyclic.commGroup
  refine ⟨(powMonoidHom d : C →* C).ker, ?_⟩
  rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd]

/-- In a finite cyclic group, one subgroup is contained in another as soon as its order
divides: the target has a subgroup of that order, and subgroups of equal order coincide. -/
theorem le_of_card_dvd_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H K : Subgroup C} (hdvd : Nat.card ↥H ∣ Nat.card ↥K) : H ≤ K := by
  obtain ⟨A, hA⟩ := exists_subgroup_card_eq_of_isCyclic (C := ↥K) hdvd
  have hAle : A.map K.subtype ≤ K := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hAcard : Nat.card ↥(A.map K.subtype) = Nat.card ↥H :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A K.subtype
      Subtype.val_injective).toEquiv).symm.trans hA
  rw [← cyclic_subgroup_eq_of_card_eq hAcard]
  exact hAle

/-- In a finite cyclic group, two subgroups meeting trivially have **coprime orders**.

The gcd `d` of the two orders divides `|C|`, so `C` has a subgroup `A` of order `d`
(`exists_subgroup_card_eq_of_isCyclic`); since `d` divides both orders, `A` sits inside both
(`le_of_card_dvd_of_isCyclic`), hence inside their trivial intersection, forcing `d = 1`.

This is the converse direction of the familiar "cyclic ⟹ order determines the subgroup"
package, and is what turns a *direct* decomposition `W = W₁ × W₂` of a cyclic group into the
arithmetic statement `gcd(|W₁|, |W₂|) = 1`. -/
theorem coprime_card_of_inf_eq_bot_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H K : Subgroup C} (h : H ⊓ K = ⊥) : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K) := by
  obtain ⟨A, hA⟩ := exists_subgroup_card_eq_of_isCyclic (C := C)
    ((Nat.gcd_dvd_left (Nat.card ↥H) (Nat.card ↥K)).trans H.card_subgroup_dvd_card)
  have hAH : A ≤ H := le_of_card_dvd_of_isCyclic (by rw [hA]; exact Nat.gcd_dvd_left _ _)
  have hAK : A ≤ K := le_of_card_dvd_of_isCyclic (by rw [hA]; exact Nat.gcd_dvd_right _ _)
  have hAbot : A = ⊥ := le_bot_iff.mp (h ▸ le_inf hAH hAK)
  rw [Nat.Coprime, ← hA, hAbot, Subgroup.card_bot]

/-- Ambient form of `coprime_card_of_inf_eq_bot_of_isCyclic`: two subgroups `H, K` of a group `G`
that both sit inside a common **cyclic** subgroup `W` and meet trivially have coprime orders.

Used for the direct factorisation `W = W₁ × W₂` of Peterfalvi (8.4.e)/(8.8.b), where `W₁` and `W₂`
are named as subgroups of the ambient group rather than of `W`. -/
theorem coprime_card_of_inf_eq_bot_of_le_cyclic {G : Type*} [Group G] {W H K : Subgroup G}
    [Finite ↥W] [IsCyclic ↥W] (hH : H ≤ W) (hK : K ≤ W) (h : H ⊓ K = ⊥) :
    Nat.Coprime (Nat.card ↥H) (Nat.card ↥K) := by
  have hbot : H.subgroupOf W ⊓ K.subgroupOf W = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, h,
      ← Subgroup.subgroupOf, Subgroup.bot_subgroupOf]
  have := coprime_card_of_inf_eq_bot_of_isCyclic (C := ↥W) hbot
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at this

/-- Every subgroup of a finite cyclic group is characteristic (it is the unique subgroup of
its order, by `cyclic_subgroup_eq_of_card_eq`). -/
theorem characteristic_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (M : Subgroup C) : M.Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun ϕ =>
    cyclic_subgroup_eq_of_card_eq
      (Nat.card_congr (Subgroup.equivMapOfInjective M ϕ.toMonoidHom ϕ.injective).toEquiv.symm)

end OddOrder.GroupTheory
