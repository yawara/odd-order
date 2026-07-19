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

end OddOrder.GroupTheory
