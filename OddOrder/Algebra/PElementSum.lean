/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SubgroupSum
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.SylowContaining

/-!
# The sum of the `p`-elements, and the sum of the `p`-regular elements

`Ĝ_p = ∑_{x ∈ G_p} x` and `Ĝ⁰ = ∑_{x ∈ G⁰} x` in `R[G]`.  Both index sets are unions of
conjugacy classes, so both elements are central.

**Navarro (4.22), second part**: in characteristic `p`,

`Ĝ_p = ∑_{P ∈ Syl_p(G)} P̂`,

because the coefficient of a `p`-element `x` on the right counts the Sylow subgroups containing
`x`, and that count is `≡ 1 (mod p)` (`card_sylow_mem_modEq_one`); a non-`p`-element lies in no
Sylow `p`-subgroup at all.

This is the expression Külshammer's formula for the principal block idempotent (Navarro (6.14))
runs on.

## Main definitions

* `OddOrder.GroupAlgebra.pElementSum` — `Ĝ_p`
* `OddOrder.GroupAlgebra.pRegularSum` — `Ĝ⁰`

## Main results

* `OddOrder.GroupAlgebra.coeff_pElementSum`, `OddOrder.GroupAlgebra.coeff_pRegularSum`
* `OddOrder.GroupAlgebra.pElementSum_eq_sum_sylow` — Navarro (4.22)
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra OddOrder.GroupTheory

variable (p : ℕ) (R : Type*) [Semiring R] {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- **The sum of the `p`-elements** `Ĝ_p = ∑_{x ∈ G_p} x`. -/
noncomputable def pElementSum : MonoidAlgebra R G :=
  ∑ x ∈ Finset.univ.filter (fun x : G => IsPElement p x), single x (1 : R)

open scoped Classical in
/-- **The sum of the `p`-regular elements** `Ĝ⁰ = ∑_{x ∈ G⁰} x`. -/
noncomputable def pRegularSum : MonoidAlgebra R G :=
  ∑ x ∈ Finset.univ.filter (fun x : G => IsPRegular p x), single x (1 : R)

variable {p R}

open scoped Classical in
theorem coeff_pElementSum (g : G) :
    (pElementSum p R (G := G)).coeff g = if IsPElement p g then 1 else 0 := by
  classical
  have hL : (pElementSum p R (G := G)).coeff g
      = ∑ x ∈ Finset.univ.filter (fun x : G => IsPElement p x), (single x (1 : R)).coeff g := by
    change ((∑ x ∈ Finset.univ.filter (fun x : G => IsPElement p x),
      single x (1 : R)) : MonoidAlgebra R G).coeff g = _
    simp
  rw [hL]
  by_cases hg : IsPElement p g
  · rw [if_pos hg, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hb]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩) h
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro b hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    exact fun h => hg (h ▸ (Finset.mem_filter.mp hb).2)

open scoped Classical in
theorem coeff_pRegularSum (g : G) :
    (pRegularSum p R (G := G)).coeff g = if IsPRegular p g then 1 else 0 := by
  classical
  have hL : (pRegularSum p R (G := G)).coeff g
      = ∑ x ∈ Finset.univ.filter (fun x : G => IsPRegular p x), (single x (1 : R)).coeff g := by
    change ((∑ x ∈ Finset.univ.filter (fun x : G => IsPRegular p x),
      single x (1 : R)) : MonoidAlgebra R G).coeff g = _
    simp
  rw [hL]
  by_cases hg : IsPRegular p g
  · rw [if_pos hg, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hb]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩) h
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro b hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    exact fun h => hg (h ▸ (Finset.mem_filter.mp hb).2)

/-! ### Navarro (4.22): `Ĝ_p` as a sum over the Sylow subgroups -/

open scoped Classical in
/-- **Navarro (4.22).**  In characteristic `p`, `Ĝ_p = ∑_{P ∈ Syl_p(G)} P̂`: the coefficient of a
`p`-element counts the Sylow subgroups containing it, and that count is `≡ 1 (mod p)`. -/
theorem pElementSum_eq_sum_sylow {k : Type*} [Field k] [Fact p.Prime] [CharP k p] :
    pElementSum p k (G := G) = ∑ P : Sylow p G, subgroupSum k (P : Subgroup G) := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  rw [coeff_pElementSum]
  have hsum : (∑ P : Sylow p G, subgroupSum k (P : Subgroup G)).coeff g
      = ((Finset.univ.filter (fun P : Sylow p G => g ∈ (P : Subgroup G))).card : k) := by
    have hpush : (∑ P : Sylow p G, subgroupSum k (P : Subgroup G)).coeff g
        = ∑ P : Sylow p G, (subgroupSum k (P : Subgroup G)).coeff g := by simp
    rw [hpush]
    rw [show (∑ P : Sylow p G, (subgroupSum k (P : Subgroup G)).coeff g)
        = ∑ P : Sylow p G, (if g ∈ (P : Subgroup G) then (1 : k) else 0) from
      Finset.sum_congr rfl fun P _ => coeff_subgroupSum (P : Subgroup G) g, Finset.sum_boole]
  rw [hsum]
  by_cases hg : IsPElement p g
  · rw [if_pos hg]
    have hcard : (Finset.univ.filter (fun P : Sylow p G => g ∈ (P : Subgroup G))).card
        = Nat.card {P : Sylow p G // g ∈ (P : Subgroup G)} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard, ← Nat.cast_one (R := k)]
    exact ((CharP.natCast_eq_natCast k p).mpr
      (card_sylow_mem_modEq_one (isPGroup_zpowers_of_isPElement hg)).symm)
  · rw [if_neg hg, Finset.filter_eq_empty_iff.mpr, Finset.card_empty, Nat.cast_zero]
    exact fun P _ hmem => hg (isPElement_of_mem_of_isPGroup P.isPGroup' hmem)

end OddOrder.GroupAlgebra
