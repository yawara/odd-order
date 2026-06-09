/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Z-groups (every Sylow subgroup cyclic)

`OddOrder.GroupTheory` shared module: a **Z-group** is a finite group all of whose Sylow
subgroups are cyclic. Bender–Glauberman use this in §10 (Lemma 10.4(b)) and §3 (Theorem 3.6).

## Main definitions

* `IsZGroup G`: every Sylow `p`-subgroup of `G` (for every prime `p`) is cyclic.

## Relation to `mathlib`

`mathlib` carries its own `_root_.IsZGroup` *class* whose defining field is character-for-character
the same predicate as `OddOrder.GroupTheory.IsZGroup`.  We keep the repository `def` (used as an
explicit hypothesis on a concrete subgroup in BG §3/§10) but bridge to the `mathlib` class
(`isZGroup_iff_mathlib`) so that the full `mathlib` Z-group API — subgroup/quotient closure
(`IsZGroup.of_injective` / `of_surjective`), `IsZGroup.exponent_eq_card`,
`IsPGroup.isCyclic_of_isZGroup` — becomes available.

## Main results

* `card_eq_prime_of_isZGroup_exponent_dvd`: a nontrivial Z-group of exponent dividing a prime `p`
  has order exactly `p`.  (BG (3.19) / (3.31): in a Z-group there is no elementary abelian
  subgroup of order `p²`.)
* `card_eq_prime_of_le_isZGroup`: the `≤ Z`-subgroup form used directly in BG Theorem 3.6.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §3, §10.
-/

namespace OddOrder.GroupTheory

/-- **Z-group**: a group all of whose Sylow subgroups are cyclic. -/
def IsZGroup (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G)

/-- The repository `IsZGroup` predicate agrees with `mathlib`'s `IsZGroup` class: both say that
every Sylow subgroup is cyclic.  This bridge unlocks the `mathlib` Z-group API (subgroup/quotient
closure, `exponent_eq_card`, `IsPGroup.isCyclic_of_isZGroup`). -/
theorem isZGroup_iff_mathlib {G : Type*} [Group G] :
    IsZGroup G ↔ _root_.IsZGroup G :=
  ⟨fun h => (isZGroup_iff G).mpr h, fun h => (isZGroup_iff G).mp h⟩

/-- A nontrivial Z-group in which every element has order dividing the prime `p` has order exactly
`p`.  (BG Theorem 3.6 (3.19)/(3.31): a Z-group contains no elementary abelian subgroup of order
`p²`.)  Proof: the group is its own Sylow `p`-subgroup, hence cyclic, so its order — equal to its
exponent (`IsZGroup.exponent_eq_card`) — divides `p`; nontriviality rules out order `1`. -/
theorem card_eq_prime_of_isZGroup_exponent_dvd {G : Type*} [Group G] [Finite G] [_root_.IsZGroup G]
    [Nontrivial G] {p : ℕ} (hp : p.Prime) (hexp : ∀ g : G, g ^ p = 1) :
    Nat.card G = p := by
  have hdvd : Nat.card G ∣ p := by
    rw [← IsZGroup.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial G›).ne'
  · exact hp'

/-- **BG Theorem 3.6 form** of `card_eq_prime_of_isZGroup_exponent_dvd`.  If `A ≤ Z` with `Z` a
Z-group, `A` nontrivial, and every element of `A` has order dividing the prime `p`, then `|A| = p`.

Used at BG (3.19) (`A = C_V(R₀) ≤ C_H(R₀)`, `V` elementary abelian `p`-group) and at (3.31)
(`A = C_K(R) ≤ C_H(R)`, `K` of exponent `q`). -/
theorem card_eq_prime_of_le_isZGroup {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : IsZGroup ↥Z) {A : Subgroup G} (hAZ : A ≤ Z) {p : ℕ} (hp : p.Prime)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hA : A ≠ ⊥) :
    Nat.card ↥A = p := by
  haveI : _root_.IsZGroup ↥Z := isZGroup_iff_mathlib.mp hZ
  haveI : _root_.IsZGroup ↥A := IsZGroup.of_injective (Subgroup.inclusion_injective hAZ)
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  have hexp' : ∀ a : ↥A, a ^ p = 1 := fun a =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp (a : G) a.2)
  exact card_eq_prime_of_isZGroup_exponent_dvd hp hexp'

end OddOrder.GroupTheory
