/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.RepresentationTheory.InducedIndicator

/-!
# Counting conjugates into the coset `uP`

Parts (ii) and (iii) of Gorenstein Lemma 7.6 (issue 9508, 段 E), for `u` a `p'`-element and `P` a
`p`-subgroup centralising `u`:

* **(ii)** if `x⁻¹ y x = u v` with `v ∈ P`, then `u` *is* the `p'`-part of `x⁻¹ y x` (the
  decomposition of a commuting `p'`-times-`p` product is unique), so the `p'`-part of `y` is
  conjugate to `u`.  Contrapositive: `σ(y) = 0` off the `p`-class of `u`.
* **(iii)** at `y = u` the only possibility is `v = 1`, because `u` and `u v` would otherwise have
  different orders; so the counted set is exactly `C_G(u)` and `σ(u) = |C_G(u)|`.

Both are statements about `conjugateCount`, so they combine with
`induceFun_indicator_eq_natCast` to give Lemma 7.6 in full.

## Main definitions

* `OddOrder.RepresentationTheory.leftCosetOf` — the coset `u P` as a set

## Main results

* `OddOrder.RepresentationTheory.conjugateCount_eq_zero_of_not_isConj` — **(ii)**
* `OddOrder.RepresentationTheory.conjugateCount_self` — **(iii)**

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G] [Fintype G] {p : ℕ} {u : G} {P : Subgroup G}

/-- **The left coset `u P`**, as a subset of `G`. -/
def leftCosetOf (u : G) (P : Subgroup G) : Set G := {g : G | u⁻¹ * g ∈ P}

omit [Fintype G] in
@[simp]
theorem mem_leftCosetOf {g : G} : g ∈ leftCosetOf u P ↔ u⁻¹ * g ∈ P := Iff.rfl

omit [Fintype G] in
theorem leftCosetOf_subset {H : Subgroup G} (hu : u ∈ H) (hP : P ≤ H) :
    leftCosetOf u P ⊆ (H : Set G) := by
  intro g hg
  have : g = u * (u⁻¹ * g) := by group
  rw [this]
  exact H.mul_mem hu (hP hg)

omit [Fintype G] in
/-- If an element of `u P` is written as `u * v`, then `u` is its `p'`-part. -/
theorem eq_pRegularPart_of_mem_leftCosetOf (hp : p.Prime) (hu : IsPRegular p u)
    (hPp : IsPGroup p ↥P) (hcomm : ∀ v ∈ P, Commute u v) {g : G}
    (hg : g ∈ leftCosetOf u P) : u = pRegularPart p g := by
  have : Fact p.Prime := ⟨hp⟩
  have hv : u⁻¹ * g ∈ P := hg
  have hprod : u * (u⁻¹ * g) = g := by group
  exact (eq_pPart_of_commute hp (hcomm _ hv).symm
    (isPElement_of_mem_of_isPGroup hPp hv) hu hprod).2

open scoped Classical in
/-- **Gorenstein Lemma 7.6(ii)**: the count vanishes off the `p`-class of `u`. -/
theorem conjugateCount_eq_zero_of_not_isConj (hp : p.Prime) (hu : IsPRegular p u)
    (hPp : IsPGroup p ↥P) (hcomm : ∀ v ∈ P, Commute u v) {y : G}
    (hy : ¬ IsConj (pRegularPart p y) u) : conjugateCount (leftCosetOf u P) y = 0 := by
  classical
  rw [conjugateCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  refine hy ?_
  have hkey := eq_pRegularPart_of_mem_leftCosetOf hp hu hPp hcomm hx
  rw [show x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ from by rw [inv_inv], pRegularPart_conj] at hkey
  exact isConj_iff.mpr ⟨x⁻¹, hkey.symm⟩

open scoped Classical in
/-- **Gorenstein Lemma 7.6(iii)**: at `u` itself the count is `|C_G(u)|`. -/
theorem conjugateCount_self (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ v ∈ P, Commute u v) :
    conjugateCount (leftCosetOf u P) u
      = Nat.card ↥(Subgroup.centralizer ({u} : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hset : (Finset.univ.filter fun x : G => x⁻¹ * u * x ∈ leftCosetOf u P)
      = Finset.univ.filter fun x : G => x ∈ Subgroup.centralizer ({u} : Set G) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      -- the `P`-part must be trivial: `u` and `u v` would otherwise have different orders
      have hv : u⁻¹ * (x⁻¹ * u * x) ∈ P := hx
      have hprod : u * (u⁻¹ * (x⁻¹ * u * x)) = x⁻¹ * u * x := by group
      have hcv : Commute u (u⁻¹ * (x⁻¹ * u * x)) := hcomm _ hv
      have hcop : Nat.Coprime (orderOf u) (orderOf (u⁻¹ * (x⁻¹ * u * x))) := by
        obtain ⟨k, hk⟩ := isPElement_of_mem_of_isPGroup hPp hv
        rw [hk]
        exact Nat.Coprime.pow_right k
          (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu))
      have horder : orderOf (x⁻¹ * u * x) = orderOf u := by
        rw [show x⁻¹ * u * x = x⁻¹ * u * (x⁻¹)⁻¹ from by rw [inv_inv], orderOf_conj]
      rw [← hprod, hcv.orderOf_mul_eq_mul_orderOf_of_coprime hcop] at horder
      have hupos : 0 < orderOf u := orderOf_pos u
      have hv1 : orderOf (u⁻¹ * (x⁻¹ * u * x)) = 1 :=
        Nat.eq_of_mul_eq_mul_left hupos (by rw [mul_one]; exact horder)
      have hvone : u⁻¹ * (x⁻¹ * u * x) = 1 := orderOf_eq_one_iff.mp hv1
      rw [hvone, mul_one] at hprod
      refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
      rw [Set.mem_singleton_iff] at hm
      rw [hm]
      have h2 : x * (x⁻¹ * u * x) = x * u := by rw [← hprod]
      rw [show x * (x⁻¹ * u * x) = u * x from by group] at h2
      exact h2
    · intro hx
      have hxu : x⁻¹ * u * x = u := by
        have hc := Subgroup.mem_centralizer_iff.mp hx u (Set.mem_singleton u)
        rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hxu, mem_leftCosetOf, inv_mul_cancel]
      exact P.one_mem
  rw [conjugateCount, hset, Nat.card_eq_fintype_card, Fintype.card_subtype]

end OddOrder.RepresentationTheory
