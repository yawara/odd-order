/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CosetInvariantCard
import OddOrder.GroupTheory.RepresentationTheory.VirtualCharacterInduction

/-!
# Inducing the indicator of a subset of a subgroup

Gorenstein's equations (7.14)–(7.15) in the proof of Lemma 7.6 (issue 9508, 段 E).  If `S ⊆ H` and

`ψ = c · 1_S : H → K`,

then the induced function counts conjugates landing in `S`:

`(Ind_H^G ψ)(y) = (c / |H|) · #{x ∈ G | x⁻¹ y x ∈ S}`.

Writing the induction sum with `x⁻¹ y x` (rather than `x y x⁻¹`, which is the same sum reindexed
by `x ↦ x⁻¹`) makes the counted set closed under **right** translation by any subgroup that
normalises `S`, which is what `card_subgroup_dvd_card_of_mul_mem` wants; with `c = |H| / |P|` the
value is then the integer `σ(y) / |P|`.

## Main results

* `OddOrder.RepresentationTheory.induceFun_indicator` — the count formula
* `OddOrder.RepresentationTheory.induceFun_indicator_eq_natCast` — its integrality

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {K G : Type*} [Field K] [Group G] [Fintype G] {H : Subgroup G}

open scoped Classical in
/-- **The conjugates of `y` landing in `S`.** -/
noncomputable def conjugateCount (S : Set G) (y : G) : ℕ :=
  (Finset.univ.filter fun x : G => x⁻¹ * y * x ∈ S).card

open scoped Classical in
/-- **Gorenstein (7.14)–(7.15)**: inducing `c · 1_S` from `H` counts conjugates landing in `S`. -/
theorem induceFun_indicator (S : Set G) (hS : S ⊆ (H : Set G)) (c : K) (y : G) :
    induceFun H (fun h : ↥H => if (h : G) ∈ S then c else 0) y
      = (Nat.card ↥H : K)⁻¹ * (c * (conjugateCount S y : K)) := by
  classical
  have hext : ∀ g : G, extendByZero H (fun h : ↥H => if (h : G) ∈ S then c else 0) g
      = if g ∈ S then c else 0 := by
    intro g
    by_cases hg : g ∈ H
    · rw [extendByZero_of_mem _ hg]
    · rw [extendByZero_of_not_mem _ hg, if_neg fun hc => hg (hS hc)]
  have hreindex : (∑ x : G, extendByZero H
        (fun h : ↥H => if (h : G) ∈ S then c else 0) (x * y * x⁻¹))
      = ∑ x : G, extendByZero H (fun h : ↥H => if (h : G) ∈ S then c else 0) (x⁻¹ * y * x) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp
  rw [induceFun, hreindex, Finset.sum_congr rfl fun x _ => hext (x⁻¹ * y * x),
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    conjugateCount]
  ring

open scoped Classical in
/-- **Gorenstein Lemma 7.6(i)**: if `S` is closed under conjugation-compatible right translation by
`P ≤ H` and `|H| = n · |P|`, the induced indicator takes the integer value `σ(y) / |P|`. -/
theorem induceFun_indicator_eq_natCast [CharZero K] {P : Subgroup G} {n : ℕ} (S : Set G)
    (hS : S ⊆ (H : Set G)) (hcard : Nat.card ↥H = n * Nat.card ↥P)
    (hinv : ∀ g ∈ S, ∀ v : G, v ∈ P → v⁻¹ * g * v ∈ S) (y : G) :
    induceFun H (fun h : ↥H => if (h : G) ∈ S then (n : K) else 0) y
      = ((conjugateCount S y / Nat.card ↥P : ℕ) : K) := by
  classical
  have hPpos : 0 < Nat.card ↥P := Nat.card_pos
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  -- the counted set is closed under right translation by `P`
  have hdvd : Nat.card ↥P ∣ conjugateCount S y := by
    refine card_subgroup_dvd_card_of_mul_mem P _ fun x hx v hv => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have : (x * v)⁻¹ * y * (x * v) = v⁻¹ * (x⁻¹ * y * x) * v := by
      rw [mul_inv_rev]; group
    rw [this]
    exact hinv _ hx v hv
  obtain ⟨k, hk⟩ := hdvd
  have hPne : (Nat.card ↥P : K) ≠ 0 := Nat.cast_ne_zero.mpr hPpos.ne'
  have hnne : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  rw [induceFun_indicator S hS _ y, hcard, hk, Nat.mul_div_cancel_left _ hPpos]
  push_cast
  field_simp

end OddOrder.RepresentationTheory
