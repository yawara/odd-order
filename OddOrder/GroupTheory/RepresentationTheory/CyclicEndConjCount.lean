/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction

/-!
# Counting lemmas for BG Prop 2.4(j)(k)

`OddOrder.GroupTheory.RepresentationTheory` shared module: elementary
finite-combinatorics building blocks for **Bender–Glauberman Prop 2.4(j)(k)**
(the eigenspace-dimension number theory behind `h ∣ qⁿ ± 1` in Thm 2.5).

The first block is field/group-free: an integer family summing to `0` whose
squares sum to `2` has exactly one `+1` and one `-1` (and is `0` elsewhere).
This is the `m = 1` shape of Prop 2.4(j) once the sum-of-squares identity (h)
turns the multiplicity hypothesis into `∑ (nᵢ − nᵢ₊₁)² = 2`.
-/

namespace OddOrder.RepresentationTheory

open Finset

/-- **Integers summing to `0` with squares summing to `2`**: the support has
exactly two points, carrying `+1` and `-1`. -/
theorem exists_pos_neg_of_sum_sq_eq_two {α : Type*} [Fintype α]
    (d : α → ℤ) (hsum : ∑ i, d i = 0) (hsq : ∑ i, d i ^ 2 = 2) :
    ∃ i j : α, i ≠ j ∧ d i = 1 ∧ d j = -1 ∧ ∀ k, d k ≠ 0 → k = i ∨ k = j := by
  classical
  set S : Finset α := univ.filter (fun i => d i ≠ 0) with hS
  have hmemS : ∀ k, k ∈ S ↔ d k ≠ 0 := by
    intro k; simp [hS]
  -- the squares supported on `S` still sum to `2`
  have hsupp : ∑ i ∈ S, d i ^ 2 = 2 := by
    rw [hS, sum_filter, ← hsq]
    exact sum_congr rfl fun i _ => by by_cases h : d i = 0 <;> simp [h]
  -- the values supported on `S` still sum to `0`
  have hsum' : ∑ i ∈ S, d i = 0 := by
    have heq : ∑ i ∈ S, d i = ∑ i, d i := by
      rw [hS, sum_filter]
      exact sum_congr rfl fun i _ => by by_cases h : d i = 0 <;> simp [h]
    rw [heq, hsum]
  -- on the support each square is `≥ 1`
  have hge : ∀ i ∈ S, (1 : ℤ) ≤ d i ^ 2 := by
    intro i hi
    have hne : d i ≠ 0 := (hmemS i).mp hi
    have h0 : d i ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have h1 : (0 : ℤ) ≤ d i ^ 2 := sq_nonneg _
    omega
  -- the support has exactly two elements
  have hcard : S.card = 2 := by
    have hle : (S.card : ℤ) ≤ 2 := by
      calc (S.card : ℤ) = ∑ _i ∈ S, (1 : ℤ) := by simp
        _ ≤ ∑ i ∈ S, d i ^ 2 := sum_le_sum hge
        _ = 2 := hsupp
    have hcard2 : S.card ≤ 2 := by exact_mod_cast hle
    have hne0 : S.card ≠ 0 := by
      intro h; rw [card_eq_zero] at h; rw [h, sum_empty] at hsupp; norm_num at hsupp
    have hne1 : S.card ≠ 1 := by
      intro h
      obtain ⟨a, ha⟩ := card_eq_one.mp h
      rw [ha, sum_singleton] at hsupp
      have hb1 : d a ≤ 2 := by nlinarith [sq_nonneg (d a - 2)]
      have hb2 : -2 ≤ d a := by nlinarith [sq_nonneg (d a + 2)]
      interval_cases (d a) <;> simp_all
    omega
  -- extract the two support points and pin their values
  obtain ⟨i, j, hij, hSeq⟩ := card_eq_two.mp hcard
  have hinotj : i ∉ ({j} : Finset α) := by simp [hij]
  have hsupp' : d i ^ 2 + d j ^ 2 = 2 := by
    rw [hSeq, sum_insert hinotj, sum_singleton] at hsupp; exact hsupp
  have hsum'' : d i + d j = 0 := by
    rw [hSeq, sum_insert hinotj, sum_singleton] at hsum'; exact hsum'
  have hii : i ∈ S := hSeq ▸ mem_insert_self i {j}
  have hjj : j ∈ S := hSeq ▸ mem_insert_of_mem (mem_singleton_self j)
  have hi2 : d i ^ 2 = 1 := by have := hge i hii; have := hge j hjj; omega
  have hj2 : d j ^ 2 = 1 := by have := hge i hii; have := hge j hjj; omega
  have hisupp : ∀ k, d k ≠ 0 → k = i ∨ k = j := by
    intro k hk
    have : k ∈ S := (hmemS k).mpr hk
    rw [hSeq, mem_insert, mem_singleton] at this; exact this
  have hival : d i = 1 ∨ d i = -1 := by rw [← mul_self_eq_one_iff, ← sq]; exact hi2
  rcases hival with h | h
  · exact ⟨i, j, hij, h, by omega, hisupp⟩
  · exact ⟨j, i, hij.symm, by omega, h, fun k hk => (hisupp k hk).symm⟩

/-- **For each nonzero shift, exactly two indices move** (BG Prop 2.4(j), `m`-step shape). If the
"squared shift difference" sum is `2`, then `n i ≠ n (i + m)` for exactly two `i`. -/
theorem card_filter_ne_shift_eq_two {h : ℕ} [NeZero h] (n : ZMod h → ℤ) {m : ZMod h}
    (hsq : ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    (univ.filter (fun i => n i ≠ n (i + m))).card = 2 := by
  classical
  have hshift : ∑ x, n (x + m) = ∑ x, n x :=
    Fintype.sum_equiv (Equiv.addRight m) (fun x => n (x + m)) n (fun _ => rfl)
  have hsum : ∑ i, (n i - n (i + m)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  obtain ⟨a, b, hab, ha, hb, hsupp⟩ :=
    exists_pos_neg_of_sum_sq_eq_two (fun i => n i - n (i + m)) hsum hsq
  have hfilter : (univ.filter (fun i => n i ≠ n (i + m))) = {a, b} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [← sub_ne_zero]
    constructor
    · exact hsupp i
    · rintro (rfl | rfl)
      · rw [ha]; norm_num
      · rw [hb]; norm_num
  rw [hfilter, Finset.card_pair hab]

end OddOrder.RepresentationTheory
