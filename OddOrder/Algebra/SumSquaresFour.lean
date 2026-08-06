/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonzero integers whose squares sum to `4`, one of them being `1`

`∑_i a_i² = 4` with every `a_i ≠ 0` leaves only two shapes: four terms `±1`, or a single term
`±2`.  As soon as there are **two** indices the second shape is impossible, so every `a_i` is
`±1` and there are exactly four of them.

This is the arithmetic step of Navarro's proof of (7.2): `∑_{χ ∈ Irr(B_0)} |d^t_{χ 1}|² = 4`
(Cartan matrix of `b_0` plus (5.13.b)), the generalized decomposition numbers at an involution
are rational integers, and none of them vanishes.  Weak block orthogonality
`∑_{χ ∈ Irr(B_0)} χ(1) χ(t) = 0` rules out `|Irr(B_0)| = 1`, so
`Irr(B_0) = {1_G, χ_1, χ_2, χ_3}` and `χ_i(t) = ±1`.

## Main results

* `OddOrder.Algebra.eq_one_or_neg_one_of_sum_sq_eq_four`
* `OddOrder.Algebra.card_eq_four_of_sum_sq_eq_four`
-/

namespace OddOrder.Algebra

variable {S : Type*} [Fintype S] {a : S → ℤ}

/-- The square of a nonzero integer is at least `1`. -/
theorem one_le_sq_of_ne_zero {n : ℤ} (hn : n ≠ 0) : 1 ≤ n ^ 2 := by
  calc (1 : ℤ) = 1 ^ 2 := by norm_num
    _ ≤ |n| ^ 2 := by gcongr; exact Int.one_le_abs hn
    _ = n ^ 2 := sq_abs n

/-- **Every term is `±1`.**  A term with `|a_j| ≥ 2` contributes `4` on its own, and any second
term contributes at least another `1`, overshooting the total. -/
theorem eq_one_or_neg_one_of_sum_sq_eq_four [Nontrivial S] (hsum : ∑ i, a i ^ 2 = 4)
    (hne : ∀ i, a i ≠ 0) (j : S) : a j = 1 ∨ a j = -1 := by
  classical
  obtain ⟨i₀, hj⟩ := exists_ne j
  have h1 : (1 : ℤ) ≤ a j ^ 2 := one_le_sq_of_ne_zero (hne j)
  have h0 : (1 : ℤ) ≤ a i₀ ^ 2 := one_le_sq_of_ne_zero (hne i₀)
  have hle : a j ^ 2 ≤ 3 := by
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i₀, j} : Finset S)) (fun i _ _ => sq_nonneg (a i))
    rw [hsum, Finset.sum_pair hj] at hpair
    linarith
  have hup : a j ≤ 1 := by nlinarith
  have hlo : -1 ≤ a j := by nlinarith
  have := hne j
  omega

/-- **There are exactly four terms.**  Each is `±1`, so the sum of squares counts them. -/
theorem card_eq_four_of_sum_sq_eq_four [Nontrivial S] (hsum : ∑ i, a i ^ 2 = 4)
    (hne : ∀ i, a i ≠ 0) : Fintype.card S = 4 := by
  classical
  have hone : ∀ i : S, a i ^ 2 = 1 := fun i => by
    rcases eq_one_or_neg_one_of_sum_sq_eq_four hsum hne i with h | h <;> rw [h] <;> norm_num
  have hcount : ∑ i : S, a i ^ 2 = (Fintype.card S : ℤ) := by
    rw [Finset.sum_congr rfl fun i _ => hone i]
    simp
  omega

/-! ### Zeros allowed

Navarro's "analysis at `y`" (p. 140) reaches the same total `4` for a column that is *not* known
to be nowhere zero — the elements of order `4` are not all `G`-conjugate to every `p`-element, so
the argument that no entry vanishes is unavailable.  What replaces it is one entry known to be
`±1` (the trivial character, whose value is `1`), and that already forbids a `±2`: it would need
`4 + 1 > 4`.  So the column consists of zeros and exactly four `±1`. -/

/-- **Every term is `0` or `±1`**, once one term is known to be `±1`. -/
theorem eq_zero_or_one_or_neg_one_of_sum_sq_eq_four (hsum : ∑ i, a i ^ 2 = 4) {i₀ : S}
    (hi₀ : a i₀ ^ 2 = 1) (j : S) : a j = 0 ∨ a j = 1 ∨ a j = -1 := by
  classical
  have hle : a j ^ 2 ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have hne : i₀ ≠ j := by rintro rfl; omega
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i₀, j} : Finset S)) (fun i _ _ => sq_nonneg (a i))
    rw [hsum, Finset.sum_pair hne] at hpair
    omega
  have hup : a j ≤ 1 := by nlinarith
  have hlo : -1 ≤ a j := by nlinarith
  omega

/-- **Exactly four terms are nonzero**, once one term is known to be `±1`: each nonzero term
contributes `1` to the total `4`. -/
theorem card_filter_ne_zero_eq_four_of_sum_sq_eq_four (hsum : ∑ i, a i ^ 2 = 4) {i₀ : S}
    (hi₀ : a i₀ ^ 2 = 1) : (Finset.univ.filter fun i => a i ≠ 0).card = 4 := by
  classical
  have hcount : ∑ i : S, a i ^ 2
      = ((Finset.univ.filter fun i => a i ≠ 0).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => a i ≠ 0)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i ^ 2
        = ∑ _i ∈ Finset.univ.filter (fun i => a i ≠ 0), (1 : ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := (Finset.mem_filter.mp hi).2
      rcases eq_zero_or_one_or_neg_one_of_sum_sq_eq_four hsum hi₀ i with h | h | h
      · exact absurd h hi'
      · rw [h]; norm_num
      · rw [h]; norm_num
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ a i ≠ 0), a i ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' := (Finset.mem_filter.mp hi).2
      push Not at hi'
      rw [hi']; norm_num
    rw [h1, h2, Finset.sum_const, add_zero, nsmul_eq_mul, mul_one]
  omega

end OddOrder.Algebra
