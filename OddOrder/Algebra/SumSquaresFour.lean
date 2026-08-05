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
`±2`.  If one of the `a_i` is known to be `1`, the second shape is impossible, so **every** `a_i`
is `±1` and there are exactly four of them.

This is the arithmetic step of Navarro's proof of (7.2): `∑_{χ ∈ Irr(B_0)} |d^t_{χ 1}|² = 4`
(Cartan matrix of `b_0` plus (5.13.b)), the generalized decomposition numbers at an involution
are rational integers, none of them vanishes, and `d^t_{1_G, 1} = 1`.  Hence
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

/-- **Every term is `±1`.**  A term with `|a_j| ≥ 2` would contribute `4` on its own, and the
term `a_{i₀} = 1` contributes another `1`, overshooting the total. -/
theorem eq_one_or_neg_one_of_sum_sq_eq_four (hsum : ∑ i, a i ^ 2 = 4) (hne : ∀ i, a i ≠ 0)
    {i₀ : S} (h₀ : a i₀ = 1) (j : S) : a j = 1 ∨ a j = -1 := by
  classical
  have hle : a j ^ 2 ≤ 3 := by
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [h₀]; norm_num
    · have hpair := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({i₀, j} : Finset S)) (fun i _ _ => sq_nonneg (a i))
      rw [hsum, Finset.sum_pair (Ne.symm hj), h₀] at hpair
      have h1 : (1 : ℤ) ≤ a j ^ 2 := one_le_sq_of_ne_zero (hne j)
      nlinarith
  have h1 : (1 : ℤ) ≤ a j ^ 2 := one_le_sq_of_ne_zero (hne j)
  have hup : a j ≤ 1 := by nlinarith
  have hlo : -1 ≤ a j := by nlinarith
  have := hne j
  omega

/-- **There are exactly four terms.**  Each is `±1`, so the sum of squares counts them. -/
theorem card_eq_four_of_sum_sq_eq_four (hsum : ∑ i, a i ^ 2 = 4) (hne : ∀ i, a i ≠ 0)
    {i₀ : S} (h₀ : a i₀ = 1) : Fintype.card S = 4 := by
  classical
  have hone : ∀ i : S, a i ^ 2 = 1 := fun i => by
    rcases eq_one_or_neg_one_of_sum_sq_eq_four hsum hne h₀ i with h | h <;> rw [h] <;> norm_num
  have hcount : ∑ i : S, a i ^ 2 = (Fintype.card S : ℤ) := by
    rw [Finset.sum_congr rfl fun i _ => hone i]
    simp
  omega

end OddOrder.Algebra
