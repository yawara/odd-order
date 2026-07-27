/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd-order groups contain no involution

A group — or a subgroup — of odd order has no element of order two: the order of an
element divides both `2` and the group order, which are coprime.

This is used all over the odd-order material (Peterfalvi Part II Ch. I and
Appendix IV, among others), so it lives in its own mathlib-only leaf rather than in
any one book file.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

/-- An element of a group of odd order satisfying `x ^ 2 = 1` is trivial. -/
theorem eq_one_of_sq_eq_one_of_odd_natCard {K : Type*} [Group K] [Finite K]
    (hodd : Odd (Nat.card K)) {x : K} (hx2 : x ^ 2 = 1) : x = 1 := by
  have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hdK : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
  have hg := Nat.dvd_gcd hd2 hdK
  rw [Nat.coprime_two_left.mpr hodd, Nat.dvd_one, orderOf_eq_one_iff] at hg
  exact hg

/-- A subgroup of odd order contains no involution. -/
theorem eq_one_of_sq_eq_one_of_odd_card {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hodd : Odd (Nat.card K)) {x : G} (hx : x ∈ K)
    (hx2 : x ^ 2 = 1) : x = 1 :=
  congrArg Subtype.val
    (eq_one_of_sq_eq_one_of_odd_natCard (K := ↥K) hodd
      (x := ⟨x, hx⟩) (Subtype.ext (by push_cast; exact hx2)))

end OddOrder.GroupTheory
