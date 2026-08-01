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

The same coprimality makes involutions *lift* through a subgroup of odd order: if
`x ^ 2 ∈ N` with `|N|` odd, then `x ^ |N|` squares to `1` and differs from `x` by an
element of `N` (`sq_pow_natCard_eq_one_of_sq_mem`), so in `G ⧸ N` every element of order
dividing `2` is the image of an element of order dividing `2`.

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

/-- **奇位数の部分群を法とすると対合が持ち上がる**: `x ^ 2 ∈ N` かつ `|N|` が奇数なら
`y := x ^ |N|` は `y ^ 2 = 1` を満たし, かつ `x⁻¹ y ∈ N` (すなわち `N` が正規なら
`G ⧸ N` で `y` と `x` は同じ像を持つ).

`|N| = 2k+1` なので `y = x · (x²)^k` — `x` との差は `x²` の冪, つまり `N` の元 — で,
`y² = (x²)^{|N|} = 1` は `x² ∈ N` に Lagrange を当てただけ. -/
theorem sq_pow_natCard_eq_one_of_sq_mem {G : Type*} [Group G] {N : Subgroup G} [Finite ↥N]
    (hodd : Odd (Nat.card ↥N)) {x : G} (hx : x ^ 2 ∈ N) :
    (x ^ Nat.card ↥N) ^ 2 = 1 ∧ x⁻¹ * x ^ Nat.card ↥N ∈ N := by
  obtain ⟨k, hk⟩ := hodd
  have hsqpow : (x ^ 2) ^ Nat.card ↥N = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x ^ 2, hx⟩ : ↥N)))
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact hsqpow
  · have hxm : x ^ Nat.card ↥N = x * (x ^ 2) ^ k := by
      rw [hk, pow_succ', pow_mul]
    rw [hxm, inv_mul_cancel_left]
    exact N.pow_mem hx k

end OddOrder.GroupTheory
