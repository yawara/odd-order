/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Fermat

/-!
# Divisibility among the numbers `aⁿ − 1`

`a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n` for `2 ≤ a` and `m ≠ 0`.  Mathlib has the easy
direction (`Nat.sub_dvd_pow_sub_pow`); the converse is the usual division
argument, `a ^ n - 1 ≡ a ^ (n % m) - 1` modulo `a ^ m - 1` with
`a ^ (n % m) - 1 < a ^ m - 1`.

The consequence recorded here is the counting step of Peterfalvi Part II,
Ch. III §3 (p. 120): a subgroup of a `2`-group of order `q²` (`q = 2ⁿ`) that is
invariant under a fixed-point-free action of order `q − 1` has order `1`, `q` or
`q²`, because its order is a power `2ʲ` with `j ≤ 2n` and `q − 1 ∣ 2ʲ − 1`.

## Main results

* `OddOrder.Nat.pow_sub_one_dvd_pow_sub_one_iff`
* `OddOrder.Nat.eq_zero_or_eq_or_eq_two_mul_of_two_pow_sub_one_dvd`
-/

namespace OddOrder.Nat

/-- **`a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n`** for `2 ≤ a`.

For the forward direction write `n = m * (n / m) + n % m`; then `a ^ m - 1`
divides both `a ^ n - 1` and `a ^ (m * (n / m)) - 1`, hence the remainder term
`a ^ (n % m) - 1`, which is smaller than `a ^ m - 1`. -/
theorem pow_sub_one_dvd_pow_sub_one_iff {a m n : ℕ} (ha : 2 ≤ a) (hm : m ≠ 0) :
    a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n := by
  have ha0 : 0 < a := by omega
  have hdvd_of_dvd : ∀ k l : ℕ, k ∣ l → a ^ k - 1 ∣ a ^ l - 1 := by
    rintro k l ⟨c, rfl⟩
    have h := _root_.Nat.sub_dvd_pow_sub_pow (a ^ k) 1 c
    rwa [one_pow, ← pow_mul] at h
  refine ⟨fun hdvd => ?_, hdvd_of_dvd m n⟩
  set r := n % m with hr
  set s := n / m with hs
  have hn : n = m * s + r := (Nat.div_add_mod n m).symm
  have hrm : r < m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
  -- `a ^ n - 1 = a ^ r * (a ^ (m * s) - 1) + (a ^ r - 1)`
  have hA : 1 ≤ a ^ (m * s) := Nat.one_le_pow _ _ ha0
  have hB : 1 ≤ a ^ r := Nat.one_le_pow _ _ ha0
  have hAB : a ^ r ≤ a ^ (m * s) * a ^ r := Nat.le_mul_of_pos_left _ (by omega)
  have hexp : a ^ r * (a ^ (m * s) - 1) = a ^ (m * s) * a ^ r - a ^ r := by
    rw [Nat.mul_sub, mul_one, mul_comm]
  have hsplit : a ^ n - 1 = a ^ r * (a ^ (m * s) - 1) + (a ^ r - 1) := by
    rw [hn, pow_add, hexp]
    omega
  have hrest : a ^ m - 1 ∣ a ^ r - 1 := by
    have h1 : a ^ m - 1 ∣ a ^ r * (a ^ (m * s) - 1) :=
      Dvd.dvd.mul_left (hdvd_of_dvd m (m * s) ⟨s, rfl⟩) _
    have h2 := hdvd
    rw [hsplit] at h2
    exact (Nat.dvd_add_right h1).mp h2
  -- but `a ^ r - 1 < a ^ m - 1`
  have hlt : a ^ r - 1 < a ^ m - 1 := by
    have : a ^ r < a ^ m := Nat.pow_lt_pow_right (by omega) hrm
    omega
  have hzero : a ^ r - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hrest hlt
  have hr0 : r = 0 := by
    by_contra hne
    have : a ^ 1 ≤ a ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at this
    omega
  exact ⟨s, by omega⟩

/-- The exponents allowed by `2 ^ n - 1 ∣ 2 ^ j - 1` and `j ≤ 2 n`: only
`j = 0`, `j = n` and `j = 2 n`.

This is the counting step of Peterfalvi Part II, Ch. III §3 (p. 120): a
`K`-invariant subgroup of `S/Q₀` (of order `q² = 2 ^ (2n)`) has order divisible
only in those three ways, because `K`, of order `q − 1`, acts freely off the
identity. -/
theorem eq_zero_or_eq_or_eq_two_mul_of_two_pow_sub_one_dvd {n j : ℕ} (hn : n ≠ 0)
    (hj : j ≤ 2 * n) (hdvd : 2 ^ n - 1 ∣ 2 ^ j - 1) :
    j = 0 ∨ j = n ∨ j = 2 * n := by
  obtain ⟨k, rfl⟩ := (pow_sub_one_dvd_pow_sub_one_iff (le_refl 2) hn).mp hdvd
  have hk : k ≤ 2 := Nat.le_of_mul_le_mul_left (by omega) (Nat.pos_of_ne_zero hn)
  interval_cases k
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

end OddOrder.Nat
