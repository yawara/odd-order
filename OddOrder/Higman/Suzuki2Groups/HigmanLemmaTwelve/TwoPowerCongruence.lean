/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Data.ZMod.Basic

/-!
# Binary uniqueness modulo `2 ^ n - 1`

G. Higman, *Suzuki 2-groups*, pp. 91--92.  The final case split of Lemma 12
(types `B`, `C`, `D`) turns on a purely arithmetic fact: a sum of *distinct*
powers of two is determined modulo `2 ^ n - 1` by its set of exponents (taken
`mod n`).  Higman phrases this, in the type-`D` case, as

> "The right-hand side is the sum of the powers `2^0, 2^r, 2^s, 2^{r+s}` whose
> exponents are distinct mod `n`, hence the exponents on the left must be equal
> to them, in some order."

This file isolates that number theory, independent of the group-theoretic
setting.  Over `ZMod (2 ^ n - 1)`:

* `two_pow_zmod_card_eq_one` / `two_pow_zmod_eq_pow_mod` reduce a power `2 ^ e`
  to `2 ^ (e % n)` — the mechanism behind "exponents mod `n`", since
  `2 ^ n ≡ 1`.
* `sum_two_pow_zmod_inj_of_ssubset_range` is the uniqueness statement: the map
  `S ↦ ∑ i ∈ S, 2 ^ i` on subsets `S ⊆ range n` is injective away from the
  single wrap-around collision `∅ ↦ 0`, `range n ↦ 2 ^ n - 1 ≡ 0`.

The workhorse mathlib input is `geomSum_injective`, the injectivity of
`S ↦ ∑ i ∈ S, 2 ^ i` on all of `Finset ℕ`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Finset

/-- `(∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n`: the carry-free form of the geometric
sum `∑ i < n, 2 ^ i = 2 ^ n - 1`. -/
theorem sum_range_two_pow_add_one (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

/-- `(2 : ZMod (2 ^ n - 1)) ^ n = 1`: the defining relation of the multiplicative
order of `2` modulo `2 ^ n - 1`. -/
theorem two_pow_zmod_card_eq_one (n : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have hmod : (1 : ℕ) ≡ 2 ^ n [MOD 2 ^ n - 1] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr dvd_rfl
  have hcast : ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) = ((1 : ℕ) : ZMod (2 ^ n - 1)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod.symm
  rwa [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hcast

/-- Reduce a power `2 ^ e` modulo `2 ^ n - 1` to `2 ^ (e % n)`: the source of
Higman's "exponents mod `n`". -/
theorem two_pow_zmod_eq_pow_mod (n e : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ e = (2 : ZMod (2 ^ n - 1)) ^ (e % n) := by
  conv_lhs =>
    rw [← Nat.div_add_mod e n, pow_add, pow_mul, two_pow_zmod_card_eq_one,
      one_pow, one_mul]

/-- A distinct-power sum over a *proper* subset of `range n` is strictly below
`2 ^ n - 1`. -/
theorem sum_two_pow_lt_of_ssubset_range {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hSne : S ≠ Finset.range n) :
    (∑ i ∈ S, 2 ^ i) < 2 ^ n - 1 := by
  have hlt : (∑ i ∈ S, 2 ^ i) < ∑ i ∈ Finset.range n, 2 ^ i := by
    obtain ⟨j, hjr, hjS⟩ := Finset.exists_of_ssubset (hS.ssubset_of_ne hSne)
    exact Finset.sum_lt_sum_of_subset hS hjr hjS (Nat.two_pow_pos _)
      (fun _ _ _ => Nat.zero_le _)
  have := sum_range_two_pow_add_one n
  omega

/-- **Binary uniqueness mod `2 ^ n - 1`** (Higman, *Suzuki 2-groups*, p. 91).
Two distinct-power sums over *proper* subsets of `range n` that agree in
`ZMod (2 ^ n - 1)` have the same set of exponents.  This is the formal content
of "the exponents ... must be equal to them, in some order": the only collision
of `S ↦ ∑ i ∈ S, 2 ^ i` modulo `2 ^ n - 1` is the wrap-around
`∅ ↦ 0`, `range n ↦ 2 ^ n - 1 ≡ 0`, excluded here by properness. -/
theorem sum_two_pow_zmod_inj_of_ssubset_range {n : ℕ}
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hSne : S ≠ Finset.range n) (hTne : T ≠ Finset.range n)
    (h : ((∑ i ∈ S, 2 ^ i : ℕ) : ZMod (2 ^ n - 1)) =
      ((∑ i ∈ T, 2 ^ i : ℕ) : ZMod (2 ^ n - 1))) :
    S = T := by
  have hSlt := sum_two_pow_lt_of_ssubset_range hS hSne
  have hTlt := sum_two_pow_lt_of_ssubset_range hT hTne
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hSlt, Nat.mod_eq_of_lt hTlt] at h
  exact geomSum_injective (le_refl 2) h

/-- `ZMod`-native form of `sum_two_pow_zmod_inj_of_ssubset_range`: the powers of
`2` already live in `ZMod (2 ^ n - 1)` (as produced by taking discrete logarithms
of a primitive-root character value), rather than as a cast of a natural-number
sum. -/
theorem sum_two_pow_zmod_native_inj_of_ssubset_range {n : ℕ}
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hSne : S ≠ Finset.range n) (hTne : T ≠ Finset.range n)
    (h : (∑ i ∈ S, (2 : ZMod (2 ^ n - 1)) ^ i) =
      ∑ j ∈ T, (2 : ZMod (2 ^ n - 1)) ^ j) :
    S = T := by
  refine sum_two_pow_zmod_inj_of_ssubset_range hS hT hSne hTne ?_
  rw [Nat.cast_sum, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact h

end OddOrder.Higman.Suzuki2Groups
