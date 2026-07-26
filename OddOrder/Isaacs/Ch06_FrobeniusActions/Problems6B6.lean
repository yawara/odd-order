/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Int.Basic

/-!
# Isaacs Problem 6B.6 — 巡回 2-群の位数 2 の自己同型 (書籍 p. 196)

**主張**: 位数 `≥ 8` の巡回 `2`-群 `C` は位数 `2` の自己同型をちょうど **3 個**持つ。

`MulAut C ≃* (ZMod (2^n))ˣ` (mathlib `IsCyclic.mulAutMulEquiv`) なので, 本質は

> `n ≥ 2` のとき `ZMod (2^n)` で `x² = 1` の解は `±1`, `2^(n-1) ± 1` の**ちょうど 4 個**

という初等整数論。`n ≥ 3` ではこの 4 個が相異なり, 位数ちょうど `2` の元は `4 - 1 = 3` 個。

このファイルはその平方根補題 (mathlib に無い) を与える。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.6: `ZMod (2^n)` の 1 の平方根 (p. 196) -/

/-- `2^n ∣ (m-1)(m+1)` (`n ≥ 2`) なら `2^(n-1)` が `m-1` か `m+1` を割る。

`m` は奇数なので `m = 2k+1` と書け, `(m-1)(m+1) = 4k(k+1)`。`k` と `k+1` は一方が奇数
なので, 素数冪 `2^(n-2)` は他方を丸ごと割る。 -/
theorem two_pow_dvd_sub_or_add {n : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (h : (2 : ℤ) ^ n ∣ (m - 1) * (m + 1)) :
    (2 : ℤ) ^ (n - 1) ∣ m - 1 ∨ (2 : ℤ) ^ (n - 1) ∣ m + 1 := by
  have h2 : (2 : ℤ) ∣ (m - 1) * (m + 1) :=
    dvd_trans (dvd_pow_self 2 (by omega)) h
  -- `m` は奇数
  obtain ⟨c, hc⟩ := h2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 2 * k + 1 := by
    have heven : Even ((m - 1) * (m + 1)) := ⟨c, by omega⟩
    rcases Int.even_mul.mp heven with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, by omega⟩
    · exact ⟨t - 1, by omega⟩
  -- `(m-1)(m+1) = 4 k (k+1)`
  have hfac : (m - 1) * (m + 1) = 4 * (k * (k + 1)) := by rw [hk]; ring
  have hdvd : (2 : ℤ) ^ (n - 2) ∣ k * (k + 1) := by
    have hpow : (2 : ℤ) ^ n = 4 * 2 ^ (n - 2) := by
      have : n = 2 + (n - 2) := by omega
      rw [this, pow_add]; norm_num
    rw [hfac, hpow] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rcases Int.even_or_odd k with ⟨t, ht⟩ | hodd
  · -- `k` 偶数 ⟹ `k+1` 奇数 ⟹ `2^(n-2) ∣ k`
    refine Or.inl ?_
    have hcop : IsCoprime ((2 : ℤ) ^ (n - 2)) (k + 1) :=
      IsCoprime.pow_left ⟨-t, 1, by omega⟩
    have hk2 : (2 : ℤ) ^ (n - 2) ∣ k := hcop.dvd_of_dvd_mul_right hdvd
    obtain ⟨v, hv⟩ := hk2
    exact ⟨v, by rw [hn1, pow_succ, hk]; linarith [hv]⟩
  · -- `k` 奇数 ⟹ `2^(n-2) ∣ k+1`
    refine Or.inr ?_
    obtain ⟨t, ht⟩ := hodd
    have hcop : IsCoprime ((2 : ℤ) ^ (n - 2)) k :=
      IsCoprime.pow_left ⟨-t, 1, by omega⟩
    have hk2 : (2 : ℤ) ^ (n - 2) ∣ k + 1 := hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨v, hv⟩ := hk2
    exact ⟨v, by rw [hn1, pow_succ, hk]; linarith [hv]⟩

variable {n : ℕ}

/-- `ZMod (2^n)` で `2^n = 0`。 -/
theorem two_pow_cast_eq_zero : ((2 : ZMod (2 ^ n)) ^ n) = 0 := by
  have h := ZMod.natCast_self (2 ^ n)
  push_cast at h
  exact h

/-- **6B.6 の核**: `n ≥ 2` のとき `ZMod (2^n)` の `1` の平方根は
`±1` と `2^(n-1) ± 1` の 4 つに限る。 -/
theorem sq_eq_one_iff_two_pow (hn : 2 ≤ n) (x : ZMod (2 ^ n)) :
    x ^ 2 = 1 ↔ x = 1 ∨ x = -1 ∨ x = (2 : ZMod (2 ^ n)) ^ (n - 1) + 1 ∨
      x = (2 : ZMod (2 ^ n)) ^ (n - 1) - 1 := by
  set a : ZMod (2 ^ n) := (2 : ZMod (2 ^ n)) ^ (n - 1) with ha
  have h2a : 2 * a = 0 := by
    rw [ha, ← pow_succ']
    have : n - 1 + 1 = n := by omega
    rw [this]
    exact two_pow_cast_eq_zero
  have ha2 : a * a = 0 := by
    have hsplit : a * a = (2 : ZMod (2 ^ n)) ^ n * (2 : ZMod (2 ^ n)) ^ (n - 2) := by
      rw [ha, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hsplit, two_pow_cast_eq_zero, zero_mul]
  have hxv : ((x.val : ℕ) : ZMod (2 ^ n)) = x := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  constructor
  · intro hx
    have hzero : ((((x.val : ℤ) - 1) * ((x.val : ℤ) + 1) : ℤ) : ZMod (2 ^ n)) = 0 := by
      push_cast
      rw [hxv]
      linear_combination hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    have hdvd : (2 : ℤ) ^ n ∣ ((x.val : ℤ) - 1) * ((x.val : ℤ) + 1) := by simpa using hzero
    have key : ∀ (u : ℤ) (b : ZMod (2 ^ n)),
        (((2 : ℤ) ^ (n - 1) * (u + u) : ℤ) : ZMod (2 ^ n)) = 0 ∧
        (((2 : ℤ) ^ (n - 1) * (2 * u + 1) : ℤ) : ZMod (2 ^ n)) = a := by
      intro u _
      constructor
      · push_cast
        rw [show ((2 : ZMod (2 ^ n)) ^ (n - 1) * ((u : ZMod (2 ^ n)) + u))
            = (2 * a) * (u : ZMod (2 ^ n)) by rw [ha]; ring, h2a, zero_mul]
      · push_cast
        rw [show ((2 : ZMod (2 ^ n)) ^ (n - 1) * (2 * (u : ZMod (2 ^ n)) + 1))
            = (2 * a) * (u : ZMod (2 ^ n)) + a by rw [ha]; ring, h2a, zero_mul, zero_add]
    rcases two_pow_dvd_sub_or_add hn hdvd with ⟨s, hs⟩ | ⟨s, hs⟩
    · rcases Int.even_or_odd s with ⟨u, hu⟩ | ⟨u, hu⟩
      · refine Or.inl ?_
        have hcast := (key u x).1
        rw [← hu, ← hs] at hcast
        push_cast at hcast
        rw [hxv] at hcast
        linear_combination hcast
      · refine Or.inr (Or.inr (Or.inl ?_))
        have hcast := (key u x).2
        rw [← hu, ← hs] at hcast
        push_cast at hcast
        rw [hxv] at hcast
        linear_combination hcast
    · rcases Int.even_or_odd s with ⟨u, hu⟩ | ⟨u, hu⟩
      · refine Or.inr (Or.inl ?_)
        have hcast := (key u x).1
        rw [← hu, ← hs] at hcast
        push_cast at hcast
        rw [hxv] at hcast
        linear_combination hcast
      · refine Or.inr (Or.inr (Or.inr ?_))
        have hcast := (key u x).2
        rw [← hu, ← hs] at hcast
        push_cast at hcast
        rw [hxv] at hcast
        linear_combination hcast
  · rintro (rfl | rfl | rfl | rfl)
    · norm_num
    · norm_num
    · have : (a + 1) ^ 2 = a * a + 2 * a + 1 := by ring
      rw [this, ha2, h2a]
      ring
    · have : (a - 1) ^ 2 = a * a - 2 * a + 1 := by ring
      rw [this, ha2, h2a]
      ring

end

end OddOrder.Isaacs.Ch06
