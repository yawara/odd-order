/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Int.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

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

/-- `0 < k < N` なら `(k : ZMod N) ≠ 0`。 -/
theorem natCast_ne_zero_of_lt {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    ((k : ℕ) : ZMod N) ≠ 0 := by
  haveI : NeZero N := ⟨by omega⟩
  intro h
  have hval : ((k : ZMod N)).val = k := ZMod.val_cast_of_lt hkN
  rw [h, ZMod.val_zero] at hval
  omega

/-- `n ≥ 3` のとき `1`, `-1`, `2^(n-1)+1`, `2^(n-1)-1` は相異なる。 -/
theorem sqrtOne_pairwise_ne (hn : 3 ≤ n) :
    ({1, -1, (2 : ZMod (2 ^ n)) ^ (n - 1) + 1, (2 : ZMod (2 ^ n)) ^ (n - 1) - 1} :
      Set (ZMod (2 ^ n))).ncard = 4 := by
  have hpow : ∀ k : ℕ, ((2 ^ k : ℕ) : ZMod (2 ^ n)) = (2 : ZMod (2 ^ n)) ^ k := by
    intro k; rw [Nat.cast_pow]; norm_num
  have h2lt : (2 : ℕ) < 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hhalf : (2 : ℕ) ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hhalf2 : (2 : ℕ) ≤ 2 ^ (n - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfour : (4 : ℕ) ≤ 2 ^ (n - 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (2 : ℕ) ^ (n - 1) + 2 < 2 ^ n := by
    have : (2 : ℕ) ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    omega
  -- 各 `≠` を `(k : ZMod _) ≠ 0` に落とす
  have e2 : (2 : ZMod (2 ^ n)) ≠ 0 := by
    have := natCast_ne_zero_of_lt (N := 2 ^ n) (k := 2) (by norm_num) h2lt
    simpa using this
  have ea : (2 : ZMod (2 ^ n)) ^ (n - 1) ≠ 0 := by
    have := natCast_ne_zero_of_lt (N := 2 ^ n) (k := 2 ^ (n - 1)) (by positivity) hhalf
    rwa [hpow] at this
  have easub : (2 : ZMod (2 ^ n)) ^ (n - 1) - 2 ≠ 0 := by
    have h := natCast_ne_zero_of_lt (N := 2 ^ n) (k := 2 ^ (n - 1) - 2) (by omega) (by omega)
    intro hcon
    refine h ?_
    have : ((2 ^ (n - 1) - 2 : ℕ) : ZMod (2 ^ n))
        = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) - ((2 : ℕ) : ZMod (2 ^ n)) := by
      rw [Nat.cast_sub (by omega)]
    rw [this, hpow]
    simpa using hcon
  have eaadd : (2 : ZMod (2 ^ n)) ^ (n - 1) + 2 ≠ 0 := by
    have h := natCast_ne_zero_of_lt (N := 2 ^ n) (k := 2 ^ (n - 1) + 2) (by omega) hsum
    intro hcon
    refine h ?_
    have hc : ((2 ^ (n - 1) + 2 : ℕ) : ZMod (2 ^ n))
        = (2 : ZMod (2 ^ n)) ^ (n - 1) + 2 := by
      rw [Nat.cast_add, hpow]
      norm_num
    rw [hc, hcon]
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact e2 (by linear_combination h)
      · exact ea (by linear_combination -h)
      · exact easub (by linear_combination -h)) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact eaadd (by linear_combination -h)
      · exact ea (by linear_combination -h)) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      intro h
      exact e2 (by linear_combination h)) (Set.toFinite _),
    Set.ncard_singleton]

/-- `n ≥ 3` のとき `ZMod (2^n)` の `1` の平方根はちょうど 4 個。 -/
theorem ncard_sq_eq_one (hn : 3 ≤ n) : {x : ZMod (2 ^ n) | x ^ 2 = 1}.ncard = 4 := by
  have hset : {x : ZMod (2 ^ n) | x ^ 2 = 1} =
      ({1, -1, (2 : ZMod (2 ^ n)) ^ (n - 1) + 1, (2 : ZMod (2 ^ n)) ^ (n - 1) - 1} :
        Set (ZMod (2 ^ n))) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact sq_eq_one_iff_two_pow (by omega) x
  rw [hset]
  exact sqrtOne_pairwise_ne hn

/-- 単位群でも同じ: `(ZMod (2^n))ˣ` の `1` の平方根はちょうど 4 個 (`n ≥ 3`)。 -/
theorem ncard_sq_eq_one_units (hn : 3 ≤ n) :
    {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1}.ncard = 4 := by
  have e : {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1} ≃ {x : ZMod (2 ^ n) | x ^ 2 = 1} :=
    { toFun := fun u => ⟨((u : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)), by
        have hu : (u : (ZMod (2 ^ n))ˣ) ^ 2 = 1 := u.2
        have := congrArg Units.val hu
        simpa using this⟩
      invFun := fun x =>
        ⟨⟨(x : ZMod (2 ^ n)), (x : ZMod (2 ^ n)),
          by have := x.2; rw [Set.mem_setOf_eq, pow_two] at this; exact this,
          by have := x.2; rw [Set.mem_setOf_eq, pow_two] at this; exact this⟩, by
          have hx : (x : ZMod (2 ^ n)) ^ 2 = 1 := x.2
          refine Units.ext ?_
          simpa using hx⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have h1 : Nat.card {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1} =
      Nat.card {x : ZMod (2 ^ n) | x ^ 2 = 1} := Nat.card_congr e
  calc {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1}.ncard
      = Nat.card {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1} := rfl
    _ = Nat.card {x : ZMod (2 ^ n) | x ^ 2 = 1} := h1
    _ = {x : ZMod (2 ^ n) | x ^ 2 = 1}.ncard := rfl
    _ = 4 := ncard_sq_eq_one hn

/-- **Isaacs Problem 6B.6** (p. 196) ⭐: 位数 `2^n` (`n ≥ 3`, すなわち位数 `≥ 8`) の
巡回群は位数 `2` の自己同型をちょうど **3 個**持つ。 -/
theorem ncard_orderOf_eq_two_mulAut {C : Type*} [Group C] [Finite C] [IsCyclic C] {n : ℕ}
    (hn : 3 ≤ n) (hC : Nat.card C = 2 ^ n) :
    {σ : MulAut C | orderOf σ = 2}.ncard = 3 := by
  have e : MulAut C ≃* (ZMod (2 ^ n))ˣ := by
    rw [← hC]
    exact IsCyclic.mulAutMulEquiv C
  have h4 : {σ : MulAut C | σ ^ 2 = 1}.ncard = 4 := by
    have hcong : Nat.card {σ : MulAut C | σ ^ 2 = 1}
        = Nat.card {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1} :=
      Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun σ => by
        change σ ^ 2 = 1 ↔ (e σ) ^ 2 = 1
        constructor
        · intro h
          rw [← map_pow, h, map_one]
        · intro h
          exact e.injective (by rw [map_pow, h, map_one]))
    calc {σ : MulAut C | σ ^ 2 = 1}.ncard
        = Nat.card {σ : MulAut C | σ ^ 2 = 1} := rfl
      _ = Nat.card {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1} := hcong
      _ = {u : (ZMod (2 ^ n))ˣ | u ^ 2 = 1}.ncard := rfl
      _ = 4 := ncard_sq_eq_one_units hn
  have hdiff : {σ : MulAut C | orderOf σ = 2} = {σ : MulAut C | σ ^ 2 = 1} \ {1} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · intro h
      refine ⟨by rw [← h]; exact pow_orderOf_eq_one σ, fun hσ => ?_⟩
      rw [hσ, orderOf_one] at h
      omega
    · rintro ⟨hsq, hne⟩
      exact orderOf_eq_prime hsq hne
  rw [hdiff, Set.ncard_sdiff_singleton_of_mem (by simp : (1 : MulAut C) ∈ {σ | σ ^ 2 = 1}), h4]

end

end OddOrder.Isaacs.Ch06
