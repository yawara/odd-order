/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Perm.Cycle.Type
import OddOrder.GroupTheory.SpecificGroups.QuaternionGroupMulAut

/-!
# Isaacs Problem 7A.6 — 一般四元数群の自己同型群の奇素因数

**主張** (書籍 p. 209): 一般四元数群 `Q` について `|Aut(Q)|` が奇素数 `p` で割れるなら
`p = 3` かつ `|Q| = 8`。

mathlib の `QuaternionGroup n` は位数 `4n` なので, 一般四元数群は `n = 2 ^ m` (`m ≥ 1`),
すなわち `Q = QuaternionGroup (2 ^ m)` (位数 `2 ^ (m + 2)`) である。

**証明**: `m ≥ 2` (位数 `≥ 16`) なら `Aut(Q)` は奇素数位数の元をもたない:

* `|Q| ≥ 16` のとき `orderOf (a 1) = 2 ^ (m+1) ≥ 8 > 4 = orderOf (xa i)` なので,
  自己同型 `σ` は `a 1` を `a j` に送る (`mulAut_apply_a_one`)。
* `σ (a i) = a (i * j)` ゆえ `σ ^ k (a i) = a (i * j ^ k)`; `σ ^ p = 1` から `j ^ p = 1`。
  `(ZMod (2 ^ (m+1)))ˣ` は位数 `2 ^ m` の `2`-群なので `p` が奇素数なら `j = 1`,
  すなわち `σ` は `⟨a⟩` を各元固定する。
* すると `σ (xa 0) = xa t` で `σ ^ k (xa 0) = xa (k * t)`, `σ ^ p = 1` から `p * t = 0`;
  `p` は `ZMod (2 ^ (m+1))` の単元なので `t = 0` となり `σ = 1`。

したがって `m = 1` (`|Q| = 8`) で, `Q₈` については既存の
`card_dvd_three_of_odd_mulAutQuaternion` (奇位数部分群の位数は `3` を割る) から `p = 3`。
-/

namespace OddOrder.Isaacs.Ch07

open QuaternionGroup

section /- 7A.6: 一般四元数群の `Aut` (p. 209) -/

variable {m : ℕ}

/-- 位数 `≥ 16` の一般四元数群では位数 `2 ^ (m+1) > 4` の元は `a i` の形に限る。 -/
private theorem eq_a_of_orderOf (hm : 2 ≤ m) {y : QuaternionGroup (2 ^ m)}
    (hy : orderOf y = 2 * 2 ^ m) : ∃ j, y = a j := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  cases y with
  | a i => exact ⟨i, rfl⟩
  | xa i =>
    exfalso
    rw [orderOf_xa] at hy
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

/-- `(a i) ^ k = a (k * i)`。 -/
private theorem a_pow (i : ZMod (2 * 2 ^ m)) (k : ℕ) :
    (a i : QuaternionGroup (2 ^ m)) ^ k = a ((k : ZMod (2 * 2 ^ m)) * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

/-- `a i = (a 1) ^ i.val`。 -/
private theorem a_eq_a_one_pow (i : ZMod (2 * 2 ^ m)) :
    (a 1 : QuaternionGroup (2 ^ m)) ^ i.val = a i := by
  have : NeZero (2 * 2 ^ m) := ⟨by positivity⟩
  rw [a_one_pow, ZMod.natCast_val, ZMod.cast_id]

/-- 位数 `≥ 16` の一般四元数群の自己同型は `⟨a⟩` を保ち, `a i ↦ a (i * j)` の形になる。 -/
private theorem exists_mulAut_apply_a (hm : 2 ≤ m)
    (σ : MulAut (QuaternionGroup (2 ^ m))) :
    ∃ j : ZMod (2 * 2 ^ m), ∀ i, σ (a i) = a (i * j) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  have hord : orderOf (σ (a 1 : QuaternionGroup (2 ^ m))) = 2 * 2 ^ m :=
    (orderOf_injective σ.toMonoidHom σ.injective (a 1)).trans orderOf_a_one
  obtain ⟨j, hj⟩ := eq_a_of_orderOf hm hord
  refine ⟨j, fun i => ?_⟩
  rw [← a_eq_a_one_pow i, map_pow, hj, a_pow, ZMod.natCast_val, ZMod.cast_id]

variable {p : ℕ}

/-- **位数 `≥ 16` の一般四元数群の自己同型群は奇素数位数の元をもたない**。 -/
theorem mulAut_eq_one_of_pow_prime_eq_one (hm : 2 ≤ m) (hp : p.Prime) (hodd : Odd p)
    (σ : MulAut (QuaternionGroup (2 ^ m))) (hσ : σ ^ p = 1) : σ = 1 := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  have : NeZero (2 * 2 ^ m) := ⟨by positivity⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨j, hj⟩ := exists_mulAut_apply_a hm σ
  -- `σ ^ k (a i) = a (i * j ^ k)`
  have hiter : ∀ (k : ℕ) (i : ZMod (2 * 2 ^ m)),
      (σ ^ k) (a i : QuaternionGroup (2 ^ m)) = a (i * j ^ k) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ]
      change (σ ^ k) (σ (a i)) = _
      rw [hj i, ih (i * j)]
      congr 1
      ring
  -- `j ^ p = 1`
  have hjp : j ^ p = 1 := by
    have h := hiter p 1
    rw [hσ] at h
    simp only [MulAut.coe_one, id_eq, one_mul] at h
    injection h with h3
    exact h3.symm
  -- `j = 1`
  have hj1 : j = 1 := by
    have hunit : IsUnit j := by
      refine IsUnit.of_mul_eq_one (j ^ (p - 1)) ?_
      have hp1 : 1 + (p - 1) = p := by have := hp.two_le; omega
      calc j * j ^ (p - 1) = j ^ (1 + (p - 1)) := by rw [pow_add, pow_one]
        _ = j ^ p := by rw [hp1]
        _ = 1 := hjp
    obtain ⟨u, rfl⟩ := hunit
    have hup : u ^ p = 1 := Units.ext hjp
    have hdvd1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
    have hcardu : Nat.card (ZMod (2 * 2 ^ m))ˣ = 2 ^ m := by
      have h2 : 2 * 2 ^ m = 2 ^ (m + 1) := by ring
      rw [h2, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    have hdvd2 : orderOf u ∣ 2 ^ m := by
      have h := orderOf_dvd_natCard u
      rwa [hcardu] at h
    have : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    rw [orderOf_eq_one_iff] at this
    rw [this, Units.val_one]
  -- `σ` は `⟨a⟩` を各元固定する
  have hafix : ∀ i, σ (a i : QuaternionGroup (2 ^ m)) = a i := by
    intro i; rw [hj i, hj1, mul_one]
  -- `σ (xa 0) = xa t`
  obtain ⟨t, ht⟩ : ∃ t, σ (xa 0 : QuaternionGroup (2 ^ m)) = xa t := by
    rcases hy : σ (xa 0 : QuaternionGroup (2 ^ m)) with i | i
    · exfalso
      have : σ (xa 0 : QuaternionGroup (2 ^ m)) = σ (a i) := by rw [hy, hafix]
      have := σ.injective this
      exact absurd this (by simp)
    · exact ⟨i, rfl⟩
  -- `σ (xa i) = xa (t + i)`, ゆえに `σ ^ k (xa 0) = xa (k * t)`
  have hxafix : ∀ i, σ (xa i : QuaternionGroup (2 ^ m)) = xa (t + i) := by
    intro i
    have hsplit : (xa i : QuaternionGroup (2 ^ m)) = xa 0 * a i := by
      rw [xa_mul_a, zero_add]
    rw [hsplit, map_mul, ht, hafix, xa_mul_a]
  have hiter2 : ∀ (k : ℕ) (i : ZMod (2 * 2 ^ m)),
      (σ ^ k) (xa i : QuaternionGroup (2 ^ m)) = xa (i + (k : ZMod (2 * 2 ^ m)) * t) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ]
      change (σ ^ k) (σ (xa i)) = _
      rw [hxafix i, ih (t + i)]
      congr 1
      push_cast
      ring
  -- `p * t = 0` から `t = 0`
  have htp : (p : ZMod (2 * 2 ^ m)) * t = 0 := by
    have h := hiter2 p 0
    rw [hσ] at h
    simp only [MulAut.coe_one, id_eq, zero_add] at h
    injection h with h3
    exact h3.symm
  have hpunit : IsUnit ((p : ZMod (2 * 2 ^ m))) := by
    rw [ZMod.isUnit_iff_coprime]
    have h2 : 2 * 2 ^ m = 2 ^ (m + 1) := by ring
    rw [h2]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have ht0 : t = 0 := by
    obtain ⟨v, hv⟩ := hpunit
    have : (v : ZMod (2 * 2 ^ m)) * t = 0 := by rw [hv]; exact htp
    calc t = (↑v⁻¹ : ZMod (2 * 2 ^ m)) * ((v : ZMod (2 * 2 ^ m)) * t) := by
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = 0 := by rw [this, mul_zero]
  -- `σ = 1`
  refine MulEquiv.ext fun x => ?_
  cases x with
  | a i => simpa using hafix i
  | xa i => rw [hxafix i, ht0, zero_add]; simp

/-- **Isaacs Problem 7A.6** — 一般四元数群 `Q = QuaternionGroup (2 ^ m)` (`m ≥ 1`,
位数 `2 ^ (m+2) ≥ 8`) について `|Aut(Q)|` が奇素数 `p` で割れるなら `p = 3` かつ `|Q| = 8`。 -/
theorem eq_three_and_card_eq_eight_of_odd_prime_dvd_card_mulAut
    (hm : 1 ≤ m) (hp : p.Prime) (hodd : Odd p)
    (hdvd : p ∣ Nat.card (MulAut (QuaternionGroup (2 ^ m)))) :
    p = 3 ∧ Nat.card (QuaternionGroup (2 ^ m)) = 8 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  let : Fintype (MulAut (QuaternionGroup (2 ^ m))) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := MulAut (QuaternionGroup (2 ^ m))) p
    (by rwa [← Nat.card_eq_fintype_card])
  -- `m ≥ 2` なら `σ = 1` となり `orderOf σ = p > 1` に矛盾
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have hone : σ = 1 :=
      mulAut_eq_one_of_pow_prime_eq_one hm2 hp hodd σ (hσ ▸ pow_orderOf_eq_one σ)
    rw [hone, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  subst hm1
  refine ⟨?_, by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num⟩
  -- `QuaternionGroup (2 ^ 1)` は `Q₈`; 既存の「奇位数部分群の位数は 3 を割る」を使う
  obtain ⟨τ, hτord⟩ : ∃ τ : MulAut (QuaternionGroup 2), orderOf τ = p := ⟨σ, hσ⟩
  have hcardD : Nat.card (Subgroup.zpowers τ) = p := by rw [Nat.card_zpowers, hτord]
  have h := OddOrder.GroupTheory.card_dvd_three_of_odd_mulAutQuaternion
    (Subgroup.zpowers τ) (by rw [hcardD]; exact hodd)
  rw [hcardD] at h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
end

end OddOrder.Isaacs.Ch07
