/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.ProblemsOrder120

/-!
# Isaacs Problems 1E (pp. 37–38) — Sylow 計数による非単純性

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1E の形式化
(campaign issue 1055)。§1E は「与えられた位数の群が単純になれない」ことを Sylow の
個数 `n_q = |Syl_q(G)|` の合同・整除条件から導く演習からなる。

* **1E.1**: `|G| = p²q²` (`p < q` 素数) なら `n_q = 1`, ただし `|G| = 36` は例外。
* **1E.2**: `|G| = pqr` (`p < q < r` 素数) なら `n_r = 1`。

## 共通の道具

`n_q ∣ [G : Q]` (`Sylow.card_dvd_index`) と `n_q ≡ 1 (mod q)` (`card_sylow_modEq_one`)。
Sylow 部分群の位数・指数を `|G|` の分解から読むために
`sylow_card_and_index_of_card_eq_mul` を用意する (既存の
`sylow_card_eq_prime_of_card_eq_mul` の任意指数版)。

## Main results

- `sylow_card_and_index_of_card_eq_mul` — `|G| = m·q^k` (`q ∤ m`) なら
  `|Q| = q^k` かつ `[G : Q] = m`。
- `card_sylow_eq_one_of_card_eq_sq_mul_sq` — **Problem 1E.1**。
- `card_sylow_eq_one_of_card_eq_mul_mul` — **Problem 1E.2**。
-/

namespace OddOrder.Isaacs.Ch01

section /- 1E: Sylow 部分群の位数と指数 (p. 37) -/

/-- `|G| = m·q^k` (`q` 素数, `q ∤ m`) のとき Sylow `q`-部分群の位数は `q^k`,
指数は `m` ちょうど。 -/
theorem sylow_card_and_index_of_card_eq_mul {G : Type*} [Group G] [Finite G] {q m k : ℕ}
    [Fact q.Prime] (h : Nat.card G = m * q ^ k) (hm : ¬ q ∣ m) (P : Sylow q G) :
    Nat.card ↥(P : Subgroup G) = q ^ k ∧ (P : Subgroup G).index = m := by
  have hq : q.Prime := Fact.out
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero q)
  have hfact : (Nat.card G).factorization q = k := by
    rw [h, Nat.factorization_mul hm0 (pow_ne_zero k hq.pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm, zero_add, hq.factorization_pow]
    simp
  have hcard : Nat.card ↥(P : Subgroup G) = q ^ k := by
    rw [Sylow.card_eq_multiplicity, hfact]
  refine ⟨hcard, ?_⟩
  have hmul := Subgroup.card_mul_index (P : Subgroup G)
  rw [hcard, h] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos k) (by linarith [hmul, mul_comm m (q ^ k)])

end -- Sylow の位数と指数

section /- 1E: Problem 1E.1 (p. 37) -/

/-- 連続する 2 つの素数 `p`, `p + 1` は `2`, `3` に限る。 -/
private lemma eq_two_three_of_prime_succ {p : ℕ} (hp : p.Prime) (hp1 : (p + 1).Prime) :
    p = 2 ∧ p + 1 = 3 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact ⟨rfl, rfl⟩
  · exfalso
    obtain ⟨j, hj⟩ := hodd
    have : (p + 1) % 2 = 0 := by omega
    have h2 : (2 : ℕ) ∣ p + 1 := Nat.dvd_of_mod_eq_zero this
    have := (Nat.Prime.eq_one_or_self_of_dvd hp1 2 h2)
    have := hp.two_le
    omega

/-- **Isaacs Problem 1E.1** (p. 37)。`|G| = p²q²` (`p < q` は素数) なら Sylow
`q`-部分群は一意 (`n_q = 1`)。ただし `|G| = 36` (`p = 2`, `q = 3`) は例外。

`n_q ∣ [G : Q] = p²` なので `n_q ∈ {1, p, p²}`。`n_q ≡ 1 (mod q)` と `p < q` から
`n_q = p` は `p = 1` を強いて不可能。`n_q = p²` なら `q ∣ p² − 1 = (p−1)(p+1)` で,
`q > p` ゆえ `q ∣ p − 1` は `p = 1` を強いるので `q ∣ p + 1`, つまり `q = p + 1`。
連続する素数は `2, 3` だけなので `|G| = 4·9 = 36`。 -/
theorem card_sylow_eq_one_of_card_eq_sq_mul_sq {G : Type*} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hG : Nat.card G = p ^ 2 * q ^ 2)
    (h36 : Nat.card G ≠ 36) : Nat.card (Sylow q G) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := Sylow.nonempty
  have hpq' : ¬ q ∣ p ^ 2 := by
    intro hdvd
    have := (Nat.Prime.dvd_of_dvd_pow hq hdvd)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp this) (by omega)
  obtain ⟨-, hindex⟩ := sylow_card_and_index_of_card_eq_mul (q := q) (m := p ^ 2) (k := 2) hG hpq' Q
  have hdvd : Nat.card (Sylow q G) ∣ p ^ 2 := hindex ▸ Sylow.card_dvd_index Q
  have hmod : Nat.card (Sylow q G) % q = 1 % q := card_sylow_modEq_one q G
  have hq1 : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
  rw [hq1] at hmod
  obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases i
  · simpa using hni
  · -- `n_q = p`: `p < q` なので `p % q = p = 1`, 素数性に矛盾
    exfalso
    rw [pow_one] at hni
    rw [hni, Nat.mod_eq_of_lt hpq] at hmod
    exact absurd hmod (by have := hp.two_le; omega)
  · -- `n_q = p²`: `q ∣ (p−1)(p+1)` から `q = p + 1`, ⟹ `|G| = 36`
    exfalso
    rw [hni] at hmod
    have hdvd2 : q ∣ p ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp (hq1.trans hmod.symm)
    have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
      have hpr : n * (n + 1 + 1) = n * n + 2 * n := by ring
      simp only [Nat.add_sub_cancel, hsq]
      omega
    rw [hfac] at hdvd2
    rcases (Nat.Prime.dvd_mul hq).mp hdvd2 with h | h
    · -- `q ∣ p − 1` は `0 < p − 1 < q` に反する
      have := hp.two_le
      have hle := Nat.le_of_dvd (by omega) h
      omega
    · -- `q ∣ p + 1` と `p < q` から `q = p + 1`
      have hle := Nat.le_of_dvd (by omega) h
      have hqe : q = p + 1 := by omega
      obtain ⟨hp2, hq3⟩ := eq_two_three_of_prime_succ hp (hqe ▸ hq)
      rw [hG, hp2, show q = 3 by omega] at h36
      norm_num at h36

end -- Problem 1E.1

end OddOrder.Isaacs.Ch01
