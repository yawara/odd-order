/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.ProblemsAlternating

/-!
# Isaacs Problems 1E (pp. 37–38) — Sylow 計数による非単純性

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1E の形式化
(campaign issue 1055)。§1E は「与えられた位数の群が単純になれない」ことを Sylow の
個数 `n_q = |Syl_q(G)|` の合同・整除条件から導く演習からなる。

* **1E.1**: `|G| = p²q²` (`p < q` 素数) なら `n_q = 1`, ただし `|G| = 36` は例外。
* **1E.2**: `|G| = pqr` (`p < q < r` 素数) なら `n_r = 1`。
* **1E.3**: 位数 `315 = 3²·5·7` の単純群は存在しない。
* **1E.4**: 位数 `144 = 2⁴·3²` の単純群は存在しない。
* **1E.5**: 位数 `336 = 2⁴·3·7` の単純群は存在しない (Hint = `n₇` を計算して 1C.5)。
* **1E.6**: 位数 `180 = 2²·3²·5` の単純群は存在しない。
* **1E.7**: 位数 `240 = 2⁴·3·5` の単純群は存在しない。

## 共通の道具

`n_q ∣ [G : Q]` (`Sylow.card_dvd_index`) と `n_q ≡ 1 (mod q)` (`card_sylow_modEq_one`)。
Sylow 部分群の位数・指数を `|G|` の分解から読むために
`sylow_card_and_index_of_card_eq_mul` を用意する (既存の
`sylow_card_eq_prime_of_card_eq_mul` の任意指数版)。具体的な位数の非単純性 (1E.3 以降) は
さらに **Thm 1.16** (`card_sylow_modEq_one_of_max_inter`, 交わり最大の Sylow 対) と
**Cor 1.3** (`card_dvd_factorial_of_simple_subgroup_index`, 単純群の部分群の指数) を使う。

## Main results

- `sylow_card_and_index_of_card_eq_mul` — `|G| = m·q^k` (`q ∤ m`) なら
  `|Q| = q^k` かつ `[G : Q] = m`。
- `card_sylow_eq_one_of_card_eq_sq_mul_sq` — **Problem 1E.1**。
- `card_sylow_eq_one_of_card_eq_prime_mul_prime` — 位数 `qr` (`q < r`) なら `n_r = 1`。
- `card_sylow_eq_one_of_card_eq_mul_mul` — **Problem 1E.2**。
- `card_sylow_mod_eq_one` / `card_sylow_eq_one_of_card_eq_prime_mul_pow` /
  `card_sylow_ne_one_of_simple` / `exists_max_inter_sylow_pair` — 1E.3 以降の共通部品。
- `not_isSimpleGroup_of_card_eq_threeonefive` — **Problem 1E.3**。
- `not_isSimpleGroup_of_card_eq_onefourfour` — **Problem 1E.4**。
- `exists_injective_hom_alternating_of_simple` — 単純群は指数 `n` の部分群があれば
  `Aₙ` に単射に埋め込める (1E.5 の Hint が要求する道具)。
- `not_isSimpleGroup_of_card_eq_threethreesix` — **Problem 1E.5**。
- `two_mul_card_ne_card_alternating_of_simple` — 単純群の位数は `|Aₙ|` の半分になれない
  (像が指数 2 で正規になり `Aₙ` の単純性に反する)。
- `exists_finset_of_sylow_inter_trivial` — Sylow が自明交叉なら非単位元は
  `n_q·(|P| − 1)` 個 (他の素数の計数と足して `|G|` を超えさせる用)。
- `not_isSimpleGroup_of_card_eq_oneeighty` — **Problem 1E.6**。
- `card_dvd_factorial_card_sylow_of_simple` — 単純群で `n_q > 1` なら `|G| ∣ n_q !`。
- `not_isSimpleGroup_of_card_eq_twofourty` — **Problem 1E.7**。
-/

namespace OddOrder.Isaacs.Ch01

section /- 1E: Sylow 部分群の位数と指数 (p. 37) -/

/-- `N = m·q^k` (`q` 素数, `q ∤ m`) なら `N` の `q`-指数はちょうど `k`。 -/
theorem factorization_of_eq_mul_pow {N m q k : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m)
    (h : N = m * q ^ k) : N.factorization q = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero q)
  rw [h, Nat.factorization_mul hm0 (pow_ne_zero k hq.pos.ne'), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, zero_add, hq.factorization_pow]
  simp

/-- `|G| = m·q^k` (`q` 素数, `q ∤ m`) のとき Sylow `q`-部分群の位数は `q^k`,
指数は `m` ちょうど。 -/
theorem sylow_card_and_index_of_card_eq_mul {G : Type*} [Group G] [Finite G] {q m k : ℕ}
    [Fact q.Prime] (h : Nat.card G = m * q ^ k) (hm : ¬ q ∣ m) (P : Sylow q G) :
    Nat.card ↥(P : Subgroup G) = q ^ k ∧ (P : Subgroup G).index = m := by
  have hq : q.Prime := Fact.out
  have hfact : (Nat.card G).factorization q = k := factorization_of_eq_mul_pow hq hm h
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

section /- 1E: Problem 1E.2 (p. 38) -/

/-- 相異なる 2 素数の積の約数は `1, p, q, pq` に限る。 -/
private lemma eq_of_dvd_prime_mul_prime {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : n ∣ p * q) : n = 1 ∨ n = p ∨ n = q ∨ n = p * q := by
  rcases hp.eq_one_or_self_of_dvd (Nat.gcd n p) (Nat.gcd_dvd_right n p) with hg | hg
  · have hdq : n ∣ q := Nat.Coprime.dvd_of_dvd_mul_left hg h
    rcases (Nat.dvd_prime hq).mp hdq with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  · obtain ⟨m, rfl⟩ : p ∣ n := hg ▸ Nat.gcd_dvd_left n p
    have hm : m ∣ q := (mul_dvd_mul_iff_left hp.pos.ne').mp h
    rcases (Nat.dvd_prime hq).mp hm with h1 | h1
    · subst h1; exact Or.inr (Or.inl (mul_one p))
    · subst h1; exact Or.inr (Or.inr (Or.inr rfl))

/-- 位数 `q·r` (`q < r` は素数) の群では Sylow `r`-部分群は一意。

`n_r ∣ [H : R] = q` と `n_r ≡ 1 (mod r)`, そして `q < r` より `q % r = q ≠ 1`。 -/
theorem card_sylow_eq_one_of_card_eq_prime_mul_prime {H : Type*} [Group H] [Finite H]
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q < r) (hH : Nat.card H = q * r) :
    Nat.card (Sylow r H) = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨R⟩ : Nonempty (Sylow r H) := Sylow.nonempty
  have hnd : ¬ r ∣ q := fun hd => by have := Nat.le_of_dvd hq.pos hd; omega
  obtain ⟨-, hindex⟩ := sylow_card_and_index_of_card_eq_mul (q := r) (m := q) (k := 1)
    (by rw [hH, pow_one]) hnd R
  have hdvd : Nat.card (Sylow r H) ∣ q := hindex ▸ Sylow.card_dvd_index R
  have hmod : Nat.card (Sylow r H) % r = 1 % r := card_sylow_modEq_one r H
  rw [Nat.mod_eq_of_lt hr.one_lt] at hmod
  rcases (Nat.dvd_prime hq).mp hdvd with h | h
  · exact h
  · exfalso
    rw [h, Nat.mod_eq_of_lt hqr] at hmod
    have := hq.two_le
    omega

/-- **Isaacs Problem 1E.2** (p. 38)。`|G| = pqr` (`p < q < r` は素数) なら Sylow
`r`-部分群は一意 (`n_r = 1`)。

`n_r ∣ [G : R] = pq` なので `n_r ∈ {1, p, q, pq}`。`p, q < r` より `n_r = p`, `n_r = q`
はどちらも `n_r % r = n_r = 1` を強いて素数性に矛盾。残る `n_r = pq` を仮定すると:

* 位数 `r` の元が `pq(r−1)` 個あるので, `n_q ≠ 1` なら `n_q ≥ r` (`n_q ∈ {1, p, r, pr}`
  で `p < q` ゆえ `n_q ≠ p`) となり計数 `pq(r−1) + r(q−1) ≤ |G| − 1` が
  `r(q−1) ≤ pq − 1` を要求する。しかし `r ≥ q+1`, `p ≤ q−1` から
  `r(q−1) ≥ q²−1 > q²−q−1 ≥ pq−1` で矛盾 ⟹ **`n_q = 1`**。
* すると `Q ⊴ G` (位数 `q`) で `M := Q ⊔ R` は位数 `qr`, その中で Sylow `r` は一意
  (`card_sylow_eq_one_of_card_eq_prime_mul_prime`) だから `R ⊴ M`, つまり
  `M ≤ N_G(R)`。しかし `|N_G(R)| = |G| / n_r = r` なので `qr ≤ r`, `q > 1` に矛盾。 -/
theorem card_sylow_eq_one_of_card_eq_mul_mul {G : Type*} [Group G] [Finite G] {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (hG : Nat.card G = p * q * r) : Nat.card (Sylow r G) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hp2 := hp.two_le
  -- Sylow `q`, `r` の位数はちょうど `q`, `r`, 指数は `pr`, `pq`。
  have hqnd : ¬ q ∣ p * r := by
    intro hd
    rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
    · have := Nat.le_of_dvd hp.pos h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hq hr).mp h; omega
  have hrnd : ¬ r ∣ p * q := by
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · have := Nat.le_of_dvd hp.pos h; omega
    · have := Nat.le_of_dvd hq.pos h; omega
  have hqdec : ∀ P : Sylow q G, Nat.card ↥(P : Subgroup G) = q ∧ (P : Subgroup G).index = p * r :=
    fun P => by
      have := sylow_card_and_index_of_card_eq_mul (q := q) (m := p * r) (k := 1)
        (by rw [hG, pow_one]; ring) hqnd P
      exact ⟨this.1.trans (pow_one q), this.2⟩
  have hrdec : ∀ P : Sylow r G, Nat.card ↥(P : Subgroup G) = r ∧ (P : Subgroup G).index = p * q :=
    fun P => by
      have := sylow_card_and_index_of_card_eq_mul (q := r) (m := p * q) (k := 1)
        (by rw [hG, pow_one]) hrnd P
      exact ⟨this.1.trans (pow_one r), this.2⟩
  obtain ⟨R⟩ : Nonempty (Sylow r G) := Sylow.nonempty
  have hmodr : Nat.card (Sylow r G) % r = 1 % r := card_sylow_modEq_one r G
  rw [Nat.mod_eq_of_lt hr.one_lt] at hmodr
  rcases eq_of_dvd_prime_mul_prime hp hq ((hrdec R).2 ▸ Sylow.card_dvd_index R) with
    h1 | h1 | h1 | h1
  · exact h1
  · rw [h1, Nat.mod_eq_of_lt (by omega : p < r)] at hmodr; omega
  · rw [h1, Nat.mod_eq_of_lt hqr] at hmodr; omega
  -- 残るのは `n_r = pq`。計数で `n_q = 1` を出し, `N_G(R)` の位数と矛盾させる。
  exfalso
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := Sylow.nonempty
  have hnq : Nat.card (Sylow q G) = 1 := by
    by_contra hne
    -- `n_q ∣ pr` かつ `n_q ≠ p` (∵ `p < q`) なので `n_q ≥ r`
    have hmodq : Nat.card (Sylow q G) % q = 1 % q := card_sylow_modEq_one q G
    rw [Nat.mod_eq_of_lt hq.one_lt] at hmodq
    have hge : r ≤ Nat.card (Sylow q G) := by
      rcases eq_of_dvd_prime_mul_prime hp hr ((hqdec Q).2 ▸ Sylow.card_dvd_index Q) with
        h2 | h2 | h2 | h2
      · exact absurd h2 hne
      · rw [h2, Nat.mod_eq_of_lt (by omega : p < q)] at hmodq; omega
      · omega
      · rw [h2]; exact Nat.le_mul_of_pos_left r hp.pos
    -- 計数: `n_r(r−1) + n_q(q−1) ≤ |G| − 1`
    have hcount := card_sylow_mul_add_card_sylow_mul_le (q₁ := r) (q₂ := q)
      (by omega) (fun P => (hrdec P).1) (fun P => (hqdec P).1)
    rw [h1, hG] at hcount
    -- `q = u+1`, `r = v+1` に置換して ℕ の切り捨て減算を消し, 線形不等式に落とす
    obtain ⟨v, rfl⟩ : ∃ v, r = v + 1 := ⟨r - 1, by have := hr.pos; omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by have := hq.pos; omega⟩
    simp only [Nat.add_sub_cancel] at hcount
    set N := Nat.card (Sylow (u + 1) G) with hN
    have hple : p ≤ u := by omega
    have hNge : u + 2 ≤ N := by omega
    -- `n_q(q−1) ≥ (q+1)(q−1) = q²−1` と `pq ≤ (q−1)q = q²−q` が `n_q(q−1)+1 ≤ pq` と衝突
    have hA : (u + 2) * u ≤ N * u := Nat.mul_le_mul_right u hNge
    have hB : p * (u + 1) ≤ u * (u + 1) := Nat.mul_le_mul_right (u + 1) hple
    have hC : (u + 2) * u = u * u + 2 * u := by ring
    have hD : u * (u + 1) = u * u + u := by ring
    have hE : p * (u + 1) * (v + 1) = p * (u + 1) * v + p * (u + 1) := by ring
    omega
  -- `Q ⊴ G` かつ `M := Q ⊔ R` は位数 `qr`, その中で `R` は正規
  haveI : Subsingleton (Sylow q G) := Nat.card_eq_one_iff_unique.mp hnq |>.1
  haveI hQnorm : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  have hcop : Nat.Coprime (Nat.card ↥(Q : Subgroup G)) (Nat.card ↥(R : Subgroup G)) := by
    rw [(hqdec Q).1, (hrdec R).1]
    exact (Nat.coprime_primes hq hr).mpr (by omega)
  set M : Subgroup G := (Q : Subgroup G) ⊔ (R : Subgroup G) with hM
  have hMcard : Nat.card ↥M = q * r := by
    rw [hM, card_sup_of_normal_of_coprime hQnorm hcop, (hqdec Q).1, (hrdec R).1]
  have hRM : (R : Subgroup G) ≤ M := le_sup_right
  have hMsyl : Nat.card (Sylow r ↥M) = 1 :=
    card_sylow_eq_one_of_card_eq_prime_mul_prime hq hr hqr hMcard
  haveI : Subsingleton (Sylow r ↥M) := Nat.card_eq_one_iff_unique.mp hMsyl |>.1
  have hRnorm : ((R.subtype hRM : Sylow r ↥M) : Subgroup ↥M).Normal :=
    Sylow.normal_of_subsingleton _
  rw [Sylow.coe_subtype] at hRnorm
  have hMle : M ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mp hRnorm
  -- `|N_G(R)| = |G| / n_r = r` に反する
  have hnorm_index : (Subgroup.normalizer ((R : Subgroup G) : Set G)).index = p * q := by
    rw [Sylow.coe_coe, ← Sylow.card_eq_index_normalizer R]; exact h1
  have hnorm_card := Subgroup.card_mul_index (Subgroup.normalizer ((R : Subgroup G) : Set G))
  rw [hnorm_index, hG] at hnorm_card
  have hMdvd : Nat.card ↥M ≤ Nat.card ↥(Subgroup.normalizer ((R : Subgroup G) : Set G)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hMle)
  rw [hMcard] at hMdvd
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hNR : Nat.card ↥(Subgroup.normalizer ((R : Subgroup G) : Set G)) = r :=
    Nat.eq_of_mul_eq_mul_right hpq0 (by rw [hnorm_card]; ring)
  have hlow : 2 * r ≤ q * r := Nat.mul_le_mul_right r hq.two_le
  have hrpos := hr.pos
  omega

end -- Problem 1E.2

section /- 1E: Problem 1E.3 (p. 38) -/

/-- 位数 `p²` の部分群の元同士は可換 (`IsPGroup.isMulCommutative_of_card_eq_prime_sq`)。 -/
private lemma mul_comm_of_card_eq_prime_sq {G : Type*} [Group G] {P : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hP : Nat.card ↥P = p ^ 2) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    a * b = b * a :=
  congrArg Subtype.val (isMulCommutative_iff.mp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥P) (p := p) hP) ⟨a, ha⟩ ⟨b, hb⟩)

/-- 位数 `p²` の部分群 `P` は, その部分群 `D ≤ P` を正規化する (`P` が可換だから)。 -/
private lemma le_normalizer_of_card_eq_prime_sq {G : Type*} [Group G] {P D : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hP : Nat.card ↥P = p ^ 2) (hDP : D ≤ P) :
    P ≤ Subgroup.normalizer (D : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rwa [show s * h * s⁻¹ = h from by rw [mul_comm_of_card_eq_prime_sq hP hs (hDP hh)]; group]
  · intro hh
    have hhP : h ∈ P := by
      rw [show h = s⁻¹ * (s * h * s⁻¹) * s from by group]
      exact P.mul_mem (P.mul_mem (P.inv_mem hs) (hDP hh)) hs
    rwa [show s * h * s⁻¹ = h from by rw [mul_comm_of_card_eq_prime_sq hP hs hhP]; group] at hh

/-- Sylow `q` の個数は `≡ 1 (mod q)` (`card_sylow_modEq_one` の `%` 版)。 -/
theorem card_sylow_mod_eq_one {H : Type*} [Group H] [Finite H] (q : ℕ) [Fact q.Prime] :
    Nat.card (Sylow q H) % q = 1 := by
  have h := card_sylow_modEq_one q H
  have hq1 : 1 % q = 1 := Nat.mod_eq_of_lt (Fact.out : q.Prime).one_lt
  unfold Nat.ModEq at h
  omega

/-- `|H| = ℓ·q^k` (`ℓ`, `q` は素数で `q ∤ ℓ`, `ℓ % q ≠ 1`) なら Sylow `q`-部分群は一意。

`n_q ∣ [H : Q] = ℓ` と `n_q ≡ 1 (mod q)` から `n_q ∈ {1, ℓ}` で, `ℓ % q ≠ 1` ゆえ `n_q = 1`。 -/
theorem card_sylow_eq_one_of_card_eq_prime_mul_pow {H : Type*} [Group H] [Finite H]
    {q ℓ k : ℕ} [Fact q.Prime] (hl : ℓ.Prime) (hH : Nat.card H = ℓ * q ^ k)
    (hnd : ¬ q ∣ ℓ) (hmod : ℓ % q ≠ 1) : Nat.card (Sylow q H) = 1 := by
  obtain ⟨P⟩ : Nonempty (Sylow q H) := Sylow.nonempty
  obtain ⟨-, hindex⟩ := sylow_card_and_index_of_card_eq_mul hH hnd P
  have hdvd : Nat.card (Sylow q H) ∣ ℓ := hindex ▸ Sylow.card_dvd_index P
  rcases (Nat.dvd_prime hl).mp hdvd with h | h
  · exact h
  · exact absurd (h ▸ card_sylow_mod_eq_one (H := H) q) hmod

/-- 単純群では, 位数が `1` でも `|G|` でもない Sylow `q`-部分群は一意になりえない。 -/
theorem card_sylow_ne_one_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {q : ℕ} [Fact q.Prime] (P : Sylow q G) (h1 : Nat.card ↥(P : Subgroup G) ≠ 1)
    (h2 : Nat.card ↥(P : Subgroup G) ≠ Nat.card G) : Nat.card (Sylow q G) ≠ 1 := by
  intro hone
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hone).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ (Sylow.normal_of_subsingleton P) with h | h
  · rw [h, Subgroup.card_bot] at h1; exact h1 rfl
  · rw [h, Subgroup.card_top] at h2; exact h2 rfl

/-- 交わりが最大の, 相異なる Sylow `q`-部分群の対 (**Thm 1.16** を当てる前段)。 -/
theorem exists_max_inter_sylow_pair {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (hgt : 1 < Nat.card (Sylow q G)) :
    ∃ S T : Sylow q G, S ≠ T ∧ ∀ S' T' : Sylow q G, S' ≠ T' →
      Nat.card ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G) ≤
      Nat.card ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) := by
  classical
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  haveI : Nontrivial (Sylow q G) := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨S₁, T₁, hST₁⟩ := exists_pair_ne (Sylow q G)
  obtain ⟨STm, hSTm_mem, hSTmax⟩ :=
    (Finset.univ.filter (fun ST : Sylow q G × Sylow q G => ST.1 ≠ ST.2)).exists_max_image
      (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
      ⟨(S₁, T₁), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST₁⟩⟩
  obtain ⟨S, T⟩ := STm
  exact ⟨S, T, (Finset.mem_filter.mp hSTm_mem).2, fun S' T' hne =>
    hSTmax (S', T') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)⟩

/-- **Isaacs Problem 1E.3** (p. 38)。位数 `315 = 3²·5·7` の単純群は存在しない。

`n₃ ∣ [G : S] = 35` かつ `n₃ ≡ 1 (mod 3)` から `n₃ ∈ {1, 7}`。単純性より `n₃ = 7`。
交わり最大の相異なる Sylow `3` 対 `S ≠ T` をとると **Thm 1.16**
(`card_sylow_modEq_one_of_max_inter`) が `7 ≡ 1 (mod |S : D|)` (`D := S ⊓ T`) を与え,
`|S : D| ∣ 6` と `|S : D| ∣ 9`, `≠ 1` から `|S : D| = 3`, つまり `|D| = 3`。
`|S| = 9 = 3²` は可換なので `S`, `T ≤ N := N_G(D)` で `9 ∣ |N| ∣ 315`, ゆえに
`|N| ∈ {9, 45, 63, 315}`。どれも矛盾する:

* `|N| = 9`: `S`, `T ≤ N` と位数比較で `S = N = T`, `S ≠ T` に矛盾。
* `|N| = 45`: 位数 45 の群の Sylow `3` は一意なのに `S ≠ T` が両方入る。
* `|N| = 63`: 指数 5 で **Cor 1.3** より `315 ∣ 5! = 120`, 偽。
* `|N| = 315`: `D ⊴ G` で `1 < |D| = 3 < 315`, 単純性に矛盾。 -/
theorem not_isSimpleGroup_of_card_eq_threeonefive {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 315) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hdec : ∀ P : Sylow 3 G,
      Nat.card ↥(P : Subgroup G) = 9 ∧ (P : Subgroup G).index = 35 := fun P => by
    have h := sylow_card_and_index_of_card_eq_mul (q := 3) (m := 35) (k := 2)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨h.1.trans (by norm_num), h.2⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 G) := Sylow.nonempty
  -- `n₃ = 7`
  have hn3mod : Nat.card (Sylow 3 G) % 3 = 1 := card_sylow_mod_eq_one 3
  have hn3ne1 : Nat.card (Sylow 3 G) ≠ 1 :=
    card_sylow_ne_one_of_simple S₀ (by rw [(hdec S₀).1]; norm_num)
      (by rw [(hdec S₀).1, hG]; norm_num)
  have hn3 : Nat.card (Sylow 3 G) = 7 := by
    rcases eq_of_dvd_prime_mul_prime (p := 5) (q := 7) (by norm_num) (by norm_num)
      ((hdec S₀).2 ▸ Sylow.card_dvd_index S₀) with h | h | h | h
    · exact absurd h hn3ne1
    · rw [h] at hn3mod; norm_num at hn3mod
    · exact h
    · rw [h] at hn3mod; norm_num at hn3mod
  -- 交わり最大の相異なる Sylow `3` 対
  have hgt : 1 < Nat.card (Sylow 3 G) := by rw [hn3]; norm_num
  obtain ⟨S, T, hST, hmax⟩ := exists_max_inter_sylow_pair (q := 3) hgt
  have hmod := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
  rw [hn3] at hmod
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  -- `|S : D| = 3`, つまり `|D| = 3`
  have hd_dvd6 : D.relIndex (S : Subgroup G) ∣ 6 := by
    have h := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 7)).mp hmod.symm
    norm_num at h; exact h
  have hd_dvd9 : D.relIndex (S : Subgroup G) ∣ 9 := by
    have hh := Subgroup.index_dvd_card (D.subgroupOf (S : Subgroup G))
    rw [(hdec S).1] at hh
    exact hh
  have hd_ne1 : D.relIndex (S : Subgroup G) ≠ 1 := by
    intro h1
    have hle : (S : Subgroup G) ≤ D := Subgroup.relIndex_eq_one.mp h1
    exact hST (Sylow.ext (Subgroup.eq_of_le_of_card_ge (hle.trans inf_le_right)
      (((hdec T).1).trans ((hdec S).1).symm).le))
  have hd3 : D.relIndex (S : Subgroup G) = 3 := by
    have hg : D.relIndex (S : Subgroup G) ∣ 3 := by
      have h := Nat.dvd_gcd hd_dvd6 hd_dvd9
      norm_num at h; exact h
    rcases (Nat.dvd_prime (by norm_num)).mp hg with h | h
    · exact absurd h hd_ne1
    · exact h
  have hidx3S : (D.subgroupOf (S : Subgroup G)).index = 3 := hd3
  have hDcard : Nat.card ↥D = 3 := by
    have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx3S, (hdec S).1] at heq
    rw [← hDdef] at heq
    omega
  -- `S`, `T ≤ N := N_G(D)` (位数 `9 = 3²` は可換)
  have hS_le : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_of_card_eq_prime_sq (p := 3) (((hdec S).1).trans (by norm_num)) inf_le_left
  have hT_le : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_of_card_eq_prime_sq (p := 3) (((hdec T).1).trans (by norm_num)) inf_le_right
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  have hNdvd : Nat.card ↥N ∣ 315 := hG ▸ Subgroup.card_subgroup_dvd_card N
  obtain ⟨e, he⟩ : (9 : ℕ) ∣ Nat.card ↥N := ((hdec S).1) ▸ Subgroup.card_dvd_of_le hS_le
  have hedvd : e ∣ 35 :=
    (mul_dvd_mul_iff_left (by norm_num : (9 : ℕ) ≠ 0)).mp (by rw [← he]; simpa using hNdvd)
  -- `|N| ∈ {9, 45, 63, 315}` のいずれも矛盾
  rcases eq_of_dvd_prime_mul_prime (p := 5) (q := 7) (by norm_num) (by norm_num) hedvd with
    h | h | h | h
  · -- `|N| = 9`: `S = N = T`
    rw [h, mul_one] at he
    exact hST (Sylow.ext ((Subgroup.eq_of_le_of_card_ge hS_le (he ▸ ((hdec S).1).ge)).trans
      (Subgroup.eq_of_le_of_card_ge hT_le (he ▸ ((hdec T).1).ge)).symm))
  · -- `|N| = 45`: 位数 45 の群の Sylow `3` は一意
    rw [h] at he
    norm_num at he
    haveI : Subsingleton (Sylow 3 ↥N) :=
      (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one_of_card_eq_prime_mul_pow
        (q := 3) (ℓ := 5) (k := 2) (by norm_num) (by rw [he]; norm_num) (by norm_num)
        (by norm_num))).1
    exact hST (Sylow.subtype_injective (hP := hS_le) (hQ := hT_le) (Subsingleton.elim _ _))
  · -- `|N| = 63`: 指数 5 で Cor 1.3 に矛盾
    rw [h] at he
    norm_num at he
    have hidx : N.index = 5 := by
      have hmul := Subgroup.card_mul_index N
      rw [he, hG] at hmul
      omega
    have hdvd := card_dvd_factorial_of_simple_subgroup_index N (by rw [hidx]; norm_num)
    rw [hG, hidx] at hdvd
    norm_num [Nat.factorial] at hdvd
  · -- `|N| = 315`: `D ⊴ G` で `1 < |D| < |G|`
    rw [h] at he
    norm_num at he
    have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [he, hG])
    have hDnorm : D.Normal := Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)
    rcases hsimple.eq_bot_or_eq_top_of_normal _ hDnorm with h1 | h1
    · rw [h1, Subgroup.card_bot] at hDcard; norm_num at hDcard
    · rw [h1, Subgroup.card_top, hG] at hDcard; norm_num at hDcard

end -- Problem 1E.3

section /- 1E: Problem 1E.4 (p. 38) -/

/-- **Isaacs Problem 1E.4** (p. 38)。位数 `144 = 2⁴·3²` の単純群は存在しない。

`n₃ ∣ [G : S] = 16` と `n₃ ≡ 1 (mod 3)` から `n₃ ∈ {1, 4, 16}`。単純性で `n₃ ≠ 1`,
`n₃ = 4` は正規化群の指数が 4 で **Cor 1.3** の `144 ∣ 4! = 24` が偽。残る `n₃ = 16` では
交わり最大の Sylow `3` 対 `S ≠ T` に **Thm 1.16** を当てて `16 ≡ 1 (mod |S : D|)`,
`|S : D| ∣ gcd(15, 9) = 3` と `≠ 1` から `|D| = 3`。`|S| = 9 = 3²` は可換なので
`S`, `T ≤ N := N_G(D)` で `9 ∣ |N| ∣ 144`, つまり `|N| ∈ {9, 18, 36, 72, 144}`:

* `9`: `S = N = T` で `S ≠ T` に矛盾。
* `18 = 2·3²`: 位数 18 の群の Sylow `3` は一意 (`2 % 3 ≠ 1`) なのに `S ≠ T` が両方入る。
* `36`: 指数 4 で `144 ∣ 4! = 24` が偽。
* `72`: 指数 2 で `144 ∣ 2! = 2` が偽。
* `144`: `D ⊴ G` で `1 < |D| = 3 < 144`, 単純性に矛盾。 -/
theorem not_isSimpleGroup_of_card_eq_onefourfour {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 144) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdec : ∀ P : Sylow 3 G,
      Nat.card ↥(P : Subgroup G) = 9 ∧ (P : Subgroup G).index = 16 := fun P => by
    have h := sylow_card_and_index_of_card_eq_mul (q := 3) (m := 16) (k := 2)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨h.1.trans (by norm_num), h.2⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 G) := Sylow.nonempty
  have hn3mod : Nat.card (Sylow 3 G) % 3 = 1 := card_sylow_mod_eq_one 3
  have hn3ne1 : Nat.card (Sylow 3 G) ≠ 1 :=
    card_sylow_ne_one_of_simple S₀ (by rw [(hdec S₀).1]; norm_num)
      (by rw [(hdec S₀).1, hG]; norm_num)
  -- `n₃ ∈ {1, 4, 16}`
  have hn3dvd : Nat.card (Sylow 3 G) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact (hdec S₀).2 ▸ Sylow.card_dvd_index S₀
  obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hn3dvd
  have hn3 : Nat.card (Sylow 3 G) = 4 ∨ Nat.card (Sylow 3 G) = 16 := by
    interval_cases i
    · exact absurd (by simpa using hni) hn3ne1
    · rw [hni] at hn3mod; norm_num at hn3mod
    · left; simpa using hni
    · rw [hni] at hn3mod; norm_num at hn3mod
    · right; simpa using hni
  rcases hn3 with hn4 | hn16
  · -- `n₃ = 4`: `N_G(S₀)` の指数が 4 で `144 ∣ 4! = 24` が偽
    have hidx : (Subgroup.normalizer ((S₀ : Subgroup G) : Set G)).index = 4 := by
      rw [Sylow.coe_coe, ← Sylow.card_eq_index_normalizer S₀]; exact hn4
    have hdvd := card_dvd_factorial_of_simple_subgroup_index
      (Subgroup.normalizer ((S₀ : Subgroup G) : Set G)) (by rw [hidx]; norm_num)
    rw [hG, hidx] at hdvd
    norm_num [Nat.factorial] at hdvd
  -- `n₃ = 16`: 交わり最大の対から `|D| = 3`
  have hgt : 1 < Nat.card (Sylow 3 G) := by rw [hn16]; norm_num
  obtain ⟨S, T, hST, hmax⟩ := exists_max_inter_sylow_pair (q := 3) hgt
  have hmod := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
  rw [hn16] at hmod
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hd_dvd15 : D.relIndex (S : Subgroup G) ∣ 15 := by
    have h := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 16)).mp hmod.symm
    norm_num at h; exact h
  have hd_dvd9 : D.relIndex (S : Subgroup G) ∣ 9 := by
    have hh := Subgroup.index_dvd_card (D.subgroupOf (S : Subgroup G))
    rw [(hdec S).1] at hh
    exact hh
  have hd_ne1 : D.relIndex (S : Subgroup G) ≠ 1 := by
    intro h1
    exact hST (Sylow.ext (Subgroup.eq_of_le_of_card_ge
      ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
      (((hdec T).1).trans ((hdec S).1).symm).le))
  have hd3 : D.relIndex (S : Subgroup G) = 3 := by
    have hg : D.relIndex (S : Subgroup G) ∣ 3 := by
      have h := Nat.dvd_gcd hd_dvd15 hd_dvd9
      norm_num at h; exact h
    rcases (Nat.dvd_prime (by norm_num)).mp hg with h | h
    · exact absurd h hd_ne1
    · exact h
  have hidx3S : (D.subgroupOf (S : Subgroup G)).index = 3 := hd3
  have hDcard : Nat.card ↥D = 3 := by
    have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx3S, (hdec S).1] at heq
    rw [← hDdef] at heq
    omega
  -- `S`, `T ≤ N := N_G(D)` で `|N| = 9·e`, `e ∣ 16`
  have hS_le : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_of_card_eq_prime_sq (p := 3) (((hdec S).1).trans (by norm_num)) inf_le_left
  have hT_le : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_of_card_eq_prime_sq (p := 3) (((hdec T).1).trans (by norm_num)) inf_le_right
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  have hNdvd : Nat.card ↥N ∣ 144 := hG ▸ Subgroup.card_subgroup_dvd_card N
  obtain ⟨e, he⟩ : (9 : ℕ) ∣ Nat.card ↥N := ((hdec S).1) ▸ Subgroup.card_dvd_of_le hS_le
  have hedvd : e ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact (mul_dvd_mul_iff_left (by norm_num : (9 : ℕ) ≠ 0)).mp (by rw [← he]; simpa using hNdvd)
  obtain ⟨j, hj, hej⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hedvd
  -- 指数から `Cor 1.3` を当てる共通形
  have hindex_absurd : ∀ n : ℕ, Nat.card ↥N * n = 144 → 1 < n → n < 5 → False := by
    intro n hmul hn1 hn5
    have hidx : N.index = n := by
      have h := Subgroup.card_mul_index N
      rw [hG] at h
      have hpos : 0 < Nat.card ↥N := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (h.trans hmul.symm)
    have hdvd := card_dvd_factorial_of_simple_subgroup_index N (by rw [hidx]; omega)
    rw [hG, hidx] at hdvd
    interval_cases n <;> norm_num [Nat.factorial] at hdvd
  interval_cases j <;> rw [hej] at he <;> norm_num at he
  · -- `|N| = 9`: `S = N = T`
    exact hST (Sylow.ext ((Subgroup.eq_of_le_of_card_ge hS_le (he ▸ ((hdec S).1).ge)).trans
      (Subgroup.eq_of_le_of_card_ge hT_le (he ▸ ((hdec T).1).ge)).symm))
  · -- `|N| = 18`: 位数 18 の群の Sylow `3` は一意
    haveI : Subsingleton (Sylow 3 ↥N) :=
      (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one_of_card_eq_prime_mul_pow
        (q := 3) (ℓ := 2) (k := 2) (by norm_num) (by rw [he]; norm_num) (by norm_num)
        (by norm_num))).1
    exact hST (Sylow.subtype_injective (hP := hS_le) (hQ := hT_le) (Subsingleton.elim _ _))
  · -- `|N| = 36`: 指数 4
    exact hindex_absurd 4 (by rw [he]) (by norm_num) (by norm_num)
  · -- `|N| = 72`: 指数 2
    exact hindex_absurd 2 (by rw [he]) (by norm_num) (by norm_num)
  · -- `|N| = 144`: `D ⊴ G`
    have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [he, hG])
    rcases hsimple.eq_bot_or_eq_top_of_normal _
      (Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)) with h1 | h1
    · rw [h1, Subgroup.card_bot] at hDcard; norm_num at hDcard
    · rw [h1, Subgroup.card_top, hG] at hDcard; norm_num at hDcard

end -- Problem 1E.4

section /- 1E: 単純群の交代群への埋め込み (1E.5 の準備) -/

/-- **単純群の `Aₙ` への埋め込み**。単純群 `G` (`2 < |G|`) が指数 `n > 1` の部分群 `H` を
もつなら, 剰余類集合 `G ⧸ H` への作用は `G` を `Fin n` 上の交代群に単射に埋め込む。

`G ⧸ H` への作用の核は `core_G(H)` で, 単純性と `n > 1` から `⊥` (**Cor 1.2/1.3** と同じ
議論)。よって `G ↪ Sym(G ⧸ H) ≃ Sₙ`。さらに `sign` との合成の核も正規なので `⊥` か `⊤`
だが, `⊥` なら `G ↪ ℤˣ` で `|G| ≤ 2` に反するので `⊤`, すなわち像は `Aₙ` に入る。 -/
theorem exists_injective_hom_alternating_of_simple {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {H : Subgroup G} {n : ℕ} (hidx : H.index = n) (hn : 1 < n)
    (hG : 2 < Nat.card G) :
    ∃ f : G →* ↥(alternatingGroup (Fin n)), Function.Injective f := by
  classical
  haveI : Finite (G ⧸ H) := Subgroup.index_ne_zero_iff_finite.mp (by omega)
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) = n := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact hidx
  set e : (G ⧸ H) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  set φ : G →* Equiv.Perm (Fin n) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)) with hφ
  -- `φ` は単射 (核は `core_G(H)`, 単純性と `n > 1` から `⊥`)
  have hkerφ : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with h | h
    · exact h
    · exfalso
      have htop : (MulAction.toPermHom G (G ⧸ H)).ker = ⊤ := by
        refine eq_top_iff.mpr fun g _ => ?_
        have hg : φ g = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
        rw [MonoidHom.mem_ker]
        refine (Equiv.permCongrHom e).injective ?_
        rw [map_one]
        simpa [hφ] using hg
      rw [← Subgroup.normalCore_eq_ker] at htop
      have hHtop : H = ⊤ := le_antisymm le_top (htop ▸ H.normalCore_le)
      rw [hHtop, Subgroup.index_top] at hidx
      omega
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerφ
  -- 像は `Aₙ` に入る (`sign ∘ φ` の核が `⊥` なら `G ↪ ℤˣ` で `|G| ≤ 2`)
  have hmem : ∀ g : G, φ g ∈ alternatingGroup (Fin n) := by
    set ψ : G →* ℤˣ := (Equiv.Perm.sign).comp φ
    have hkerψ : ψ.ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker inferInstance with h | h
      · exfalso
        have hle := Nat.card_le_card_of_injective ψ ((MonoidHom.ker_eq_bot_iff ψ).mp h)
        rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at hle
        omega
      · exact h
    intro g
    rw [Equiv.Perm.mem_alternatingGroup]
    have hg : g ∈ ψ.ker := hkerψ ▸ Subgroup.mem_top g
    rwa [MonoidHom.mem_ker] at hg
  exact ⟨φ.codRestrict _ hmem, fun a b hab => hinj (congrArg Subtype.val hab)⟩

end -- 単純群の交代群への埋め込み

section /- 1E: Problem 1E.5 (p. 38) -/

/-- `n ∣ 48` かつ `n ≡ 1 (mod 7)` なら `n = 1` または `n = 8`。 -/
private lemma eq_one_or_eight_of_dvd_fortyeight {n : ℕ} (h : n ∣ 48) (hm : n % 7 = 1) :
    n = 1 ∨ n = 8 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 48 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h hm <;> decide

/-- **Isaacs Problem 1E.5** (p. 38)。位数 `336 = 2⁴·3·7` の単純群は存在しない。

書籍の Hint どおり `n₇` を計算して **Problem 1C.5** を使う。`n₇ ∣ [G : P] = 48` と
`n₇ ≡ 1 (mod 7)` から `n₇ ∈ {1, 8}` で, 単純性より `n₇ = 8`。すると
`N := N_G(P)` は指数 8, 位数 `336 / 8 = 42`。単純群は指数 8 の部分群をもつので
`G ↪ A₈` (`exists_injective_hom_alternating_of_simple`)。`P` の像 `Q` は位数 7 で,
`|A₈| = 8!/2 = 20160 = 2880·7` だから `Q` は `A₈` の Sylow `7`-部分群。`N` の像は
`N_{A₈}(Q)` に入るので `42 ≤ |N_{A₈}(Q)|` だが, **1C.5**
(`card_normalizer_sylow_alternating`) は `|N_{A₈}(Q)| = 7·6/2 = 21` を与える。矛盾。 -/
theorem not_isSimpleGroup_of_card_eq_threethreesix {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 336) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := Sylow.nonempty
  obtain ⟨hPcard, hPindex⟩ := sylow_card_and_index_of_card_eq_mul (q := 7) (m := 48) (k := 1)
    (by rw [hG]; norm_num) (by norm_num) P
  rw [pow_one] at hPcard
  -- `n₇ = 8`
  have hn7 : Nat.card (Sylow 7 G) = 8 := by
    rcases eq_one_or_eight_of_dvd_fortyeight (hPindex ▸ Sylow.card_dvd_index P)
      (card_sylow_mod_eq_one 7) with h | h
    · exact absurd h (card_sylow_ne_one_of_simple P (by rw [hPcard]; norm_num)
        (by rw [hPcard, hG]; norm_num))
    · exact h
  -- `N := N_G(P)` は指数 8, 位数 42
  set N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
  have hNindex : N.index = 7 + 1 := by
    rw [hNdef, Sylow.coe_coe, ← Sylow.card_eq_index_normalizer P, hn7]
  have hNcard : Nat.card ↥N = 42 := by
    have h := Subgroup.card_mul_index N
    rw [hNindex, hG] at h
    omega
  -- `G ↪ A₈`
  obtain ⟨f, hfinj⟩ := exists_injective_hom_alternating_of_simple (H := N) (n := 7 + 1)
    hNindex (by norm_num) (by rw [hG]; norm_num)
  -- `|A₈| = 20160`
  have hAcard : Nat.card ↥(alternatingGroup (Fin (7 + 1))) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  -- `Q := f(P)` は `A₈` の Sylow `7`-部分群
  set Q : Subgroup ↥(alternatingGroup (Fin (7 + 1))) := (P : Subgroup G).map f with hQdef
  have hQcard : Nat.card ↥Q = 7 := by
    rw [hQdef, Subgroup.card_map_of_injective hfinj, hPcard]
  have hQsylow : Nat.card ↥Q
      = 7 ^ (Nat.card ↥(alternatingGroup (Fin (7 + 1)))).factorization 7 := by
    rw [hQcard, hAcard, factorization_of_eq_mul_pow (q := 7) (m := 2880) (k := 1)
      (by norm_num) (by norm_num) (by norm_num), pow_one]
  set R : Sylow 7 ↥(alternatingGroup (Fin (7 + 1))) := Sylow.ofCard Q hQsylow with hRdef
  have hRcoe : (R : Subgroup ↥(alternatingGroup (Fin (7 + 1)))) = Q :=
    Sylow.coe_ofCard Q hQsylow
  -- **1C.5**: `|N_{A₈}(Q)| = 21`
  have h21 : Nat.card
      ↥(Subgroup.normalizer (R : Set ↥(alternatingGroup (Fin (7 + 1))))) = 21 := by
    have h := card_normalizer_sylow_alternating (p := 7) (by norm_num) R
    rwa [show 7 * (7 - 1) / 2 = 21 from by norm_num] at h
  -- `f(N) ≤ N_{A₈}(Q)`
  have hmapN : N.map f ≤ Subgroup.normalizer ((Q : Subgroup _) : Set _) := by
    rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    have hxn := Subgroup.mem_normalizer_iff.mp hx
    have hxin := Subgroup.mem_normalizer_iff.mp (N.inv_mem hx)
    intro h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
      refine Subgroup.mem_map.mpr ⟨x * g * x⁻¹, (hxn g).mp hg, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hh
      obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hh
      have hmem : x⁻¹ * g * x ∈ (P : Subgroup G) := by
        have hc := (hxin g).mp hg
        rwa [inv_inv] at hc
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * g * x, hmem, ?_⟩
      rw [map_mul, map_mul, map_inv, hgeq]
      group
  -- `42 ≤ 21` は偽
  have hle : Nat.card ↥(N.map f) ≤
      Nat.card ↥(Subgroup.normalizer ((Q : Subgroup _) : Set _)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hmapN)
  rw [Subgroup.card_map_of_injective hfinj, hNcard, ← hRcoe, Sylow.coe_coe] at hle
  omega

end -- Problem 1E.5

section /- 1E: 追加の共通部品 (1E.6 以降) -/

/-- 単純群 `G` (`2 < |G|`) が指数 `n` (`5 ≤ n`) の部分群をもつとき, `|G|` は `|Aₙ|` の
ちょうど半分にはなれない。

半分なら `G ↪ Aₙ` の像は指数 2 の部分群で正規になるが, `Aₙ` (`n ≥ 5`) は単純なので
像は `⊥` か `⊤`, どちらも位数と矛盾する。 -/
theorem two_mul_card_ne_card_alternating_of_simple {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {H : Subgroup G} {n : ℕ} (hidx : H.index = n) (hn : 5 ≤ n)
    (hG : 2 < Nat.card G) :
    2 * Nat.card G ≠ Nat.card ↥(alternatingGroup (Fin n)) := by
  intro heq
  obtain ⟨f, hfinj⟩ :=
    exists_injective_hom_alternating_of_simple hidx (by omega) hG
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hrange : Nat.card ↥f.range = Nat.card G := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfinj, Subgroup.card_top]
  have hmul := Subgroup.card_mul_index f.range
  rw [hrange] at hmul
  have hidx2 : f.range.index = 2 := by
    have hpos : 0 < Nat.card G := by omega
    have h2 : Nat.card G * f.range.index = Nat.card G * 2 := by rw [hmul, ← heq]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  haveI : f.range.Normal := Subgroup.normal_of_index_eq_two hidx2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.range inferInstance with h | h
  · rw [h, Subgroup.card_bot] at hrange; omega
  · rw [h, Subgroup.index_top] at hidx2; omega

/-- 相異なる Sylow `q`-部分群が自明にしか交わらないなら, それらの非単位元全体は
`n_q·(m − 1)` 個の Finset をなす (`m` は Sylow の位数; 各元の位数は `m` を割る)。

他の素数の元の個数と足し合わせて `|G|` を超えさせる, という計数に使う。 -/
theorem exists_finset_of_sylow_inter_trivial {G : Type*} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] (htriv : ∀ S T : Sylow q G, S ≠ T →
      (S : Subgroup G) ⊓ (T : Subgroup G) = ⊥)
    {m : ℕ} (hm : ∀ S : Sylow q G, Nat.card ↥(S : Subgroup G) = m) :
    ∃ U : Finset G, U.card = Nat.card (Sylow q G) * (m - 1) ∧
      ∀ x ∈ U, x ≠ 1 ∧ orderOf x ∣ m := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  set A : Sylow q G → Finset G := fun S => ((S : Subgroup G) : Set G).toFinset.erase 1 with hA
  have hcardA : ∀ S : Sylow q G, (A S).card = m - 1 := by
    intro S
    have h1 : ((S : Subgroup G) : Set G).toFinset.card = m := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, ← hm S]
      rfl
    rw [hA, Finset.card_erase_of_mem (Set.mem_toFinset.mpr (one_mem _)), h1]
  have hdisj : ∀ S ∈ (Finset.univ : Finset (Sylow q G)), ∀ T ∈ (Finset.univ : Finset (Sylow q G)),
      S ≠ T → Disjoint (A S) (A T) := by
    intro S _ T _ hne
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hx1 : x ≠ 1 := (Finset.mem_erase.mp hxS).1
    have hmem : x ∈ (S : Subgroup G) ⊓ (T : Subgroup G) :=
      ⟨Set.mem_toFinset.mp (Finset.mem_erase.mp hxS).2,
        Set.mem_toFinset.mp (Finset.mem_erase.mp hxT).2⟩
    rw [htriv S T hne, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  refine ⟨Finset.univ.biUnion A, ?_, ?_⟩
  · have hbi := Finset.card_biUnion hdisj
    rwa [Finset.sum_congr rfl (fun S _ => hcardA S), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Nat.card_eq_fintype_card] at hbi
  · intro x hx
    obtain ⟨S, -, hxS⟩ := Finset.mem_biUnion.mp hx
    refine ⟨(Finset.mem_erase.mp hxS).1, ?_⟩
    have hmem : x ∈ (S : Subgroup G) := Set.mem_toFinset.mp (Finset.mem_erase.mp hxS).2
    rw [← hm S, ← Subgroup.orderOf_mk x hmem]
    exact orderOf_dvd_natCard _

end -- 追加の共通部品

section /- 1E: Problem 1E.6 (p. 38) -/

/-- `n ∣ 36` かつ `n ≡ 1 (mod 5)` なら `n ∈ {1, 6, 36}`。 -/
private lemma eq_of_dvd_thirtysix {n : ℕ} (h : n ∣ 36) (hm : n % 5 = 1) :
    n = 1 ∨ n = 6 ∨ n = 36 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 36 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h hm <;> decide

/-- `n ∣ 20` かつ `n ≡ 1 (mod 3)` なら `n ∈ {1, 4, 10}`。 -/
private lemma eq_of_dvd_twenty {n : ℕ} (h : n ∣ 20) (hm : n % 3 = 1) :
    n = 1 ∨ n = 4 ∨ n = 10 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 20 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h hm <;> decide

/-- `20` の約数は `1, 2, 4, 5, 10, 20`。 -/
private lemma divisors_twenty {n : ℕ} (h : n ∣ 20) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 5 ∨ n = 10 ∨ n = 20 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 20 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h <;> decide

/-- **Isaacs Problem 1E.6** (p. 38)。位数 `180 = 2²·3²·5` の単純群は存在しない。

`n₅ ∣ [G : P₅] = 36` と `n₅ ≡ 1 (mod 5)` から `n₅ ∈ {1, 6, 36}`。単純性で `n₅ ≠ 1`。

* `n₅ = 6`: `N_G(P₅)` は指数 6 で `|A₆| = 6!/2 = 360 = 2·180`, つまり像が `A₆` の
  指数 2 の部分群になり `A₆` の単純性に反する
  (`two_mul_card_ne_card_alternating_of_simple`)。
* `n₅ = 36`: 位数 5 の元が `36·4 = 144` 個。Sylow `3` は位数 9・指数 20 で
  `n₃ ∈ {1, 4, 10}`。`n₃ = 4` は指数 4 で `180 ∣ 4! = 24` が偽。`n₃ = 10` では
  **Thm 1.16** が `|S : D| ∈ {3, 9}` を与え,
  - `|S : D| = 9` (`D = ⊥`, 最大性より全対が自明交叉): 3-冪位数の非単位元が `10·8 = 80` 個で
    位数 5 の 144 個と交わらず `80 + 144 + 1 = 225 > 180` で矛盾。
  - `|S : D| = 3` (`|D| = 3`): `S`, `T ≤ N := N_G(D)` で `9 ∣ |N| ∣ 180`,
    `|N| ∈ {9, 18, 36, 45, 90, 180}` を全て潰す。 -/
theorem not_isSimpleGroup_of_card_eq_oneeighty {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 180) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h5dec : ∀ P : Sylow 5 G,
      Nat.card ↥(P : Subgroup G) = 5 ∧ (P : Subgroup G).index = 36 := fun P => by
    have hh := sylow_card_and_index_of_card_eq_mul (q := 5) (m := 36) (k := 1)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨hh.1.trans (by norm_num), hh.2⟩
  obtain ⟨P₅⟩ : Nonempty (Sylow 5 G) := Sylow.nonempty
  have hn5ne1 : Nat.card (Sylow 5 G) ≠ 1 :=
    card_sylow_ne_one_of_simple P₅ (by rw [(h5dec P₅).1]; norm_num)
      (by rw [(h5dec P₅).1, hG]; norm_num)
  rcases eq_of_dvd_thirtysix ((h5dec P₅).2 ▸ Sylow.card_dvd_index P₅)
    (card_sylow_mod_eq_one 5) with h | h | h
  · exact hn5ne1 h
  · -- `n₅ = 6`: `|A₆| = 360 = 2 · 180`
    refine two_mul_card_ne_card_alternating_of_simple
      (H := Subgroup.normalizer ((P₅ : Subgroup G) : Set G)) (n := 6)
      (by rw [Sylow.coe_coe, ← Sylow.card_eq_index_normalizer P₅]; exact h)
      (by norm_num) (by rw [hG]; norm_num) ?_
    rw [hG, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  -- `n₅ = 36`: 位数 5 の元が 144 個
  obtain ⟨U₅, hU₅card, hU₅⟩ :=
    exists_finset_orderOf_eq_card_sylow_mul (q := 5) (fun P => (h5dec P).1)
  rw [h] at hU₅card
  norm_num at hU₅card
  have h3dec : ∀ P : Sylow 3 G,
      Nat.card ↥(P : Subgroup G) = 9 ∧ (P : Subgroup G).index = 20 := fun P => by
    have hh := sylow_card_and_index_of_card_eq_mul (q := 3) (m := 20) (k := 2)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨hh.1.trans (by norm_num), hh.2⟩
  obtain ⟨P₃⟩ : Nonempty (Sylow 3 G) := Sylow.nonempty
  have hn3ne1 : Nat.card (Sylow 3 G) ≠ 1 :=
    card_sylow_ne_one_of_simple P₃ (by rw [(h3dec P₃).1]; norm_num)
      (by rw [(h3dec P₃).1, hG]; norm_num)
  rcases eq_of_dvd_twenty ((h3dec P₃).2 ▸ Sylow.card_dvd_index P₃)
    (card_sylow_mod_eq_one 3) with h3 | h3 | h3
  · exact hn3ne1 h3
  · -- `n₃ = 4`: 指数 4 で `180 ∣ 4! = 24` が偽
    have hidx : (Subgroup.normalizer ((P₃ : Subgroup G) : Set G)).index = 4 := by
      rw [Sylow.coe_coe, ← Sylow.card_eq_index_normalizer P₃]; exact h3
    have hdvd := card_dvd_factorial_of_simple_subgroup_index
      (Subgroup.normalizer ((P₃ : Subgroup G) : Set G)) (by rw [hidx]; norm_num)
    rw [hG, hidx] at hdvd
    norm_num [Nat.factorial] at hdvd
  -- `n₃ = 10`: 交わり最大対
  have hgt : 1 < Nat.card (Sylow 3 G) := by rw [h3]; norm_num
  obtain ⟨S, T, hST, hmax⟩ := exists_max_inter_sylow_pair (q := 3) hgt
  have hmodT := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
  rw [h3] at hmodT
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hd_dvd9 : D.relIndex (S : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    have hh := Subgroup.index_dvd_card (D.subgroupOf (S : Subgroup G))
    rw [(h3dec S).1] at hh
    exact hh
  have hd_ne1 : D.relIndex (S : Subgroup G) ≠ 1 := by
    intro h1
    exact hST (Sylow.ext (Subgroup.eq_of_le_of_card_ge
      ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
      (((h3dec T).1).trans ((h3dec S).1).symm).le))
  obtain ⟨i, hi, hdi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hd_dvd9
  interval_cases i
  · exact hd_ne1 (by simpa using hdi)
  · -- `|S : D| = 3` ⟹ `|D| = 3`, `N := N_G(D)` の位数で場合分け
    have hd3 : D.relIndex (S : Subgroup G) = 3 := by rw [hdi]; norm_num
    have hidx3S : (D.subgroupOf (S : Subgroup G)).index = 3 := hd3
    have hDcard : Nat.card ↥D = 3 := by
      have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx3S, (h3dec S).1] at heq
      rw [← hDdef] at heq
      omega
    have hS_le : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
      le_normalizer_of_card_eq_prime_sq (p := 3) (((h3dec S).1).trans (by norm_num)) inf_le_left
    have hT_le : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
      le_normalizer_of_card_eq_prime_sq (p := 3) (((h3dec T).1).trans (by norm_num)) inf_le_right
    set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
    have hNdvd : Nat.card ↥N ∣ 180 := hG ▸ Subgroup.card_subgroup_dvd_card N
    obtain ⟨e, he⟩ : (9 : ℕ) ∣ Nat.card ↥N := ((h3dec S).1) ▸ Subgroup.card_dvd_of_le hS_le
    have hedvd : e ∣ 20 :=
      (mul_dvd_mul_iff_left (by norm_num : (9 : ℕ) ≠ 0)).mp (by rw [← he]; simpa using hNdvd)
    -- 指数から Cor 1.3 を当てる共通形
    have hindex_absurd : ∀ n : ℕ, Nat.card ↥N * n = 180 → 1 < n → n < 6 → False := by
      intro n hmul hn1 hn6
      have hidx : N.index = n := by
        have hh := Subgroup.card_mul_index N
        rw [hG] at hh
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans hmul.symm)
      have hdvd := card_dvd_factorial_of_simple_subgroup_index N (by rw [hidx]; omega)
      rw [hG, hidx] at hdvd
      interval_cases n <;> norm_num [Nat.factorial] at hdvd
    -- `N` の Sylow `3` が一意なら `S = T` で矛盾
    have hSylowUnique : ∀ ℓ : ℕ, ℓ.Prime → Nat.card ↥N = ℓ * 3 ^ 2 → ¬ 3 ∣ ℓ →
        ℓ % 3 ≠ 1 → False := by
      intro ℓ hℓ hNc hnd hmod
      haveI : Subsingleton (Sylow 3 ↥N) :=
        (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one_of_card_eq_prime_mul_pow
          (q := 3) (ℓ := ℓ) (k := 2) hℓ hNc hnd hmod)).1
      exact hST (Sylow.subtype_injective (hP := hS_le) (hQ := hT_le) (Subsingleton.elim _ _))
    rcases divisors_twenty hedvd with he1 | he1 | he1 | he1 | he1 | he1
    · -- `|N| = 9`: `S = N = T`
      have heN : Nat.card ↥N = 9 := by rw [he, he1, mul_one]
      exact hST (Sylow.ext
        ((Subgroup.eq_of_le_of_card_ge hS_le (le_of_eq (by rw [heN, (h3dec S).1]))).trans
          (Subgroup.eq_of_le_of_card_ge hT_le (le_of_eq (by rw [heN, (h3dec T).1]))).symm))
    · exact hSylowUnique 2 (by norm_num) (by rw [he, he1]; norm_num) (by norm_num) (by norm_num)
    · exact hindex_absurd 5 (by rw [he, he1]) (by norm_num) (by norm_num)
    · exact hSylowUnique 5 (by norm_num) (by rw [he, he1]; norm_num) (by norm_num) (by norm_num)
    · exact hindex_absurd 2 (by rw [he, he1]) (by norm_num) (by norm_num)
    · -- `|N| = 180`: `D ⊴ G`
      have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [he, he1, hG])
      rcases hsimple.eq_bot_or_eq_top_of_normal _
        (Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)) with h1 | h1
      · rw [h1, Subgroup.card_bot] at hDcard; norm_num at hDcard
      · rw [h1, Subgroup.card_top, hG] at hDcard; norm_num at hDcard
  · -- `|S : D| = 9` ⟹ `D = ⊥`, 最大性より全対が自明交叉 ⟹ 計数矛盾
    have hd9 : D.relIndex (S : Subgroup G) = 9 := by rw [hdi]; norm_num
    have hidx9S : (D.subgroupOf (S : Subgroup G)).index = 9 := hd9
    have hDcard1 : Nat.card ↥D = 1 := by
      have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx9S, (h3dec S).1] at heq
      rw [← hDdef] at heq
      omega
    have htriv : ∀ S' T' : Sylow 3 G, S' ≠ T' →
        (S' : Subgroup G) ⊓ (T' : Subgroup G) = ⊥ := by
      intro S' T' hne
      have hle := hmax S' T' hne
      rw [hDcard1] at hle
      exact Subgroup.eq_bot_of_card_le _ hle
    obtain ⟨U₃, hU₃card, hU₃⟩ :=
      exists_finset_of_sylow_inter_trivial (q := 3) htriv (fun S' => (h3dec S').1)
    rw [h3] at hU₃card
    norm_num at hU₃card
    have hdisj : Disjoint U₃ U₅ := by
      rw [Finset.disjoint_left]
      intro x hx3 hx5
      have hd9 := (hU₃ x hx3).2
      rw [(hU₅ x).mp hx5] at hd9
      norm_num at hd9
    have hnotin : (1 : G) ∉ U₃ ∪ U₅ := by
      simp only [Finset.mem_union, not_or]
      refine ⟨fun hc => (hU₃ 1 hc).1 rfl, fun hc => ?_⟩
      have h1 := (hU₅ 1).mp hc
      rw [orderOf_one] at h1
      norm_num at h1
    have hle : (insert (1 : G) (U₃ ∪ U₅)).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_insert_of_notMem hnotin, Finset.card_union_of_disjoint hdisj,
      hU₃card, hU₅card, hG] at hle
    omega

end -- Problem 1E.6

section /- 1E: Problem 1E.7 (p. 38) -/

/-- `15` の約数は `1, 3, 5, 15`。 -/
private lemma divisors_fifteen {n : ℕ} (h : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 15 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h <;> decide

/-- 単純群では Sylow `q`-部分群が複数あれば `|G| ∣ n_q !` (**Cor 1.3** を正規化群に当てる)。 -/
theorem card_dvd_factorial_card_sylow_of_simple {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {q : ℕ} [Fact q.Prime] (P : Sylow q G)
    (hgt : 1 < Nat.card (Sylow q G)) :
    Nat.card G ∣ Nat.factorial (Nat.card (Sylow q G)) := by
  have hidx : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index
      = Nat.card (Sylow q G) := by
    rw [Sylow.coe_coe, ← Sylow.card_eq_index_normalizer P]
  have h := card_dvd_factorial_of_simple_subgroup_index
    (Subgroup.normalizer ((P : Subgroup G) : Set G)) (by rw [hidx]; exact hgt)
  rwa [hidx] at h

/-- **Isaacs Problem 1E.7** (p. 38)。位数 `240 = 2⁴·3·5` の単純群は存在しない。

Sylow `2` で押す。`n₂ ∣ [G : S] = 15` は奇数なので `n₂ ∈ {1, 3, 5, 15}`。単純性で `n₂ ≠ 1`,
`n₂ = 3` は `240 ∣ 3! = 6`, `n₂ = 5` は `240 ∣ 5! = 120` がどちらも偽 (**Cor 1.3**)。
残る `n₂ = 15` では交わり最大の Sylow `2` 対 `S ≠ T` に **Thm 1.16** を当てて
`15 ≡ 1 (mod |S : D|)`, つまり `|S : D| ∣ gcd(14, 16) = 2` と `≠ 1` から `|S : D| = 2`,
`|D| = 8`。指数 2 ゆえ `D` は `S`, `T` の双方で正規で `S`, `T ≤ N := N_G(D)`,
`16 ∣ |N| ∣ 240` から `|N| ∈ {16, 48, 80, 240}`:

* `16`: `S = N = T` で `S ≠ T` に矛盾。
* `48`: 指数 5 で `240 ∣ 5! = 120` が偽。
* `80`: 指数 3 で `240 ∣ 3! = 6` が偽。
* `240`: `D ⊴ G` で `1 < |D| = 8 < 240`, 単純性に矛盾。 -/
theorem not_isSimpleGroup_of_card_eq_twofourty {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 240) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hdec : ∀ P : Sylow 2 G,
      Nat.card ↥(P : Subgroup G) = 16 ∧ (P : Subgroup G).index = 15 := fun P => by
    have hh := sylow_card_and_index_of_card_eq_mul (q := 2) (m := 15) (k := 4)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨hh.1.trans (by norm_num), hh.2⟩
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 G) := Sylow.nonempty
  have hne1 : Nat.card (Sylow 2 G) ≠ 1 :=
    card_sylow_ne_one_of_simple P₂ (by rw [(hdec P₂).1]; norm_num)
      (by rw [(hdec P₂).1, hG]; norm_num)
  -- `n₂ = 15`
  have hn2 : Nat.card (Sylow 2 G) = 15 := by
    rcases divisors_fifteen ((hdec P₂).2 ▸ Sylow.card_dvd_index P₂) with h | h | h | h
    · exact absurd h hne1
    · exfalso
      have hd := card_dvd_factorial_card_sylow_of_simple P₂ (by rw [h]; norm_num)
      rw [hG, h] at hd
      norm_num [Nat.factorial] at hd
    · exfalso
      have hd := card_dvd_factorial_card_sylow_of_simple P₂ (by rw [h]; norm_num)
      rw [hG, h] at hd
      norm_num [Nat.factorial] at hd
    · exact h
  -- 交わり最大の対から `|D| = 8`
  have hgt : 1 < Nat.card (Sylow 2 G) := by rw [hn2]; norm_num
  obtain ⟨S, T, hST, hmax⟩ := exists_max_inter_sylow_pair (q := 2) hgt
  have hmodT := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
  rw [hn2] at hmodT
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hd_dvd14 : D.relIndex (S : Subgroup G) ∣ 14 := by
    have hh := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 15)).mp hmodT.symm
    norm_num at hh; exact hh
  have hd_dvd16 : D.relIndex (S : Subgroup G) ∣ 16 := by
    have hh := Subgroup.index_dvd_card (D.subgroupOf (S : Subgroup G))
    rw [(hdec S).1] at hh
    exact hh
  have hd_ne1 : D.relIndex (S : Subgroup G) ≠ 1 := by
    intro h1
    exact hST (Sylow.ext (Subgroup.eq_of_le_of_card_ge
      ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
      (((hdec T).1).trans ((hdec S).1).symm).le))
  have hd2 : D.relIndex (S : Subgroup G) = 2 := by
    have hg : D.relIndex (S : Subgroup G) ∣ 2 := by
      have hh := Nat.dvd_gcd hd_dvd14 hd_dvd16
      norm_num at hh; exact hh
    rcases (Nat.dvd_prime (by norm_num)).mp hg with h | h
    · exact absurd h hd_ne1
    · exact h
  have hidx2S : (D.subgroupOf (S : Subgroup G)).index = 2 := hd2
  have hDcard : Nat.card ↥D = 8 := by
    have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx2S, (hdec S).1] at heq
    rw [← hDdef] at heq
    omega
  have hidx2T : (D.subgroupOf (T : Subgroup G)).index = 2 := by
    have heq := Subgroup.card_mul_index (D.subgroupOf (T : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : D ≤ (T : Subgroup G))).toEquiv, hDcard, (hdec T).1] at heq
    omega
  -- 指数 2 ゆえ `D` は `S`, `T` で正規, したがって `S`, `T ≤ N_G(D)`
  have hS_le : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    have htop := Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_of_index_eq_two hidx2S)
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_left : D ≤ (S : Subgroup G))] at htop
    exact Subgroup.subgroupOf_eq_top.mp htop
  have hT_le : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    have htop := Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_of_index_eq_two hidx2T)
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : D ≤ (T : Subgroup G))] at htop
    exact Subgroup.subgroupOf_eq_top.mp htop
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  have hNdvd : Nat.card ↥N ∣ 240 := hG ▸ Subgroup.card_subgroup_dvd_card N
  obtain ⟨e, he⟩ : (16 : ℕ) ∣ Nat.card ↥N := ((hdec S).1) ▸ Subgroup.card_dvd_of_le hS_le
  have hedvd : e ∣ 15 :=
    (mul_dvd_mul_iff_left (by norm_num : (16 : ℕ) ≠ 0)).mp (by rw [← he]; simpa using hNdvd)
  have hindex_absurd : ∀ n : ℕ, Nat.card ↥N * n = 240 → 1 < n → n < 6 → False := by
    intro n hmul hn1 hn6
    have hidx : N.index = n := by
      have hh := Subgroup.card_mul_index N
      rw [hG] at hh
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans hmul.symm)
    have hdvd := card_dvd_factorial_of_simple_subgroup_index N (by rw [hidx]; omega)
    rw [hG, hidx] at hdvd
    interval_cases n <;> norm_num [Nat.factorial] at hdvd
  rcases divisors_fifteen hedvd with he1 | he1 | he1 | he1
  · -- `|N| = 16`: `S = N = T`
    have heN : Nat.card ↥N = 16 := by rw [he, he1, mul_one]
    exact hST (Sylow.ext
      ((Subgroup.eq_of_le_of_card_ge hS_le (le_of_eq (by rw [heN, (hdec S).1]))).trans
        (Subgroup.eq_of_le_of_card_ge hT_le (le_of_eq (by rw [heN, (hdec T).1]))).symm))
  · exact hindex_absurd 5 (by rw [he, he1]) (by norm_num) (by norm_num)
  · exact hindex_absurd 3 (by rw [he, he1]) (by norm_num) (by norm_num)
  · -- `|N| = 240`: `D ⊴ G`
    have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [he, he1, hG])
    rcases hsimple.eq_bot_or_eq_top_of_normal _
      (Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)) with h1 | h1
    · rw [h1, Subgroup.card_bot] at hDcard; norm_num at hDcard
    · rw [h1, Subgroup.card_top, hG] at hDcard; norm_num at hDcard

end -- Problem 1E.7

end OddOrder.Isaacs.Ch01
