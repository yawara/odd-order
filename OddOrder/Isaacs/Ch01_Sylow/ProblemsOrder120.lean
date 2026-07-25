/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.Basic
import OddOrder.Isaacs.Ch01_Sylow.Theorem131
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs Problem 1C.4 — 位数 120 の群の指数 3 または 5 の部分群

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1C (p. 18) のうち位数 120 の
群についての演習 **1C.4** の形式化 (campaign issue 1055)。

**Problem 1C.4**: `|G| = 120 = 2³·3·5` のとき `G` は指数 3 または指数 5 の部分群を持つ
(hint: `n₂(G)` の 4 通りで場合分け)。

## 証明の構造

`n₂ ∣ [G : P] = 15` から `n₂ ∈ {1, 3, 5, 15}`:

- `n₂ = 3, 5`: `N_G(P)` の指数がちょうど `n₂` (Sylow C の帰結 `Sylow.card_eq_index_normalizer`)。
- `n₂ = 1`: `P ⊴ G` で `P ⊔ F` (`F ∈ Syl₅(G)`) が位数 40 = 指数 3。
- `n₂ = 15`: **Thm 1.16** (`card_sylow_modEq_one_of_max_inter`) — 交わり最大の Sylow 対
  `S ≠ T` で `15 ≡ 1 (mod |S : S∩T|)`。`|S : S∩T|` は 8 の約数かつ 14 の約数で 1 でない
  ⟹ `= 2`。`D := S∩T` は `S`, `T` 双方で指数 2 ゆえ正規 ⟹ `N := N_G(D)` は `S`, `T` を含み
  位数は 8 の倍数・120 の約数・8 超 ⟹ `|N| ∈ {24, 40, 120}`。24 → 指数 5、40 → 指数 3、
  120 → `D ⊴ G` で `G/D` は位数 30 ⟹ 位数 30 の群の補題を quotient に適用し `comap` で
  引き戻す。

支持補題 (どれも一般形で切り出し、他の演習でも再利用可能):

- `card_sup_of_normal_of_coprime`: 正規 `N` と coprime な `S` の join の位数は積。
- `exists_finset_orderOf_eq_card_sylow_mul`: 素数位数 Sylow の非単位元は全体で
  `n_q·(q−1)` 個 (相異なる素数位数 Sylow は自明交叉 `sylow_q_disjoint_of_prime_card`)。
- `card_sylow_mul_add_card_sylow_mul_le`: 2 素数分の計数 `n_{q₁}(q₁−1) + n_{q₂}(q₂−1) ≤ |G|−1`。
- `exists_subgroup_index_eq_three_or_five_of_card_thirty`: 位数 30 の群は指数 3 か 5 の
  部分群を持つ (`n₅ = 6 ∧ n₃ = 10` は計数矛盾 24 + 20 > 29 ⟹ 正規 Sylow 5 か 3 が存在、
  Sylow 2 との join が位数 10 か 6)。
-/

namespace OddOrder.Isaacs.Ch01

section /- 1C: Problem 1C.4 (p. 18) -/

open Pointwise in
/-- 正規部分群 `N` と部分群 `S` の位数が互いに素なら `|N ⊔ S| = |N|·|S|`
(`N ⊔ S = N·S` と積公式 `card_mul_card_inf`、`N ⊓ S = 1`)。 -/
theorem card_sup_of_normal_of_coprime {G : Type*} [Group G] [Finite G]
    {N S : Subgroup G} (hN : N.Normal) (h : Nat.Coprime (Nat.card N) (Nat.card S)) :
    Nat.card ↥(N ⊔ S) = Nat.card N * Nat.card S := by
  haveI := hN
  have hinf : Nat.card ↥(N ⊓ S) = 1 := by
    have hd : Nat.card ↥(N ⊓ S) ∣ Nat.gcd (Nat.card N) (Nat.card S) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)
    rw [Nat.Coprime.gcd_eq_one h] at hd
    exact Nat.dvd_one.mp hd
  have hprod := card_mul_card_inf N S
  rw [hinf, mul_one] at hprod
  have hset : ((N ⊔ S : Subgroup G) : Set G) = (N : Set G) * (S : Set G) :=
    Subgroup.normal_mul N S
  calc Nat.card ↥(N ⊔ S) = Nat.card ((N ⊔ S : Subgroup G) : Set G) := rfl
    _ = Nat.card ((N : Set G) * (S : Set G) : Set G) := by rw [hset]
    _ = Nat.card N * Nat.card S := hprod

open scoped Classical in
/-- Sylow `q`-部分群がどれも素数位数 `q` ちょうどのとき、それらの非単位元を集めた集合は
ちょうど `n_q·(q−1)` 個で、各元の位数は `q` (相異なる素数位数 Sylow の交わりは自明)。 -/
theorem exists_finset_orderOf_eq_card_sylow_mul {G : Type*} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] (hq : ∀ P : Sylow q G, Nat.card (P : Subgroup G) = q) :
    ∃ U : Finset G, U.card = Nat.card (Sylow q G) * (q - 1) ∧ ∀ x ∈ U, orderOf x = q := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  have hqprime : q.Prime := Fact.out
  refine ⟨(Finset.univ : Finset (Sylow q G)).biUnion
      (fun P => (P : Subgroup G).carrier.toFinset \ {1}), ?_, ?_⟩
  · have hf_card : ∀ P : Sylow q G,
        ((P : Subgroup G).carrier.toFinset \ {1}).card = q - 1 := by
      intro P
      have hcard_P : (P : Subgroup G).carrier.toFinset.card = q := by
        rw [Set.toFinset_card]
        change Fintype.card (P : Subgroup G) = q
        rw [← Nat.card_eq_fintype_card]; exact hq P
      have h_sub : ({(1 : G)} : Finset G) ⊆ (P : Subgroup G).carrier.toFinset := by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      rw [Finset.card_sdiff_of_subset h_sub, hcard_P, Finset.card_singleton]
    have hf_pwd : ((Finset.univ : Finset (Sylow q G)) : Set (Sylow q G)).PairwiseDisjoint
        (fun P => (P : Subgroup G).carrier.toFinset \ {1}) := by
      intro P1 _ P2 _ hne
      simp only [Function.onFun, Finset.disjoint_iff_ne]
      rintro x hx y hy rfl
      simp only [Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx hy
      have h_in : x ∈ (P1 : Subgroup G) ⊓ (P2 : Subgroup G) := ⟨hx.1, hy.1⟩
      rw [sylow_q_disjoint_of_prime_card hne (hq P1)] at h_in
      exact hx.2 (Subgroup.mem_bot.mp h_in)
    rw [Finset.card_biUnion hf_pwd]
    simp_rw [hf_card]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  · intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Set.mem_toFinset, Finset.mem_singleton] at hx
    obtain ⟨P, hxP, hx_ne⟩ := hx
    have h_ord_dvd : orderOf (⟨x, hxP⟩ : (P : Subgroup G)) ∣ Nat.card (P : Subgroup G) :=
      orderOf_dvd_natCard _
    rw [hq P, Subgroup.orderOf_mk] at h_ord_dvd
    rcases (Nat.dvd_prime hqprime).mp h_ord_dvd with h1 | hqq
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact hqq

/-- 相異なる素数 `q₁ ≠ q₂` の Sylow がどちらも素数位数ちょうどのとき、位数 `q₁`・`q₂` の
元の計数から `n_{q₁}·(q₁−1) + n_{q₂}·(q₂−1) ≤ |G| − 1`。 -/
theorem card_sylow_mul_add_card_sylow_mul_le {G : Type*} [Group G] [Finite G] {q₁ q₂ : ℕ}
    [Fact q₁.Prime] [Fact q₂.Prime] (hne : q₁ ≠ q₂)
    (h₁ : ∀ P : Sylow q₁ G, Nat.card (P : Subgroup G) = q₁)
    (h₂ : ∀ P : Sylow q₂ G, Nat.card (P : Subgroup G) = q₂) :
    Nat.card (Sylow q₁ G) * (q₁ - 1) + Nat.card (Sylow q₂ G) * (q₂ - 1) ≤ Nat.card G - 1 := by
  haveI : Fintype G := Fintype.ofFinite G
  classical
  obtain ⟨U₁, hU₁card, hU₁ord⟩ := exists_finset_orderOf_eq_card_sylow_mul h₁
  obtain ⟨U₂, hU₂card, hU₂ord⟩ := exists_finset_orderOf_eq_card_sylow_mul h₂
  have hdisj : Disjoint U₁ U₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact hne ((hU₁ord x hx1).symm.trans (hU₂ord x hx2))
  have hsub : U₁ ∪ U₂ ⊆ (Finset.univ : Finset G) \ {1} := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_singleton]
    rintro rfl
    rcases Finset.mem_union.mp hx with hx' | hx'
    · have h := hU₁ord 1 hx'; rw [orderOf_one] at h
      exact (Fact.out (p := q₁.Prime)).one_lt.ne' h.symm
    · have h := hU₂ord 1 hx'; rw [orderOf_one] at h
      exact (Fact.out (p := q₂.Prime)).one_lt.ne' h.symm
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hU₁card, hU₂card] at hle
  have hcard : ((Finset.univ : Finset G) \ {1}).card = Nat.card G - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr (Finset.mem_univ _)),
      Finset.card_univ, Finset.card_singleton, Nat.card_eq_fintype_card]
  rwa [hcard] at hle

/-- `|G| = q·m` (`q` 素数, `q ∤ m`) のとき Sylow `q`-部分群の位数は `q` ちょうど。 -/
theorem sylow_card_eq_prime_of_card_eq_mul {G : Type*} [Group G] [Finite G] {q m : ℕ}
    [Fact q.Prime] (h : Nat.card G = q * m) (hm : ¬ q ∣ m) (hm0 : 0 < m) (P : Sylow q G) :
    Nat.card (P : Subgroup G) = q := by
  have hq : q.Prime := Fact.out
  have hfact : (Nat.card G).factorization q = 1 := by
    rw [h, Nat.factorization_mul hq.pos.ne' hm0.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self hq, Nat.factorization_eq_zero_of_not_dvd hm]
  rw [Sylow.card_eq_multiplicity, hfact, pow_one]

/-- 数値補題: `n ∣ 15`, `n > 0` ⟹ `n ∈ {1, 3, 5, 15}`。 -/
private lemma eq_of_dvd_fifteen {n : ℕ} (h0 : 0 < n) (h : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have h15 : n ≤ 15 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

/-- 数値補題: `n ∣ 6`, `n ≡ 1 (mod 5)` ⟹ `n ∈ {1, 6}`。 -/
private lemma eq_of_dvd_six_mod_five {n : ℕ} (h0 : 0 < n) (h : n ∣ 6) (hm : n % 5 = 1) :
    n = 1 ∨ n = 6 := by
  have h6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

/-- 数値補題: `n ∣ 10`, `n ≡ 1 (mod 3)` ⟹ `n ∈ {1, 10}`。 -/
private lemma eq_of_dvd_ten_mod_three {n : ℕ} (h0 : 0 < n) (h : n ∣ 10) (hm : n % 3 = 1) :
    n = 1 ∨ n = 10 := by
  have h10 : n ≤ 10 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

/-- 数値補題: `n ∣ 14`, `n ∣ 8`, `n ≠ 1` ⟹ `n = 2`。 -/
private lemma eq_two_of_dvd_fourteen_of_dvd_eight {n : ℕ} (h14 : n ∣ 14) (h8 : n ∣ 8)
    (h1 : n ≠ 1) : n = 2 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h8 (by norm_num)
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  interval_cases n <;> omega

/-- 位数 30 の群は指数 3 または指数 5 の部分群を持つ (Problem 1C.4 の `|N| = 120` case 用)。

`n₅ ∈ {1, 6}`・`n₃ ∈ {1, 10}` (Sylow 計数)。`n₅ = 6 ∧ n₃ = 10` は位数 5 の元 24 個 +
位数 3 の元 20 個 ≤ 29 に反する。よって正規な Sylow 5 か Sylow 3 が存在し、Sylow 2
(位数 2) との join が位数 10 (指数 3) または位数 6 (指数 5) を与える。 -/
theorem exists_subgroup_index_eq_three_or_five_of_card_thirty {H : Type*} [Group H] [Finite H]
    (h30 : Nat.card H = 30) : ∃ K : Subgroup H, K.index = 3 ∨ K.index = 5 := by
  haveI f2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI f3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI f5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S₂⟩ := (Sylow.nonempty : Nonempty (Sylow 2 H))
  obtain ⟨P₃⟩ := (Sylow.nonempty : Nonempty (Sylow 3 H))
  obtain ⟨P₅⟩ := (Sylow.nonempty : Nonempty (Sylow 5 H))
  have hc2 : ∀ P : Sylow 2 H, Nat.card (P : Subgroup H) = 2 :=
    sylow_card_eq_prime_of_card_eq_mul (m := 15) (by rw [h30]) (by norm_num) (by norm_num)
  have hc3 : ∀ P : Sylow 3 H, Nat.card (P : Subgroup H) = 3 :=
    sylow_card_eq_prime_of_card_eq_mul (m := 10) (by rw [h30]) (by norm_num) (by norm_num)
  have hc5 : ∀ P : Sylow 5 H, Nat.card (P : Subgroup H) = 5 :=
    sylow_card_eq_prime_of_card_eq_mul (m := 6) (by rw [h30]) (by norm_num) (by norm_num)
  -- n₅ ∈ {1, 6}
  have hn5 : Nat.card (Sylow 5 H) = 1 ∨ Nat.card (Sylow 5 H) = 6 := by
    have hidx : (P₅ : Subgroup H).index = 6 := by
      have hmi := Subgroup.card_mul_index (P₅ : Subgroup H)
      rw [hc5 P₅, h30] at hmi; omega
    have hdvd : Nat.card (Sylow 5 H) ∣ 6 := hidx ▸ P₅.card_dvd_index
    have hmod : Nat.card (Sylow 5 H) % 5 = 1 := by
      simpa [Nat.ModEq] using card_sylow_modEq_one 5 H
    exact eq_of_dvd_six_mod_five Nat.card_pos hdvd hmod
  -- n₃ ∈ {1, 10}
  have hn3 : Nat.card (Sylow 3 H) = 1 ∨ Nat.card (Sylow 3 H) = 10 := by
    have hidx : (P₃ : Subgroup H).index = 10 := by
      have hmi := Subgroup.card_mul_index (P₃ : Subgroup H)
      rw [hc3 P₃, h30] at hmi; omega
    have hdvd : Nat.card (Sylow 3 H) ∣ 10 := hidx ▸ P₃.card_dvd_index
    have hmod : Nat.card (Sylow 3 H) % 3 = 1 := by
      simpa [Nat.ModEq] using card_sylow_modEq_one 3 H
    exact eq_of_dvd_ten_mod_three Nat.card_pos hdvd hmod
  -- n₅ = 1 か n₃ = 1 (両方 6, 10 だと計数矛盾: 24 + 20 ≤ 29 は偽)
  have hkey : Nat.card (Sylow 5 H) = 1 ∨ Nat.card (Sylow 3 H) = 1 := by
    rcases hn5 with h5 | h5
    · exact Or.inl h5
    rcases hn3 with h3 | h3
    · exact Or.inr h3
    exfalso
    have hcount := card_sylow_mul_add_card_sylow_mul_le (q₁ := 5) (q₂ := 3)
      (by norm_num) hc5 hc3
    rw [h5, h3, h30] at hcount
    omega
  have hS₂card : Nat.card (S₂ : Subgroup H) = 2 := hc2 S₂
  rcases hkey with h5 | h3
  · -- Sylow 5 正規 → `P₅ ⊔ S₂` は位数 10、指数 3
    haveI : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp h5).1
    have hnorm : (P₅ : Subgroup H).Normal := Sylow.normal_of_subsingleton P₅
    have hcop : Nat.Coprime (Nat.card (P₅ : Subgroup H)) (Nat.card (S₂ : Subgroup H)) := by
      rw [hc5 P₅, hS₂card]
      exact ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr (by norm_num)
    refine ⟨(P₅ : Subgroup H) ⊔ (S₂ : Subgroup H), Or.inl ?_⟩
    have hK : Nat.card ↥((P₅ : Subgroup H) ⊔ (S₂ : Subgroup H)) = 10 := by
      rw [card_sup_of_normal_of_coprime hnorm hcop, hc5 P₅, hS₂card]
    have hmi := Subgroup.card_mul_index ((P₅ : Subgroup H) ⊔ (S₂ : Subgroup H))
    rw [hK, h30] at hmi
    omega
  · -- Sylow 3 正規 → `P₃ ⊔ S₂` は位数 6、指数 5
    haveI : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp h3).1
    have hnorm : (P₃ : Subgroup H).Normal := Sylow.normal_of_subsingleton P₃
    have hcop : Nat.Coprime (Nat.card (P₃ : Subgroup H)) (Nat.card (S₂ : Subgroup H)) := by
      rw [hc3 P₃, hS₂card]
      exact ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr (by norm_num)
    refine ⟨(P₃ : Subgroup H) ⊔ (S₂ : Subgroup H), Or.inr ?_⟩
    have hK : Nat.card ↥((P₃ : Subgroup H) ⊔ (S₂ : Subgroup H)) = 6 := by
      rw [card_sup_of_normal_of_coprime hnorm hcop, hc3 P₃, hS₂card]
    have hmi := Subgroup.card_mul_index ((P₃ : Subgroup H) ⊔ (S₂ : Subgroup H))
    rw [hK, h30] at hmi
    omega

/-- **Isaacs Problem 1C.4**. `|G| = 120 = 2³·3·5` のとき `G` は指数 3 または指数 5 の
部分群を持つ (両方でもよい)。

Hint 通り `n₂(G) ∈ {1, 3, 5, 15}` で場合分けする。核心の `n₂ = 15` では **Thm 1.16**
(`card_sylow_modEq_one_of_max_inter`) の交わり最大対から `|S ∩ T| = 4` を導き、
`N_G(S ∩ T) ⊇ ⟨S, T⟩` の位数解析 (24/40/120) に帰着する。`|N| = 120` の場合は
`G/(S∩T)` が位数 30 で、位数 30 の群の補題
(`exists_subgroup_index_eq_three_or_five_of_card_thirty`) を `comap` で引き戻す。 -/
theorem exists_subgroup_index_eq_three_or_five_of_card_onetwenty {G : Type*} [Group G]
    [Finite G] (h120 : Nat.card G = 120) : ∃ K : Subgroup G, K.index = 3 ∨ K.index = 5 := by
  haveI f2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI f5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  -- Sylow 2 は位数 8
  have hc2 : ∀ Q : Sylow 2 G, Nat.card (Q : Subgroup G) = 8 := by
    have hfact : (Nat.card G).factorization 2 = 3 := by
      rw [h120, show (120 : ℕ) = 2 ^ 3 * 15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    intro Q
    rw [Sylow.card_eq_multiplicity, hfact]; norm_num
  -- n₂ ∈ {1, 3, 5, 15}
  have hPidx : (P : Subgroup G).index = 15 := by
    have hmi := Subgroup.card_mul_index (P : Subgroup G)
    rw [hc2 P, h120] at hmi; omega
  have hn2_dvd : Nat.card (Sylow 2 G) ∣ 15 := hPidx ▸ P.card_dvd_index
  rcases eq_of_dvd_fifteen Nat.card_pos hn2_dvd with hn2 | hn2 | hn2 | hn2
  · -- n₂ = 1: `P ⊴ G`、`P ⊔ F` (F ∈ Syl₅) は位数 40 = 指数 3
    haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp hn2).1
    have hnorm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    obtain ⟨F⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
    have hF5 : Nat.card (F : Subgroup G) = 5 :=
      sylow_card_eq_prime_of_card_eq_mul (m := 24) (by rw [h120]) (by norm_num)
        (by norm_num) F
    have hcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card (F : Subgroup G)) := by
      rw [hc2 P, hF5]
      exact (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr (by norm_num)).symm
    refine ⟨(P : Subgroup G) ⊔ (F : Subgroup G), Or.inl ?_⟩
    have hK : Nat.card ↥((P : Subgroup G) ⊔ (F : Subgroup G)) = 40 := by
      rw [card_sup_of_normal_of_coprime hnorm hcop, hc2 P, hF5]
    have hmi := Subgroup.card_mul_index ((P : Subgroup G) ⊔ (F : Subgroup G))
    rw [hK, h120] at hmi
    omega
  · -- n₂ = 3: normalizer が指数 3
    refine ⟨Subgroup.normalizer (P : Set G), Or.inl ?_⟩
    rw [← Sylow.card_eq_index_normalizer P]; exact hn2
  · -- n₂ = 5: normalizer が指数 5
    refine ⟨Subgroup.normalizer (P : Set G), Or.inr ?_⟩
    rw [← Sylow.card_eq_index_normalizer P]; exact hn2
  · -- n₂ = 15: 交わり最大対 → `|S ∩ T| = 4` → `N_G(S ∩ T)` の解析
    classical
    haveI : Fintype (Sylow 2 G) := Fintype.ofFinite _
    have hgt : 1 < Nat.card (Sylow 2 G) := by rw [hn2]; norm_num
    haveI : Nontrivial (Sylow 2 G) := by
      apply Fintype.one_lt_card_iff_nontrivial.mp
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨S₀, T₀, hST₀⟩ := exists_pair_ne (Sylow 2 G)
    -- 交わり最大の相異なる対 (S, T)
    obtain ⟨STm, hSTm_mem, hSTmax⟩ :=
      (Finset.univ.filter (fun ST : Sylow 2 G × Sylow 2 G => ST.1 ≠ ST.2)).exists_max_image
        (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
        ⟨(S₀, T₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST₀⟩⟩
    obtain ⟨S, T⟩ := STm
    have hST : S ≠ T := (Finset.mem_filter.mp hSTm_mem).2
    have hmax : ∀ S' T' : Sylow 2 G, S' ≠ T' →
        Nat.card ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G) ≤
        Nat.card ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) := fun S' T' hne =>
      hSTmax (S', T') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    -- Thm 1.16: 15 ≡ 1 (mod |S : S∩T|)
    have hmod := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
    rw [hn2] at hmod
    set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
    -- |S : D| = 2
    have hd_dvd14 : D.relIndex (S : Subgroup G) ∣ 14 := by
      have h := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 15)).mp hmod.symm
      norm_num at h; exact h
    have hd_dvd8 : D.relIndex (S : Subgroup G) ∣ 8 := by
      have hh := Subgroup.index_dvd_card (D.subgroupOf (S : Subgroup G))
      rw [hc2 S] at hh
      exact hh
    have hd_ne1 : D.relIndex (S : Subgroup G) ≠ 1 := by
      intro h1
      have hle : (S : Subgroup G) ≤ D := Subgroup.relIndex_eq_one.mp h1
      have heq : (S : Subgroup G) = (T : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge (hle.trans inf_le_right) ((hc2 T).trans (hc2 S).symm).le
      exact hST (Sylow.ext heq)
    have hd2 : D.relIndex (S : Subgroup G) = 2 :=
      eq_two_of_dvd_fourteen_of_dvd_eight hd_dvd14 hd_dvd8 hd_ne1
    have hidx2S : (D.subgroupOf (S : Subgroup G)).index = 2 := hd2
    -- |D| = 4
    have hDcard : Nat.card D = 4 := by
      have heq := Subgroup.card_mul_index (D.subgroupOf (S : Subgroup G))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : D ≤ (S : Subgroup G))).toEquiv, hidx2S, hc2 S] at heq
      rw [← hDdef] at heq
      omega
    have hidx2T : (D.subgroupOf (T : Subgroup G)).index = 2 := by
      have heq := Subgroup.card_mul_index (D.subgroupOf (T : Subgroup G))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : D ≤ (T : Subgroup G))).toEquiv, hDcard, hc2 T] at heq
      omega
    -- S, T ≤ N := N_G(D) (指数 2 部分群は正規)
    have hS_le : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
      have hnormS : (D.subgroupOf (S : Subgroup G)).Normal :=
        Subgroup.normal_of_index_eq_two hidx2S
      have htop := Subgroup.normalizer_eq_top_iff.mpr hnormS
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_left : D ≤ (S : Subgroup G))] at htop
      exact Subgroup.subgroupOf_eq_top.mp htop
    have hT_le : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
      have hnormT : (D.subgroupOf (T : Subgroup G)).Normal :=
        Subgroup.normal_of_index_eq_two hidx2T
      have htop := Subgroup.normalizer_eq_top_iff.mpr hnormT
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : D ≤ (T : Subgroup G))] at htop
      exact Subgroup.subgroupOf_eq_top.mp htop
    set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
    -- |N| は 8 の倍数、120 の約数、8 でない → 24 / 40 / 120
    have h8N : (8 : ℕ) ∣ Nat.card N := by
      have h := Subgroup.card_dvd_of_le hS_le
      rwa [hc2 S] at h
    have hNdvd : Nat.card N ∣ 120 := by
      have h := Subgroup.card_subgroup_dvd_card N
      rwa [h120] at h
    have hN_ne8 : Nat.card N ≠ 8 := by
      intro h8
      have hSN : (S : Subgroup G) = N :=
        Subgroup.eq_of_le_of_card_ge hS_le (h8.trans (hc2 S).symm).le
      have hTN : (T : Subgroup G) = N :=
        Subgroup.eq_of_le_of_card_ge hT_le (h8.trans (hc2 T).symm).le
      exact hST (Sylow.ext (hSN.trans hTN.symm))
    obtain ⟨m, hm⟩ := h8N
    have hm15 : m ∣ 15 := by
      have h1 : 8 * m ∣ 8 * 15 := by
        rw [← hm, show (8 : ℕ) * 15 = 120 by norm_num]
        exact hNdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp h1
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        rw [h0, mul_zero] at hm
        exact Nat.card_pos.ne' hm
      · exact h0
    have hm_ne1 : m ≠ 1 := fun h1 => hN_ne8 (by rw [hm, h1, mul_one])
    rcases eq_of_dvd_fifteen hm0 hm15 with hmv | hmv | hmv | hmv
    · exact absurd hmv hm_ne1
    · -- |N| = 24: 指数 5
      refine ⟨N, Or.inr ?_⟩
      have hmi := Subgroup.card_mul_index N
      rw [hm, hmv, h120] at hmi
      omega
    · -- |N| = 40: 指数 3
      refine ⟨N, Or.inl ?_⟩
      have hmi := Subgroup.card_mul_index N
      rw [hm, hmv, h120] at hmi
      omega
    · -- |N| = 120: `D ⊴ G`、`G/D` は位数 30 → 位数 30 補題を comap で引き戻す
      have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hm, hmv, h120])
      have hDnorm : D.Normal := Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)
      haveI := hDnorm
      have hDidx : D.index = 30 := by
        have hidxS : (S : Subgroup G).index = 15 := by
          have hmi := Subgroup.card_mul_index (S : Subgroup G)
          rw [hc2 S, h120] at hmi; omega
        have hrel := Subgroup.relIndex_mul_index (inf_le_left : D ≤ (S : Subgroup G))
        rw [hd2, hidxS] at hrel
        rw [← hDdef] at hrel
        omega
      have hq30 : Nat.card (G ⧸ D) = 30 := by
        rw [← Subgroup.index_eq_card]; exact hDidx
      obtain ⟨Kbar, hKbar⟩ := exists_subgroup_index_eq_three_or_five_of_card_thirty hq30
      refine ⟨Kbar.comap (QuotientGroup.mk' D), ?_⟩
      rw [Kbar.index_comap_of_surjective (QuotientGroup.mk'_surjective D)]
      exact hKbar

end -- 1C

end OddOrder.Isaacs.Ch01
