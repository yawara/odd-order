/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.ProblemsSylowCounting

/-!
# Isaacs Problems 1E (p. 38) — 1E.6 / 1E.7 / 1E.8

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1E の後半。道具立てと
1E.1–1E.5 は `ProblemsSylowCounting.lean` にあり, 本ファイルはそれらを使って残りの
具体的位数の非単純性を扱う。

* **1E.6**: 位数 `180 = 2²·3²·5` の単純群は存在しない。
* **1E.7**: 位数 `240 = 2⁴·3·5` の単純群は存在しない。
* **1E.8**: 位数 `252 = 2²·3²·7` の単純群は存在しない。

これで **§1E は 1E.1–1E.8 全問完済**。

## Main results

- `not_isSimpleGroup_of_card_eq_oneeighty` — **Problem 1E.6**。
- `card_dvd_factorial_card_sylow_of_simple` — 単純群で `n_q > 1` なら `|G| ∣ n_q !`。
- `not_isSimpleGroup_of_card_eq_twofourty` — **Problem 1E.7**。
- `not_isSimpleGroup_of_card_eq_twofivetwo` — **Problem 1E.8**。
-/

namespace OddOrder.Isaacs.Ch01

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

section /- 1E: Problem 1E.8 (p. 38) -/

/-- `n ∣ 36` かつ `n ≡ 1 (mod 7)` なら `n = 1` または `n = 36`。 -/
private lemma eq_of_dvd_thirtysix_mod_seven {n : ℕ} (h : n ∣ 36) (hm : n % 7 = 1) :
    n = 1 ∨ n = 36 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 36 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h hm <;> decide

/-- `n ∣ 28` かつ `n ≡ 1 (mod 3)` なら `n ∈ {1, 4, 7, 28}`。 -/
private lemma eq_of_dvd_twentyeight {n : ℕ} (h : n ∣ 28) (hm : n % 3 = 1) :
    n = 1 ∨ n = 4 ∨ n = 7 ∨ n = 28 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 28 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h hm <;> decide

/-- `28` の約数は `1, 2, 4, 7, 14, 28`。 -/
private lemma divisors_twentyeight {n : ℕ} (h : n ∣ 28) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 7 ∨ n = 14 ∨ n = 28 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 28 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h <;> decide

/-- **Isaacs Problem 1E.8** (p. 38)。位数 `252 = 2²·3²·7` の単純群は存在しない。

`n₇ ∣ [G : P₇] = 36` と `n₇ ≡ 1 (mod 7)` から `n₇ ∈ {1, 36}`, 単純性で `n₇ = 36` となり
**位数 7 の元が `36·6 = 216` 個** (残りは `252 − 216 = 36` 個しかない)。
Sylow `3` は位数 9・指数 28 で `n₃ ∈ {1, 4, 7, 28}`。`n₃ = 4` は指数 4 で `252 ∣ 4! = 24` が
偽なので `n₃ ≥ 7`。**Thm 1.16** から `|S : D| ∈ {3, 9}`:

* `|S : D| = 9` (`D = ⊥`, 最大性より全対が自明交叉): 3-冪位数の非単位元が `n₃·8 ≥ 56` 個で
  位数 7 の 216 個と交わらず `56 + 216 + 1 = 273 > 252` で矛盾。
* `|S : D| = 3` (`|D| = 3`): `S`, `T ≤ N := N_G(D)` で `9 ∣ |N| ∣ 252`,
  `|N| ∈ {9, 18, 36, 63, 126, 252}`。`9` は `S = N = T`, `18` は位数 18 の Sylow `3` が一意,
  `63` は指数 4, `126` は指数 2, `252` は `D ⊴ G` で潰れる。**`36` だけ別扱い**:
  位数 7 の元が 216 個, 残りがちょうど 36 個なので `N` は「位数 7 でない元」全体に一致し,
  その集合は共役不変ゆえ `N ⊴ G` — `1 < |N| = 36 < 252` で単純性に矛盾。 -/
theorem not_isSimpleGroup_of_card_eq_twofivetwo {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 252) : ¬ IsSimpleGroup G := by
  intro hsimple
  classical
  haveI := hsimple
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h7dec : ∀ P : Sylow 7 G,
      Nat.card ↥(P : Subgroup G) = 7 ∧ (P : Subgroup G).index = 36 := fun P => by
    have hh := sylow_card_and_index_of_card_eq_mul (q := 7) (m := 36) (k := 1)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨hh.1.trans (by norm_num), hh.2⟩
  obtain ⟨P₇⟩ : Nonempty (Sylow 7 G) := Sylow.nonempty
  -- `n₇ = 36`: 位数 7 の元が 216 個
  have hn7 : Nat.card (Sylow 7 G) = 36 := by
    rcases eq_of_dvd_thirtysix_mod_seven ((h7dec P₇).2 ▸ Sylow.card_dvd_index P₇)
      (card_sylow_mod_eq_one 7) with h | h
    · exact absurd h (card_sylow_ne_one_of_simple P₇ (by rw [(h7dec P₇).1]; norm_num)
        (by rw [(h7dec P₇).1, hG]; norm_num))
    · exact h
  obtain ⟨U₇, hU₇card, hU₇⟩ :=
    exists_finset_orderOf_eq_card_sylow_mul (q := 7) (fun P => (h7dec P).1)
  rw [hn7] at hU₇card
  norm_num at hU₇card
  -- Sylow `3` は位数 9・指数 28
  have h3dec : ∀ P : Sylow 3 G,
      Nat.card ↥(P : Subgroup G) = 9 ∧ (P : Subgroup G).index = 28 := fun P => by
    have hh := sylow_card_and_index_of_card_eq_mul (q := 3) (m := 28) (k := 2)
      (by rw [hG]; norm_num) (by norm_num) P
    exact ⟨hh.1.trans (by norm_num), hh.2⟩
  obtain ⟨P₃⟩ : Nonempty (Sylow 3 G) := Sylow.nonempty
  have hn3ge : 7 ≤ Nat.card (Sylow 3 G) := by
    rcases eq_of_dvd_twentyeight ((h3dec P₃).2 ▸ Sylow.card_dvd_index P₃)
      (card_sylow_mod_eq_one 3) with h3 | h3 | h3 | h3
    · exact absurd h3 (card_sylow_ne_one_of_simple P₃ (by rw [(h3dec P₃).1]; norm_num)
        (by rw [(h3dec P₃).1, hG]; norm_num))
    · exfalso
      have hd := card_dvd_factorial_card_sylow_of_simple P₃ (by rw [h3]; norm_num)
      rw [hG, h3] at hd
      norm_num [Nat.factorial] at hd
    · omega
    · omega
  -- 交わり最大の対
  have hgt : 1 < Nat.card (Sylow 3 G) := by omega
  obtain ⟨S, T, hST, hmax⟩ := exists_max_inter_sylow_pair (q := 3) hgt
  have hmodT := card_sylow_modEq_one_of_max_inter hgt S T hST hmax
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
  · -- `|D| = 3`: `N := N_G(D)` の位数で場合分け
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
    have hNdvd : Nat.card ↥N ∣ 252 := hG ▸ Subgroup.card_subgroup_dvd_card N
    obtain ⟨e, he⟩ : (9 : ℕ) ∣ Nat.card ↥N := ((h3dec S).1) ▸ Subgroup.card_dvd_of_le hS_le
    have hedvd : e ∣ 28 :=
      (mul_dvd_mul_iff_left (by norm_num : (9 : ℕ) ≠ 0)).mp (by rw [← he]; simpa using hNdvd)
    have hindex_absurd : ∀ n : ℕ, Nat.card ↥N * n = 252 → 1 < n → n < 6 → False := by
      intro n hmul hn1 hn6
      have hidx : N.index = n := by
        have hh := Subgroup.card_mul_index N
        rw [hG] at hh
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans hmul.symm)
      have hdvd := card_dvd_factorial_of_simple_subgroup_index N (by rw [hidx]; omega)
      rw [hG, hidx] at hdvd
      interval_cases n <;> norm_num [Nat.factorial] at hdvd
    rcases divisors_twentyeight hedvd with he1 | he1 | he1 | he1 | he1 | he1
    · -- `|N| = 9`: `S = N = T`
      have heN : Nat.card ↥N = 9 := by rw [he, he1, mul_one]
      exact hST (Sylow.ext
        ((Subgroup.eq_of_le_of_card_ge hS_le (le_of_eq (by rw [heN, (h3dec S).1]))).trans
          (Subgroup.eq_of_le_of_card_ge hT_le (le_of_eq (by rw [heN, (h3dec T).1]))).symm))
    · -- `|N| = 18`: 位数 18 の Sylow `3` は一意
      haveI : Subsingleton (Sylow 3 ↥N) :=
        (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one_of_card_eq_prime_mul_pow
          (q := 3) (ℓ := 2) (k := 2) (by norm_num) (by rw [he, he1]; norm_num) (by norm_num)
          (by norm_num))).1
      exact hST (Sylow.subtype_injective (hP := hS_le) (hQ := hT_le) (Subsingleton.elim _ _))
    · -- `|N| = 36`: `N` は「位数 7 でない元」全体で共役不変 ⟹ `N ⊴ G`
      have heN : Nat.card ↥N = 36 := by rw [he, he1]
      have hdisj : Disjoint ((N : Set G)).toFinset U₇ := by
        rw [Finset.disjoint_left]
        intro x hxN hx7
        have hdvd : orderOf x ∣ Nat.card ↥N := by
          rw [← Subgroup.orderOf_mk x (Set.mem_toFinset.mp hxN)]
          exact orderOf_dvd_natCard _
        rw [heN, (hU₇ x).mp hx7] at hdvd
        norm_num at hdvd
      have hunion : ((N : Set G)).toFinset ∪ U₇ = Finset.univ := by
        refine Finset.eq_univ_of_card _ ?_
        have hNc : ((N : Set G)).toFinset.card = 36 := by
          rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
          exact heN
        have hGc : Fintype.card G = 252 := by rw [← Nat.card_eq_fintype_card]; exact hG
        rw [Finset.card_union_of_disjoint hdisj, hNc, hU₇card, hGc]
      have hmemN : ∀ y : G, orderOf y ≠ 7 → y ∈ N := by
        intro y hy
        have hmem : y ∈ ((N : Set G)).toFinset ∪ U₇ := hunion ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp hmem with hh | hh
        · exact Set.mem_toFinset.mp hh
        · exact absurd ((hU₇ y).mp hh) hy
      have hNnormal : N.Normal := by
        refine ⟨fun x hx g => hmemN _ ?_⟩
        have hord : orderOf (g * x * g⁻¹) = orderOf x :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        rw [hord]
        intro hc
        have hdvd : orderOf x ∣ Nat.card ↥N := by
          rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _
        rw [heN, hc] at hdvd
        norm_num at hdvd
      rcases hsimple.eq_bot_or_eq_top_of_normal N hNnormal with h1 | h1
      · rw [h1, Subgroup.card_bot] at heN; norm_num at heN
      · rw [h1, Subgroup.card_top, hG] at heN; norm_num at heN
    · exact hindex_absurd 4 (by rw [he, he1]) (by norm_num) (by norm_num)
    · exact hindex_absurd 2 (by rw [he, he1]) (by norm_num) (by norm_num)
    · -- `|N| = 252`: `D ⊴ G`
      have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [he, he1, hG])
      rcases hsimple.eq_bot_or_eq_top_of_normal _
        (Subgroup.normalizer_eq_top_iff.mp (hNdef ▸ hNtop)) with h1 | h1
      · rw [h1, Subgroup.card_bot] at hDcard; norm_num at hDcard
      · rw [h1, Subgroup.card_top, hG] at hDcard; norm_num at hDcard
  · -- `D = ⊥`: 全対が自明交叉 ⟹ 計数矛盾
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
    have hdisj : Disjoint U₃ U₇ := by
      rw [Finset.disjoint_left]
      intro x hx3 hx7
      have hd9' := (hU₃ x hx3).2
      rw [(hU₇ x).mp hx7] at hd9'
      norm_num at hd9'
    have hnotin : (1 : G) ∉ U₃ ∪ U₇ := by
      simp only [Finset.mem_union, not_or]
      refine ⟨fun hc => (hU₃ 1 hc).1 rfl, fun hc => ?_⟩
      have h1 := (hU₇ 1).mp hc
      rw [orderOf_one] at h1
      norm_num at h1
    have hle : (insert (1 : G) (U₃ ∪ U₇)).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_insert_of_notMem hnotin, Finset.card_union_of_disjoint hdisj,
      hU₃card, hU₇card, hG] at hle
    omega

end -- Problem 1E.8

end OddOrder.Isaacs.Ch01
