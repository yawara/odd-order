/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Ch.7 → Ch.3 forward dependency: Isaacs Thm 3.15 (converse of Hall E)

**Isaacs FGT Thm 3.15** (p.84, proof p.89) は Burnside `p^a q^b` (Thm 7.8,
`burnside_p_pow_q_pow`) に依存するため, owner chapter (Ch.7) ディレクトリに配置する.

> **Thm 3.15**: 有限群 `G` が全ての素数 `p` について `p`-complement
> (= Hall `{p}'`-部分群) を持てば `G` は可解.

証明 (帰納法, p.89 "Proof of Theorem 3.15 (assuming Burnside)"):
`|G|` の素因子数 `n` で帰納. `n ≤ 2` は Burnside. `n ≥ 3` なら相異なる素因子
`p, q, r` の complement `H, K, L` を取ると指数はそれぞれ `p`-冪, `q`-冪, `r`-冪で
pairwise coprime. 各 `H` は帰納法の仮定で可解 — `H` の各素因子 `s` について
`G` の `s`-complement `Q` との交差 `Q ∩ H` が `H` の `s`-complement になる
(Lemma 3.16 の index clause `|H : H∩Q| = |G:Q|`). よって Wielandt (Thm 3.17,
`isSolvable_of_pairwise_coprime_index`, Ch.3 で Burnside 無しで証明済) で `G` 可解.

なお Thm 3.17 は当初ここに置く予定だったが, 教科書証明が Burnside を使わない
ことが判明したため Ch.3 (`Theorem315.lean`) に実装した.
-/

namespace OddOrder.Isaacs.Ch07

open OddOrder.Isaacs.Ch03

/-- **Isaacs Thm 3.15** (converse of Hall E): 有限群 `G` が全ての素数 `p` について
`p`-complement (= Hall `{p}'`-部分群) を持てば `G` は可解.

仮定は書籍の「`|G|` の素因子 `p` について」より形式上強い「全ての素数 `p`」だが
同値 (`p ∤ |G|` なら `G` 自身が `p`-complement).

証明は `|G|` の強帰納法 (素因子数の帰納法を包含):
- 素因子 ≤ 2 個: Burnside `p^a q^b` (`burnside_p_pow_q_pow`).
- 素因子 ≥ 3 個: 相異なる素因子 `p, q, r` の complement `H, K, L` は pairwise
  coprime index (指数の素因子がそれぞれ `{p}`, `{q}`, `{r}` に限る). 各 `W` は
  帰納法で可解: `W` の素数 `s ≠ p` の complement は `Q.subgroupOf W` (`Q` = `G` の
  `s`-complement) — index は Lemma 3.16 clause (`relIndex_eq_index_of_coprime_index`)
  で `|G:Q|` (= `s`-冪), 位数は `|Q|` を割るので `s` と coprime. Wielandt
  (Thm 3.17) で結論. -/
theorem isSolvable_of_pcomplement_exists.{u} {G : Type u} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∃ H : Subgroup G, IsHallSubgroup {q | q ≠ p} H) :
    IsSolvable G := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (G' : Type u) [Group G'] [Finite G'], Nat.card G' = n →
      (∀ p : ℕ, p.Prime → ∃ H : Subgroup G', IsHallSubgroup {q | q ≠ p} H) →
      IsSolvable G'
  suffices hmain : motive (Nat.card G) by exact hmain G rfl h
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih G' _ _ hcard h
  have hn0 : Nat.card G' ≠ 0 := Nat.card_pos.ne'
  by_cases hsmall : (Nat.card G').primeFactors.card ≤ 2
  · -- ≤ 2 個の素因子: `|G'| = p^a q^b` として Burnside.
    obtain ⟨p, q, hp, hq, hpq, hsub⟩ :
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
          (Nat.card G').primeFactors ⊆ {p, q} := by
      rcases Finset.eq_empty_or_nonempty (Nat.card G').primeFactors with h0 | ⟨p, hp_mem⟩
      · exact ⟨2, 3, Nat.prime_two, Nat.prime_three, by norm_num, by simp [h0]⟩
      · have hp := Nat.prime_of_mem_primeFactors hp_mem
        by_cases h1 : (Nat.card G').primeFactors ⊆ {p}
        · refine ⟨p, if p = 2 then 3 else 2, hp, ?_, ?_,
            h1.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self p _))⟩
          · split_ifs with h2
            · exact Nat.prime_three
            · exact Nat.prime_two
          · split_ifs with h2
            · rw [h2]; norm_num
            · exact h2
        · obtain ⟨x, hx_mem, hx_ne⟩ := Finset.not_subset.mp h1
          have hx := Nat.prime_of_mem_primeFactors hx_mem
          have hx_ne_p : x ≠ p := by simpa using hx_ne
          refine ⟨p, x, hp, hx, hx_ne_p.symm, ?_⟩
          have hsub2 : ({p, x} : Finset ℕ) ⊆ (Nat.card G').primeFactors := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact hp_mem
            · rw [Finset.mem_singleton.mp hy]; exact hx_mem
          have hc2 : ({p, x} : Finset ℕ).card = 2 := Finset.card_pair hx_ne_p.symm
          intro y hy
          rwa [← Finset.eq_of_subset_of_card_le hsub2 (by rw [hc2]; exact hsmall)] at hy
    have hfact : Nat.card G' =
        p ^ (Nat.card G').factorization p * q ^ (Nat.card G').factorization q := by
      have h1 : ∏ x ∈ (Nat.card G').primeFactors, x ^ (Nat.card G').factorization x
          = Nat.card G' := by
        rw [← Nat.support_factorization]
        exact Nat.prod_factorization_pow_eq_self hn0
      have h2 : ∏ x ∈ (Nat.card G').primeFactors, x ^ (Nat.card G').factorization x
          = ∏ x ∈ ({p, q} : Finset ℕ), x ^ (Nat.card G').factorization x := by
        refine Finset.prod_subset hsub fun x _ hx => ?_
        have hx0 : (Nat.card G').factorization x = 0 := by
          rw [← Nat.support_factorization] at hx
          exact Finsupp.notMem_support_iff.mp hx
        rw [hx0, pow_zero]
      conv_lhs => rw [← h1]
      rw [h2, Finset.prod_pair hpq]
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    exact burnside_p_pow_q_pow ⟨_, _, hfact⟩
  · -- ≥ 3 個の素因子: 相異なる素因子 p, q, r を取り Wielandt へ.
    rw [not_le] at hsmall
    obtain ⟨p, hpS⟩ :=
      Finset.card_pos.mp (show 0 < (Nat.card G').primeFactors.card by omega)
    obtain ⟨q, hqS, hqp⟩ :=
      Finset.exists_mem_ne (show 1 < (Nat.card G').primeFactors.card by omega) p
    have hsd : 0 < ((Nat.card G').primeFactors \ {p, q}).card := by
      have h1 := Finset.le_card_sdiff ({p, q} : Finset ℕ) (Nat.card G').primeFactors
      have h2 : ({p, q} : Finset ℕ).card ≤ 2 := by
        simpa using Finset.card_insert_le p ({q} : Finset ℕ)
      omega
    obtain ⟨r, hr_mem⟩ := Finset.card_pos.mp hsd
    rw [Finset.mem_sdiff] at hr_mem
    obtain ⟨hrS, hr_notin⟩ := hr_mem
    have hrp : r ≠ p := fun hEq => hr_notin (by rw [hEq]; exact Finset.mem_insert_self p _)
    have hrq : r ≠ q := fun hEq => hr_notin
      (by rw [hEq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hq := Nat.prime_of_mem_primeFactors hqS
    have hr := Nat.prime_of_mem_primeFactors hrS
    -- 相異なる素数の complement の指数は coprime (指数の素因子がその素数のみ).
    have hcop : ∀ {s t : ℕ} {W V : Subgroup G'}, s ≠ t →
        IsHallSubgroup {u | u ≠ s} W → IsHallSubgroup {u | u ≠ t} V →
        Nat.Coprime W.index V.index := by
      intro s t W V hst hW hV
      refine Nat.coprime_of_isPiGroup_of_isPiGroup_compl
        Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
        (π := ({s} : Set ℕ)) ?_ ?_
      · intro u hu
        have hus := hW.2 u hu
        simp only [Set.mem_setOf_eq, not_not] at hus
        simp [hus]
      · intro u hu
        have hut := hV.2 u hu
        simp only [Set.mem_setOf_eq, not_not] at hut
        rw [Set.mem_singleton_iff, hut]
        exact fun hts => hst hts.symm
    -- 任意の素因子 s の complement W は帰納法で可解.
    have hsolv : ∀ (s : ℕ), s.Prime → s ∣ Nat.card G' →
        ∀ (W : Subgroup G'), IsHallSubgroup {u | u ≠ s} W → IsSolvable W := by
      intro s hs hs_dvd W hW
      have hmul : Nat.card ↥W * W.index = Nat.card G' := Subgroup.card_mul_index W
      have hW_card_lt : Nat.card ↥W < n := by
        have hidx_ne_one : W.index ≠ 1 := by
          intro h1
          have hcardEq : Nat.card ↥W = Nat.card G' := by rw [← hmul, h1, mul_one]
          have hs_mem : s ∈ (Nat.card ↥W).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hs, hcardEq ▸ hs_dvd, Nat.card_pos.ne'⟩
          exact (hW.1 s hs_mem) rfl
        have hidx_pos : 1 < W.index :=
          lt_of_le_of_ne
            (Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite)
            (Ne.symm hidx_ne_one)
        calc Nat.card ↥W
            < Nat.card ↥W * W.index := (lt_mul_iff_one_lt_right Nat.card_pos).mpr hidx_pos
          _ = n := by rw [hmul, hcard]
      -- W は全ての素数 t について t-complement を持つ.
      have hWcompl : ∀ t : ℕ, t.Prime →
          ∃ V : Subgroup ↥W, IsHallSubgroup {u | u ≠ t} V := by
        intro t ht
        by_cases hts : t = s
        · -- t = s: `s ∤ |W|` なので ⊤ 自身が s-complement.
          subst hts
          refine ⟨⊤, fun u hu => ?_, fun u hu => ?_⟩
          · have hcard_top : Nat.card ↥(⊤ : Subgroup ↥W) = Nat.card ↥W :=
              Nat.card_congr Subgroup.topEquiv.toEquiv
            rw [hcard_top] at hu
            exact hW.1 u hu
          · rw [Subgroup.index_top] at hu
            simp at hu
        · -- t ≠ s: G' の t-complement Q と交差する.
          obtain ⟨Q, hQ⟩ := h t ht
          have hcop' : Nat.Coprime W.index Q.index := hcop (Ne.symm hts) hW hQ
          refine ⟨Q.subgroupOf W, fun u hu => ?_, fun u hu => ?_⟩
          · -- |Q ∩ W| は |Q| を割るので素因子は t を避ける.
            have hcardEq : Nat.card ↥(Q.subgroupOf W) =
                Nat.card ↥(Q ⊓ W : Subgroup G') := by
              rw [← Subgroup.inf_subgroupOf_right]
              exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
            have hdvd : Nat.card ↥(Q.subgroupOf W) ∣ Nat.card ↥Q := by
              rw [hcardEq]
              exact Subgroup.card_dvd_of_le inf_le_left
            exact hQ.1 u (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hu)
          · -- |W : Q ∩ W| = |G : Q| (Lemma 3.16 clause) の素因子は t のみ.
            have hidx : (Q.subgroupOf W).index = Q.index := by
              have h1 : (Q.subgroupOf W).index = Q.relIndex W := rfl
              rw [h1, relIndex_eq_index_of_coprime_index hcop']
            rw [hidx] at hu
            exact hQ.2 u hu
      exact ih _ hW_card_lt ↥W rfl hWcompl
    -- 3 complement を取り Wielandt (Thm 3.17).
    obtain ⟨H, hH⟩ := h p hp
    obtain ⟨K, hK⟩ := h q hq
    obtain ⟨L, hL⟩ := h r hr
    exact isSolvable_of_pairwise_coprime_index
      (hcop hqp.symm hH hK) (hcop hrp.symm hH hL) (hcop hrq.symm hK hL)
      (hsolv p hp (Nat.dvd_of_mem_primeFactors hpS) H hH)
      (hsolv q hq (Nat.dvd_of_mem_primeFactors hqS) K hK)
      (hsolv r hr (Nat.dvd_of_mem_primeFactors hrS) L hL)

end OddOrder.Isaacs.Ch07
