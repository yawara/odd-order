/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic

/-!
# Isaacs Problems 3C (書籍 pp. 90–91) — Hall 部分群と Sylow system

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3C の形式化
(campaign issue 1055)。

* **3C.1** (Hall D-定理) は `Ch03_SplitExtensions/Basic.lean` の `hall_D` として landing 済。
* **3C.2**: `π` の各素数 `p` について `p`-補元 (= Hall `{p}ᶜ`-部分群) `H_p` が存在するなら,
  それらの交わりは Hall `π'`-部分群。→ `isHallSubgroup_finset_inf_of_pComplement`。

## 3C.2 の証明

有限集合 `s` の帰納。`s = ∅` なら交わりは `⊤` で Hall `univ`。
`insert p t` では `X := H p ⊓ t.inf H` について

* **位数**: `X ≤ H p` と `X ≤ t.inf H` から `|X|` は両者の位数を割るので, その素因子は
  `p` も `t` の元も避ける。
* **指数**: `(H p).index` の素因子は `{p}` のみ, `(t.inf H).index` の素因子は `t` に入るので,
  `p ∉ t` より互いに素。したがって `X.index = (H p).index · (t.inf H).index`
  (`index_inf_eq_mul_of_coprime`) で, その素因子は `insert p t` に収まる。

## Main results

- `index_inf_eq_mul_of_coprime` — 指数が互いに素な 2 部分群の交わりの指数は積。
- `isHallSubgroup_finset_inf_of_pComplement` — **Problem 3C.2**。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup

section /- 3C: Problem 3C.2 (p. 90) -/

variable {G : Type*} [Group G] [Finite G]

/-- 指数が互いに素な 2 つの部分群について, 交わりの指数は指数の積。

`H.index ∣ (H ⊓ K).index` と `K.index ∣ (H ⊓ K).index` (指数は包含に沿って割る) から
互いに素性で `H.index · K.index ∣ (H ⊓ K).index`, 逆向きは `Subgroup.index_inf_le`。 -/
theorem index_inf_eq_mul_of_coprime {H K : Subgroup G}
    (hcop : Nat.Coprime H.index K.index) : (H ⊓ K).index = H.index * K.index := by
  have hHne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hKne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hIne : (H ⊓ K).index ≠ 0 := Subgroup.index_inf_ne_zero hHne hKne
  have h1 : H.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_left
  have h2 : K.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_right
  have h3 : H.index * K.index ∣ (H ⊓ K).index := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
  exact le_antisymm Subgroup.index_inf_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hIne) h3)

/-- **Isaacs Problem 3C.2** (p. 90)。素数の有限集合 `s` の各元 `p` について `p`-補元
(= Hall `{p}ᶜ`-部分群) `H p` が存在するなら, それらの交わりは Hall `(↑s)ᶜ`-部分群。

書籍は「素数の集合 `π`」で述べるが, Hall 性は `|G|` の素因子にしか依らないので
有限集合版で十分 (`π` のうち `|G|` を割らない素数の補元は `⊤` になる)。 -/
theorem isHallSubgroup_finset_inf_of_pComplement (s : Finset ℕ) (H : ℕ → Subgroup G)
    (hH : ∀ p ∈ s, IsHallSubgroup ({p}ᶜ : Set ℕ) (H p)) :
    IsHallSubgroup ((↑s : Set ℕ)ᶜ) (s.inf H) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun q _ => by simp, fun q hq => ?_⟩
    rw [Finset.inf_empty, Subgroup.index_top] at hq
    simp at hq
  | @insert p t hpt ih =>
    have hHp : IsHallSubgroup ({p}ᶜ : Set ℕ) (H p) := hH p (Finset.mem_insert_self _ _)
    have hHt : IsHallSubgroup ((↑t : Set ℕ)ᶜ) (t.inf H) :=
      ih (fun q hq => hH q (Finset.mem_insert_of_mem hq))
    rw [Finset.inf_insert]
    -- 指数の互いに素性
    have hcop : Nat.Coprime (H p).index (t.inf H).index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqp : q ∈ (H p).index.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqd.trans (Nat.gcd_dvd_left _ _),
          Subgroup.index_ne_zero_of_finite⟩
      have hqt : q ∈ (t.inf H).index.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqd.trans (Nat.gcd_dvd_right _ _),
          Subgroup.index_ne_zero_of_finite⟩
      have h1 : q = p := by
        have := hHp.2 q hqp
        simpa using this
      have h2 : q ∈ t := by
        have := hHt.2 q hqt
        simpa using this
      exact hpt (h1 ▸ h2)
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · -- 位数の素因子は `insert p t` を避ける
      have hdvdp : Nat.card ↥(H p ⊓ t.inf H) ∣ Nat.card ↥(H p) :=
        Subgroup.card_dvd_of_le inf_le_left
      have hdvdt : Nat.card ↥(H p ⊓ t.inf H) ∣ Nat.card ↥(t.inf H) :=
        Subgroup.card_dvd_of_le inf_le_right
      have hp' : q ∈ ({p}ᶜ : Set ℕ) :=
        hHp.1 q (Nat.primeFactors_mono hdvdp Nat.card_pos.ne' hq)
      have ht' : q ∈ ((↑t : Set ℕ)ᶜ) :=
        hHt.1 q (Nat.primeFactors_mono hdvdt Nat.card_pos.ne' hq)
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact ⟨by simpa using hp', by simpa using ht'⟩
    · -- 指数の素因子は `insert p t` に入る
      rw [index_inf_eq_mul_of_coprime hcop] at hq
      rw [Nat.primeFactors_mul Subgroup.index_ne_zero_of_finite
        Subgroup.index_ne_zero_of_finite] at hq
      rcases Finset.mem_union.mp hq with h | h
      · have := hHp.2 q h
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_not]
        exact Or.inl (by simpa using this)
      · have := hHt.2 q h
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_not]
        exact Or.inr (by simpa using this)

end -- Problem 3C.2

end OddOrder.Isaacs.Ch03
