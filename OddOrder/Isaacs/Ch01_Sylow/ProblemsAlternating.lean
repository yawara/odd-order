/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Centralizer
import OddOrder.Isaacs.Ch01_Sylow.ProblemsOrder120

/-!
# Isaacs Problem 1C.5 — `A_{p+1}` の Sylow `p`-正規化群の位数

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1C (p. 18) の演習 **1C.5**
(campaign issue 1055)。

**Problem 1C.5**: `P ∈ Syl_p(G)`, `G = A_{p+1}` (交代群) のとき `|N_G(P)| = p(p−1)/2`
(hint: 位数 `p` の元を数える)。

⚠ `p = 2` (`A₃ ≅ C₃`) では Sylow 2 が自明で `|N_G(P)| = 3 ≠ 1 = p(p−1)/2` となり不成立。
Isaacs は暗黙に `p` 奇素数を仮定しているので、本形式化は `3 ≤ p` を仮定に置く
(repo 側の明示化であって書籍のギャップではない)。

## 証明 (hint 通り、除算を避けて multiplicative に)

- `2|A| = (p+1)!` (`two_mul_nat_card_alternatingGroup`)。`(p+1)! = p·((p+1)(p−1)!)` と
  `p` 奇数から `|A| = p·m` (`m = ((p+1)/2)·(p−1)!`, `¬p ∣ m`) ⟹ Sylow `p` は位数 `p`
  ちょうど (`sylow_card_eq_prime_of_card_eq_mul`)。
- 位数 `p` の元は `p`-cycle: `cycleType = replicate (n+1) p` (`cycleType_prime_order`) の
  台の大きさ `(n+1)p ≤ p+1` から `n = 0`。逆に `cycleType = {p}` なら位数 `p`
  (`lcm_cycleType`) かつ `p` 奇数ゆえ偶置換 (`IsCycle.sign`) で `A` に属する ⟹
  `A` の位数 `p` の元 ↔ `Perm` の `cycleType = {p}` の元 (bijection)。
- 個数: `card_of_cycleType_mul_eq` で `c · p = (p+1)!` (`c` := `cycleType = {p}` の元数)。
- Sylow 計数 (`natCard_orderOf_eq_of_sylow_card_eq`): `c = n_p·(p−1)`。
  `|N|·n_p = |A|` (`Sylow.card_eq_index_normalizer` + `card_mul_index`)。
- 掛け合わせ: `(2|N|)·(c·p) = 2|A|·(p−1)·p = (p+1)!·(p−1)·p = (p·(p−1))·(c·p)`、
  `c·p > 0` で cancel して `2|N| = p(p−1)`。
-/

namespace OddOrder.Isaacs.Ch01

open Equiv
open scoped Nat

section /- 1C: Problem 1C.5 (p. 18) -/

/-- `A_{p+1}` (`p` 奇素数) の位数 `p` の元と、`Perm (Fin (p+1))` の `p`-cycle
(`cycleType = {p}`) の対応が全単射であること (`Nat.card` の等式)。 -/
private lemma natCard_orderOf_eq_natCard_cycleType {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p}
      = Nat.card {g : Perm (Fin (p + 1)) // g.cycleType = {p}} := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- (i) `a ∈ A` 位数 `p` ⟹ `cycleType ↑a = {p}`
  have hdir1 : ∀ a : ↥(alternatingGroup (Fin (p + 1))), orderOf a = p →
      Perm.cycleType (a : Perm (Fin (p + 1))) = {p} := by
    intro a ha
    have hord : orderOf (a : Perm (Fin (p + 1))) = p := by
      rw [Subgroup.orderOf_coe, ha]
    obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [hord]; exact hp)
    rw [hord] at hn
    -- 台の大きさ: (n+1)·p ≤ p+1
    have hsum := Perm.sum_cycleType (a : Perm (Fin (p + 1)))
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hle : (n + 1) * p ≤ p + 1 := by
      rw [hsum]
      calc (Perm.support (a : Perm (Fin (p + 1)))).card
          ≤ (Finset.univ : Finset (Fin (p + 1))).card := Finset.card_le_univ _
        _ = p + 1 := by rw [Finset.card_univ, Fintype.card_fin]
    have hn0 : n = 0 := by
      by_contra hne
      have h2 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
      omega
    rw [hn, hn0]
    rfl
  -- (ii) `cycleType g = {p}` ⟹ 偶置換 (∈ A)
  have hdir2mem : ∀ g : Perm (Fin (p + 1)), g.cycleType = {p} →
      g ∈ alternatingGroup (Fin (p + 1)) := by
    intro g hg
    rw [Perm.mem_alternatingGroup]
    have hcyc : g.IsCycle := Perm.card_cycleType_eq_one.mp (by rw [hg]; rfl)
    have hsupp : g.support.card = p := by
      have h := Perm.sum_cycleType g
      rw [hg, Multiset.sum_singleton] at h
      exact h.symm
    rw [hcyc.sign, hsupp, hodd.neg_one_pow, neg_neg]
  -- (iii) `cycleType g = {p}` ⟹ 位数 `p`
  have hdir2ord : ∀ g : Perm (Fin (p + 1)), g.cycleType = {p} → orderOf g = p := by
    intro g hg
    rw [← Perm.lcm_cycleType, hg]
    simp
  -- 全単射
  exact Nat.card_congr
    { toFun := fun a => ⟨(a.1 : Perm (Fin (p + 1))), hdir1 a.1 a.2⟩
      invFun := fun g => ⟨⟨g.1, hdir2mem g.1 g.2⟩, by
        rw [Subgroup.orderOf_mk]
        exact hdir2ord g.1 g.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext rfl }

/-- `Perm (Fin (p+1))` の `p`-cycle の個数 `c` は `c · p = (p+1)!` をみたす
(`card_of_cycleType_mul_eq` の特殊化: `(p+1)! / ((1)!·p·1!)` の除算回避形)。 -/
private lemma natCard_cycleType_mul_eq {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    Nat.card {g : Perm (Fin (p + 1)) // g.cycleType = {p}} * p = (p + 1)! := by
  classical
  have hp : p.Prime := Fact.out
  have h := Perm.card_of_cycleType_mul_eq (α := Fin (p + 1)) ({p} : Multiset ℕ)
  rw [if_pos ?side] at h
  case side =>
    constructor
    · rw [Multiset.sum_singleton, Fintype.card_fin]; omega
    · intro a ha
      rw [Multiset.mem_singleton] at ha
      subst ha
      exact hp.two_le
  -- 係数の簡約: (p+1−p)! = 1, prod {p} = p, ∏ count! = 1
  rw [Multiset.sum_singleton, Multiset.prod_singleton, Fintype.card_fin] at h
  have h1 : p + 1 - p = 1 := by omega
  rw [h1, Nat.factorial_one, one_mul] at h
  have h2 : ∏ n ∈ ({p} : Multiset ℕ).toFinset, (({p} : Multiset ℕ).count n)! = 1 := by
    simp
  rw [h2, mul_one] at h
  -- h : #{g | g.cycleType = {p}} * p = (p+1)!  を Nat.card に読み替え
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert h using 3

end

section /- 1C.5 本体 -/

/-- **Isaacs Problem 1C.5** (multiplicative 形)。`p` 奇素数 (`3 ≤ p`)、
`G = A_{p+1}`、`P ∈ Syl_p(G)` のとき `2·|N_G(P)| = p(p−1)`。

Hint 通り位数 `p` の元 (= `p`-cycle、全て偶置換) を数える: 個数 `c` は
`c·p = (p+1)!` かつ `c = n_p(p−1)`。`|N|·n_p = |A|`、`2|A| = (p+1)!` から
`(2|N|)(c·p) = (p(p−1))(c·p)` で cancel。 -/
theorem two_mul_card_normalizer_sylow_alternating {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (P : Sylow p ↥(alternatingGroup (Fin (p + 1)))) :
    2 * Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
      = p * (p - 1) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Nontrivial (Fin (p + 1)) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  -- 2|A| = (p+1)!
  have hA2 : 2 * Nat.card ↥(alternatingGroup (Fin (p + 1))) = (p + 1)! := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  -- |A| = p·m, ¬p∣m (m = ((p+1)/2)·(p−1)!)
  obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩
  have hfac : (p + 1)! = 2 * (k * (p * (p - 1)!)) := by
    have h1 : (p + 1)! = (p + 1) * p ! := Nat.factorial_succ p
    have h2 : p ! = p * (p - 1)! := (Nat.mul_factorial_pred hp.pos.ne').symm
    rw [h1, h2, hk]
    ring
  have hAcard : Nat.card ↥(alternatingGroup (Fin (p + 1))) = p * (k * (p - 1)!) := by
    have h2 : 2 * Nat.card ↥(alternatingGroup (Fin (p + 1)))
        = 2 * (p * (k * (p - 1)!)) := by
      rw [hA2, hfac]; ring
    have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2
    exact this
  have hpk : ¬ p ∣ k * (p - 1)! := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have hk_pos : 0 < k := by omega
      have := Nat.le_of_dvd hk_pos h
      omega
    · rw [Nat.Prime.dvd_factorial hp] at h
      omega
  have hm0 : 0 < k * (p - 1)! := Nat.mul_pos (by omega) (Nat.factorial_pos _)
  -- Sylow p は位数 p ちょうど
  have hcSyl : ∀ Q : Sylow p ↥(alternatingGroup (Fin (p + 1))),
      Nat.card (Q : Subgroup ↥(alternatingGroup (Fin (p + 1)))) = p :=
    sylow_card_eq_prime_of_card_eq_mul hAcard hpk hm0
  -- 計数: c = n_p·(p−1), c·p = (p+1)!
  have hc_eq : Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p}
      = Nat.card (Sylow p ↥(alternatingGroup (Fin (p + 1)))) * (p - 1) :=
    natCard_orderOf_eq_of_sylow_card_eq hcSyl
  have hcp : Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p} * p
      = (p + 1)! := by
    rw [natCard_orderOf_eq_natCard_cycleType hp3]
    exact natCard_cycleType_mul_eq hp3
  -- |N|·n_p = |A|
  have hNn : Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
      * Nat.card (Sylow p ↥(alternatingGroup (Fin (p + 1))))
      = Nat.card ↥(alternatingGroup (Fin (p + 1))) := by
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.card_mul_index _
  -- cancel 用の正値
  have hc_pos : 0 < Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p} := by
    rcases Nat.eq_zero_or_pos
      (Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p}) with h0 | h0
    · exfalso
      have := hcp
      rw [h0, zero_mul] at this
      exact (Nat.factorial_pos (p + 1)).ne' this.symm
    · exact h0
  -- (2|N|)·(c·p) = (p(p−1))·(c·p) → cancel
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos hc_pos hp.pos :
      0 < Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p} * p)
  calc 2 * Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
        * (Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p} * p)
      = 2 * Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
        * ((Nat.card (Sylow p ↥(alternatingGroup (Fin (p + 1)))) * (p - 1)) * p) := by
        rw [hc_eq]
    _ = 2 * (Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
        * Nat.card (Sylow p ↥(alternatingGroup (Fin (p + 1))))) * ((p - 1) * p) := by
        ring
    _ = 2 * Nat.card ↥(alternatingGroup (Fin (p + 1))) * ((p - 1) * p) := by rw [hNn]
    _ = (p + 1)! * ((p - 1) * p) := by rw [← mul_assoc, hA2, mul_assoc]
    _ = p * (p - 1)
        * (Nat.card {a : ↥(alternatingGroup (Fin (p + 1))) // orderOf a = p} * p) := by
        rw [hcp]; ring

/-- **Isaacs Problem 1C.5**。`p` 奇素数 (`3 ≤ p`)、`G = A_{p+1}`、`P ∈ Syl_p(G)` のとき
`|N_G(P)| = p(p−1)/2` (書籍の除算形)。 -/
theorem card_normalizer_sylow_alternating {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (P : Sylow p ↥(alternatingGroup (Fin (p + 1)))) :
    Nat.card ↥(Subgroup.normalizer (P : Set ↥(alternatingGroup (Fin (p + 1)))))
      = p * (p - 1) / 2 := by
  have h := two_mul_card_normalizer_sylow_alternating hp3 P
  omega

end

end OddOrder.Isaacs.Ch01
