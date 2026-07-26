/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.DQSDRecognition
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B6

/-!
# Isaacs Problem 6B.7 — 指数 2 の巡回部分群を持つ非可換 2-群 (書籍 p. 196)

**主張**: `P` を非可換 `2`-群で指数 `2` の巡回部分群 `C = ⟨c⟩` を持つものとする。
`|P : Z(P)| > 4` なら `P` は二面体群・半二面体群・一般四元数群のいずれか。

**構成**: repo には既に **Isaacs Lemma 6.13** が両分岐とも在る
(`DQSDRecognition.lean` の `dihedralOrQuaternion_of_invertingConjugation` /
`semiDihedral_of_twistConjugation`)。したがって仕事は

> `a ∈ P − C` の `C` への作用が `c ↦ c⁻¹` (inverting) か `c ↦ z c⁻¹` (twist) のどちらか

を示すことに尽きる。`C` は指数 `2` ゆえ正規で `a² ∈ C` は `C` を中心化するので, `a` の誘導
自己同型は位数 `∣ 2`。巡回なので `a c a⁻¹ = c^j` と書け `j² ≡ 1 (mod 2^m)`, したがって
**6B.6 の `sq_eq_one_iff_two_pow`** から `j ∈ {1, -1, 2^(m-1)+1, 2^(m-1)-1}` の 4 通り。

* `j = 1`: `P = ⟨a, c⟩` が可換になり非可換仮定に反する。
* `j = 2^(m-1)+1`: `a c² a⁻¹ = (zc)² = c²` なので **`⟨c²⟩ ≤ Z(P)`**, ゆえに
  `|P : Z(P)|` は `|P : ⟨c²⟩| = 4` を割り, 仮定 `> 4` に反する。
* 残る `j = -1` / `j = 2^(m-1)-1` がちょうど Lemma 6.13 の 2 分岐。
-/

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

section /- 6B.7: 指数 2 の巡回部分群を持つ非可換 2-群 (p. 196) -/

/-- `a` の `C = ⟨c⟩` への共役作用の 4 分類 (`m ≥ 3`, `orderOf c = 2^m`)。

`a² ∈ C` が `C` を中心化するので誘導自己同型は位数 `∣ 2`, すなわち `a c a⁻¹ = c^j` の
`j` は `j² ≡ 1 (mod 2^m)` をみたし, 6B.6 (`sq_eq_one_iff_two_pow`) で 4 通りに決まる。 -/
theorem conj_eq_four_cases_of_index_two {P : Type*} [Group P] [Finite P]
    {c a : P} {m : ℕ} (hm : 3 ≤ m) (hord : orderOf c = 2 ^ m)
    (h_idx : (Subgroup.zpowers c).index = 2) :
    a * c * a⁻¹ = c ∨ a * c * a⁻¹ = c⁻¹ ∨
      a * c * a⁻¹ = c ^ (2 ^ (m - 1)) * c ∨ a * c * a⁻¹ = c ^ (2 ^ (m - 1)) * c⁻¹ := by
  sorry

/-- **Isaacs Problem 6B.7** (p. 196) ⭐: 指数 `2` の巡回部分群を持つ非可換 `2`-群 `P` が
`|P : Z(P)| > 4` をみたすなら, `P` は二面体・半二面体・一般四元数のいずれか。 -/
theorem dihedralOrQuaternionOrSemiDihedral_of_index_two_cyclic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    {c a : P} {m : ℕ} (hm : 3 ≤ m) (hord : orderOf c = 2 ^ m)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_center : 4 < (Subgroup.center P).index) :
    Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
      Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) ∨
      ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k) := by
  classical
  -- `z := c ^ (2 ^ (m-1))` は `C` の唯一の involution
  set z : P := c ^ (2 ^ (m - 1)) with hz
  have hzsq : z ^ 2 = 1 := by
    have hmm : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ]; congr 1; omega
    rw [hz, ← pow_mul, hmm, ← hord]
    exact pow_orderOf_eq_one c
  have hzne : z ≠ 1 := by
    rw [hz]
    intro hcon
    have hdvd : orderOf c ∣ 2 ^ (m - 1) := orderOf_dvd_of_pow_eq_one hcon
    rw [hord] at hdvd
    exact absurd (Nat.le_of_dvd (by positivity) hdvd)
      (by exact Nat.not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  rcases conj_eq_four_cases_of_index_two (a := a) hm hord h_idx with h | h | h | h
  · -- `a` が `c` を中心化 ⟹ `P` 可換で矛盾
    exfalso
    sorry
  · exact (dihedralOrQuaternion_of_invertingConjugation hP c a h_idx h_a_notmem h).imp
      id Or.inl
  · -- `a c a⁻¹ = z c` ⟹ `⟨c²⟩ ≤ Z(P)` で `|P : Z(P)| ∣ 4`
    exfalso
    sorry
  · refine Or.inr (Or.inr ?_)
    refine semiDihedral_of_twistConjugation hP h_nonab c a z h_idx h_a_notmem
      (by rw [hz]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
      hzsq hzne ?_ h
    -- `z` は `C` の唯一の involution
    intro y hy hy2 hyne
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : c ^ (2 * k) = 1 := by
      rw [mul_comm, zpow_mul]
      exact_mod_cast hy2
    have h2 : ((orderOf c : ℤ)) ∣ 2 * k := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at h2
    have h3 : ((2 : ℤ) ^ (m - 1)) ∣ k := by
      have hsplit : ((2 ^ m : ℕ) : ℤ) = 2 * 2 ^ (m - 1) := by
        have hm1 : m = (m - 1) + 1 := by omega
        rw [hm1]
        push_cast
        ring
      rw [hsplit] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    obtain ⟨t, rfl⟩ := h3
    have hzsq' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hzsq
    have hzt : c ^ ((2 : ℤ) ^ (m - 1) * t) = z ^ t := by
      rw [hz, ← zpow_natCast c (2 ^ (m - 1)), ← zpow_mul]
      norm_cast
    rw [hzt] at hyne ⊢
    rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact absurd (by rw [hu, show u + u = 2 * u by ring, zpow_mul, hzsq', one_zpow]) hyne
    · rw [hu, zpow_add, zpow_mul, hzsq', one_zpow, one_mul, zpow_one]

end

end OddOrder.Isaacs.Ch06
