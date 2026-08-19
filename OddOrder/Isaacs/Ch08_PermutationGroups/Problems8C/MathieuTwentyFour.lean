/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuEleven
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.SimpleStabilizer

/-!
# Isaacs Problem 8C.5 (p. 257) — 次数 24 の 5-transitive 群

`G` が 24 点集合に 5-transitive に作用し, 3 点の安定化群が単純なら, 2 点の安定化群,
1 点の安定化群, そして `G` 自身がすべて単純。

**Note** (Isaacs)。これは Mathieu 群 `M₂₂`, `M₂₃`, `M₂₄` を記述している。3 点安定化群は
`PSL(3, 4)` に同型で, `21 = (4³ - 1)/(4 - 1)` 点に 2-transitive に作用する
(Lemma 8.29)。

## 証明の流れ

Wielandt 9.1 (`SubMulAction.ofStabilizer.isMultiplyPretransitive`) で 1 点ずつ剥がす:

| 段 | 群 | 台集合 | 濃度 | 可移度 |
|---|---|---|---|---|
| 0 | `G` | `Ω` | 24 | 5 |
| 1 | `G_α` | `Ω ∖ {α}` | 23 | 4 |
| 2 | `G_αβ` | `Ω ∖ {α,β}` | 22 | 3 |
| 3 | `G_αβγ` | `Ω ∖ {α,β,γ}` | 21 | 2 (仮説: 単純) |

* 段 2 (22 点) と段 0 (24 点) は `22 = 2·11`, `24 = 2³·3` が相異なる 2 素数で割れるので
  `isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer` が直接効く。
* 段 1 (23 点) は素数次数なので `isSimpleGroup_of_two_transitive_of_prime_card` を使う。
  そこで要求される `|G_αβ| ≠ 22` は「位数 22 の単純群は存在しない」から従う。

## Main results

- `not_isSimpleGroup_of_card_eq_twentytwo` — 位数 22 の単純群は存在しない。
- `isSimpleGroup_of_five_transitive_degree_twentyfour` — **Problem 8C.5** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8C.5 -/

/-- 位数 22 の単純群は存在しない。Sylow `11`-部分群の個数は `2` を割り `1 (mod 11)` に
合同なので `1`, つまり正規で真の非自明部分群。 -/
theorem not_isSimpleGroup_of_card_eq_twentytwo {H : Type*} [Group H] (h : Nat.card H = 22) :
    ¬ IsSimpleGroup H := by
  intro hsimp
  have := hsimp
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 11) (G := H)
  have hPcard : Nat.card (P : Subgroup H) = 11 :=
    card_sylow_eq_prime_of_not_dvd_sq P (by rw [h]; norm_num) (by rw [h]; norm_num)
  have hn : Nat.card (Sylow 11 H) = 1 := by
    have hidx : (P : Subgroup H).index = 2 := by
      have h2 := Subgroup.card_mul_index (P : Subgroup H)
      rw [hPcard, h] at h2
      omega
    have hdvd : Nat.card (Sylow 11 H) ∣ 2 := hidx ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow 11 H) ≡ 1 [MOD 11] := card_sylow_modEq_one 11 H
    unfold Nat.ModEq at hmod
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · rw [h1] at hmod
      omega
  have : Subsingleton (Sylow 11 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  have : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup H) inferInstance with hb | ht
  · rw [hb] at hPcard
    simp at hPcard
  · rw [ht, Subgroup.card_top, h] at hPcard
    omega

/-- mathlib の `IsMultiplyPretransitive _ _ 2` から, **Problem 8A.9** 系の補題が要求する
2-transitivity の形へ。 -/
theorem two_transitive_of_isMultiplyPretransitive {G Ω : Type*} [Group G] [MulAction G Ω]
    (h : IsMultiplyPretransitive G Ω 2) :
    ∀ a b c : Ω, b ≠ a → c ≠ a → ∃ g : G, g • a = a ∧ g • b = c := by
  intro a b c hb hc
  rw [MulAction.is_two_pretransitive_iff] at h
  exact h (Ne.symm hb) (Ne.symm hc)

/-- **Isaacs Problem 8C.5** (p. 257)。24 点への 5-transitive な忠実作用で 3 点の安定化群が
単純なら, 2 点の安定化群・1 点の安定化群・`G` 自身がすべて単純。

**Note** (Isaacs)。これは Mathieu 群 `M₂₂`, `M₂₃`, `M₂₄` を記述している。 -/
theorem isSimpleGroup_of_five_transitive_degree_twentyfour
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]
    (hΩ : Nat.card Ω = 24) [h5 : IsMultiplyPretransitive G Ω 5]
    (α : Ω) (β : ↥(SubMulAction.ofStabilizer G α))
    (γ : ↥(SubMulAction.ofStabilizer ↥(stabilizer G α) β))
    (h3 : IsSimpleGroup ↥(stabilizer ↥(stabilizer ↥(stabilizer G α) β) γ)) :
    IsSimpleGroup ↥(stabilizer ↥(stabilizer G α) β) ∧
      IsSimpleGroup ↥(stabilizer G α) ∧ IsSimpleGroup G := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  -- 段 0: `G` は `Ω` (24 点) に 5-transitive
  have : IsPretransitive G Ω :=
    is_one_pretransitive_iff.mp
      (isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by rw [hΩ]; norm_num))
  -- 段 1: `G_α` は `Ω ∖ {α}` (23 点) に 4-transitive
  have h4 : IsMultiplyPretransitive ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) 4 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive (n := 4) (a := α)).mp h5
  have : FaithfulSMul ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) :=
    faithfulSMul_ofStabilizer α
  have hc1 : Nat.card ↥(SubMulAction.ofStabilizer G α) = 23 := by rw [card_ofStabilizer, hΩ]
  have : IsPretransitive ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) :=
    is_one_pretransitive_iff.mp
      (isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by rw [hc1]; norm_num))
  -- 段 2: `G_αβ` は `Ω ∖ {α, β}` (22 点) に 3-transitive
  have h3t : IsMultiplyPretransitive ↥(stabilizer ↥(stabilizer G α) β)
      ↥(SubMulAction.ofStabilizer ↥(stabilizer G α) β) 3 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive (n := 3) (a := β)).mp h4
  have : FaithfulSMul ↥(stabilizer ↥(stabilizer G α) β)
      ↥(SubMulAction.ofStabilizer ↥(stabilizer G α) β) := faithfulSMul_ofStabilizer β
  have hc2 : Nat.card ↥(SubMulAction.ofStabilizer ↥(stabilizer G α) β) = 22 := by
    rw [card_ofStabilizer, hc1]
  have : IsPretransitive ↥(stabilizer ↥(stabilizer G α) β)
      ↥(SubMulAction.ofStabilizer ↥(stabilizer G α) β) :=
    is_one_pretransitive_iff.mp
      (isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by rw [hc2]; norm_num))
  -- 段 2 の結論: `22 = 2·11`
  have hs2 : IsSimpleGroup ↥(stabilizer ↥(stabilizer G α) β) :=
    isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer γ
      (two_transitive_of_isMultiplyPretransitive
        (isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by rw [hc2]; norm_num)))
      h3 (p := 2) (q := 11) Nat.prime_two (by norm_num) (by norm_num)
      (by rw [hc2]; norm_num) (by rw [hc2]; norm_num)
  -- 段 1 の結論: 素数次数 23, `|G_αβ| ≠ 22`
  have hs1 : IsSimpleGroup ↥(stabilizer G α) :=
    isSimpleGroup_of_two_transitive_of_prime_card β
      (two_transitive_of_isMultiplyPretransitive
        (isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by rw [hc1]; norm_num)))
      hs2 (by norm_num) hc1
      (fun hcard => not_isSimpleGroup_of_card_eq_twentytwo (by simpa using hcard) hs2)
  -- 段 0 の結論: `24 = 2³·3`
  refine ⟨hs2, hs1, ?_⟩
  exact isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer α
    (two_transitive_of_isMultiplyPretransitive
      (isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by rw [hΩ]; norm_num)))
    hs1 Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hΩ]; norm_num) (by rw [hΩ]; norm_num)

end -- Problem 8C.5

end OddOrder.Isaacs.Ch08
