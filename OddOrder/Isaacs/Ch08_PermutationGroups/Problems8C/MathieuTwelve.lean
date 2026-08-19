/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuEleven
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.SimpleStabilizer

/-!
# Isaacs Problem 8C.3 (p. 256) — 次数 12, 位数 95040 の推移置換群は単純

`Ω` を 12 点集合, `G` を `Ω` 上忠実かつ推移的に作用する位数
`95040 = 12·11·10·9·8` の群とすると `G` は単純。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₂` に同型。

## 証明の流れ (Isaacs のヒント)

1. 点安定化群 `G_α` は位数 `7920` で `Ω ∖ {α}` (11 点) に忠実に作用する。Sylow
   `11`-部分群が regular なので `G_α` は `Ω ∖ {α}` に推移的, すなわち `G` は
   **2-transitive**。さらに **Problem 8C.2** より `G_α` は**単純**。
2. `1 ≠ N ◁ G` なら `N ∩ G_α ◁ G_α` は `1` か `G_α`。後者なら `G_α ≤ N` と
   `N` の推移性 (**Problem 8A.9**) から `N = G`。よって `N ∩ G_α = 1`,
   つまり `N` は **regular** (`|N| = 12`)。
3. `N` が regular だと `n ↦ n • α` が `N ≃ Ω` を与え, 2-transitivity から
   `N ∖ {1}` の元はすべて `G` で共役 — 位数が等しくなければならない。しかし
   `|N| = 12` は位数 2 と位数 3 の元をともにもつ (Cauchy)。矛盾。
   (Isaacs の「位数 12 の群は極小正規部分群になり得ない」に対応。)

## Main results

- `isSimpleGroup_of_card_eq_95040` — **Problem 8C.3** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8C.3 本体 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- **Isaacs Problem 8C.3** (p. 256)。次数 12, 位数 `95040 = 12·11·10·9·8` の
**推移**置換群は単純。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₂` に同型。 -/
theorem isSimpleGroup_of_card_eq_95040 [IsPretransitive G Ω]
    (hΩ : Nat.card Ω = 12) (hG : Nat.card G = 95040) :
    IsSimpleGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- (1) 点安定化群は位数 7920
  have hstabcard : ∀ α : Ω, Nat.card ↥(stabilizer G α) = 7920 := by
    intro α
    have h := index_stabilizer_of_transitive (G := G) (x := α)
    rw [hΩ] at h
    have h2 := Subgroup.card_mul_index (stabilizer G α)
    rw [h, hG] at h2
    omega
  -- 点安定化群は `Ω ∖ {α}` に忠実・推移的に作用し, さらに単純 (Problem 8C.2)
  have hcard11 : ∀ α : Ω, Nat.card ↥(SubMulAction.ofStabilizer G α) = 11 := by
    intro α
    rw [card_ofStabilizer, hΩ]
  have htrans : ∀ α : Ω,
      IsPretransitive ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) := by
    intro α
    have := faithfulSMul_ofStabilizer (G := G) α
    obtain ⟨S⟩ := Sylow.nonempty (p := 11) (G := ↥(stabilizer G α))
    have hS : Nat.card (S : Subgroup ↥(stabilizer G α)) = 11 :=
      card_sylow_eq_prime_of_not_dvd_sq S (by rw [hstabcard α]; norm_num)
        (by rw [hstabcard α]; norm_num)
    have := isPretransitive_of_card_eq_prime (by norm_num) (hcard11 α) _ hS
    refine ⟨fun a b => ?_⟩
    obtain ⟨s, hs⟩ := exists_smul_eq ↥(S : Subgroup ↥(stabilizer G α)) a b
    exact ⟨s, hs⟩
  have hsimple : ∀ α : Ω, IsSimpleGroup ↥(stabilizer G α) := by
    intro α
    have := faithfulSMul_ofStabilizer (G := G) α
    exact isSimpleGroup_of_card_eq_7920 (hcard11 α) (hstabcard α)
  -- (2) `G` は 2-transitive (Problem 8A.9 が要求する形)
  have h2 : ∀ α β γ : Ω, β ≠ α → γ ≠ α → ∃ g : G, g • α = α ∧ g • β = γ := by
    intro α β γ hβ hγ
    have := htrans α
    obtain ⟨g, hg⟩ := exists_smul_eq ↥(stabilizer G α)
      (⟨β, (SubMulAction.mem_ofStabilizer_iff G α).mpr hβ⟩ :
        ↥(SubMulAction.ofStabilizer G α))
      ⟨γ, (SubMulAction.mem_ofStabilizer_iff G α).mpr hγ⟩
    exact ⟨(g : G), mem_stabilizer_iff.mp g.2, congrArg Subtype.val hg⟩
  -- (3) 単純性 (共通補題: 2-transitive + 点安定化群が単純 + `12 = 2^2·3`)
  obtain ⟨α⟩ : Nonempty Ω := (Nat.card_pos_iff.mp (by omega)).1
  exact isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer α h2 (hsimple α)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [hΩ]; norm_num)
    (by rw [hΩ]; norm_num)

end -- Problem 8C.3

end OddOrder.Isaacs.Ch08
