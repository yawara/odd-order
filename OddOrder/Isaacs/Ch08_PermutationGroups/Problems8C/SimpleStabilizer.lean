/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group

/-!
# 点安定化群が単純な推移作用 (Isaacs Problems 8C.3 / 8C.4 の共通部分)

点安定化群 `G_α` が単純な推移作用では, 推移的な真の正規部分群は **regular** になる。
Isaacs Problem 8C.3 (`M₁₂`) と 8C.4 (`HS`) が共通に使う一歩。

## Main results

- `stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer` — `N ◁ G` が推移的で
  `N ≠ ⊤` なら `N` の点安定化群は自明。
- `card_eq_card_of_stabilizer_eq_bot` — そのとき `|N| = |Ω|` (regular)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 点安定化群が単純な作用 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **点安定化群が単純なら, 推移的な真の正規部分群は semiregular**。

`N ∩ G_α` は `G_α` の正規部分群なので単純性から `1` か `G_α`。後者だと `G_α ≤ N` と
`N` の推移性から `N = ⊤` になってしまうので, 前者。 -/
theorem stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer (α : Ω)
    (hsimple : IsSimpleGroup ↥(stabilizer G α))
    {N : Subgroup G} [hN : N.Normal] [IsPretransitive ↥N Ω] (hNtop : N ≠ ⊤) :
    stabilizer ↥N α = ⊥ := by
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (stabilizer G α))
      inferInstance with hbot | htop
  · have hdisj : Disjoint N (stabilizer G α) := Subgroup.subgroupOf_eq_bot.mp hbot
    have h : (stabilizer G α).subgroupOf N = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj.symm
    rw [← h]
    ext y
    rfl
  · exact absurd (eq_top_iff.mpr fun g _ => by
      have hle : stabilizer G α ≤ N := fun y hy =>
        show (⟨y, hy⟩ : ↥(stabilizer G α)) ∈ N.subgroupOf (stabilizer G α) by rw [htop]; trivial
      obtain ⟨m, hm⟩ := exists_smul_eq ↥N α (g • α)
      have hm' : ((m : ↥N) : G) • α = g • α := hm
      have hmem : (m : G)⁻¹ * g ∈ stabilizer G α := by
        rw [mem_stabilizer_iff, mul_smul, ← hm', inv_smul_smul]
      have hg : g = (m : G) * ((m : G)⁻¹ * g) := by group
      rw [hg]
      exact N.mul_mem m.2 (hle hmem)) hNtop

/-- 点安定化群が自明な推移作用 (= regular) では `|N| = |Ω|`。 -/
theorem card_eq_card_of_stabilizer_eq_bot (α : Ω) {N : Subgroup G} [IsPretransitive ↥N Ω]
    (h : stabilizer ↥N α = ⊥) : Nat.card ↥N = Nat.card Ω := by
  have hidx := index_stabilizer_of_transitive (G := ↥N) (x := α)
  rwa [h, Subgroup.index_bot] at hidx

end -- 点安定化群が単純な作用

end OddOrder.Isaacs.Ch08
