/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# Glauberman Replacement Theorem (Gorenstein Thm 2.7)

Gorenstein, *Finite Groups* (1968), Ch.8 §2, **Theorem 2.7** (pp. 273-275):
`P` 有限 p-群 (p odd), `B ⊴ P` class ≤ 2 with `B' ≤ Z(J(P))`, `A ∈ A(P)` が
`B` に正規化されないとき, `A* ∈ A(P)` で `A ∩ B < A* ∩ B` かつ `A* ≤ N(A)` なる
ものが存在する。`ThompsonSubgroupAbelian.lean` (定義 + Lem 2.1-2.6, 2.8) の続き。
Issue 9403 (証明分解は同 issue の「Thm 2.7 の完全分解」節)。

## 実装状況

- `commutator_sup_le_of_centralizer` — 共通 wrap-up エンジン
  (`⁅M ⊔ C, Y⁆ ≤ T` の十分条件; `A* = M ⊔ C_A(M) ≤ N(A)` の核)。
- `exists_not_le_centralizer_elementCommutator` — `x` の選択補題
  (Case 1 の `x ∈ [B,A;r-3]`, Case 2 の `x ∈ B` に共通)。
- Case 1 / Case 2 本体と組立は後続 (issue 9403)。

p odd は Case 2 (`[[x,u],[x,v]]² = 1 ⟹ = 1`) でのみ使用 — `Odd (Nat.card G)`
の形で受ける (Gorenstein 自身が p = 2 でも `[B,A;3] ≠ 1` なら成立と注記)。
-/

namespace Subgroup

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

/-- **`A* ≤ N(A)` の核となる評価**: `C` が `M` と `Y` を中心化し, `⁅M,Y⁆ ≤ T` で
`C` が `T` を正規化するなら `⁅M ⊔ C, Y⁆ ≤ T`.

分解 `↑(C ⊔ M) = C·M` (中心化 ⟹ 正規化) の good-elements 計算:
`⁅cm, y⁆ = c ⁅m,y⁆ c⁻¹` (`⁅c,y⁆ = 1`) で, `T` の `c`-共役不変性から従う.
Gorenstein Thm 2.7 の `[A*,A] = [MC_A(M),A] ⊆ [B,A;r-1]` step の一般形. -/
theorem commutator_sup_le_of_centralizer {M C Y T : Subgroup G}
    (hCM : C ≤ centralizer (M : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hMT : ⁅M, Y⁆ ≤ T) (hCT : C ≤ normalizer (T : Set G)) :
    ⁅M ⊔ C, Y⁆ ≤ T := by
  rw [commutator_le]
  intro g hg y hy
  have hCnormM : C ≤ normalizer (M : Set G) :=
    hCM.trans (centralizer_le_normalizer _)
  have hset : ((C ⊔ M : Subgroup G) : Set G) = (C : Set G) * (M : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C M hCnormM
  have hg' : g ∈ (C : Set G) * (M : Set G) := by
    rw [← hset]
    have : g ∈ C ⊔ M := by rwa [sup_comm C M]
    exact this
  obtain ⟨c, hc, m, hm, heq⟩ := hg'
  subst heq
  have hcy : ⁅c, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
    ((mem_centralizer_iff.mp (hCY hc) y hy).symm)
  have key : ⁅c * m, y⁆ = c * ⁅m, y⁆ * c⁻¹ * ⁅c, y⁆ := by group
  rw [key, hcy, mul_one]
  have hmT : ⁅m, y⁆ ∈ T := hMT (commutator_mem_commutator hm hy)
  exact (mem_normalizer_iff.mp (hCT hc) ⁅m, y⁆).mp hmT

/-- **`x` の選択補題** (Gorenstein Thm 2.7 Case 1/2 共通):
`⁅⁅X,A⁆,A⁆ ≠ ⊥` なら, `x ∈ X` で `A` が `[x,A]` を中心化しないものが存在する
(さもなくば `⁅X,A⁆` の全生成元が `A` に中心化される). -/
theorem exists_not_le_centralizer_elementCommutator {X A : Subgroup G}
    (h : ⁅⁅X, A⁆, A⁆ ≠ ⊥) :
    ∃ x ∈ X, ¬ (A ≤ centralizer (elementCommutator x A : Set G)) := by
  by_contra hall
  push Not at hall
  apply h
  rw [commutator_eq_bot_iff_le_centralizer, commutator_le]
  intro x hx a ha
  exact le_centralizer_iff.mp (hall x hx)
    (commutatorElement_mem_elementCommutator ha)

end Subgroup
