/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import OddOrder.Isaacs.Ch03_SplitExtensions

/-!
# OddOrder.Isaacs.Ch04 — Commutators (Main, 設計のみ)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4
"Commutators" (pp. 113-146) の Lean 化 — **本 commit はファイル設計と mathlib 対応表のみ**.
実 Lemma 実装は次セッション以降.

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 4A | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | 設計段階 |
| 4B | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | TODO |
| 4C | A acts on G via automorphisms | 4.20 – 4.27 | TODO |
| 4D | Coprime action: Fitting + Thompson P×Q + Baer | 4.28 – 4.38 | TODO |

## 方針

mathlib `Commutator/Basic.lean` の API を活用. mathlib に直接対応する補題は
**薄いラッパーを書かない** (CLAUDE.md "no mathlib wrapper" policy). 教科書 ↔ mathlib
対応は本 docstring 内の表で記録.

## Mathlib direct correspondence (no wrapper)

| Isaacs | mathlib | 場所 |
|---|---|---|
| `[g₁, g₂] = 1 ↔ g₁ g₂ = g₂ g₁` | `commutatorElement_eq_one_iff_mul_comm` | `Commutator/Basic.lean:36` |
| `⁅H, K⁆ = ⁅K, H⁆` | `Subgroup.commutator_comm` | `Commutator/Basic.lean:129` |
| `[g₁,g₂] ∈ ⁅H,K⁆` if `g₁∈H, g₂∈K` | `Subgroup.commutator_mem_commutator` | `Commutator/Basic.lean:88` |
| 生成元判定 `⁅H₁,H₂⁆ ≤ M ↔ ...` | `Subgroup.commutator_le` | `Commutator/Basic.lean:92` |
| **Lemma 4.2** quotient `f(⁅H,K⁆) = ⁅fH, fK⁆` | **`Subgroup.map_commutator`** | `Commutator/Basic.lean:183` |
| `⁅H,K⁆ = ⊥ ↔ H ⊆ Z_G(K)` | `Subgroup.commutator_eq_bot_iff_le_centralizer` | `Commutator/Basic.lean:101` |
| `⁅H₁, H₂⁆ ≤ H₂` (H₂ normal 仮定) | `Subgroup.commutator_le_right` | `Commutator/Basic.lean:152` |
| `⁅⊤, H⁆ ≤ H ↔ H normal` | `Subgroup.commutator_top_left_le_iff` | `Commutator/Basic.lean:160` |
| 下降中心列 `G^k` | `lowerCentralSeries`, `lowerCentralSeries_succ` | `Nilpotent.lean:299, 316` |

注: mathlib `lowerCentralSeries` の index 規約は Isaacs `G^k` と **オフセット 1 ずれ** —
mathlib `lcs 0 = ⊤ = G^1`, `lcs 1 = G' = G^2`, `lcs n = G^{n+1}`. 本 chapter 全体で
mathlib offset を採用する.

## §4A 着手予定

* **Lemma 4.1** (`H, K normalize ⁅H, K⁆`): TODO. mathlib `commutator_normal` は両者 normal 仮定要;
  本補題は仮定なし一般版で `[xy, z] = x ⁅y, z⁆ x⁻¹ ⁅x, z⁆` 元 identity 経由で証明 (Isaacs p.114).
  `Subgroup.map (MulAut.conj x) ⁅H, K⁆ ≤ ⁅H, K⁆` を `commutator_le` + 生成元 conj 経由で示す
  方針. ~30 LOC 推定.
* **Lemma 4.2**: mathlib `Subgroup.map_commutator` 直接対応, no wrapper.
* **Lemma 4.3** (`K ≤ N(H) ↔ ⁅H, K⁆ ≤ H`): TODO. mathlib `commutator_top_*_le_iff` は K = ⊤ のみ.
  任意 K へ拡張. `k y k⁻¹ = ⁅k, y⁆ * y` element identity 経由 (⇐ direction) + k⁻¹ ∈ K の対称
  論法 (⇒ direction). ~40 LOC 推定. 本セッションで実装試行したが `group` tactic timeout が
  発生 (heartbeats 200000 不足). 次セッションで再試行: maxHeartbeats 増やすか, `Subgroup.normalizer`
  の coercion 路を整理する.

ノート: [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md)
-/

namespace OddOrder.Isaacs.Ch04

-- 意図的に空. 上記 docstring が§4A 着手前の設計記録. 実装は次セッション以降.

end OddOrder.Isaacs.Ch04
