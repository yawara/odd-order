/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

/-!
# Peterfalvi §1: Introduction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Chapter §1 (pp. 1-2, mmd 40 行) の Lean 化.

**結果数**: 0 (本節は導入文・FT 戦略宣言のみ. 番号付き結果なし.)

形式化先 (本ファイル): `OddOrder/Peterfalvi/S01_Introduction.lean` — docstring + namespace
declaration のみ. 実体は持たない (mmd 内容は本 docstring に圧縮した上で本書 §3 以降で
本格形式化).

ROADMAP 位置: **Phase 2b 第 1 波** (前提なし, BG 並行可).

## §1 の内容: FT 定理証明戦略の宣言

Peterfalvi §1 は **Feit-Thompson 定理 (1963)** の証明戦略を改めて宣言する:

> **Feit-Thompson 定理**: 奇数位数の有限群は可解である.
>
> **同値形**: 奇数位数の非可換単純群は存在しない.

証明の **二部構成**:

1. **第一部 (局所構造分析)**: 最小反例 G を仮定し、G の最大部分群の構造を研究.
   - 部分的: [Su] (Suzuki 1957)
   - 中程度: [FHT] (Feit-Hall-Thompson 1960)
   - 完全: [FT] (Feit-Thompson 1963) Chapter III, IV
   - **改訂版**: [BG] = Bender-Glauberman 1994 — **本プロジェクト Phase 2a**

2. **第二部 (指標論分析)**: 指標論を用いて第一部の出力から矛盾を導出.
   - 原典: [FT] Chapter V
   - **改訂版**: **本書 Peterfalvi 2000** — **本プロジェクト Phase 2b**

[BG] と Peterfalvi は **相互独立に読める** (Peterfalvi §8 で必要な [BG] 結果をレビュー
する設計). ただし §9, §10-§16 で BG 結果を頻繁に参照.

## 本プロジェクトでの位置付け

| Phase | 内容 | 対応 |
|---|---|---|
| Phase 1 | Isaacs FGT (前提一式) | 群論基礎 + Frobenius + Transfer |
| Phase 2a | [BG] (局所解析) | FT 第一部 |
| **Phase 2b** | **本書 Peterfalvi** | **FT 第二部 (指標論)** |
| Phase 3 | BG App.C ≅ Peterfalvi §9 / §16 統合 | 最終矛盾 |
| Phase 4 | `FeitThompson` メイン定理 | 完成 |

## 前提知識: Isaacs [Is] 1976 (Character Theory of Finite Groups)

⚠️ 注意: 本書 [Is] は **Isaacs *Character Theory of Finite Groups* (Academic Press
1976)** であり, 本プロジェクトが採用する **Isaacs *Finite Group Theory*
(AMS GSM 92, 2008)** とは別書. 内容の多くは重複するが、章番号体系が異なる.

Peterfalvi が前提とする [Is] (Character Theory 1976) の章節:

- **Ch.1-2**: 既約指標 + 直交関係 + 誘導・制限 (基本)
- **Ch.3 (3.1)-(3.7), (3.11), (3.14)**: 既約指標個数・次数, Galois auto, 実指標
- **Ch.4 (4.1), (4.2), (4.20), (4.21)**: 部分群制限・誘導, Frobenius criterion
- **Ch.5 (5.1)-(5.5), (5.7)-(5.9)**: Transfer + focal subgroup + Thompson 系
- **Ch.6 (6.1)-(6.8), (6.10), (6.11), (6.28), (6.32)-(6.34)**: Frobenius 群 +
  complement/kernel/character
- **Ch.7 (7.1)-(7.7)**: Thompson 定理 + normal p-complement
- **Problem 2.2**: `χ^σ` (σ ∈ Aut(Q_n)) が既約指標

⚠️ audit 訂正 (2026-05-23): mathlib v4.29.1 character theory infrastructure は
これらの大部分を **カバーしていない**:
- `ClassFunction G` 型不在
- Classical induced character `(Ind χ)(g)` formula 不在 (categorical `IndV`
  coinvariants のみ)
- `ZIrr G` (virtual character lattice) 不在
- Brauer permutation lemma ([Is] Thm 6.32) 不在
- Character-level Frobenius reciprocity (numerical) 不在
- Inertia subgroup + induction from inertia ([Is] Thm 6.11) 不在
- Clifford theorem ([Is] Thm 6.5) 不在
- Schur center bound ([Is] Cor 2.30) 不在

**Wave 1a 新規 shared modules** が真の Phase 2b 前提条件:
`OddOrder/GroupTheory/RepresentationTheory/` 配下 11 件 ~1100 LOC + `OddOrder/GroupTheory/TISubset.lean`.
詳細: `notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md` §3.1.

## その他の参照

- **[HB]** Huppert-Blackburn *Finite Groups* (1982): Thm 12.4 (Ch.XI) — p-群構造
- **[H]** Huppert *Endliche Gruppen* (1967): Satz 8.18 (Kap.V) — p-群部分群格子
- **[BG]** Bender-Glauberman *Local Analysis for the Odd Order Theorem* (1994):
  Phase 2a で形式化中. §9, §10-§16 で多用.
- **[FT]** Feit-Thompson "Solvability of groups of odd order" (1963): 原典.
- **[Si1]** Sibley "Coherence in finite groups containing a Frobenius section"
  (*Illinois J. Math.* 20, 1976): 本書 §8 (6.8) Main Theorem の基盤.
  ⚠️ audit 訂正: 旧 per-section ノートの "Sibley 1984 Contemp. Math. 47" は捏造,
  正は本 [Si1] 1976. "Reynolds 1965 Duke Math. J." も捏造で存在せず.
- **[Su]** Suzuki "The nonexistence of a certain type of simple groups of odd
  order" (Proc. AMS 1957): 付録 A で再録.
- **[L]** Lang *Algebra* Ch.VIII Thm 3.1: cyclotomic auto.

## 本書全体構成 (Peterfalvi 自身の宣言)

> "The text is divided into sections. Sections 1 to 7 contain preliminary results.
> Sections 8 to 14 study a minimal counterexample to the Feit-Thompson Theorem."

| Peterfalvi | 内容 | Phase 2b 位置 |
|---|---|---|
| §1-§2 | 序 + 記号 | 本ファイル + `S02_Notation.lean` |
| §3-§8 | **指標論基本 + Dade isometry + Coherence (前提)** | 第 1-3 波, **山場** |
| §9 | Non-existence of a certain type ≡ BG App.C | 第 4 波, Phase 3 統合 |
| §10-§15 | 最小単純群 G の Type I-V 分析 | 第 5-6 波 |
| §16 | G の非存在 = FT 完了 | 第 6 波, Phase 4 直前 |

**結果番号体系**: `(N.M)` 形式 (N 節, M 番号) で Hypothesis/Theorem/Lemma 列挙.
中間補題は `(N.M.1)`, `(N.M.2)` etc. ⚠️ audit 訂正: §4-§8 で旧 overview の
`^**(N.M)**` grep が top-bolded label のみ拾い (2.7)-(2.11), (3.6)-(3.9),
(4.6)-(4.10), (5.7)-(5.9), (6.5)-(6.8) 完全欠落. per-section ノートで訂正済.

## 形式化対象

**本ファイル**: なし (docstring のみ). §1 は導入文.

**次ファイル** `S02_Notation.lean`: 記号対応表 (Peterfalvi ↔ mathlib). 実体定義は
mathlib 既存 API への notation alias と若干の helper のみ.

**§3 以降**: 番号付き結果を Lean 化.

## 関連ノート

- 全体: [`notes/peterfalvi/_overview.md`](../../notes/peterfalvi/_overview.md)
- §1+§2 詳細: [`notes/peterfalvi/s01s02_intro_notation.md`](../../notes/peterfalvi/s01s02_intro_notation.md)
- §3-§8 audit: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../../notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md)
- 3 冊間 cross-ref: [`notes/meta/phase2_cross_refs.md`](../../notes/meta/phase2_cross_refs.md)
-/

namespace OddOrder.Peterfalvi.S01

-- §1 は導入文のみ. 形式化対象なし.
-- Phase 2b 全体の context は本 docstring に集約.

end OddOrder.Peterfalvi.S01
