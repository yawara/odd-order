---
id: 73
slug: s08-cluster-resplit
title: "S08 cluster re-split (CoherenceCore* / CaseB* が >1500 に再膨張)"
created: 2026-06-19
---

# S08 cluster re-split (CoherenceCore* / CaseB* が >1500 に再膨張)

## 背景

Lane B の (6.8) case-B coherence frontier の活発な進行で、S08 系の複数ファイルが
粒度規約 (1,500 行) を大きく超えて再膨張した。`S08_CoherenceCore` は旧 issue 0066 で
一度分割済 (closed) だが 3949 行に再成長。merge_monitor サイズ watch (2026-06-19 tick)
で検出。

現状 (2026-06-19, 1500 行超の S08 系):

| ファイル | 行数 |
|---|---|
| `S08_CoherenceCorePart2.lean` | 4662 |
| `S08_CoherenceCore.lean` | 3949 (旧 0066 で分割済→再膨張) |
| `S08_CoherenceCorePart1.lean` | 3452 |
| `S08_CaseBCoherence2.lean` | 2185 (issue 0068) |
| `S08_CaseBAssembly.lean` | 1988 (issue 0070) |
| `S08_CaseBCoherence.lean` | 1516 (2026-06-20 tick で 1500 超過、(6.8.2.2) m=2 relabel 追記による) |

## やること

- [ ] (6.8) capstone 着地後、上表の各ファイルを prefix-split (先頭の凍結済 K 宣言を
      上流 leaf へ、残りが import)。root closure (OddOrder.lean) + AxiomsCheck 追記。

## 完了条件

S08 系の各ファイルが概ね 1,500 行以下に収まり、full build green + axiom-clean を維持。

## owner / trigger

- **owner**: hub (prefix-split, lane B の frontier と衝突しない凍結境界で)。
- **trigger**: **Lane B の (6.8) capstone (`S08_CoherenceTheorems:59`) が閉じた後**。
  それまで S08 は B の active frontier ゆえ凍結境界が取れない。reducible-break チェーン
  step 1-8 + case-A glue は完了済、残 = (6.8.3) bootstrap (notes cont.²⁵)。

## 参照

- 既存 split issue: 0068 (CaseBCoherence2) / 0070 (CaseBAssembly) — 同 trigger
- 旧 (closed): 0066 (CoherenceCore 初回分割)
- 規約: CLAUDE.md「ファイル粒度」/ notes/meta/merge_monitor.md「サイズ watch」

## 🧾 注記 (2026-07-02 hub 全体レビュー): トリガー発火 — 実行可

- **trigger 成立**: (6.8) capstone (`S08_CoherenceTheorems:59`) close 済 — Pf S08 band は
  **実 sorry 0** (comment-strip で確認, 2026-07-02)。
- **実行可 (hub batch)**。ただし `S08_PGroupReduction` (570 行, lane b active 系) /
  `S07_Coherence*` (lane b active) は対象外。
- 行数 refresh (2026-07-02, 1500 行超の S08 系):

  | ファイル | 行数 |
  |---|---|
  | `S08_CoherenceCore.lean` | 5842 |
  | `S08_CoherenceCorePart2.lean` | 4836 |
  | `S08_CoherenceCorePart1.lean` | 3452 |
  | `S08_CaseBCoherence2.lean` | 2187 (issue 0068) |
  | `S08_CaseBAssembly.lean` | 1988 (issue 0070) |
  | `S08_CaseBCoherence.lean` | 1516 |

## ✅ 完了 (2026-07-15)

凍結済み S08 coherence cluster を topic-coherent な8組へ再分割した。

| 親 module (分割後) | 新しい上流 leaf |
|---|---|
| `S08_CaseBCoherence2.lean` (689) | `ConstituentPinning.lean` (1076) |
| `S08_CaseBAssembly.lean` (994) | `BranchBundles.lean` (1032) |
| `S08_YsetInner.lean` (702) | `CharacterBreaks.lean` (1055) |
| `S08_CoherenceCorePart1.lean` (682) | `CoherentAdjoin.lean` (1044) |
| `S08_YsetConjugation.lean` (1125) | `InducedFamilies.lean` (534) |
| `S08_DegreeSums.lean` (931) | `CoherenceGlue.lean` (730) |
| `S08_CoherenceCorePart2.lean` (330) | `SibleyBounds.lean` (1326) |
| `S08_CaseBCoherence.lean` (800) | `CentralCongruence.lean` (755) |

- S08 全体を再監査し、最大 1497 行・1500 行超 0 件を確認。
- 8組すべてで宣言 multiset が分割前後一致し、当該ファイル群の実 `sorry` は 0 → 0。
- repository 全体の実 `sorry` は 25 で不変、root import closure も維持。
- `lake build OddOrder OddOrder.AxiomsCheck`: 4243 jobs 完走、AxiomsCheck OK。
- 個別 issue #0068 / #0070 も本 batch で完了。
