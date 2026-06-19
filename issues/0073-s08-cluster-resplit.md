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
