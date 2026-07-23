---
id: 0146
slug: lint-lane-c-owned
title: "lane c 所有ファイルの lint backlog 解消 (baseline ratchet down)"
created: 2026-07-23
---

# lane c 所有ファイルの lint backlog 解消 (baseline ratchet down)

## 背景

issue 0138 の zero-warning ratchet gate は baseline 199 (2026-07-23)。CLAUDE.md「lint 警告ゼロ方針」
= **自領域の残 backlog は frontier 通過時に owner が解消する**。lane c は Q₈ (hub 裁定で低優先繰延)
待ちの間に、**lane-c 所有ファイルの lint backlog** を掃いて baseline を ratchet down する。

owner 境界 (hub 9407/9318 裁定): lane c = **BG/** + Peterfalvi/Appendices/{NearFields,
ExceptionalNearField, SemilinearField, RankOneAffineModel, NearFieldClass, Huppert} +
GroupTheory/NearFieldFromSharplyTransitive** 等の near-field 系。
⚠ **除外 (他レーン所有・触らない)**: Peterfalvi/Appendices/Suzuki/** (lane b) /
Suzuki2Groups/** (lane b Higman) / FeitSibley* (lane a)。

## 対象 (baseline TSV の lane-c-owned 行)

安全な機械カテゴリから: `style.show` (show→change) / `style.longLine` / `style.header` /
`deprecation` / `unusedSimpArgs` / `unnecessarySimpa` / `unusedVariables` / `unusedSectionVars`。
⚠ `flexible` (AppE_FiliformGroup 67 / AppE_FiliformCounterexample 6) は leaf build で検出不能な
cascade を起こす (0123 で main 2 回破壊) ので **full build + 敵対的検証必須** — 慎重に別途。
`style.openClassical` (SemilinearField) は statement-dependent (issue 0133) ゆえ owner 判断。

## 完了条件

lane-c-owned 行の warning を解消し、full check-warnings green + baseline 更新 (ratchet down)。
build green・AxiomsCheck 非退行・sorry 非退行を維持。

## 参照

- issue 0138 (zero-warning gate) / 0123 (linter cleanup) / 0133 (openClassical)
- `bin/lint-baseline.tsv` / `bin/check-warnings`

## 進捗 (2026-07-23 lane c) — 安全な機械カテゴリ 37 件解消

full build 検証中。解消した lane-c-owned warning (37 件):

| ファイル | カテゴリ | 件数 |
|---|---|---|
| Peterfalvi/Appendices/NearFields.lean | style.show 10 / style.longLine 7 / deprecation(push_neg→push Not) 2 | 19 |
| Peterfalvi/Appendices/ExceptionalNearField.lean | style.header (copyright block 追加) | 1 |
| BG/AppE_ExponentP.lean | style.show | 4 |
| BG/AppE_FurtherResults.lean | style.show 2 / style.longLine 1 | 3 |
| BG/AppE_EigenvalueCombinatorics.lean | style.longLine | 2 |
| BG/AppE_AbelianCentralizer.lean | style.longLine 1 / unusedVariables(_hcard) 1 | 2 |
| BG/AppD_CNGroups/MaximalSylowIntersection.lean | unusedSectionVars (`omit hne in` + caller 修正) | 1 |
| BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean | style.longLine (docstring reflow) | 4 |
| BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeBridges.lean | style.longLine | 1 |

**繰延 (grandfather 継続)**:
- `S03g_Thm310General.lean` の `K` unusedVariables (1): caller (`:427`) が `(K := …)` で named 参照
  → `_K` rename は caller 破壊。theorem body では未使用だが external 参照ゆえ触らない (revert 済)。
- **`flexible` (AppE_FiliformGroup 67 / AppE_FiliformCounterexample 6 = 73)**: leaf build 検出不能な
  cascade リスク (0123 で main 2 回破壊) → **full build + 敵対的検証を要する別途慎重パス**に繰延。
- `SemilinearField.lean` の `style.openClassical` (1): statement-dependent (issue 0133)、owner 判断繰延。

baseline は full build 確認後 199→~162 に ratchet down 予定。
