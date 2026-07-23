---
id: 146
slug: lint-lane-c-owned
title: "lint backlog — lane c 所有分 (BG AppE / Pf NearFields / BrauerSuzuki / BG Ch4) の解消"
created: 2026-07-23
---

# lint backlog — lane c 所有分の解消

親 issue = [0138](0138-zero-warning-gate.md)。本 issue は **lane c が territory 所有する file の残 lint 警告**を列挙。
方針は [0144](0144-lint-lane-a-owned.md) 冒頭「方針」節と共通。lane c は残 backlog **最大 (123 件)** で、
うち **`flexible` 73 件が最重量** (full build + 敵対検証必須、下記)。

> ⚠ lane c の territory (AppE / NearFields / BrauerSuzuki) は c の active zone
> (2026-07-23 時点で NearFieldFromSharplyTransitive を編集中)。hub/d は触らない。

## lane c 所有ファイルと残警告 (2026-07-23 fresh build 実測、計 123 件)

### BG/AppE_* (Filiform 系) — flexible の集中

| ファイル | カテゴリ×件数 |
|---|---|
| `AppE_FiliformGroup.lean` | **`flexible` 67** / `style.show` 8 |
| `AppE_FiliformCounterexample.lean` | **`flexible` 6** |
| `AppE_ExponentP.lean` | `style.show` 4 |
| `AppE_FurtherResults.lean` | `style.show` 2 / `style.longLine` 1 |
| `AppE_EigenvalueCombinatorics.lean` | `style.longLine` 2 |
| `AppE_AbelianCentralizer.lean` | `style.longLine` 1 / `unusedVariables` 1 |

### Peterfalvi/Appendices/ (NearFields = Prop C 系)

| ファイル | カテゴリ×件数 |
|---|---|
| `NearFields.lean` | `style.show` 10 / `style.longLine` 7 / `deprecation` 2 |
| `ExceptionalNearField.lean` | `style.header` 1 |

### GroupTheory/ (Brauer–Suzuki)

| ファイル | カテゴリ×件数 |
|---|---|
| `BrauerSuzuki.lean` | `style.header` 1 |
| `BrauerSuzukiNormalizer.lean` | `style.header` 1 / `style.missingEnd` 1 |
| `BrauerSuzukiSetup.lean` | `style.header` 1 |

### BG/AppD_CNGroups/, BG/Ch4_FamilyOfMaximal/

| ファイル | カテゴリ×件数 |
|---|---|
| `AppD_CNGroups/MaximalSylowIntersection.lean` | `unusedSectionVars` 1 |
| `Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean` | `style.longLine` 4 (L417/650/663/665) |
| `Ch4_FamilyOfMaximal/S16_MainResults/TypeBridges.lean` | `style.longLine` 1 (L1027) |

## 手法メモ

- **`flexible` 73 件 (⚠ 最重量・要 full build + 敵対検証)**: `simp ... at h1 h2 ...` 等が
  fragile と判定されている。**`simp only` 化は過去 revert 実績** (issue 0123 で main を 2 回破壊) ゆえ
  **`simp?` の出力を採用** (Lean が最小 simp set を提示) するか、理由付き per-decl
  `set_option linter.flexible false in`。**leaf build では cascade を検出できない** —
  必ず **full build + 敵対的検証** (fix 後に別 build で regression ゼロ確認)。
  1 commit = 1 wave、`--update-baseline` で段階的に下げる。
- **`style.header` 4 / `style.missingEnd` 1**: 標準 4 行ヘッダ追加 / `end <section>` 補完 (機械的・安全)。
  ⚠ header は `import Mathlib.Tactic` 丸 import (0136 track) と混同しない — S05_GridTrichotomy は
  baseline 上 header だが実体は import (着手判断は census 実測で)。
- **`deprecation` 2 (NearFields)**: `push_neg`→`push Not` / `push_cast` 削除 / ncard rename の類。機械的。
- **`style.show` 24 / `style.longLine` 16**: [0145](0145-lint-lane-b-owned.md) 手法メモと同じ (per-site 判断)。
- **`unusedVariables` 1 / `unusedSectionVars` 1**: `_`-prefix / `omit ... in` (named-arg・型注意)。

## 別トラック (本 issue 対象外)

- `SemilinearField.lean` の `style.openClassical` 1 は **[0133](0133-open-scoped-classical-statement-dependent.md)** track。
- `OddOrder/FeitThompsonNuGrid.lean` の `flexible` 1 は FT spine (frozen) — hub の flexible wave で処理。

## 完了条件

lane c 所有ファイルの非 sorry 警告ゼロ → `bin/check-warnings --update-baseline`。

## 進捗 (2026-07-23 lane c セッション) — 安全な機械カテゴリ 37 件解消 + BrauerSuzuki header

full build green で以下を解消 (この issue を main の hub 版で受領し継続):

- **NearFields.lean** (19): `style.show` 10 (→`change`) / `style.longLine` 7 / `deprecation` 2 (`push_neg`→`push Not`)
- **ExceptionalNearField.lean** (1): `style.header` (copyright block 追加)
- **AppE_ExponentP** (4 `show`) / **AppE_FurtherResults** (2 `show` + 1 longLine) / **AppE_EigenvalueCombinatorics** (2 longLine) / **AppE_AbelianCentralizer** (1 longLine + `unusedVariables`→`_hcard`)
- **AppD_CNGroups/MaximalSylowIntersection** (1): `unusedSectionVars` = `omit hne in` + caller の `hne` 実引数削除
- **OpicoreCentralizer** (4 longLine) / **TypeBridges** (1 longLine)
- **BrauerSuzuki{,Normalizer,Setup}.lean**: `style.header` 3 (copyright block 追加) + `style.missingEnd` 1
  (`BrauerSuzukiNormalizer` に `end QuaternionSylowSetup` / `end OddOrder.GroupTheory` 補完) — 解消済

計 **41 件解消** (37 + BrauerSuzuki 4)。baseline は merged tree で `--update-baseline` 再生成
(main の d 第2 wave 190 を基点に、非重複の c-fixes 41 を反映 → 149 見込み)。

**繰延 (grandfather)**: `flexible` 73 (AppE_Filiform*、full build + 敵対検証の別パス) /
`SemilinearField` openClassical (0133) / `FeitThompsonNuGrid` flexible (FT spine, hub wave)。
S03g `K` は lane d が第2 wave で解消済 (本 issue 対象外)。
