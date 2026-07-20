---
id: 134
slug: split-appe-furtherresults-2000
title: "分割: AppE_FurtherResults.lean が 2016 行 (CLAUDE.md 上限超過) — c の frontier 通過後に prefix-split"
created: 2026-07-20
---

# 分割: `AppE_FurtherResults.lean` が 2016 行 (CLAUDE.md 上限超過)

## 検出 (2026-07-20 15:53 hub tick)

lane c が BG App.E の E.3(b) Step 2 を猛烈な速度で積んだ結果 (本日だけで (E.4)〜(E.12))、
`OddOrder/BG/AppE_FurtherResults.lean` が **2016 行**に達し、CLAUDE.md「ファイル粒度」の
**hard 上限 2000 行**を超えた。2000 行超は現在 `AxiomsCheck.lean` (機械列挙・per-file 例外) と
`S03f_Thm36.lean` (3822、既知) に次いで 3 本目。

## ⏸ 今は分割しない (意図的)

分割の実施 owner は hub (merge_monitor.md) だが、**lane c が数分おきに同ファイルへ commit している
最中**に切ると衝突が確実。frontier が (E.10)-(E.12) = ファイル末尾にあるため、末尾を触りながらの
prefix-split は c の未コミット作業を巻き込む危険がある。

⟹ **c が App.E を締めた (= E.3(b) 全体が landing した) 時点で実施**する。

## 分割案 (実測した section 構造)

| 行 | section | 状態 |
|---|---|---|
| 68-286 | `HallCollection` | 凍結 (E.1 系、sorry-free) |
| 290-359 | `RegularPGroup` | 凍結 (Step 1 は `GroupTheory/RegularPGroup.lean` に外出し済) |
| 363-1973 | `RegularOperator` | **c の active frontier** — E.3(b) 本体、内部に `### The structure of C_R(R₀) = R₀ × R₁` (478-) / `### (E.6): BG's descending series` (1119-) の小見出し |
| 1977-2014 | `MaximalApplication` | 凍結 |

**第一案 (flat な兄弟 prefix-split、module 名不変ゆえ下流無変更)**:
先頭の凍結 2 section (`HallCollection` + `RegularPGroup`、~290 行) を
`OddOrder/BG/AppE_HallCollection.lean` へ切り出し、`AppE_FurtherResults` がそれを import する。
残 ~1730 行で上限内に収まる。

**第二案 (ディレクトリ化)**: `AppE_FurtherResults.lean` を pure re-export hub にして
`AppE_FurtherResults/{HallCollection,RegularOperator,MaximalApplication}.lean` に分ける。
`RegularOperator` が 1600 行と大きいので、E.6 の下降列 (1119-1709) を更に割る余地がある。
c の frontier が落ち着いてからならこちらが筋。

## 完了条件

`AppE_FurtherResults.lean` (および分割後の各 leaf) が 2000 行以下になり、full build green。

## 参照

- CLAUDE.md「ファイル粒度」(本リポジトリ上限 2000 行、mathlib は 1500)
- `notes/meta/merge_monitor.md`「分割の owner と trigger」
- `issues/3021-appe-hall-collection.md` (lane c の App.E 本体)
- `issues/0124-file-size-watch-1500.md` (1500 行 watch)
