---
id: 124
slug: file-size-watch-1500
title: "1500 行超 leaf の分割 watch (S01_Solvable / TypeP1Criteria)"
created: 2026-07-19
---

# 1500 行超 leaf の分割 watch (S01_Solvable / TypeP1Criteria)

## 背景

2026-07-18 深夜の合流 tick (merge `ba8dfe04` = lane b / `e4407935` = lane c) で、
CLAUDE.md「ファイル粒度」の hub gate (1,500 行超ファイルへの追記を検出したら flag + 分割 issue 起票)
に該当した:

| file | 行数 | owner | 状況 |
|---|---|---|---|
| `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` | 1560 | c | 本 tick で +156 (Cn 三段論法系) → 1500 を新たに超過 |
| `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeP1Criteria.lean` | 1655 | c | 既に超過、本 tick で +16 |
| `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremsAE.lean` | 1800 | c | 2026-07-19 tick (merge `2a2df98`) で検出。本 tick では -60 行 (15.7(b) 強化に伴う恒真 disjunct 削除) と**減少方向**だが、watch 対象中で最大。`PisetBetaDisjoint.lean` (1469) は 1500 直下ゆえ次の追記で超過見込み |
| `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean` | 1728 | a | 2026-07-19 tick (merge `1e1b0ed`) で追記 — 新規検出。Lem 3.1 本体は新 leaf `SplitExtensionUniqueness.lean` に切られており (lane trigger 遵守)、Basic.lean 側は薄い wrapper 追加のみ |

`OddOrder/AxiomsCheck.lean` (9790 行) は機械列挙 file ゆえ**恒久例外** (対象外)。

## やること

- [ ] どちらかが **2000 行 (本リポジトリの hard 上限、CLAUDE.md 2026-07-09 裁定)** に達したら hub が
      凍結境界で分割する。両者とも現状 2000 未満ゆえ **即時分割は必須でない** — 本 issue は watch。
- [ ] 分割時の形: ディレクトリ化を第一候補 — `S01_Solvable.lean` は pure re-export hub 化 →
      `S01_Solvable/<Topic>.lean` の topic leaves。`TypeP1Criteria` は既に `S16_MainResults/` 配下ゆえ
      flat な兄弟 prefix-split で足りる。いずれも module 名不変 = 下流 import 無変更。
- [ ] lane c 側 trigger の再確認: 同 file に**次の主結果番号**を書き始めるときは新 leaf を切る
      (同一 file 追記は「現に証明中の定理の helper」のみ)。

## 完了条件

両 file が 1500 行未満に戻る (分割実施)、または frontier が離れて追記が止まり watch 不要と hub が判断。

## 参照

- CLAUDE.md「開発規約 > ファイル粒度」/ `notes/meta/merge_monitor.md` (hub gate)
- issue 0103 (機械分割の道具立て: preamble 再現・private public 化・sorry/宣言/namespace 文脈保存検証)
