---
id: 78
slug: s16-mainresults-split
title: "S16_MainResults split — 2614行 (>1500), lane-f active frontier (Prop 16.1 bridges)"
created: 2026-06-23
---

# S16_MainResults split — 2614行 (>1500), lane-f active frontier (Prop 16.1 bridges)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

size-watch (2026-06-23): `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` が **2614 行** (>1500)。
lane-f の active frontier (Prop 16.1 forward bridges = `proposition_type_classification` の 7 残 bridge:
hFI/hP1neIIIIV/hP1eqV/hIF/hIIP2/hIIIIVP1/hVP1, issue 8015) ゆえ、分割は **active frontier と衝突しない
凍結境界待ち**。lane-f が Prop 16.1 bridges を一段落させたら hub が prefix-split (Theorem A-E 等の凍結クラスタを
上流 leaf へ、Prop 16.1/Thm I/II の active 部を残す)。

## 完了条件

frozen 境界で prefix-split し、各 leaf <1500 行 (or active leaf のみ frontier に残す)。実施 owner = hub。
