---
id: 100
slug: s13-maximaliii-iv-split
title: "サイズ watch: S13_MaximalIII_IV.lean 分割 (3,024 行、1019 frontier 急成長中)"
created: 2026-07-08
---

# サイズ watch: S13_MaximalIII_IV.lean 分割 (3,024 行、1019 frontier 急成長中)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

- 2026-07-08 監視 tick で 3,024 行を確認 (07-07 時点 2,171 行 → 1019 の (9.11) 組立で急成長)。
- 粒度規約 (CLAUDE.md): 1,500 行超ファイルへの追記は hub が分割 issue を起票、実施 owner = hub。
- ⚠ **実施タイミング注意**: 本ファイルは lane a の 1019 active frontier (毎 tick 追記中)。
  prefix-split は「lane frontier と衝突しない凍結境界」でのみ安全 → **1019 の (9.11)/(11.8)
  capstone landing 後に実施** (それまでは起票のみで待機)。凍結済み上流クラスタ (§9 counts 系の
  完成部) を先頭 K 宣言として上流ファイルへ押し出し、残りが import する標準 prefix-split。

## 完了条件

- [ ] 1019 capstone landing 確認 (trigger)
- [ ] 凍結境界の特定 (先頭側 sorry-free クラスタ)
- [ ] prefix-split 実施 + build green + 下流 import 不変
