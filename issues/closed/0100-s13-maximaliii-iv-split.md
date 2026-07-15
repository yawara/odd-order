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

## 更新 (2026-07-08 監視 tick)

- caseB rewire (9.11) 進行に伴い **3,024 → 3,524 行** に成長 (+500)。lane a の active frontier
  (`caseB_sOf_memberRFamily` per-member R-family dispatcher + reduction 補題群) がこの file 内。
- **⚠ 分割は a の caseB rewire (9075 step 3、hRorth 3-way dispatch 残) が landing してから** —
  今は全域が active frontier ゆえ凍結境界が取れず prefix-split が frontier と衝突する。
  rewire 完遂後に hub が凍結クラスタ (§13.1-13.x の landed 部) を上流 leaf へ push する。

## 更新 (2026-07-08 監視 tick #2)

- caseB rewire 3/3 完成 (hDeg 撤去) landing で **S13_MaximalIII_IV 3,524 → 3,672 行**。
- **⚠ 新規: S13_CoreStructure.lean が 1,556 行で 1,500 を超過** (このクラスタで 2 つ目の large file)。
  両 S13 file とも a の active frontier (S13 char-核) ゆえ分割は依然保留。
- 9075 (norm-general engine + caseB rewire) は CLOSE 済。次の S13 frontier が落ち着いた段階で
  hub が両 file の凍結クラスタ (§13.1-13.x landed 部) を上流 leaf へ prefix-split する。

## ✅ CLOSED (hub 裁定 2026-07-15 tick #8): S13_MaximalIII_IV 1207行 (<1500), split 完了。実施 owner=hub の split 完了確認済。
