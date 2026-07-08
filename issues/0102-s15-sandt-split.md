---
id: 102
slug: s15-sandt-split
title: "S15_SAndT.lean split (4569 行 >1500) — active frontier 凍結後に prefix-split"
created: 2026-07-08
---

# S15_SAndT.lean split (4569 行 >1500) — active frontier 凍結後に prefix-split

## 背景

`OddOrder/Peterfalvi/S15_SAndT.lean` が merge-monitor のサイズ watch (粒度規約 1,500 行) を
超過。2026-07-08 の合流 tick (`a3ecec5c` lane c (13.18.c) gammaGrid_orthogonal_one 実証明化)
時点で **4569 行**。merge_monitor.md 手順 4 に従い flag + 起票。

⚠ **この file は active dual-lane frontier**:
- **lane b** = §16 char cascade ((13.9)-(13.19)) の char-family/(C')# 系 (~845 周辺)
- **lane c** = (13.18) S-side A0-rewire ブロック (~4147 `gammaGrid_defGamma` 周辺、carve-out 9076 4c-3)

両レーンが同 file を active に編集中ゆえ、**今 prefix-split すると frontier と衝突する**。
hub の prefix-split は**凍結境界**で行う規約 (merge_monitor.md 手順 4) — S15_SAndT は未凍結。
∴ 実分割は **frontier 沈静化まで deferred** (下記トリガー)。

## やること

- [ ] frontier 沈静化を待つ (b の char cascade landing + c の (13.18) gate discharge が一段落)
- [ ] 沈静化後、凍結クラスタ (先頭 K 宣言) を上流 file (例 `S15_SAndT_Core.lean`) へ prefix-split、
      残り (active frontier) が import。owner = hub (lane frontier と非衝突な宣言境界で切る)
- [ ] 下流は hub file を import するだけで不変を確認

## 完了条件

S15_SAndT.lean (または後継 leaf 群) が各 1,500 行以下、full build green・sorry 不変・
下流 import 不変。

## 参照

- merge_monitor.md 手順 4 (サイズ watch) / CLAUDE.md「ファイル粒度」
- 姉妹 split issue: [0094](0094-s15-setup-split.md) (S15_SAndT_Setup.lean)
- content 依存: [9076](9076-cyclicti-rigidity-dade-crossrel.md) (c の (13.18) carve-out)、
  [1016](1016-tside-typepdata-threading.md)、[3003](3003-gammagrid-overstatement-and-crossrel.md)
- 検出 tick: 合流 `a3ecec5c` (2026-07-08)
