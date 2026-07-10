---
id: 108
slug: s04-dadeisometry-split
title: "S04_DadeIsometry.lean 分割 (1555 行 > 1500 閾値)"
created: 2026-07-10
---

# S04_DadeIsometry.lean 分割 (1555 行 > 1500 閾値)

## 背景

- 2026-07-10 監視 tick の lane a 合流 (merge 2afd06a6、Pf (2.5) Dade 像支持制限 bound
  `exists_base_of_map_apply_ne_zero` 追加) で `OddOrder/Peterfalvi/S04_DadeIsometry.lean` が
  1536→**1555 行**。main 時点で既に 1500 flag 閾値を超えていたが分割 issue 未起票だった
  (すり抜け) ので本 issue で追跡する (repo hard 上限 = 2000 行)。
- S04 は Dade isometry の基盤 file で lane a の active frontier ((8.18.b) 部品供給) が
  かかっている。分割は frontier と衝突しない**凍結境界での prefix-split** に限る。
- 分割実施 owner = **hub** (merge_monitor.md step 4)。第一候補は directory 化
  (`S04_DadeIsometry.lean` を pure re-export hub 化し、実体を `S04_DadeIsometry/<Topic>.lean` へ)
  または flat な兄弟 prefix-split (module 名不変・下流 import 無変更)。

## やること

- [ ] hub: a の (8.18.b) 供給が一段落したタイミング (または 2000 行接近で即時) で、
      冒頭の凍結クラスタ (Dade map 定義 + 基本 API 等、a の現 frontier が編集しない部分) を
      新 leaf へ prefix-split (記述的英語名、内容で命名)
- [ ] build green + AxiomsCheck OK を確認、a へ issue/notes で通知

## 完了条件

S04_DadeIsometry.lean が 1,500 行未満に戻り、full build green + AxiomsCheck OK。

## 参照

- issues/0107-s14-minimalcounterexample-split.md (同型の直近先例)
- notes/meta/merge_monitor.md step 4 (サイズ watch) / CLAUDE.md「ファイル粒度」
- merge 2afd06a6 (lane a、Pf 2.5/10.7)
