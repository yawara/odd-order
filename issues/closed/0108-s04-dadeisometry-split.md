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

- [x] 冒頭の凍結済み (2.10) Möbius assembly クラスタを、記述的英語名の directory leaf
      `S04_DadeIsometry/MobiusAssembly.lean` へ prefix-split
- [x] build green + AxiomsCheck OK を確認し、本 issue に main 統合結果を記録

## 完了条件

S04_DadeIsometry.lean が 1,500 行未満に戻り、full build green + AxiomsCheck OK。

## 実施記録 (2026-07-15, hub)

- `MobiusAssembly.lean` 597 行を新設し、親 `S04_DadeIsometry.lean` は 1007 行へ縮小。
  旧 module 名と全 downstream import は不変で、親から新 leaf を import。
- 分割前後の宣言名 multiset 一致、root closure 到達、`bin/count-sorry` 25 不変、
  `git diff --check` clean を機械確認。分割境界前に private 宣言なし。
- focused build `OddOrder.Peterfalvi.S04_DadeIsometry` 成功 (3237 jobs)。
- `lake build OddOrder OddOrder.AxiomsCheck` 成功 (4235 jobs)。
  `OddOrder.feitThompson` は allowlist 内の 3 公理のみに依存。


## 参照

- issues/0107-s14-minimalcounterexample-split.md (同型の直近先例)
- notes/meta/merge_monitor.md step 4 (サイズ watch) / CLAUDE.md「ファイル粒度」
- merge 2afd06a6 (lane a、Pf 2.5/10.7)
