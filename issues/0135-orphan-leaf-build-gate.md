---
id: 135
slug: orphan-leaf-build-gate
title: "hub gate 強化: 新 leaf の OddOrder.lean 未配線 (orphan) を毎 tick 検出する"
created: 2026-07-20
---

# hub gate 強化: 新 leaf の `OddOrder.lean` 未配線 (orphan) を毎 tick 検出する

## 事象 (2026-07-20 21:30 hub tick) — 同じ穴が 2 度目

lane c の新 leaf `OddOrder/BG/AppE_SemidirectFrattini.lean` (289 行, issue 3021 App.E Step 4) が
`OddOrder.lean` から import されておらず、**`lake build OddOrder` の import closure 外**にあった。

結果、合流 gate のフルビルドが

```
Build completed successfully (4564 jobs).   ELAPSED 0:01.31
```

と **jobs 数不変・1.3 秒で green** を返した。新規 289 行は**一度も elaborate されていない**。
import 追加後は **4565 jobs** になり、green を再確認した (commit 66f65bb59)。

⚠ **これは 2 度目**。同じ経路で c の `FormalCommutator` / `FormalCollection` /
`PolynomialSequences` の 3 本が 2 tick すり抜けている (`merge_monitor.md` の 2026-07-20 追加検査)。
前回は検査手順を note に書いたが**スクリプト本体を `... (実装は本 tick の hub 手順を参照)` の
placeholder のままにした**ため、次 tick で実行されず再発した。

## 実害の程度 (今回は軽微)

c の実装自体は健全だった: leaf 単体ビルドは green・sorry 0
(`lake build OddOrder.BG.AppE_SemidirectFrattini`, 3310 jobs)。c は自分の leaf を
ローカルで検証しており、**配線漏れのみ**。到達性を全数監査した結果、orphan は本 file 1 本だけ
(reachable 850 / total 850 に復帰)。

ただし「hub のフルビルド gate を通った」が**新規コードの検証を意味しない**状態が
2 tick 続いていた点は gate の欠陥であり、次に unsound な leaf が来たときに素通しする。

## 対処 (実施済)

1. `OddOrder.lean` に import 追加 (commit 66f65bb59)。
2. `notes/meta/merge_monitor.md` の該当節を **実行可能なスクリプトに差し替え** (placeholder 廃止)。
   併せて「**jobs 数が前 tick と同じで数秒 green なら配線漏れを疑う**」という判定のコツを明記。

## 恒久対策の候補 (未実施 — 次に触る hub が判断)

- **A. gate の手順書化で足りる** (現状)。毎 tick スクリプトを回す。人手依存が残る。
- **B. CI 的に強制**: `OddOrder.lean` の import 集合と `OddOrder/**/*.lean` の全 module 集合が
  一致するかを検査する小スクリプトを `bin/` に置き、hub tick の定形コマンドに含める。
  ⚠ 単純な「全 file を import」規則にはできない — 中間 leaf は上位 leaf 経由で到達するのが正常なので、
  **到達可能性 (transitive closure)** で見る必要がある (現行スクリプトはそうなっている)。
- **C. レーン側の規律として明文化**: 新 leaf を作ったら同じ commit で `OddOrder.lean` に配線する。
  `OddOrder.lean` は共有ファイル (merge_monitor.md の territory 表で全 lane 可) なので、
  レーンが自分で追加してよい。→ CLAUDE.md「ファイル粒度」に 1 行足すのが最も安い。

B と C は排他でない。**C を先に入れて A/B を保険にする**のが妥当と思われる。

## 関連

- `notes/meta/merge_monitor.md` 「🕳 2026-07-20 hub tick への追加検査」節 (本 issue で加筆)
- issue 0124 (1500 行 watch) — 同じく「hub tick の定形検査」系
