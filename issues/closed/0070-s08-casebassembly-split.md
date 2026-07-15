---
id: 70
slug: s08-casebassembly-split
title: "S08_CaseBAssembly.lean 分割 (1518行>1500, size watch)"
created: 2026-06-16
---

# S08_CaseBAssembly.lean 分割 (1518行>1500, size watch)

## 背景

`OddOrder/Peterfalvi/S08_CaseBAssembly.lean` が **1518 行**に到達し粒度規約 1,500 行上限を超過
(merge monitor size watch 検出、2026-06-16)。Lane B が (6.8.2.3) case-B coherence assembly を
本ファイルで active に証明中 (CaseBColBundle / CaseBIrrBundle constructor + linchpin 群)。

分割 owner = **hub** (merge_monitor.md 規約: lane の frontier と衝突しない凍結境界で prefix-split)。

## トリガー条件 (いつ実行するか)

**今すぐは実行しない** — B が毎 tick このファイルに active commit 中で、今 prefix-split すると B の次マージと
確実に conflict する。以下のいずれかで実行:

- [ ] B が **(6.8) capstone `sibleySetup_is_coherent` を完全 landing** して case-B assembly が一段落、または
- [ ] B が明示的に idle/pause、または
- [ ] B 自身が次の主結果で新 leaf を切る (lane 側デフォルト) で自然に縮む

## やること (prefix-split 案)

凍結している先頭部 (bundle 定義 + 基本 helper 群) を上流 leaf へ切り出し、active frontier
(最終 assembly / HYBRID union wiring) を `S08_CaseBAssembly` に残す:

- [ ] 候補 leaf `S08_CaseBBundles.lean` (または同等) = `CaseBColBundle` / `CaseBIrrBundle` 構造体 +
      各 constructor (hcol/hirr) + column/irreducible-branch helper 群 (凍結境界は B の最新 frontier 次第)。
- [ ] `S08_CaseBAssembly` は上流 leaf を import し、最終 (6.8.2.3) assembly を残す。
- [ ] 新 leaf を `OddOrder.lean` (+ 必要なら AxiomsCheck) に import (root closure)。
- [ ] full build green + AxiomsCheck OK + sorry 不変を確認。
- [ ] 切る境界は B の最新 frontier を見て決定 (前方参照不可ゆえ任意の宣言境界で安全)。

## 完了条件

- S08_CaseBAssembly.lean が 1,500 行以下、または topic-coherent に分割完了。
- build green / AxiomsCheck OK / sorry 不変。

## 参照

- 規約: `notes/meta/merge_monitor.md`「サイズ watch」、CLAUDE.md「分割の owner と trigger」
- 関連: issue 0068 (S08_CaseBCoherence2 split, 別ファイル)、[[feedback-record-deferred-hub-tasks-as-issues]]
- notes: `notes/peterfalvi/s08_6_8_assembly_plan.md` (B の (6.8.2.3) frontier)

## 🧾 注記 (2026-07-02 hub 全体レビュー): トリガー発火 — 実行可

- **trigger 成立**: (6.8) capstone close 済 — Pf S08 band は **実 sorry 0** (comment-strip
  で確認, 2026-07-02)。lane b の frontier は §12 tower / (6.5.c) へ移動済。
- **実行可 (hub batch)**。ただし `S08_PGroupReduction` / `S07_Coherence*` (lane b active)
  は本 batch の対象外。
- 行数 refresh (2026-07-02): `S08_CaseBAssembly.lean` = **1988 行**。

## ✅ 完了 (2026-07-15)

- `S08_CaseBAssembly/BranchBundles.lean` (1032 行) を上流 leaf として切り出した。
- 親 `S08_CaseBAssembly.lean` は 994 行となり、下流 module 名と import closure を維持した。
- 宣言 multiset は分割前後で一致し、当該クラスタの実 `sorry` は 0 → 0。
- `lake build OddOrder OddOrder.AxiomsCheck`: 4243 jobs 完走、AxiomsCheck OK。
