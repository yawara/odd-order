---
id: 68
slug: s08-casebcoherence2-split
title: "S08_CaseBCoherence2.lean 分割 (1561>1500, B frontier 凍結後)"
created: 2026-06-15
---

# S08_CaseBCoherence2.lean 分割 (1561>1500, B frontier 凍結後)

## 背景

`OddOrder/Peterfalvi/S08_CaseBCoherence2.lean` が **1561 行**(粒度規約の 1,500 行閾値超)。
merge monitor のサイズ watch で検出(2026-06-15、Lane B の Pf (6.8.2.3) seam-1 直交補題群
合流 `7c55fae1` で 1436→1561)。これは **Lane B (lane-b) の active frontier**(case-B
coherence の disjointness machine を継続実装中)なので、F の `S13_PrimeActionTransition`
(issue 0067)と同型 = **frontier が動いている間は分割しない**(凍結境界が定まらないため)。

## やること

- [ ] **トリガー条件**: Lane B が (6.8.2.3) disjointness/seam クラスタを landing し、
      S08_CaseBCoherence2 への追記が止まったら(= frontier 凍結)実施。
- [ ] **分割 owner = hub**(prefix-split)。B の frontier と衝突しない凍結境界(先頭 K 宣言)を
      上流 leaf へ押し出し、残りがそれを import。前方参照は構文上不可ゆえ任意の宣言境界で安全。
- [ ] 分割後 `lake build OddOrder OddOrder.AxiomsCheck` 緑 + 実 sorry 不変を確認。
- [ ] 新 leaf を `OddOrder.lean` の root closure に登録(import 行)。

## 完了条件

S08_CaseBCoherence2.lean(と派生 leaf)がいずれも 1,500 行以下、build 緑、sorry 不変。

## 参照

- 手順: [`notes/meta/merge_monitor.md`](../notes/meta/merge_monitor.md) サイズ watch + 分割メカニズム
- 同型先行例: issue 0067 (`S13_PrimeActionTransition` 2357 行, Lane F frontier)
- 検出コミット: `7c55fae1` (Merge 'lane-b' seam-1 orthogonality)

## 2026-06-15 追記 (session 42): トリガー成立 — frontier が新 leaf へ移動

Lane B の active assembly が **新 leaf `S08_CaseBAssembly.lean`** へ移動 (session 42)。
S08_CaseBCoherence2 は現 **2157 行**(さらに増、cY 一般化 `per_phi_anchored_image` 込み)で
**frontier 凍結**(B は今後 S08_CaseBCoherence2 へ追記せず、S08_CaseBAssembly で作業)。
⟹ **分割トリガー成立。hub は prefix-split 実施可**。

凍結境界の候補: 先頭の汎用 helper 群(`inner_compHom_of_mulEquiv` 〜 `per_constituent_Y_eq_smul`
あたり、行 ~429–924 = 純 ℂ-線形/aggregate/pinning helper、case-B 固有でない)を上流 leaf へ。
case-B 固有部 (ticVdiff 系・coherent extension・columnDecompositionTau 等 ~1052+) は残置。
⚠ `per_phi_anchored_image` (cY 一般化済) は S08_CaseBAssembly が import するので、分割後も
S08_CaseBAssembly の import closure に入ること。

## 🧾 注記 (2026-07-02 hub 全体レビュー): トリガー発火 — 実行可

- **trigger 成立**: (6.8) capstone close 済 — Pf S08 band は **実 sorry 0** (comment-strip
  で確認, 2026-07-02)。lane b の frontier は §12 tower / (6.5.c) へ移動済。
- **実行可 (hub batch)**。ただし `S08_PGroupReduction` / `S07_Coherence*` (lane b active)
  は本 batch の対象外。
- 行数 refresh (2026-07-02): `S08_CaseBCoherence2.lean` = **2187 行**。

## ✅ 完了 (2026-07-15)

- `S08_CaseBCoherence2/ConstituentPinning.lean` (1076 行) を上流 leaf として切り出した。
- 親 `S08_CaseBCoherence2.lean` は 689 行となり、下流 module 名と import closure を維持した。
- 宣言 multiset は分割前後で一致し、当該クラスタの実 `sorry` は 0 → 0。
- `lake build OddOrder OddOrder.AxiomsCheck`: 4243 jobs 完走、AxiomsCheck OK。
