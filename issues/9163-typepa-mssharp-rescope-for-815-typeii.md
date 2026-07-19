---
id: 9163
slug: typepa-mssharp-rescope-for-815-typeii
title: "HUB: (8.15) type-II 完全形式化に向けた typePA の M_s^# 添字化設計確認 (9008 re-open trigger)"
created: 2026-07-19
---

# HUB: (8.15) type-II 完全形式化に向けた typePA の M_s^# 添字化設計確認 (9008 re-open trigger)

lane a → hub。issue 1042 着手順 3 の gate (1042 の gate 注記が「着手時に 9000 issue で
hub に設計確認を出すこと」と指定)。

## 背景

- **9008 裁定 (closed)**: repo の `typePA` は `(M′)^#` 添字固定 (`typePA_eq_sharpSubgroup_derivedInG`)。
  書籍 (8.10) は core `M_s^#` 添字 (`A(M) = ⋃_{x∈M_s^#} C_{M′}(x)^#`) で、type P₂ (= type II,
  `M_s = M_F ⊊ M′`) では書籍の A(M) は真に小さい (`(M′)^# ∩ …`、Frobenius 補元点 `U^#` を除く)。
  9008 は「全 consumer が P₁ 域でのみ使う」ことを根拠に Option B (現状維持 + IsTypeP1 narrow) を
  採用し、「S-side honest 化の設計変更が起きた場合のみ Option A (typePA 訂正) を再検討・re-open」
  と裁定した。
- **trigger 発火**: 全 3 冊フェーズで (8.15) の**番号としての完全形式化** (type II 込み) が
  lane a の割当に入った (issue 1042)。着手順 1 ((5.2) instance, P₁ 域) と 2 ((4.6) instance,
  H = M_F / M_s 両方、P₁ 域) は 2026-07-19 に完了:
  `OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean` / `S10_Hypothesis46TypeP.lean` (axiom-clean)。
  残り = type II での忠実な A(M) を要する部分のみ。

## 設計分岐 (hub 裁定を求める点)

type II で書籍忠実な `A(M)` をどう持つか:

- **Option A (9008 の再検討対項)**: `typePA` 自体を `M_s^#` 添字に訂正
  (`centralizerSupport (sharpSubgroup M_s) (derivedInG M)` 相当へ)。
  - 影響: shared infra。`typePA` の全 consumer (S10/S12/S13/S15 系、lane b の S12/S14 consumer
    含む) に波及。P₁ 域では `M_s = M′` ゆえ値は不変だが、`typePA_eq_sharpSubgroup_derivedInG` が
    「P₁ 仮定つき」へ弱まり、全 rw 箇所に IsTypeP1 仮定が伝播する。
  - 利点: (8.10)/(8.15) が全型で書籍どおり 1 本の def で立つ。
- **Option B′ (新 def 並置)**: `typePA` は現状維持 (P₁ 域専用のまま)、型 II 用に別 def
  (例: `typePACore M data` = `M_s^#` 添字版) を新設し、(8.15) type-II instance はそちらで立てる。
  P₁ 域では `typePACore = typePA` の等式 lemma で接続。
  - 影響: 既存 consumer 無変更 (波及ゼロ)。二重定義の管理コスト + 「どちらが正本か」の
    docstring 明示が必要。
- 前提の追加確認事項: repo に `M_s` (Peterfalvi (8.10) の core; type I/II/V = M_F, III/IV = M′)
  の def が既にあるか (BG 側 `Msigma`/FTcore 系との対応込み) の実測。無ければ M_s def の
  新設から (これ自体は ungated)。

lane a の推奨 = **Option B′** (波及ゼロ、9008 の「P₁ 域は現状維持」裁定と両立、
type II instance が必要とする最小追加)。ただし cross-lane 影響 (lane b の S12/S14) を持つのは
Option A のみなので、hub の裁定対象は「A を再検討するか、B′ で確定するか」。

## 追記 (2026-07-19, lane a): (8.18) も本裁定に gated

(8.15) だけでなく **(8.18) の一般化も同じ gate に当たる** (frontier note 項目 8 の次候補として
実測): 書籍 (8.18) は S, T を型仮定なしの非共役 maximal で述べ、証明中で
「A(T) − A₁(T) ≠ ∅ ⟹ T は type I/II」を導出する (PDF p.49 確認済)。repo の (8.18.a/b/c) は
`TypeIData S/T` 固定 (S10_MinimalSimpleStructure.lean:404/481/575) で、type-II 側へ広げるには
**type II の忠実な A(T)** が要る — つまり P₂ 域の typePA 問題そのもの。type-II consumer が
(8.18.b) を導出せず structure field `cross_zero` として仮定している件も、この gate が解けるまで
解消不能。⟹ 本裁定の scope は (8.15) type-II instance + (8.18) 一般化 + cross_zero 導出の 3 件。

## やること

- [ ] hub: Option A vs B′ を裁定 (必要なら consumer grep で波及を実測)
- [ ] 裁定後 lane a: M_s def の実測 → (無ければ) 新設 → type-II 側 (8.15) instance
      (claim 1 の typeII datum は既存 = `S10_MinimalSimpleBasic` の typeII instance;
      claim 2 は `typePData_toHypothesis46_hallKernel` が H 側は既に忠実 (type II で
      M_s = M_F)、A 側の差し替えのみ; claim 3 は `S10_SubcoherentTypeP` の A パラメータ
      差し替え)

## 完了条件

hub 裁定が本 issue に記録され、lane a が type-II 側 (8.15) instance の実装方針を
一意に決められる状態になること。

## 参照

- issues/closed/9008 (Option B 裁定と re-open 条件)
- issues/1042-pf-8-15-dade-hypothesis-instances.md (着手順 3 の gate 注記)
- OddOrder/GroupTheory/MaximalSubgroupType.lean:436 (`typePA_eq_sharpSubgroup_derivedInG` の
  caveat docstring = 9008 の要約)
- OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean / S10_Hypothesis46TypeP.lean (P₁ 側完了分)
