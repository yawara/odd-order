---
id: 9000
slug: hub-witness-coherence-unsound-and-6-5-c-clifford
title: "HUB裁定: witness coherence (12.6) 3-case 修正の優先度 + (6.5.c)/構成的Clifford の shared-infra 割当"
created: 2026-07-01
---

# HUB裁定: witness coherence (12.6) 3-case 修正 + shared-infra 割当

lane b (β, Pf §12/S14) が (5.5) landing 後の frontier 精査で発見した 2 件の設計事項。
**lane b は待たず tractable な部分を進める**が、以下は hub 裁定 / 割当が要る。

## 事項 1: `sibleyTarget_frobI` / `frobenius_typeI_coherent` は現状 unsound (issue 2032 詳細)

- (6.8)(a) は「H^# is a TI-subset of G」必須。だが Pf (12.10) は (12.16) witness で「H^# is **not**
  TI in G」と明言 → `SibleyDadeHypothesis.dade_H_eq_bot` が偽 → `sibleyTarget_frobI` は witness で unprovable。
- 正しい (12.6) 証明は **3-case split** (H^# TI→(6.8) / abelian→(5.7) / exp∣p-1→(6.5.c))。
- **lane b の対応 (裁定不要、進行中)**: `frobenius_typeI_coherent` を `TypeIData.alternative` で case-split。
  case(a) sibleyTarget+TI仮説, case(b) `coherent_of_constant_degree` 在庫。

## 事項 2 (要裁定): shared coherence/char infra の割当

**(A) (6.5.c) coherence producer** — case(c) [|L/H|∣p-1, H は p-group] の coherence。
現状 S07/S08 に**在庫なし** (`six_five_*` は numerical contradiction のみ)。§6.5 = 汎用 coherence infra。
→ **どのレーンが build する? lane b が自 case-split の一部として build してよい? α (§10-13 char) も要する見込み?**

**(A') case(b) の (5.7) route も infra 課題あり** (2026-07-01 追記): `coherent_of_constant_degree`
(S07:513) は `S07.Hypothesis` (5.2, S07:1704) を要求し、その `tau_isometry : IsIntegralIsometry tau`
は **global 等長** (全 CF(L))。だが witness の Dade map `hyp.tau` は dim CF(L) > dim CF(G) ゆえ
global isometry でない (IsCoherent が lattice-relative に weakened されている理由と同じ)。⟹
`coherent_of_constant_degree` を witness の hyp.tau に直接使えない。case(b) は **Dade-map ベースの
等次数 coherence producer** (global isometry を要さない lattice-relative 版、`isCoherent_pair_of_differenceImage`
(S07:86) の等次数 n-member 一般化) が要る。→ **これも coherence infra の build 事項。**

**(B) 構成的 Clifford correspondence (issue 0026)** — M-side (12.14) が gated (issue 0026, notes loop⁶¹)。
`typeI_induced_char_constituents` / `constituent_diff_support_subset_nonescaping` が
Ind_H^L θ の構成要素分解 (Isaacs 6.2/6.11 + Pf 1.7) を要す。現状 `clifford_decomposition` は
conditional 形のみ (構成的 producer なし)。→ **shared infra、claim-before-build 対象。lane b が
claim して build? α も §10-13 char で要する見込み — 重複回避の調整要。**

## 裁定してほしいこと

1. 事項 1 の case-split 修正、lane b が進めてよいか (owned file 内なので進めるが、hub 認識のため)。
2. (6.5.c) coherence を lane b が build するか、別レーン/別 issue に割り当てるか。
3. 構成的 Clifford (issue 0026) の claim を lane b が取るか、α と調整するか。

## 参照
- issues/2032 (sibleyTarget_frobI unsound 詳細), issue 0026 (Clifford core)
- notes/peterfalvi/s14_maximalI.md loop⁶⁰-⁶²
- Pf 原文: 04.8 (6.8), 04.14 (12.6/12.9/12.10)
