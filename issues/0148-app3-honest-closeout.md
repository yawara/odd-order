---
id: 148
slug: app3-honest-closeout
title: "Appendix III honest close-out: Lemma 1(a)/Lemma 2/Prop 1/Prop 2 の実形式化"
created: 2026-07-24
---

# Appendix III honest close-out: Lemma 1(a)/Lemma 2/Prop 1/Prop 2 の実形式化

## 背景

`OddOrder/Peterfalvi/Appendices/Suzuki2Groups.lean` に居座っていた opaque-Prop
scaffold 4 本 (`square_map_quadratic` / `higman_classification` /
`typeB_field_model` / `typeB_automorphism_structure`) + 空 structure 3 本
(`QuadraticMapData` / `FiniteFieldTwoMapBasis` / `SuzukiTypeData`) は
**論理的空虚** (`⟨True, trivial⟩` で閉じるトートロジー、issue 0127 ② の audit)
のため 2026-07-24 に削除した (削除トリガー = 2048/9160 closed + Higman 完成、成立済)。

`higman_classification` は **置換不要の純削除** — 実体は
`OddOrder.Higman.Suzuki2Groups.higmanClassification` /
`higmanClassification_of_isSuzuki2Group` として完成済みで、0127 ③ の
ユーザー裁定「分類定理の薄い Peterfalvi wrapper は作らない」により
Pf 側の再掲は書かない。

残り 3 本の scaffold が指していた **App III の番号付き結果は未形式化のまま**
なので、本 issue で honest 形式化を追跡する (sorry マーカーは無いが genuine
残作業; sorry 数で進捗を測らない原則)。

## やること (文書順)

- [ ] **Lemma 1(a)**: 中心拡大 `W ≤ Z(P)`, `P/W` 元位数 ≤2, `W` 元位数 ≤2 の下で
      squaring `P/W → W` が quadratic (polar form が bilinear) — 一般形。
      Higman 側の具体形は `HigmanSquareMap.lean`
      (`lowerCentralSquareMapAdditive_add` / `lowerCentralSquareQuadraticMap_polarBilin`)
      に lower-central 特化版があるので、そこから一般化 or 独立に短証明。
      Lemma 1(b) (逆方向の構成) は `QuadraticExtensions.lean` で実装済。
- [ ] **Lemma 2**: `F_{2^n}` 上の linear / bilinear / quadratic map の基底表示
      (`x ↦ Σ aᵢ x^{2ⁱ}` 形)。`HigmanFiniteFieldTrace.lean` に部分素材あり。
      Prop 1/2 の証明で必要になる範囲を優先。
- [ ] **Proposition 1**: `B(n,1,ε)` が field model `q(x) = x·x̄` を許容する。
      `Types.lean` の `TypeBModel`/`typeBQuadraticMap` (φ, ε パラメータ) が
      土台。原文は `references/peterfalvi/pdf/08.0_pp_139_143_On_Suzuki_2-Groups.pdf`
      (pdftotext は本章 per-char 崩れのため PDF ページ画像で読むこと)。
- [ ] **Proposition 2**: `B(n,1)` の automorphism map が surjective で
      kernel が elementary abelian 2-group。
- [ ] Theorem (e) ⟹ 方向は既存 [issue 2052](2052-pf-appendix3-e-forward.md) —
      本 issue とは独立に追跡継続。

## 完了条件

上記 4 項が sorry-free で landing し AxiomsCheck 登録、
`Suzuki2Groups.lean` hub docstring の「Still to be formalized」段落を更新。

## 参照

- issue 0127 ②③ (audit と削除裁定・wrapper 不要裁定)
- `OddOrder/Higman/Suzuki2Groups/` (Higman 定理本体・完成済)
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/` (concrete leaves)
