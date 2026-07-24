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

- [x] **Lemma 1(a)** ✅ 2026-07-24 (hub): `QuadraticExtensions.lean` (1(b) と同居) に一般形で
      実装 — `centralSquare` (squaring の descend) / `centralCommPairing` (**polarization として
      定義**することで well-definedness 証明を丸ごと回避する設計) / `centralCommPairing_mk`
      (polar form = commutator pairing `⁅y,x⁆`) / `centralCommPairing_mul_left/right`
      (biadditivity — 今日 dedup したばかりの `commutatorElement_mul_*_of_class_le_two` を cite) /
      **`centralSquareQuadraticMap`** (bundled `QuadraticMap (ZMod 2)`、AxiomsCheck 登録済)。
      書籍の「P 2-group」仮定は不要 (使うのは W ≤ Z(P) + 両 exponent 2 のみ) なので一般化。
      ⚠ 実装知見: `IsMulCommutative.instCommGroup` は **scoped instance** — `open scoped
      IsMulCommutative` が無いと letI 連鎖が組めず zmodModule の型と不一致になる。
- [ ] **Lemma 2**: `F_{2^n}` 上の linear / bilinear / quadratic map の基底表示。
      **(a) ✅ 2026-07-24 (hub)**: `SemilinearFieldAut.lean` に一般標数で実装 —
      `linearIndependent_algAut_toLinearMap` (Dedekind `linearIndependent_monoidHom` を
      `LinearIndependent.comp` + `.of_comp coeFnLinear` で 𝔽_p-線形写像空間へ転送) /
      `finrank_linearMap_self_eq_finrank` (`Module.finBasis` + `Basis.constr F` の equiv で
      dim_F Hom = [F:𝔽_p]) / **`algAutLinearBasis : Module.Basis (F ≃ₐ[ZMod p] F) F
      (F →ₗ[ZMod p] F)`** (`basisOfLinearIndependentOfCardEqFinrank` +
      `IsGalois.card_aut_eq_finrank`、AxiomsCheck 登録)。
      **(b)(c) 残**: bilinear は σ(x)τ(y) 族 ((a) を 2 回適用 + dim n²)、quadratic は
      σ(x)τ(x) 族 ({σ,τ} サイズ 1–2、char 2 特有の対称化)。(b) は
      `LinearMap.BilinMap (ZMod 2) F F` 上で同じ骨格 (basis constr² + 独立性)。
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
