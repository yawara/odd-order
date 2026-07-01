---
id: 9002
slug: lane-c-claims-constructive-clifford
title: "lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース"
created: 2026-07-02
---

# lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース

> **CLAIM (lane c=γ, hub 再裁定 issue 9001 2026-07-02)**: 構成的 Clifford correspondence
> (Ind_H^L θ の構成要素分解 = Isaacs 6.2/6.11 + Pf 1.7) を lane c が build。**coherence 非依存の
> generic char 補題**。consumer = lane b (12.14 M-side) + lane c (deep char) の両方 = shared infra。
> **他レーンは着手前に本 issue を scan、cite (再構築しない)**。issue 0026 を subsume。

## 現状 (2026-07-02 精査、issue 0026 は 2026-05-30 更新で stale)

**⚠ 重要: 一般 module-core (BLOCKER B) は既に landing 済**。issue 0026 が「残る唯一の hard blocker =
module-theoretic Clifford core (orbit transitivity)、3-5 セッション」としたものは**その後 sorry-free 化**:
- `CliffordSingleOrbit.lean:122` `restrictionConstituentsSingleOrbit_of_isIrreducible` — Clifford
  (Isaacs 6.5) 第1節「Res^G_H χ の既約構成要素は単一 G-orbit」= **sorry-free landed**。
- 同 `:175` `apply_one_eq_restrictionMultiplicity_mul_index_inertia` — degree formula
  `χ(1)=⟨Res χ,θ₀⟩·[G:I]·θ₀(1)` = landed。
- `InducedIrreducible.lean`: `card_mul_inner_self_induce_eq_card_inertia` (⟨Ind θ,Ind θ⟩=[I:H])、
  `card_conjByOrbit_eq_index_inertia`、`induce_eq_induce_iff_conj`、`inner_induce_eq_zero_of_not_conj`
  = induction-side Clifford (Frobenius 相互律 + inertia orbit) landed。
- `CliffordMultiplicityOne.lean`: `restriction_isSimpleModule` (BG 2.2(a) mult-one) + conj semilinear
  端末 landed。**全 Clifford*.lean = 0 sorry**。

**∴ hub の「構成的 producer なし」前提は stale。** 一般 Clifford 核は在庫。残 gap は **assembly**。

## 残 gap = `typeI_induced_char_constituents` (S14_MaximalI.lean:389, sorry S14:398) 一般ケース

- **Frobenius ケースは proven**: `frobenius_typeI_induced_char_constituents` (S14:465, sorry-free) —
  L が Frobenius (kernel H) なら Ind_H^L θ は既約 → singleton {χ}。docstring 明記「(12.16) witness-side
  R(χ)/(12.3)/(12.4) が実消費するのは Frobenius ケース」。witness L は Frobenius ゆえこちらで足りる。
- **一般ケース (sorried)**: 一般 type-I maximal L で χ=Ind_H^L θ (θ∈Irr H∖{1}) が **等次数・非実・
  A(L)∪{1} 台の既約構成要素の mult-one 和**。body = §8 type-F Clifford:
  - Pf (1.7) **cyclic inertia quotient I_L(θ)/H → mult-one 等次数 Ind 分解** (核心、要精査で
    landed 有無確認)。
  - (8.2.c) `I(θ)∩U⊆U₁` inertia bound (§8 specific)。
  - (1.5.a) `(Res_H φ,1_H)=0` + (1.2) → 台 A(L)∪{1}。
  - 非実 = 奇数位数 (`not_isReal_of_ne_trivial_of_odd_card'` 既存)。

## やること

- [ ] Pf (1.7) 一般 mult-one 等次数 Ind 分解が landed か精査 (CliffordMultiplicityOne/InducedIrreducible)。
      無ければ generic shared leaf (`OddOrder/GroupTheory/RepresentationTheory/` or Pf §3
      `S03_PreliminaryCharacter`) で build。
- [ ] (8.2.c) inertia bound + (1.5.a)/(1.2) 台 argument を §8/§14 で assemble。
- [ ] `typeI_induced_char_constituents` (S14:398) を sorry-free 化。lane b (12.14) は cite。

## 完了条件

`typeI_induced_char_constituents` (S14:398) sorry-free、`lake build` 緑。generic Clifford 部が shared leaf
で lane b から cite 可能な signature。

## 参照

- 親 issue: 0026 (peterfalvi-clifford-core、subsume)、0023 (clifford-decomposition)
- hub 再裁定: issue 9001「HUB 再裁定 (2026-07-02) — σ-theory-dual 撤回 + lane c に構成的 Clifford 再配分」
- landed 核: `CliffordSingleOrbit.lean` / `InducedIrreducible.lean` / `CliffordMultiplicityOne.lean` /
  `Clifford.lean` / `Inertia.lean`
- consumer: `S14_MaximalI.lean:389` (lane c) / Pf (12.14) M-side (lane b)
- Pf 原文: 03 §3 (1.5)/(1.7)、04.8 §8 (8.2.c)
