---
id: 1015
slug: hzeta0nu-coherence-orth-one
title: "coherence extension ⊥1_G (hzeta0nu) — IsCoherent 強化 or Sibley-local"
created: 2026-07-01
---

# coherence extension ⊥1_G (hzeta0nu) — IsCoherent 強化 or Sibley-local

## 背景

lane-b の witness hB=(7.8.b) `1 - e/kH ≤ normRho` (`S09.zetaNuRhoNormSqGeOfDade` で産出) の
**唯一の残 blocker** = `hzeta0nu : ⟨ν(Ind θ_0), Hypothesis71.constOne G⟩ = 0`
(ν = coherent extension, Ind θ_0 = witness の区別された指標 = 次数 e≥3 の既約)。

他の (7.8.b) 入力は全て tractable/既存:
- hζ0norm `⟨Ind θ_0,Ind θ_0⟩=1` = `inner_self_induce_eq_one_of_frobeniusGroup` (既存)。
- hsmall `2e+1≤h` = `frobenius_two_mul_card_complement_add_one_le_card_kernel` (landed, S14)。
- a/ha = `exists_betaDecomp_a` + `induce_mem_ZIrr` + `coh.extension_mem_ZIrr` (既存)。

witness の (7.8) 構造自体は `witness_L_hypothesis78` (landed, S14) で構成済。

## root-cause

Peterfalvi の coherence (5.x) は本来 ℤ[S] を **1_G の直交補空間**へ写す (S は 1_L 直交の
induced-from-nontrivial、Dade isometry が ⊥1_G 空間に landing、coherent 拡張がそれを保つ)。
しかし repo の抽象 `IsCoherent` (S07_Coherence.lean:1596) は
**isometry (`extension_inner_eq`) + extends-Dade (`extends_on_supported`) + ZIrr-codomain
(`extension_mem_ZIrr`) のみ保持し、⊥1_G / degree 保存を落としている**。
産出経路 `frobenius_typeI_coherent`→`CoherenceWiring.coherent_of_sibleyTarget`→
`S08.nonempty_coherent_of_sibley` も抽象 IsCoherent を返すのみ。

**⟹ hzeta0nu は抽象 IsCoherent から原理的に導けない**:
- ν(ζ_0) は norm-1 virtual char (isometry + hζ0norm) = ±既約。⟨ν ζ_0,1_G⟩=0 ⟺ ν(ζ_0)≠±1_G。
- hagree からは ⟨ν ζ_i,1_G⟩ = d_i·c (c=⟨ν ζ_0,1_G⟩) が全 i で従うのみ (τ image ⊥1_G via
  `inner_tau_supported_constOne` + ⟨ψ_i,1_L⟩=0)。norm 制約 Σd_i²|c|²≤1 は c=0 を強制しない。
- ζ_0−ζ_{ind1H} は ζ_{ind1H}=Ind 1_K∉zSpan S ゆえ zSupportedSpan に入らず extends_on_supported 不可。
- **degree 保存 (ν(χ)(1)=χ(1)=e≥3 ⟹ ν(ζ_0)≠±1_G) があれば即**だが、IsCoherent にも
  retarget/CoherenceWiring/Sibley 構成にも degree 保存 lemma 無し (grep 済)。

## やること (修正の 2 択)

- [ ] **(a) 共有 `IsCoherent` に field 追加** (`extension_orthogonal_constOne : ∀ φ∈zSpan S,
  ⟨extension φ, constOne⟩ = 0` or degree 保存 `extension_apply_one`)。全 constructor
  (`nonempty_coherent_of_sibley` S08 / `galoisTransport` S07 / case-B の xChiExtension・
  caseBXsetExtension・retarget_isCoherent 等) で証明要。**最もクリーンで全 coherence consumer
  (lane-a §11/§13, lane-c) に裨益**するが **shared-structure signature 変更** →
  CLAUDE.md「signature 無断変更=STOP」。lane-a coherence-core と overlap。**要 hub/lane 調整**。
- [ ] **(b) witness-local**: IsCoherent 非依存で、Sibley 構成 (`nonempty_coherent_of_sibley` の
  extension formula) から witness の ν(Ind θ_0) ⊥1_G を直接証明する standalone lemma。additive
  だが S08 case-B coherence machinery への deep dive を要し、共有版より重複的。

## 完了条件

`hzeta0nu` (witness の ⟨ν(Ind θ_0),1_G⟩=0) が証明可能になり、witness hB=(7.8.b) が
`zetaNuRhoNormSqGeOfDade` で産出可能になる (→ `exists_counterexample_dade_data` の hB field)。

## 参照

- 正本分析 = issue 1013 の 2026-07-01 loop⁷ エントリ。
- ユーザー裁可 (2026-07-01): lane-b は当面 hB 保留、coherence-core に触れない §12 上流
  (12.11/12.14/12.15) を上流優先で先行。hzeta0nu は本 issue で coordinated fix として track。
  (a) を採るなら lane-a coherence machinery と協調 (⊥1_G は coherence の普遍性質)。
- 関連: `witness_L_hypothesis78` / `frobenius_two_mul_card_complement_add_one_le_card_kernel`
  (S14_MaximalI.lean)、`zetaNuRhoNormSqGeOfDade` (S09_CertificateDischarge.lean:2347)。
