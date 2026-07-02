---
id: 2005
slug: s14-9-faithful-in-s16
title: "Cor 14.9 faithful 化 (M̃ 被覆) を §16 で tildeM に対して書く"
created: 2026-06-15
---

# Cor 14.9 faithful 化 (M̃ 被覆) を §16 で tildeM に対して書く

## 背景

BG Corollary 14.9 (mmd L3997) は `G^#` を共役片 `𝒞_G(M̃ᵢ)` (+ `𝓜_𝓟` 非空時の `𝒞_G(Ẑ)`)
で **disjoint 被覆**する counting capstone。Lane H の §14 surface
`nonidentity_covered_by_sigma_pieces` (`OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`)
は被覆を **`sigmaConjugacySaturation = 𝒞_G(M_σ^#)`** で行うが、`M_σ^# ⊊ M̃` ゆえ ℓ_σ=2 の
twisted 元 (`x x'`, `x'∈R(x)^#`) を取りこぼし **as-is で偽**。faithful 版は BG `M̃` 必須。

`M̃` は既に **§16 `S16_MainResults.lean` に `tildeM M R` (R carrier 付き) として存在**
(`def tildeM`, `def rCoset`, `def RData`, `def ConjSharplyTransitiveOn`)。§16 は §14 を import
するため、§14 側で `tildeM` を参照すると **循環** ⟹ faithful な 14.9 は §16 (Lane G 領域) で
書くのが正しい。Lane H の 2026-06-15 faithful 化セッションで §14 内 3 件 (14.3/14.4/14.12) を
着地させた際に切り分け (commit `15d57bdb`, notes `notes/bg/s14_typeP_counting.md`
「✅ Faithful reformulation 着地 (2026-06-15)」)。

> **2026-06-15 追記 — Lemma 14.6 も同枠 (R(x) gated → §16)**: §14 signature interface 完成作業
> (notes「🧩 §14 signature interface 完成」) で **Lemma 14.6** (mmd L3945, 各 `g∈G^#` は
> 「`g=xx', ℓ_σ(x)=1, x'∈R(x)`」/「`g=yy', y'` が `κ(M)`-元」の exactly one) も **R(x) 必須**ゆえ §14
> では循環で書けないと判明。14.6 は 14.9/14.10 の土台 + §16 Thm E が cite ⟹ **14.6 も §16 で `tildeM`/
> `RData` に対して statement 化すべき**。14.5(c) (count `|𝒞_G(M̃)|=(|M_σ|−1)|G:M|`) も同様 (R(x) 要)。

## やること

- [ ] §16 (Lane G) で `tildeM`/`RData` に対する faithful な **Cor 14.9** を statement 化
  (`G^#` を `conjClassSet (tildeM Mᵢ (R Mᵢ))` over class reps で disjoint 被覆, `𝓜_𝓟` 非空時は
  `conjClassSet (zTilde K Kstar)` 片を追加)。§16 既存の `RData`/`ConjSharplyTransitiveOn` を再利用。
- [ ] **Lemma 14.6** (g∈G^# dichotomy) を §16 で `tildeM`/`R(x)` に対して statement 化 (14.9/14.10 の土台)。
- [ ] **Lemma 14.5(c)** (`|𝒞_G(M̃)|=(|M_σ|−1)|G:M|`) を §16 で statement 化 (Thm E が cite)。
- [ ] (任意) §14 の `nonidentity_covered_by_sigma_pieces` を §16 の faithful 版へ誘導する
  docstring 追記、または deprecation 方針を hub と決定。
- [ ] (関連) G が §15/§16 で `sigmaSharp` を M̃ のつもりで使っている箇所 (約 9 refs) を監査し、
  M̃ を意図する所は `tildeM` へ移行 (notes の defect #1)。

## 完了条件

- §16 に faithful な Cor 14.9 が landed (sorry でも可、ただし `tildeM` ベースで BG L3997 と一致)。
- §14 surface との関係 (どちらを下流が使うか) が docstring/notes で明確。

## 参照

- `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` (`nonidentity_covered_by_sigma_pieces`)
- `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` (`tildeM`, `RData`, `ConjSharplyTransitiveOn`)
- `notes/bg/s14_typeP_counting.md` (defect #1, #3; 2026-06-15 reformulation section)
- mmd `references/bg/local-analysis.mmd` L3997 (Cor 14.9), L3910 (M̃ 定義)
- commit `15d57bdb` (§14 faithful reformulation 14.3/14.4/14.12)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

faithful M̃ trio landed (検証 2026-07-02、S14_TypePCounting.lean): `exists_mem_conjClassSet_Mtilde_of_ne_one`
(:5553) + `sigmaConjugacySaturation_Mtilde_ncard` (:5948) + `sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`
(:8292)、いずれも sorry-free。配置は issue 提案の §16 でなく S14 — 前提の circularity が消えたため。
