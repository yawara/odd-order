---
id: 8015
slug: prop161-type-classification
title: "BG Proposition 16.1 type classification (11-input decomposition)"
created: 2026-06-20
---

# BG Proposition 16.1 type classification (11-input decomposition)

## 背景

`proposition_type_classification` (`S16_MainResults.lean:894`, BG Prop 16.1, mmd L4478) は §16 の
**型分類辞書**で sorry。§14-§15 の局所族 (`kappa(M)` ベースの `IsTypeF`/`IsTypeP1`/`IsTypeP2`) と
Peterfalvi が下流で使う構造的 shared 述語 (`GroupTheory.IsTypeI`–`IsTypeV` = `Nonempty (TypeXData M)`)
が同一であることを 6 clause (a)-(f) で確立する。

下流 consumer = `not_isTypeI_of_isTypeNonI` (S16:926, sorry-free, **FT path 上** —
`FeitThompson.lean:334` の section16MaximalPair producer が cite) + Peterfalvi S10_BGInterface の
`isTypeI_iff_isTypeF`/`isTypeII_iff_isTypeP2` (Pf §10-13 が BG endpoint を shared 述語に翻訳)。
⟹ Prop 16.1 は §16 → S16.Hypothesis の FT-critical gate。

### 既存インフラ (lane-g が landed 済)
- **`proposition_type_classification_of_inputs`** (S16:817, **sorry-free gated-endpoint skeleton**):
  11 個の方向別 input を仮説に取り 6-clause iff を組み立てる。⟹ 本 issue = この 11 input を実証明で供給。
- **`typeFData_of_kappa_eq_bot`** (S16:555): `kappa M = ∅` → `TypeFData M` (input hFI の TypeFData 部分)。
- **Thm 15.2(a)** = `isTypeP1_of_mf_ne_msigma` (S15_MF, 2026-06-20 lane-f で Thm 15.2 完全 close): input
  `h152a` を**直接供給可能** (✅ 即 wire 可)。

## 11 input の分解 (= `proposition_type_classification_of_inputs` の仮説)

| # | input | 内容 | 方向 | 難易度 |
|---|---|---|---|---|
| 1 | `hFI` | `IsTypeF M → IsTypeI M` | κ=∅ → TypeIData 構成 | **hard** (8.3 三分岐 `alternative` + 15.7(c)) |
| 2 | `hP2II` | `IsTypeP2 M → IsTypeII M` | κ⊊ → TypeIIData 構成 | **hard** (Thm C(1)(10)+B(1)(4)) |
| 3 | `hP1neIIIIV` | `IsTypeP1 M → MF≠Mσ → III∨IV` | TypeIII/IV 構成 | **hard** (Frattini+σ, Thm A(8)) |
| 4 | `hP1eqV` | `IsTypeP1 M → MF=Mσ → IsTypeV` | TypeVData 構成 | **hard** (15.7(c)) |
| 5 | `hIF` | `IsTypeI M → IsTypeF M` | TypeIData → κ=∅ | **medium** (Thm C(2) 背理: K≠1⟹C_H(K)=1 と矛盾) |
| 6 | `hIIP2` | `IsTypeII M → IsTypeP2 M` | TypeIIData → κ⊊ | **medium** (π(W₁)⊆κ ∧ U≠1) |
| 7 | `hIIIIVP1` | `III∨IV → IsTypeP1 ∧ MF≠Mσ` | → κ=σ' | **medium** (π(W₁)⊆κ + U=1) |
| 8 | `hVP1` | `IsTypeV M → IsTypeP1 ∧ MF=Mσ` | → κ=σ' ∧ MF=Mσ | **medium** (π(W₁)⊆κ + U=1+V=1) |
| 9 | `hP_derived` | `IsTypeP M → ∃U Hall, M'=U⊔Mσ` | Thm C(3) | **hard** (§14 structure) |
| 10 | `hF_not_derived` | `IsTypeF M → ¬∃U …` | (e) の片方 | **medium** (κ=∅⟹MF=Mσ=M', U-complement 矛盾) |
| 11 | `h152a` | `MF≠Mσ → IsTypeP1 M` | **= Thm 15.2(a)** | ✅ **DONE** (`isTypeP1_of_mf_ne_msigma`) |

### medium 方向 (5-8) の共通核 = mmd の "obvious fact"
「M が Type II/III/IV/V ⟹ π(W₁) ⊆ κ(M)」: TypePData の W₁ は cyclic 非自明、W₁∩Mσ ⊆ W₁∩M'=1
(`M_complement`)、C_H(W₁) ≠ 1 (W₂=C_{M'}(W₁#) 非自明、W₂≤H)。各 p∈π(W₁) について rank-1 P≤W₁ を取り、
C_{M_σ}(P) ⊇ C_{M_σ}(W₁) ⊇ C_H(W₁) ≠ 1、かつ **p ∈ τ₁∪τ₃** を示せば `p ∈ kappa(M)` (定義 S14:121)。
⟹ κ≠∅ ⟹ IsTypeP。`p∈τ₁∪τ₃` 部分が非自明 (W₁ の prime が τ₁∪τ₃ にある構造的事実)。

**⚠ 2026-06-20 調査で判明した crux**: `p∈τ₁∪τ₃` の供給元 = 既存 `mem_kappa_of_mem_primeFactors_card_E1`
(S14:436) / `mem_tau1_union_tau3_of_mem_primeFactors_card_E` (S14:352) は **`SubgroupESetup` ベース**で
`TypePData.W1` を直接扱わない。memory [[typep-w1-kappa-carrier-not-derivable]] の通り **`TypePData.W1 = BG
κ-Hall` は bare TypePData から導出不可** (2 つの IsTypeP 述語 kappa-nonempty vs Nonempty-TypePData は別物)
⟹ W₁ を E-setup の E₁ (or κ-Hall K) に同定する bridge が要り、これは **§16 maximal-pair / carrier
(Section16MaximalPair) レベル**の情報を要する可能性大。⟹ medium 方向も「W₁↔E₁/K 同定」を要する
真の構造論 (carrier-aware)。次セッションは **(i) W₁↔E-setup 橋渡しの所在確認** から着手すべき
(`exists_subgroupESetup` + W₁ の complement 性質から E₁ 同定が可能か, or §16 carrier 必須か)。

### hard 方向 (1-4, 9) = type-data CONSTRUCTION
κ-membership から TypeXData の全フィールド (TypePData の H/U/W1/W2/W + Frobenius/complement/centralizer
条件) を群構造から構成。BG 証明は Thm A(5-8)/B(1-4)/C(1,2,3,8,10)/D(1)/15.7(c) を cite ⟹ **§16 endpoint
cluster (Theorems A-E) と相互依存**。多くが §16 sorried endpoint 自身ゆえ、Prop 16.1 単独でなく A-E と
セットで進める必要。

## やること

- [ ] **input 11 `h152a` wire** (即可): `isTypeP1_of_mf_ne_msigma` を named helper として供給。
- [ ] **medium 核 `typePData_kappa_nonempty`**: `TypePData M → (kappa M).Nonempty` (π(W₁)⊆κ 論法)。
      `p∈τ₁∪τ₃` の供給元を特定 (W₁ の構造 or 別 §14 補題)。これが input 6/7/8 の "→IsTypeP" 部分。
- [ ] **input 5-8 の MF/Mσ・U 条件抽出**: TypeIIData→U≠1 (normalizer_not_le 等)、TypeV→U=⊥ (U_eq_bot)、
      MF≠Mσ ⟺ U≠⊥ の bridge (Thm 15.2 の MF=Q⊔… 構造から)。
- [ ] **input 1-4, 9 (hard 構成)**: §16 endpoint A-E と協調。`typeFData_of_kappa_eq_bot` を起点に
      TypeIData の `alternative` (8.3 三分岐) を構成 (要 Thm 15.7(c))。← 最深、後回し。
- [ ] **assembly**: 全 input が揃ったら `proposition_type_classification := …_of_inputs h11 …` で close。
      揃うまでは各 input を named lemma 化 (tractable は sorry-free、hard は sorry'd named residual)。

## 完了条件

`proposition_type_classification` (S16:894) が sorry-free。中間状態は各 input lemma が個別に landing し、
残りが正確に §16 hard-construction (Theorems A-E 連動) を named residual で指す状態を維持
([[feedback-gated-endpoint-skeleton-pattern]])。

## 参照

- `proposition_type_classification_of_inputs` (S16_MainResults:817) — 11-input skeleton (sorry-free)。
- `typeFData_of_kappa_eq_bot` (S16:555) / `isTypeP1_of_mf_ne_msigma` (Thm 15.2(a), S15_MF)。
- `TypeFData`/`TypePData`/`TypeIData`..`TypeVData` (`GroupTheory/MaximalSubgroupType.lean:82-244`)。
- `kappa`/`sigmaComplementPrimes`/`IsTypeF`/`IsTypeP1`/`IsTypeP2` (S14_TypePCounting:115-140)。
- mmd `references/bg/local-analysis.mmd` L4478-4536 (Prop 16.1 statement + proof)。
- memory [[bg-s16-gated-on-typedata-construction]] (§16 type-data construction gate)。
- issue 8012 (closed): Thm 15.2 (= input 11 h152a の供給元)。
