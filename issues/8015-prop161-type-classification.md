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

### ✅ 2026-06-20 kappa bridge `p∈π(W₁) → p∈κ(M)` の精密分解 (3 条件に分けて crux を特定)
`κ(M)` 定義 (S14:121) = `{p prime ∧ p∈τ₁∪τ₃ ∧ ∃P∈elemAbRank 1, P≤M ∧ M_σ⊓C(P)≠⊥}`、
`τ₁∪τ₃ = {p | p∉σ(M) ∧ pRank_M p=1}` (τ定義 S12_ECore:51-60: τ₁=rank1∧p∤|M'|, τ₃=rank1∧p∣|M'|,
τ₂=rank2)。⟹ `p∈π(W₁) → p∈κ(M)` は 3 条件に分かれる:
1. **centralizer `M_σ⊓C(P)≠⊥`** (P=⟨x⟩, x∈W₁#): ✅ **bare TypePData から導出可・landed**
   (`typePData_msigma_inf_centralizer_W1_ne_bot`, c8484496): W₂=M'⊓C(x)≤M_σ⊓C(x) かつ W₂≠⊥。
   W₁=κ-Hall 同定**不要**。
2. **σ-complement `p∉σ(M)`**: 導出可 (未 landed)。論法: p∈σ(M) なら M_σ (=σ-Hall, normal) が
   Sylow_p(M) を含む ⟹ W₁ の p-part Q は Sylow 共役 + M_σ◁M で Q≤M_σ ⟹ Q≤W₁⊓M_σ=1 (W₁∩M_σ⊆W₁∩M'=1,
   `M_complement`) ⟹ p∤|W₁| 矛盾。要 `Msigma_isHall`/`Msigma.Normal`。
3. **rank-1 `pRank_M p=1`** (τ₂ 除外): ❌ **carrier-gated・真の残 crux**。bare TypePData の W₁ は
   cyclic だが M の Sylow_p は rank≥2 かも (p∈τ₂)。これを排除するには **W₁=BG κ-Hall** (κ-prime は
   定義上 rank 1) が必要で、bare TypePData から導出不可 [[typep-w1-kappa-carrier-not-derivable]]。
   ⟹ carrier (`Section16MaximalPair`/`Section16TypePStructure`, lane-f 所有 issue 7005/7006) の
   W₁=κ-Hall witness が要る。

**⟹ 次セッションの分岐判断**: medium reverse 方向 (hIIP2/hIIIIVP1/hVP1 の →IsTypeP 部分) は
**rank-1 条件で carrier-gated**。よって Prop 16.1 は (i) bare M でなく carrier 文脈で reverse を
証明する形に再設計するか、(ii) `Section16TypePStructure` が W₁=κ-Hall を供給する経路を使うか。
condition 2 (σ-complement) は次に landing 可 (要 Sylow/Hall 補題確認)。

### hard 方向 (1-4, 9) = type-data CONSTRUCTION
κ-membership から TypeXData の全フィールド (TypePData の H/U/W1/W2/W + Frobenius/complement/centralizer
条件) を群構造から構成。BG 証明は Thm A(5-8)/B(1-4)/C(1,2,3,8,10)/D(1)/15.7(c) を cite ⟹ **§16 endpoint
cluster (Theorems A-E) と相互依存**。多くが §16 sorried endpoint 自身ゆえ、Prop 16.1 単独でなく A-E と
セットで進める必要。

## やること

- [x] **input 11 `h152a`** = `isTypeP1_of_mf_ne_msigma` (Thm 15.2(a)) で即供給可 (assembly 時に cite)。
- [x] **medium 核の centralizer 半分** `typePData_msigma_inf_centralizer_W1_ne_bot` (c8484496, axiom-clean):
      x∈W₁# で M_σ⊓C(x)≠⊥。kappa bridge の 3 条件のうち条件 1 を bare TypePData から discharge。
- [x] **hVP1 の MF=Mσ 半分** `mf_eq_msigma_of_typePData_U_eq_bot` (c8484496, axiom-clean, A(8)-free)。
- [x] **σ-complement 半分** `typePData_W1_prime_not_mem_sigma` (2d59f42d, axiom-clean): `p∈π(W₁) → p∉σ(M)`
      (条件 2)。order-p subgroup L≤W₁ を `sigma_subgroup_le_Msigma_of_isHall` で M_σ に落とし W₁∩M'=⊥ と矛盾。
- [x] **kappa-nonempty capstone** `typePData_kappa_nonempty_of_rank1` (2d6bde51, axiom-clean):
      TypePData + (∀p∈π(W₁), pRank_M p=1) ⟹ κ(M)≠∅。3 building block を組み上げ "→IsTypeP" を
      **rank-1 named input 1 つに精密還元** (gated-endpoint)。
- [ ] **rank-1 input の供給 (残 crux)**: `pRank_M p=1` for p∈π(W₁)。下記 DAG の通り §16 Theorems A-D
      gate。carrier 経由も §16 endpoint 経由ゆえ root は §16 Theorems。

### 🔑 2026-06-20 dependency DAG 確定 (carrier shortcut は無い)
`exists_section16MaximalPair_data` (producer, FeitThompson:298) は **その構築内で Prop 16.1 を cite**
(`notTypeI_imp_typeP`/`typeP_imp_nonI`/`hone` が `proposition_type_classification` 経由, FeitThompson:322/358)。
⟹ **carrier (`Section16MaximalPair`) も Prop 16.1 から作られる**ので「carrier が rank-1/κ-Hall を供給」
は循環で使えない。真の DAG:
```
§14 κ-structure (Prop 14.2✅, typeP_duality✅) + §15 (Thm 15.2✅, 15.7?)
  → §16 Theorems A/B/C/D (sorried endpoints)
    → Prop 16.1 (本 issue)  → §16 producer → S16.Hypothesis → FT
```
各 input の真の gate (BG 証明より): hFI←A(8)+B(1-3)+15.7(c) / hP2II←C(1)(10)+B(1)(4)+A(8) /
hP1neIIIIV←A(8)+Frattini / hP1eqV←15.7(c) / **reverse hIIP2/hIIIIVP1/hVP1 の →IsTypeP←rank-1**
(capstone で還元済、rank-1 は κ-Hall=Prop 14.2/C 由来) / **hIF←A(8)+Frobenius FPF** (type-F⟹κ=∅:
M_σ=M_F[A(8)] なら U が M_σ に FPF 作用 ⟹ σ-complement 元の M_σ-centralizer=1 ⟹ κ=∅)。
**⟹ 次の実質前進 = §16 Theorems A-D (特に Theorem A の MF/Mσ 構造 = `theoremA_maximal_structure`
S16:144 sorry, と Theorem C) を attack する**。Prop 16.1 はそれらの downstream assembly。
本 issue で landed の 4 補題 (MF=Mσ / centralizer / σ-complement / kappa-nonempty capstone) は
A-D landing 時に reverse 方向で消費される honest infra。

### 🎯 最有力エントリ = Theorem A(8) を Thm 15.2 から導出 (lane-f の今セッション成果を直接活用)
`theoremA_ungated_conjuncts` (S16:181) が既に A(1)/A(5)/A(6) を sorry-free 化済。残 monolith
`theoremA_maximal_structure` の **A(8)** (`MF≠Mσ → U=⊥ ∧ FittingIsTI M ∧ ∃p prime |K|=p`) は
**Thm 15.2 `mf_ne_msigma_typeP1_structure` (今セッション完成) から部分導出可能**:
- `U=⊥`: ✅ **landed** `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (e0894437, axiom-clean):
  IsTypeP1 ⟹ κ=π\σ ⟹ π(M)⊆κ∪σ ⟹ (κ∪σ)ᶜ-Hall は素因子なし ⟹ `U.subgroupOf M = ⊥`。
- `∃p prime |K|=p`: 15.2 が `p.Prime ∧ Nat.card ↥K = p` を直接供給 (cite のみ)。
- `FittingIsTI M`: 15.2 conjunct に直接は無い → 要確認 (Thm 15.7 由来か、別途)。**次セッションの A(8) 残務**。
⟹ A(8) の U=⊥ landed + |K|=p は 15.2 cite。次セッションは (i) FittingIsTI の供給元特定 →
A(8) を `theoremA_maximal_structure` の該当 branch に配線 → A(8) は hIF/hP2II/hP1neIIIIV の共通 gate
ゆえ Prop 16.1 を大きく前進。

### 本セッション landed の building block (全 axiom-clean, S16_MainResults)
1. `mf_eq_msigma_of_typePData_U_eq_bot` — TypePData+U=⊥ ⟹ MF=Mσ (hVP1 部分)
2. `typePData_msigma_inf_centralizer_W1_ne_bot` — κ bridge 条件1 (centralizer)
3. `typePData_W1_prime_not_mem_sigma` — κ bridge 条件2 (σ-complement)
4. `typePData_kappa_nonempty_of_rank1` — κ-nonempty capstone (rank-1 gated-endpoint)
5. `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` — Thm A(8) の U=⊥ 核 (IsTypeP1→U=⊥)
6. `kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot` — 逆 (U=⊥→κ=σ')
   ⟹ **IsTypeP1 ⟺ Hall (κ∪σ)ᶜ-complement trivial characterization 完成** (IsTypeP modulo)

### ⚠ 残務の正直な評価 (2026-06-20 セッション末)
6 補題は全て Prop 16.1/Theorem A の reverse・forward で消費される honest infra だが、**いずれも
深い §16 endpoint theorem を closure には要する**。具体的な残 gate:
- **FittingIsTI M** (A(8) 残 conjunct): どこからも未供給の深い §15 構造事実 (F(M) が TI-set;
  Thm 15.2 の Q/Q̄ 構造から導く?)。A(8) の真の hard core。
- **rank-1 `pRank_M p=1` for p∈π(W₁)** (reverse →IsTypeP の残): carrier (W₁=κ-Hall) gated。
- **TypePData.U ↔ Hall (κ∪σ)ᶜ-complement U の同定**: characterization (補題5/6) は Hall U の話、
  TypeVData.U=TypePData.U は derived-complement で別物。reverse 方向で両者の bridge が要る。
⟹ **次の実質 closure = §16 Theorems A-D の本体着手** (FittingIsTI / Theorem C の構造論)。
Prop 16.1 はそれらの downstream。本 issue の 6 補題は前倒し infra として valid。
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
