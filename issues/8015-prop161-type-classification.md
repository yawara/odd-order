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
7. `theoremA8_complement_eq_bot_and_kappa_prime` — **Thm A(8) の 2/3 を de-gate**
   (MF≠Mσ ⟹ U=⊥ ∧ ∃p prime |K|=p、Thm 15.2 直接活用)。残 = FittingIsTI のみ。

### 🔬 FittingIsTI 精査結論 (2026-06-20 セッション末)
**FittingIsTI は Theorem 15.2 の結論に無い** (mmd L4180-4202 確認: 15.2 は Q/Q̄/D 構造 + M''=Mσ'⊆F(M)=
C_{Mσ}(Q̄) + q∈β のみ、TI 言及なし)。FittingIsTI は **Theorem A(8) の content** で Theorem A 証明
(§16, mmd L4346-4355) 内で確立される深い §15/§16 fusion 事実。既存 TI 機構 (`isTISubset_sigmaSharp_of_sigma_eq_beta`
S14:1443 [σ=β 時]、`typeP_family_T_isTI` S14:6222、`typeP_zTilde_isTI` S14:7210) の上に type-P1 構造
(F(M)=C_{Mσ}(Q̄)⊂Mσ、Q̄ minimal normal) を接続する argument が要る。**深い multi-session 定理** —
F(M) TI を Q=O_q(M) の TI 性 (§10 σ-uniqueness 由来) + F(M)=QC_M(Q) から組む or sigmaSharp TI から
還元する経路を要形式化。次セッションの focused 着手対象。

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

### ✅ 2026-06-20² FittingIsTI を Thm 15.7(a) 単一 rank 残務に還元 + ≥3 側を証明 (本セッション)
**FittingIsTI 精査結論を訂正・前進。** 前回「Thm 15.2 外の深い fusion」と評したが、**A(8) FittingIsTI =
Theorem 15.7(a) の `M_F = M_σ` 結論の対偶**と特定 (schematic proof: A(6)(7)(8) ← 15.2(a)/Cor15.5/
**15.7(a)(b)**)。15.7(a) は `¬FittingIsTI ⟹ H=M_σ` (= `fitting_not_ti_cases` 第2 conjunct, S15 sorry)。
依存 (Cor15.5/Thm10.1/Lem12.17/Thm12.13/Uniqueness/15.2(b)/β⊆σ/pRank-mono/nilpotent-commute) は**全て
sorry-free 在庫**と確認。

**landed (2 commits, full build 3869 green, AxiomsCheck OK):**
- **A(8) 配線チェーン** (`32a243e1`, S15_MF + S16): `mf_eq_msigma_of_piSet_inf_beta_disjoint`
  (ENDGAME, **axiom-clean**: π(M_F)∩β=∅ ⟹ M_F=M_σ、Hall κ-構成 + 15.2(b) 対偶) → 
  `mf_eq_msigma_of_not_fittingIsTI` (COMBINE) → `fitting_isTI_of_mf_ne_msigma` (A(8) 方向=対偶) →
  **`theoremA8_structure`** (S16, A(8) 完全形 U=⊥ ∧ FittingIsTI ∧ |K|=p, sorry-free)。
- **pRank-index 補題 dedup** (`9e74c51f`): `pRank_eq_of_le_of_not_dvd_index` を S12 の 2 private 重複
  → `OddOrder.GroupTheory` (PRank.lean) public 昇格。
- **G1 = `three_le_pRank_mf_of_mem_beta`** (`9e74c51f`, **sorry-free + axiom-clean, AxiomsCheck 登録**):
  r∈π(M_F)∩β ⟹ r_r(M_F)≥3 (M_F Hall ⟹ r_r(M_F)=r_r(M)、β⊆α)。15.7(a) rank dichotomy の **≥3 側**。

**⟹ A(8) FittingIsTI は「all of Thm 15.7」gate から単一 sorry に縮小**:
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` (S15:7206) は partial proof 化済 —
G1 で ≥3 側 discharge、**残 sorry = `pRank (M_F) r < 3`** (1 点)。

### ✅ 2026-06-20³ residual の building block 2 本を証明 (本セッション続き)
`pRank (M_F) r < 3` の証明 building block のうち概念核 2 本を sorry-free 化 (commits `e3e6cd97`/
`8f6fe3e2`, full build 3869 green):
- **`exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI`** (step 1 setup): ¬FittingIsTI ⟹
  ∃g∉M, F(M)⊓conj g•F(M)≠⊥。push_neg + F(M)⊴M (fittingInG_subgroupOf_normal)。
- **`rank_lt_three_of_le_two_maximals`** (step 7 核, 汎用再利用可): 異なる 2 極大に含まれる部分群は
  rank<3 (isUniquelyMaximal_of_three_le_rank_of_lt_top 対偶 + eq_of_isCoatom_of_le)。
⟹ residual の docstring に 5-step assembly + 各 located upstream 補題を精密記載済。残 assembly =
step3 (p∈σ, **最深**: simplicity 経由)/step5 (p∉β)/step6 (C_G(X₁)⊄M)/step8 (bridge) + 組立。
**step3 の fiddly 核** = 「cyclic O_p(F) の unique order-p 部分群 X₁ が char ⟹ M≤N(X₁)」
(char-in-normalized 転送 + cyclic-unique-subgroup) + `normalizer_eq_of_normal_of_mem_maximal`
(S08 private、要 public 化) の simplicity 矛盾。infra: `characteristic_of_isCyclic` (Peterfalvi 在、
要 GroupTheory 昇格 or S15 複製)、`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent` (S08)、
`opiCoreInG_fittingInG_subgroupOf_normal` (S08)。step8 infra: `commute_of_coprime_orderOf_of_isNilpotent`
(要 subgroup-level lift)。

### ✅✅✅ 2026-06-20⁴ Thm 15.7(a) rank core 完成 → A(8) FittingIsTI sorry-free (本セッション続行)
**residual `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` を完全に sorry-free 化**。⟹
`fitting_isTI_of_mf_ne_msigma` (A(8) FittingIsTI) + `theoremA8_structure` (A(8) 完全形) が
**sorry-free declaration**。実 sorry 138→137。下記すべて landed (commits `ee5586e6` infra /
`165317a7` step3 / `614ac0b1` back-half):
- **infra** (S15): `eq_of_card_eq_of_isCyclic`/`eq_of_le_isCyclic_of_card_eq`/
  `le_normalizer_of_le_isCyclic_normalized` (cyclic 部分群一意・正規化転送) +
  `opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic` (Cor 15.5(a): O_{σ'}(F) cyclic、
  fitting_decomposition から modularity で抽出) + S10/S08 で `maximal_normalizer_le_self`/
  `normalizer_eq_of_normal_of_mem_maximal` を private→public 化。
- **step 3 gateway**: `mem_sigma_of_prime_dvd_card_inf_conj_fitting` (p | |F⊓F^g| ⟹ p∈σ、simplicity)。
- **back-half**: step5 (p∉β/12.17)・step6 (C_G(X₁)⊄M/fusion 10.1e)・step7 (rank<3/uniqueness)・
  step8 (nilpotent bridge/Sylow index)。
- ⚠ **axiom status**: chain は sorry-free declaration だが `fitting_decomposition` 経由で **upstream
  sorryAx を transitively 保持** (既存 gap; 本作業導入でない)。完全 axiom-clean には
  fitting_decomposition の transitive sorryAx 解消が別途要。
**⟹ A(8) の 3 conjunct (U=⊥ / FittingIsTI / |K|prime) すべて sorry-free declaration で揃った**
(theoremA8_structure)。次 = §16 Theorems B-E / Prop 16.1 hard 方向、または fitting_decomposition
の axiom-clean 化。

### 🔬 2026-06-20⁵ axiom-clean 化の調査結論 (option 1 = A(8) を axiom-clean に)
A(8) FittingIsTI chain の **唯一の sorryAx 源を特定**: `mf_hall_centralizer_control` (BG **Cor 15.3**,
`S15_MF:2488` literal sorry) を `fitting_decomposition` (Cor 15.5) が **H=M_σ で 1 箇所 cite**
(`S15_MF:6694`) → `opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic` → `mem_sigma_...` → residual。
**他は全 axiom-clean** (`#print axioms` 確認: rank_lt_three / three_le_pRank / fusion_control /
Msigma_inf_conj_isBetaCompl / centralizer_singleton_lt_top すべて allowlist 3 軸のみ)。
- **Cor 15.3 の証明 engine `mf_hall_centralizer_control_of_inputs` は proven** (3 input ha/hconj/hfratt
  を取る)。fitting_decomposition は `.1` (=ha) のみ使用。
- **ha (=C_M(H)=C_{M_σ}(H)⊔X, X cyclic τ₂) の crux = 「C_M(H) は κ'-group」(Prop 14.2(b1)(e))**。
  これは **§14 で deferred** (`typeP_structure` は (b1)(e) の κ'-group 句を expose せず) かつ **shortcut なし**
  (`ActsPrimeOn` は `C_N(g)=C_N(X)` のみで faithfulness を与えない)。cyclic-τ₂ 核
  `typeP_hall_small_subgroup_cyclic_tau2` (S14:2234) は sorry-free 在庫。
- **⟹ A(8) を完全 axiom-clean にするには BG Prop 14.2(b1)(e) (C_M(M_σ) κ'-group) を先に証明し
  Cor 15.3 を assemble する必要** = 実質的な §14 上流仕事 (multi-session、quick assembly ではない;
  Explore の「feasible assembly」判定は κ'-group 句を未確認の楽観)。
- **現状の clean な到達点**: A(8) FittingIsTI は sorry-free declaration、axiom gap は **正確に Cor 15.3
  一本**に収束。次は (i) Prop 14.2(b1)(e)+Cor 15.3 の §14 effort を行う or (ii) この状態を受容し
  §16 Theorems B-E / Prop 16.1 hard 方向へ。

### 🎯 残 `pRank (M_F) r < 3` の証明計画 (✅ 上記で完了)
`¬FittingIsTI M` から導出。base 補題は全在庫:
1. **setup**: ¬FittingIsTI unfold (`IsTISubset` def S15... = `∀g,(∃a∈A,gag⁻¹∈A)→g∈L`) ⟹ ∃g, a∈
   `fittingSharp M`, gag⁻¹∈fittingSharp, g∉N_G(F(M))。`F(M)=fittingInAmbient M` ⊴ M
   (`fittingInG_subgroupOf_normal` S08:142) ⟹ M≤N(F(M)) ⟹ **g∉M**。X:=F(M)⊓(conj g•F(M))≠⊥
   (gag⁻¹ を含む)。
2. **X⊆M_σ**: p∈π(X)、X₁=order-p ≤ X。O_p(M) cyclic なら X₁ char ⟹ X₁⊴M,M^g ⟹ 単純性矛盾
   ⟹ O_p(M) 非 cyclic ⟹ (Cor15.5 `fitting_decomposition`: O_{σ'}(F(M)) cyclic) p∈σ(M)。∀p∈π(X)
   ⟹ X⊆O_σ(F(M))=F(M_σ)⊆M_σ。
3. **C_G(X₁)⊄M**: Thm10.1(a) (`fusion_control_of_mem_sigma` S10:906) + Lem12.17。
4. **C_{M_F}(X₁) rank<3** ★最深: 𝓜(C_{M_F}(X₁))≠{M} (C_G(X₁)⊄M 経由) ⟹ Thm12.13
   (`nonabelian_pgroup_isUniquelyMaximal` S12_1213:862) + Uniqueness (`uniquenessTheorem`) で
   abelian rank<3。
5. **bridge to r_r(M_F)<3**: M_F≤F(M) nilpotent ⟹ r≠p の O_r(M_F) が X₁ (p-group) を中心化
   (`commute_of_coprime_orderOf_of_isNilpotent` S10_LLC:679) ⟹ O_r(M_F)≤C_{M_F}(X₁) ⟹
   r_r(M_F)=r_r(O_r(M_F))<3 (`pRank_mono_of_le`/`pRank_sylow_eq`)。r=p は X cyclic 経由。

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
