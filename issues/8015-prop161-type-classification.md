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

### 🔧 2026-06-20⁶ Cor 15.3 (axiom-clean) 着手 — 証明戦略 + type-P2 subtlety 確定
ユーザー裁可で §14 effort 着手。fitting_decomposition は Cor 15.3 を **H=M_σ で 1 箇所のみ** cite
(`S15:6694`)、消費は `⟨X, hXcyc, hXτ₂, hCeq: C_G(M_σ)⊓M=(C_G(M_σ)⊓M_σ)⊔X⟩` (=`ha`)。⟹ 目標 =
`ha` (H=M_σ) を sorry-free 化し fitting_decomposition を refactor (full Cor 15.3 の hconj/hfratt 不要)。

**証明戦略 (確定)**:
1. **crux: C_M(M_σ) κ'-group** ⟸ C_K(M_σ)=1 ⟸ ∀k∈K#, C_{M_σ}(k)=K* (ActsPrimeOn, typeP_structure
   第1連言 + `fixedBy_eq_of_le_of_ne_bot` S13:110) ∧ **K*⊊M_σ** ∧ κ-prime⟹Sylow_p(M) cyclic
   (`tau1/tau3_pRank_eq_one` + odd) + Sylow 共役で κ-元を K に共役。
2. Hall σ/σ' 分解 (Schur-Zassenhaus): C_M(M_σ)=(C⊓M_σ)⊔X, X=σ'-Hall。κ'-group ⟹ X は (κ∪σ)'-group
   ⟹ U に共役。
3. `typeP_hall_small_subgroup_cyclic_tau2` (S14:2234, sorry-free): X≤U + M_σ⊓C(X)≠⊥ ⟹ X cyclic τ₂。
4. assemble `ha` + refactor fitting_decomposition。

**⚠ type-P2 subtlety (確定した残課題)**: 上記 1 の **K*⊊M_σ** は
- type-F (κ=∅): vacuous。
- type-P1: `[M_σ,K]=M_σ` (`msigma_eq_commutator_kappa_of_isComplement'`, M=KM_σ complement) で K*⊊M_σ。
- **type-P2 (M=KUM_σ, M_σ nilpotent ∵ 15.2): GAP** — 既存 `[M_σ,K]=M_σ` は M=KM_σ complement 前提
  (P1-only)。P2 では M_σ は KU の complement ゆえ `[M_σ,KU]=M_σ` は出るが、K 単独の非自明作用
  (K*⊊M_σ) は別途要 (典型: Lem 6.3a を E=KU でなく K に restrict する一般形 or K-faithfulness の
  別証)。「K acts nontrivially on M_σ」を type-P 一般で与える repo 補題は未発見。
⟹ fitting_decomposition は一般 M (P2 含む) ゆえ、完全 axiom-clean には type-P2 K-faithfulness が要。
これが Cor 15.3 axiom-clean 化の真の残 core (genuine multi-session)。次セッション着手点。

### 🔬 2026-06-20⁷ type-P2 K-faithfulness 深掘り結論 — 自然 route は CIRCULAR (重要)
ユーザー裁可で type-P2 K-faithfulness (K*⊊M_σ) を深掘り。**自然 route が循環と判明** (`#print axioms`
で確認):
- **K*⊊M_σ の自然証明 = Cor 15.6 (`typeP_kstar_in_mf`): K* cyclic ∧ M_F not cyclic ∧ K*⊆M_F**
  ⟹ K*=M_σ なら M_F=M_σ=K* cyclic で M_F not cyclic と矛盾。**しかし `typeP_kstar_in_mf` は sorryAx
  を持つ** (`fitting_decomposition` (Cor 15.5) 経由) → Cor 15.3 を証明するのに使えない (**循環**:
  Cor15.3 ← K*⊊M_σ ← Cor15.6 ← Cor15.5 ← Cor15.3、Lean で順序不能)。
- **clean な部品**: `msigma_eq_commutator_kappa_of_isComplement'` (P1: [M_σ,K]=M_σ, **axiom-clean ✓**)、
  `typeP_duality` (K/K* cyclic, **axiom-clean ✓**)。
- **P1**: [M_σ,K]=M_σ で K*⊊M_σ clean ✅。
- **P2 (M=KUM_σ, M_σ nilpotent)**: ⛔ 非循環 route 無し。`[M_σ,KU]=M_σ` は出る (E=KU complement) が
  K 単独の非自明作用を与えない (U が full に作用しうる)。「M_σ non-cyclic / M''≠1 / M_σ non-abelian
  for type-P2」も**全て循環** (Cor 15.6/fitting_decomposition 経由)。typeP_structure (Prop 14.2 partial)
  は κ'-group 句 (b1)(e) を expose せず。
- **⟹ A(8) 完全 axiom-clean の真の blocker = BG Prop 14.2(b1)(e) (C_M(H) κ'-group) を §14 の
  E-setup/Frobenius-normalizer 機構から非循環に証明すること** (= 独立 §14 定理、issue 別建て)。
  A(8) endpoint は M_F≠M_σ=type-P1 だが、証明 path (residual→Cor15.5→Cor15.3) は一般 M (P2 含む) を
  通るため P1 限定にはできない。
**現状維持が妥当**: A(8) FittingIsTI sorry-free、axiom gap=Cor 15.3 (=Prop 14.2(b1)(e) §14 deferred)。

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

## 2026-06-23 (cont., lane-f) — 配線済 + 残 7 bridge の精密 gate 分析

**`proposition_type_classification` を engine に配線済** (commit `2c849316`): 4 input が proved で wire 済、
残り 7 bridge を named inline residual に隔離 (gated-endpoint、宣言 sorry-count 不変、full build 3881 green)。

**proved + wired (4/11)**:
- `hP2II` = `isTypeII_of_isTypeP2` (cont.¹¹、issue 7007 で landing、type-P₂ ⟹ Type II 完成)
- `hP_derived` = `typeP_exists_hall_derived_eq` (Thm C(3))
- `hF_not_derived` = `typeF_not_exists_hall_derived_eq` (Thm A(3))
- `h152a` = `isTypeP1_of_mf_ne_msigma` (Thm 15.2(a))

**残 7 bridge (全て deep、2 系統)**:
- **(A) deep trichotomy 系 (Thm 15.7(d)(e) = Coq `nonTI_Fitting_structure` 未形式化)**: `hFI` (type-F ⟹ I、
  Pf (8.3): H# TI / H abelian rank 2 / exponent) / `hP1neIIIIV` (P1 ⟹ III/IV、(8.3)) / `hP1eqV`
  (P1, M_F=M_σ ⟹ V、(8.8))。**`nonTI_Fitting_structure` (BGsection15.v:939, ~80行、deep deps:
  Fitting_structure/sigma_complement/Cor 15.3(b)/p-core) の移植が必要 = lane-f 大物 multi-session**。
  Lean 現状 = `fitting_not_ti_cases` (Thm 15.7 partial、(d)(e) の rank-2/exponent を欠く)。
- **(B) carrier `W₁=κ-Hall` 系 ([[typep-w1-kappa-carrier-not-derivable]])**: `hIIP2`/`hIIIIVP1`/`hVP1`
  (reverse → M_P) + `hIF` (I ⟹ F)。いずれも **`π(W₁) ⊆ κ(M)`** (`typePData_kappa_nonempty_of_rank1` の
  `hrank` = W₁ primes rank-1) または **`U=(κ∪σ)'-Hall`** (`kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot`
  の仮説) に bottom-out。**`TypePData` が W₁/U を abstract subgroup として持ち Hall 特徴付けを field に持たない**ため
  bare data から導出不可 (carrier=Section16MaximalPair のみ供給)。hVP1 の `M_F=M_σ` 半分は
  `mf_eq_msigma_of_typePData_U_eq_bot` landed (残=IsTypeP1 の κ 半分)。
  - **設計判断 (HUB 候補)**: `TypePData` に Hall 特徴付け field 追加 (enrich) or reverse 群を carrier 経由証明。
    enrich は cross-lane (TypePData=GroupTheory、多数 consumer)。

## 完了条件

`proposition_type_classification` (S16:2173) が sorry-free。中間状態は各 input lemma が個別に landing し、
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

## ✅ 2026-06-25 進捗 — reverse IsTypeP 半分を全型完成 (lane-f, commits 032eab7c + 2a4be9bb)

**重要訂正: rank-1 条件は carrier-gated でなかった。** 上の 2026-06-20 分析が "carrier-gated・真の残 crux"
とした「π(W₁) の prime が M で rank 1」は、**純群論 (char gate 無し・carrier 不要) で解ける**:

- **核心**: FT-critical consumer `not_isTypeI_of_isTypeNonI` (S16) は各 .mp から `IsTypeP` のみ抽出
  (P₁/P₂ 精密化・MF 関係を捨てる)。⟹ reverse bridge の FT 本質 = `IsTypeNonI → IsTypeP` (κ≠∅) だけ。
- **type V** `isTypeP_of_isTypeV`: U=⊥ ⟹ M'=M_F Hall ⟹ q∤|M'| ⟹ Sylow_q cyclic ⟹ rank 1。
- **type II/III/IV** `isTypeP_of_typePData_of_card_W1_prime`: |W₁|=q 素数 (TypePNontrivialCore) +
  `centralizer_W1` (C_{M'}(x)=W₂) + p-群固定点合同 `prime_dvd_card_inf_centralizer_of_mem_normalizer`
  (q-元 x 正規化 N∧q∣|N| ⟹ q∣|C_N(x)|、`IsPGroup.card_modEq_card_fixedPoints` 経由・reusable) ⟹
  q∤|M'| (∵ q∤|W₂| via cyclic W、`typePData_not_dvd_card_W2_of_card_W1_prime`) ⟹ rank 1。
- 補助: `typePData_pRank_eq_one_of_not_dvd_card_derived` (q∤|M'|⟹pRank=1)、
  `typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived`、`pRank_le_one_of_forall_isElementaryAbelian_isCyclic`
  (GroupTheory/PRank)。全 sorry-free + axiom-clean (AxiomsCheck 10 本登録)。
- 統合 = `isTypeP_of_isTypeNonI` (IsTypeNonI → IsTypeP、全 4 型)。

**残**: (1) `hIF` (型I⟹κ=∅、TypeFData→Frobenius/M_σ 論法、別系統 — 次の最大 W1 win)、
(2) P₁/P₂ 精密化 (κ=π∖σ vs ≠、proposition_type_classification の bridge を完全に閉じるのに必要だが
consumer 非使用)、(3) `not_isTypeI_of_isTypeNonI` を `isTypeP_of_isTypeNonI`+`hIF` で再配線 (6 sorry→1)。

## ✅ 2026-06-26 進捗 — hIF (型I⟹型F) 骨格を実証明 + FT-critical surface を crux 1 本に縮小 (lane-f, commit 043a6fb0)

上の戦略 (3) を landed。**`isTypeF_of_isTypeI` (型 I ⟹ κ(M)=∅) を実証明** (背理法、BG mmd L4486):
- κ≠∅ ⟹ κ-Hall K≠⊥ (`isTypeF_of_isHall_kappa_eq_bot` の対偶) + (κ∪σ)ᶜ-Hall U を構成 (Hall's thm)。
- **`theoremC_paired_structure` (axiom-clean)** で `K*=M_σ⊓C(K)≠⊥` かつ `K*≤M_F`。
- crux `M_F⊓C(K)=⊥` と合わせ `K*≤M_F⊓C(K)=⊥` で `K*≠⊥` と矛盾。
- **`not_isTypeI_of_isTypeNonI` を再配線**: `proposition_type_classification` (6 sorry) 経由 →
  `isTypeF_of_isTypeI`+`isTypeP_of_isTypeNonI` のみに依存。**FT が透過的に触る §16 type-classification
  の sorry が 6 → crux 1 本に縮小**。`proposition_type_classification` の hIF case も cite。
- full build 3884 green、AxiomsCheck OK (新 2 定理は crux 経由 sorryAx ゆえ未登録)。

**残 crux = `typeF_mf_inf_centralizer_kappaHall_eq_bot` (S16, sorry)**: type-F の M で κ-Hall K の
M_F-centralizer trivial。**genuine に深い**:
- TypeFData の Frobenius は **H⊔U0 のみ** (`is_typeF_complement`)、M 全体でない。
- `centralizer_kernel_le` (Ch06/FrobeniusGroup:503、↥(H⊔U0) 内 `C(x)⊆kernel` for x∈H#) は在庫だが、
  **K⊄H⊔U0** (K は κ-part、H⊔U0 は κ'-group = H σ-part + U0 (κ∪σ)'-part) ゆえ verbatim 適用不可。
- 正しい議論 = BG condition (Iiii) の C_H(K)=1: K の M=M_F⋊U action + `is_typeF_inertia` (C_U(x)⊆U1)
  経由の semidirect 計算、または **Coq `BGsection16` の structure→κ correspondence (`of_typeF ⟹ K=1`)** を移植。
- **次の一手**: Coq `BGsection16`/`BGsummaryI` の of_typeF⟹kappa 証明精査、または ChatGPT consult
  ([[feedback-ask-chatgpt-for-elided-gaps]]、self-contained プロンプト + 厳密検証)。

## ✅ 2026-06-26² 進捗 — hIF crux の核心 Frobenius FPF を実証明 (axiom-clean)、crux を正しい helper 2 本に再カット (commit 2bcdced5)

Coq `BGsection16.v:1031` 精査 (Explore) で hIF の正しい証明構造が判明: **前回 docstring の crux
`M_F⊓C(K)=⊥` は誤定式化、正しくは U₀ の κ-element X 経由** (K⊄H⊔U₀ 問題を回避)。crux を 2 helper に再カット:
- **`typeFData_fitting_inf_centralizer_eq_bot` (sorry-free + axiom-clean, AxiomsCheck 登録)**: 核心
  Frobenius FPF。`X ≤ U₀` (≠⊥) ⟹ `M_F ⊓ C_G(X) = ⊥`。`frobenius_HU0` (kernel M_F, complement U₀) を
  ↥(M_F⊔U₀) に lift (⟨x,_⟩, ⟨y,_⟩) → `centralizer_complement_le` で C∈U₀ → `M_F⊓U₀=⊥` (complement) 締結。
- **`typeFData_exists_kappaElement_le_kappaHall` (sorry, 残 residual)**: p∈κ ⟹ ∃ X≤U₀ p-group≠⊥ ⊆ κ-Hall K。
- **`isTypeF_of_isTypeI` (hIF) sorry-free 本体に書き換え**: X∈U₀ で M_F⊓C(X)=⊥ (helper A)、X⊆K で
  C(K)⊆C(X)、K*≤M_F ∧ K*≤C(K) (theoremC) ⟹ K*⊆M_F⊓C(X)=⊥ で K*≠⊥ と矛盾。

**残 helper B = tractable (building block 全在庫、次セッション ~50 行で hIF 完全 sorry-free 化可能)**:
- Hall superset (κ-group X ⊆ κ-Hall K) = **`hall_D` (Isaacs 3C.1 Wielandt, `Ch03_SplitExtensions/Main.lean:1486`)**:
  `(∀ q ∈ π(|U|), q ∈ π) ⟹ ∃ H, IsHallSubgroup π H ∧ U ≤ H`。X.subgroupOf M に適用。
- p∈π(U₀): p∈κ ⟹ p∉σ (`kappa_subset_sigmaCompl`) + p∈π(M)、M_F⊆M_σ (`maxNilpotentNormalHall_le_Msigma`) +
  M_σ σ-Hall (`Msigma_isHall`) で p∤|M_F|、`td.complement` で |M|=|M_F||U| ⟹ p∣|U|、`td.exponent_eq`
  (exp U₀=exp U) で π(U₀)=π(U) ∋ p (Cauchy: p∣|G|⟺p∣exp G)。
- X = Sylow `p` of U₀ (≠⊥ since p∈π(U₀))。

## ✅✅✅ 2026-06-26³ hIF bridge 完全 sorry-free + axiom-clean COMPLETE (commit 9cf19fdf + 1104acb1)

helper B `typeFData_exists_kappaElement_le_kappaHall` を実証明 (sorry-free + axiom-clean、AxiomsCheck 登録):
- p∈π(U₀): p∈κ ⟹ p∉σ (`tau1/tau3_subset_sigma_compl`) + P 経由 p∈π(M)、M_F⊆M_σ σ-Hall で p∤|M_F|、
  `complement.card_mul` で p∣|U|、`exponent_eq` + Cauchy (`exists_prime_orderOf_dvd_card` + `Monoid.order_dvd_exponent`) で p∣|U₀|。
- X=⟨g⟩ (order-p element of U₀)、K=κ-Hall⊇X (`Ch03.hall_D` = Isaacs 3C.1 Wielandt, Hall superset)。

⟹ **`isTypeF_of_isTypeI` (型 I ⟹ κ(M)=∅) が完全 sorry-free + axiom-clean** (helper A + B + theoremC)。
⟹ **`not_isTypeI_of_isTypeNonI` (FT-critical consumer、FeitThompson:334 producer が cite) も axiom-clean**。
⟹ **FT が透過的に必要とする §16 type-classification 依存が完全 honest**。

### ⚠ 2026-06-26⁴ 訂正 — 残 bridge の FT 必要性を依存追跡で精査 (ユーザー指摘)

前の「残 5 bridge 非 critical」は**誤り** (依存を grep せず断言、CLAUDE.md が戒める FT-orphaned 言い回し)。
正確には FeitThompson.lean を辿ると **2 bridge が FT-critical**:
- **`hP1neIIIIV` (forward P₁∧MF≠Mσ → III/IV)**: `typeP_imp_nonI` (FeitThompson:356, `hcIII_IV.mpr`) +
  `card_kappaHall_lt_of_isTypeP1` (:602) が使用。mp producer `exists_section16MaximalPair_data` の核心。
- **`hP1eqV` (forward P₁∧MF=Mσ → V)**: `typeP_imp_nonI` (:355, `hdV.mpr`) + no_typeV 経路 (:600) が使用。

`typeP_imp_nonI` (:348-359) は「type-P 極大 ⟹ 非 type-I」を proposition_type_classification の **forward
`.mpr` 方向** (hP1neIIIIV/hP1eqV/hP2II) で示す。hP2II は proved ゆえ残 sorry は hP1neIIIIV/hP1eqV の 2 本。

**off-path (FeitThompson 未使用)**: `hIIP2`/`hIIIIVP1`/`hVP1` (reverse, clause `.mp`)。FeitThompson は
`.mpr`=forward のみ使い、`hbII.mpr`=hP2II (proved); reverse は S12.bgTypeP の char 機構のみが cite。

⟹ **残 W1 FT-critical = `hP1neIIIIV`/`hP1eqV`** = type-P₁ `TypeXData` 構成 (Pf (8.3)/(8.8))。issue の
「hard 方向 (1-4,9) = type-data CONSTRUCTION、§16 endpoint A-E 連動」に該当。hub 委譲でなく W1 で埋める。

## ✅ 2026-06-26⁵ 進捗 — hP1eqV (型 V) を型 V TypePData 完全構成で trichotomy 残差 1 本に還元 (lane-f, commit 52f132b1 + 後続)

Coq `BGsection16` `typePfacts`/`Fcore_structure` 併読で type-P₁ の正確な構造を確定:
- **型 P₁ では M' = M_σ** (outer (κ∪σ)'-Hall U=⊥)、**M_F = M_σ ⟺ inner-U = 1** (型 V ⟺ U=1)、
  **M_F ≠ M_σ → prime|K| ∧ normedTI F(M)#** = Coq `(*8*)` = Lean `theoremA8_structure` (既存)、
  **型 P₁ で U≠1 ⟹ N(U)⊆M** (P₁ 特性)。

**landed (3 定理すべて sorry-free + axiom-clean, AxiomsCheck 登録)**:
- **`isTypeP1_derivedInG_eq_Msigma`**: 型 P₁ で M' = M_σ。`typeP_auxiliary_structure` conj5 (M'=U⊔M_σ)
  + `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (U=⊥) で collapse。両 P₁ bridge の基盤。
- **`fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma`**: 型 V の F(M)=M_F。
  `fitting_decomposition` (Cor 15.5(d)) の `¬IsTypeF→F(M)≤M'` + M'=M_σ=M_F + M_F≤F(M) で締結。
- **`typePData_of_isTypeP1_mf_eq_msigma`**: 型 V (P₁∧MF=Mσ) の TypePData を **U=⊥ で完全構成**。
  M'=M_F ゆえ全 U-field 自明化 (hKnorm=N(⊥)=⊤ / hUnilp=⊥ nilpotent / hDcompl=IsComplement' ⊤ ⊥ /
  hSDfit=M''≤M_F / hFiteq=F(M)=M_F)。型 P₂ の `typePData_of_isTypeP2` に対応する
  **carrier-constructibility milestone**。

**`isTypeV_of_isTypeP1_mf_eq_msigma`** で `proposition_type_classification` の **hP1eqV case を配線**
(`case hP1eqV => exact isTypeV_of_isTypeP1_mf_eq_msigma hG hM`)。さらに型 I bridge `isTypeI_of_isTypeF`
と同様 **FittingIsTI ケースを実証明**で discharge (disjunct (a) = M_F# TI via
`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`)。

⟹ **hP1eqV 残差 = ¬FittingIsTI の Peterfalvi (8.8) Suzuki ケースのみ** (M_F rank-2 abelian で |W₁|∣p-1、
または O_p(M_F)=p³ で |W₁|∣p+1、Coq `nonTI_Fitting_structure`)。型 I の non-TI ケース (rank=2 / exp U∣p-1)
と違い **|W₁|-Frobenius 整除条件** (|W₁|∣p∓1) を要し、(8.8) の W₁-action 解析が未形式化。型 V は K-action
が FPF でない (K*=C_{M_F}(K)≠⊥) ため型 F の U₀-Frobenius (`typeF_exponent_dvd_sub_one_of_invariant_card`)
を直接再利用不可。

### 残 hP1neIIIIV (型 III/IV、MF≠Mσ) の精密 gate
TypePData(P₁, U≠⊥) を要する。M' = M_σ 内の M_F-complement U を構成:
- ✅ **2026-06-26⁶ construction landed**: **`exists_typeP1_mf_complement`** (sorry-free + axiom-clean、
  AxiomsCheck 登録) が K-invariant complement U (U≤M', M_F⊔U=M', K≤N(U), M_F⊓U=⊥) を供給。
  `exists_aInvariant_complement_within_normal` (GroupTheory/AInvariantComplement) に M'=M_σ (solvable)・
  M_F が M' で Hall (`maxNilpotentNormalHall_isHall` を index-divisibility `relIndex_mul_relIndex` で transfer)・
  |K| coprime |M_σ| (κ⊆σᶜ via `kappa_subset_sigmaCompl`、`coprime_of_isPiGroup_of_isPiGroup_compl`) を供給。
  ⟹ **hUle/hKnorm/hDcompl/U≠⊥ は achievable** (構成核 = Coq `of_typeP` の U 構成に対応)。
- ✅ **2026-06-26⁶ hcommon landed**: **`typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma`**
  (sorry-free+axiom-clean、AxiomsCheck 登録) = 型 P₁(MF≠Mσ)・U≠⊥ の TypePData が TypePNontrivialCore
  (U≠⊥ ∧ |W₁| prime ∧ M_F# TI) を満たす。|W₁|=|K|=[M:M']=p prime (`theoremA8_structure`) + M_F# TI
  (`fitting_isTI_of_mf_ne_msigma`+`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`)。
  ⟹ III/IV last mile `isTypeIII_or_IV_of_typePData` の hcommon 入力を供給。
- **⟹ hP1neIIIIV の achievable 部分は全 discharge** (complement + hcommon)。**残 deep residual = TypePData
  の U-fields (hUnilp=M'/M_F nilpotent / hSDfit / hFiteq) + N(U)≤M、全て Coq `Fcore_structure` 内容**。
  次セッション = gated `typePData_of_isTypeP1_mf_ne_msigma_of_inputs` (complement の hDcompl 変換 +
  3 deep residual を hypothesis) で wire、または M'/M_F nilpotent を Fcore_structure から形式化。
- **deep 残差 3 本** (全て Coq `Fcore_structure` の MF≠Mσ branch に entangle):
  - **hUnilp (U nilpotent)** ← **M'/M_F nilpotent** (Coq `Fcore_structure` の `nilpotent(M'/M_F)`、
    Lean 未形式化 "deferred quotient API")。U ≅ M'/M_F ゆえ。**最深 gate**。
  - **hSDfit/hFiteq** (Fitting 分解 F(M)=M_F⊔(U⊓C(M_F)) の U≠⊥ 版)。
  - **N(U)≤M** (P₁ 特性、Coq `typePfacts` の `M∈M_P1 ⟺ U=1∨N(U)⊆M`、embedding 由来)。
- TypePNontrivialCore の |W₁| prime + M_F# TI は `theoremA8_structure` + 
  `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI` で achievable (data があれば)。
- III/IV last mile = `isTypeIII_or_IV_of_typePData` (既存、U abelian で III/IV split)。

⟹ hP1neIIIIV と hP1eqV-trichotomy は**両方 Coq `Fcore_structure`/`nonTI_Fitting_structure` の
深い §15/§16 構造定理**に bottom-out。次の実質前進 = (i) **M'/M_F nilpotent** を Fcore_structure から
形式化 (hP1neIIIIV の核 gate を解く、再利用性高) または (ii) **(8.8) trichotomy の W₁-action 解析**
(hP1eqV を完全 close)。どちらも multi-session。

### ✅ 2026-06-27 (lane-f): hP1neIIIIV の deep residual 3 本を全 close — TypePData 完全構成 (Cor 15.5)

前項が「最深 gate・multi-session」とした **M'/M_F nilpotent (hUnilp) / hSDfit / hFiteq を全て実証明**
(BG Cor 15.5)。型 `P₁` (`M_F≠M_σ`) 極大の **完全な TypePData が sorry-free+axiom-clean で構成可能**に
(type III/IV carrier-constructibility milestone、`typePData_of_isTypeP2` の P₁ 版)。残 gate は
**N(U)≤M (Pf 8.7) のみ**。commit `5671e77a`/`29c5f5bf`/`7f5d784f`/`33c58fa8`。

新規 (全 sorry-free+axiom-clean、AxiomsCheck 登録済):
- `isNilpotent_complement_of_isTypeP1_mf_ne_msigma` (hUnilp): U≅M_σ/M_F、Thm 15.2 の `Q⋊D=M_σ`
  (D nilpotent) ⟹ M_σ/M_F は D の商写像像で nilpotent ⟹ U nilpotent。**前項の "deferred quotient
  API" は不要だった** — `nilpotent_of_surjective` + `MulEquiv.ofBijective` で直接。
- `isComplement'_mf_complement_of_sup_inf` (hDcompl): sup/inf + M_F◁M' から第二同型 (`relIndex_sup_right`)
  + `isComplement'_of_card_mul_and_disjoint`。`fitting_decomposition` 非依存。
- `mem_centralizer_of_inner_conj_of_coprime` (再利用可能 coprime-action 核): x が N を normalize +
  conj_x が inner (=conj_n) + orderOf x ⊥ |N| ⟹ x∈C(N) (`normalizerMonoidHom` の像位数論法)。
- `fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma` (hFiteq+hSDfit): F(M)=M_F⊔(U⊓C(M_F))。
  F(M) nilpotent + M_F normal Hall ⟹ Dedekind で F(M)=M_F⊔(U⊓F(M)); crux U⊓F(M)⊆C(M_F) は
  F(M)=C_M(M_F)·M_F 分解 + 上記 coprime 核。hSDfit は M''≤F(M) (fitting_decomposition) 経由。
- `typePData_of_isTypeP1_mf_ne_msigma`: 上記 + `exists_typeP1_mf_complement` を
  `typePData_of_isTypeP_of_inputs` に供給して完全構成。
- `isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma`: bridge 配線 (hP1eqV/hFI と同パターン)。`case hP1neIIIIV`
  を wire、残 sorry = N(U)≤M のみ (Pf 8.7、type II と区別する complement 自己正規化性)。

⟹ **残 W1 forward = hP1eqV trichotomy (8.8 W₁-action) + hP1neIIIIV の N(U)≤M (8.7)**。両者は char/Coq
`Fcore_structure` の complement uniqueness。reverse 4 bridge (π(W₁)⊆κ carrier) は別 (lane-b char gate)。

### ✅✅✅ 2026-06-27² (lane-f): hP1neIIIIV bridge を完全 close — N(U)≤M (Pf 8.7) を実証明 (axiom-clean)

前項が「最深 gate・char/Coq `Fcore_structure`」とした **N(U)≤M を完全に実証明**。⟹
**`isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma` (hP1neIIIIV) が完全 sorry-free + axiom-clean**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` のみ)。Coq `BGsection16` `typePfacts`
(P1maxM/U≠1 枝) の ~10 行論法を移植。前項の「multi-session 深い構造定理」評価は過大評価だった —
σ-Sylow normalizer uniqueness (BG §10、repo 在庫) で済む。

**重要訂正**: 前 entry が hP1neIIIIV を「char/Coq `Fcore_structure` complement uniqueness」に
bottom-out するとしたのは**誤り**。正しくは N(U)⊆M は **Coq `typePfacts` の純群論論法** (Sylow-of-U の
一意性 + σ-Sylow normalizer ⊆ M) で、char gate も `Fcore_structure` の depth も不要。

新規 (全 sorry-free + axiom-clean、AxiomsCheck 登録、`S16_MainResults`):
- **`normalizer_le_normalizer_map_sylow_of_isNilpotent`** (汎用・再利用可): U nilpotent ⟹ Sylow_p(U)=P̄
  が一意 (`Ch01.Sylow.normal_of_isNilpotent` + `Sylow.unique_of_normal`) ⟹ N_G(U) ≤ N_G(P̄)
  (g∈N(U) が U の唯一 Sylow を保存)。Coq の `char_norms (pcore_char p U)` ステップ。
- **`typeP1_complement_mem_sigma_and_factorization`**: 型 P₁ の M_F-complement U と p∈π(U) について
  (1) p∈σ(M) (p∣|U|∣|M_σ|、`Msigma_subgroupOf_isHall`) (2) p-part|U|=p-part|M| (= Sylow_p(U) は
  σ-Sylow of M)。[M:U]=[M':U]·[M:M']、[M':U]=|M_F| (`IsComplement'.index_eq_card`)、p∤|M_F|
  (M_F Hall in M + |U|∣[M:M_F])、p∤[M:M_σ] (σ-Hall)。Coq の `sMp`/`sylP` ステップ。
- **`isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma`** 本体を sorry-free 化: p∣|U| を取り P̄=Sylow_p(U)、
  helper で N(U)≤N(P̄)、P̄ を `Sylow.ofCard` で `Sylow p ↥M` に package、
  `normalizer_sylow_map_le_of_mem_sigma` (BG §10) で N(P̄)≤M。

⟹ **`proposition_type_classification` の hP1neIIIIV case が axiom-clean に閉じた** (full build 3884
green、AxiomsCheck OK)。**残 W1 forward = hP1eqV trichotomy (8.8 W₁-action) のみ** (`isTypeV_…` 2511、
¬FittingIsTI の Suzuki/SL₂ 構造 |W₁|∣p∓1 = Coq `nonTI_Fitting_structure`)。reverse 4 bridge
(hIIP2/hIIIIVP1/hVP1、π(W₁)⊆κ carrier) は別系統 (lane-b char、FeitThompson 未使用)。

### 🔬 2026-06-27³ hP1eqV (残 W1 forward) の精密 scoping — 次セッションの entry point

**FT 必要性の確定**: `typeP_imp_nonI` (FeitThompson:355) は型 P₁∧M_F=M_σ で `hdV.mpr` (hP1eqV) ⟹
`IsTypeV` を構成し `no_typeV_maximal` (Pf 10.10) で背理。`IsTypeNonI := IsTypeII∨III∨IV∨V`
(positive disjunction) ゆえ型 V を**構成**する必要があり、`TypeVData` の `alternative` field を埋める
=trichotomy 証明が要る。**`alternative` の値自体は FT-path で読まれない** (consumer は
`MaximalSubgroupTypeConj` の equivariance のみ; dade chain/`typeV_forces_coherence` は `typeP`/
`type_alt` のみ消費) が、`TypeVData` を inhabit するには field を埋めねばならず bypass 不可
(carrier `TypeVData` 定義変更は cross-lane で blast radius 大、かつ Thm 15.7(d)(e) は genuine BG 数学)。

**型 V 固有の単純化**: 型 V は型 P₁ ⟹ Coq の abelian-H 枝 (e1=型F, rank 2) は**排除** (P1 で K_s≠1∧
M''=1 矛盾)、必ず非 abelian H = (e2)/(e3) (Suzuki/SL₂)。⟹ disjunct 1 (FittingIsTI) は別途 handle 済、
**残 = disjunct 2 (|W₁|∣p-1) ∨ disjunct 3 (|O_p(M_F)|=p³ ∧ |W₁|∣p+1)** のみ。

**既存 building blocks (S15_MF、過去 lane-f、全 sorry-free)**:
- `not_isCyclic_opiCore_mf_of_orderP_le_conj` (8147、Coq `not_cycMp`): O_p(M_F) 非 cyclic。
- `not_isUniquelyMaximal_mf_inf_centralizer_of_not_le` (8252、Coq `E1X_facts` C1∉𝒰)。
- `isMulCommutative_mf_inf_centralizer_of_not_le` (8313、Coq `E1X_facts` abelian C1)。
- **`typeF_nonabelian_cyclic_opiCore_compl` (8475、Coq `cycHp'`)**: `IsCyclic (O_{p}ᶜ M_F)` —
  **両 disjunct の共通項を直接供給** (要 wire)。

**残 deep core (genuine multi-session、Lean 未形式化)**:
1. **|Z0| prime** (Z0=Ω₁(Z(O_p(M_F)))): Coq は Lemma 10.13(b) + **Cor 15.3(b)** (B maximal in G,
   text 未言及) で導出。最深。
2. **|W₁| ∣ p∓1** (W₁=K の B=X1×Z0 への作用の Frobenius 整除性) + disjunct 2 vs 3 の choice。
   ⚠ **型 F の U₀-Frobenius engine `typeF_exponent_dvd_sub_one_of_invariant_card` は K-action が
   FPF でない (K*=C_{M_F}(K)≠⊥) ため直接再利用不可** ([[ft-endgame-two-poles]] 2026-06-26⁵)。
3. **|O_p(M_F)| = p³** (disjunct 3、SL₂(p) 型 Sylow)。

⟹ 次セッション: (a) `not_cycMp`/`E1X_facts`/`cycHp'` を wire して disjunct の共通項 (p∈π(M_F)+
IsCyclic O_{p'}) を sorry-free 化、(b) deep core (|Z0| prime ← Lemma 10.13(b)/Cor 15.3(b)、
|W₁|∣p∓1 ← W₁-action) を named residual に isolate or 上流形式化。Coq `BGsection15.v:939-1095+`
精読が必須。**multi-session、上流から (|Z0| prime か W₁-action engine から)**。

### ✅ 2026-06-27⁴ (lane-f): hP1eqV type-V trichotomy の共通部分を実証明、残差を |W₁|∣p∓1 に縮小 (commit 8a7f544e)

上 (a) を landed。**型 V `TypeVData.alternative` (Pf (8.8) (e2)/(e3)) の共通項を実証明** ⟹
`isTypeV_of_isTypeP1_mf_eq_msigma` の ¬FittingIsTI sorry が「alternative 全体」→「`|W₁|∣p∓1`
divisibility のみ」に縮小。新規 (全 axiom-clean、AxiomsCheck 登録、S16_MainResults):
- **`not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma`**: 型 V で M_F 非abelian (Coq abelian-H 排除)。
  TypePData の W₂=C_{M'}(W₁#) が nontrivial かつ ⊆ M''、型V で M'=M_σ=M_F ⟹ M''=(M_F)'⊇W₂≠⊥
  (`commutator_eq_bot` + `secondDerivedInAmbient`)。**過去 entry の「Ks≤M'' (Ptype_cyclics) が要・未形式化」
  は不要だった** — TypePData.W2_le が直接 W₂≤M'' を供給。
- **`exists_prime_cyclic_opiCore_compl_of_isTypeV`**: 型 V ¬FittingIsTI で ∃p∈π(M_F), IsCyclic O_{p'}(M_F)。
  **既存 `exists_inf_conj_fitting_orderP_witness` (S15、witness 抽出 — 自前重複 `exists_nonTI_witness` は
  削除、CLAUDE.md 重複回避)** を `typeF_nonabelian_cyclic_opiCore_compl` (cycHp') に供給。
- `isTypeV_of_isTypeP1_mf_eq_msigma` ¬FittingIsTI case 再構成: 共通項 proved、残 sorry =
  `|W₁|∣p-1 ∨ (|O_p(M_F)|=p³ ∧ |W₁|∣p+1)` のみ。

**残 deep core (検証済み深い、Lean 未形式化)**: `|Z0|=p` (Z0=Ω₁(Z(O_p(M_F))))= Coq `basic_p2maxElem_structure`
(B=X1×Z0, r_p(B)=2, oZ0=p) + Lemma 10.13(b)/Cor 15.3(b)。`|W₁|∣p∓1` engine: disjunct2 は
`card_dvd_sub_one_of_isFrobeniusAction` (S15:8354 在庫) を K-on-Z_p Frobenius 作用に適用、disjunct3
(|K|∣p+1) は Singer/GL₂(p) 作用 (別 engine)。S05 に omega1Center prime lemma 在庫 (要 p2maxElem 接続)。
**次セッション = |Z0| prime の p2maxElem 形式化 (上流)、その後 Frobenius/Singer 作用で divisibility**。

### 🔬 2026-06-27⁵ divisibility core の精密 mapping — disjunct 2 は到達可能、disjunct 3 が deep Singer

**重要発見 1: `|Z0|=p` は既に形式化済み**。`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`
(S15:8562、Coq `oZ` の q=p case) が「∀q∈π(M_F), order-q の Z≤M_F が M-normal」を供給
(q=p で Z=Ω₁(Z(O_p))、|Z|=p を rank≤2 bound で証明済)。⟹ |Z0|=p の自前再構築は**不要**。

**重要発見 2: disjunct 2 (`|W₁|∣p-1`) は到達可能** (path 確定):
- data.W1 = K (κ-Hall、type-V `typePData_of_inputs (W1:=K)` line 2113)。
- `exists_orderQ` で Z order p (=witness)、M-normal。K≤M が Z に作用。
- **semiprime** `M⊓C(k)=K⊔Kstar` (`typeP_centralizer_kappaElement_eq` S14:9333) ⟹
  C_{M_F}(k)≤M_σ∩(K⊔Kstar)=Kstar (σ-decomp)。
- **by_cases Z⊓Kstar=⊥**: ⊥ なら C_Z(k)≤Z∩Kstar=⊥ ∀k∈K# ⟹ K FPF on Z ⟹
  `card_dvd_sub_one_of_isFrobeniusAction` で `|K|∣p-1` = **disjunct 2**。
- 残 helper: (i) `M_σ∩(K⊔Kstar)=Kstar` σ-decomp (~40行、K σ'-Hall + Kstar σ、未在庫) (ii)
  IsFrobeniusAction K-on-Z setup (~50行、`typeF_exponent_dvd_sub_one_of_invariant_card` S16:1778 の
  U0-on-Z pattern を K に流用)。

**disjunct 3 (Z⊓Kstar≠⊥ ⟺ Z≤Kstar=Z0)**: `|O_p(M_F)|=p³ ∧ |W₁|∣p+1` = deep Singer/GL₂(p) 作用
(Coq defZP/rPle2/oZ0 + `basic_p2maxElem_structure`)。**真に残る最深部**。

⟹ **次セッション = disjunct 2 を上記 path で landing** (σ-decomp helper + Frobenius setup、
sorry を Z≤Kstar/disjunct-3 case のみに縮小)、その後 disjunct 3 の Singer 解析。

### ✅✅ 2026-06-27⁶ (lane-f): hP1eqV disjunct 2 (|W₁|∣p-1) を実証明 — 残を disjunct 3 (Singer p³) のみに (commit 9024ad0d)

上の path 通り **disjunct 2 を完全 landing**。⟹ `isTypeV_of_isTypeP1_mf_eq_msigma` の残 sorry が
**disjunct 3 (Z≤Kstar, |O_p(M_F)|=p³ ∧ |W₁|∣p+1, deep Singer/SL₂(p)) の 2 本のみ**に。新 engine
(全 axiom-clean、AxiomsCheck 登録、S16_MainResults):
- **`centralizer_msigma_kappaElement_eq_kstar`**: k∈K# で C_{M_σ}(k)=Kstar。σ-decomp は modular law
  (非可換で無効) でなく **`ActsPrimeOn` (Prop 14.2 typeP_structure.1) + `S13.fixedBy_eq`** で直接
  (fixedByElement(M_σ,k)=fixedBy(M_σ,K)=Kstar、全 defeq、~5行)。
- **`kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot`**: κ-Hall K が M-normal order-p Z≤M_σ を
  normalize ∧ Z⊓Kstar=⊥ ⟹ K は Z に Frobenius 作用 (C_Z(k)≤Z⊓Kstar=⊥) ⟹
  `card_dvd_sub_one_of_isFrobeniusAction` (typeF engine の U0→K 流用) で |K|∣p-1。

wiring (isTypeV ¬FittingIsTI case): witness (exists_inf_conj) + cycHp' + |Z0|=p (exists_orderQ 再利用) +
|data.W1|=|K| + **by_cases Z⊓Kstar=⊥**: ⊥ なら disjunct 2 (engine)、≠⊥ (Z≤Kstar) なら disjunct 3 sorry。

**残 = disjunct 3 (Singer p³) のみ = 真の最深部**: Z⊆Kstar (=Z0=Ks) ⟹ K が Z(P) を中心化 ⟹
P=O_p(M_F) extraspecial of order p³ + K⊆Singer cyclic ⟹ |K|∣p+1。要 extraspecial 群論 +
Singer cycle/GL₂(p) 作用 (Coq defKs/defZP/rPle2 + `basic_p2maxElem_structure`)。**次セッション =
disjunct 3 の extraspecial/Singer 形式化** (genuine 最深、新インフラ大)。

### 2026-06-27⁷ (lane-f): disjunct 3 着手 — by_cases 再構成 + `p3group_extraspecial` 前提を実証明

disjunct 3 (Singer p³) の formalization に着手。深い 3 BG 前提に bottom-out すると確定したため、上流の
再利用可能 prerequisite から積み上げ開始。

**landed (2 commit):**
1. **`isTypeV_of_isTypeP1_mf_eq_msigma` の (e3) ケースを `by_cases |W₁|∣p-1` に再構成** (commit `99c49650`,
   build green): Coq `nonTI_Fitting_structure` の実分岐 (`Ks=Z0 → |K|∣p-1`) に整合。
   - |W₁|∣p-1 成立 → disjunct (e2) 直接 (cyclic O_{p'} = hcyc)。
   - ¬(|W₁|∣p-1) → disjunct (e3)。このとき Z⊓Kstar≠⊥ (Frobenius engine の対偶) ⟹ Z≤Kstar=Z0=Z(P)。
   - **正しさの改善**: 旧コードは Z⊓Kstar≠⊥ ∧ |K|∣p-1 の sub-case で偽の goal |K|∣p+1 を追っていた。
     新構成で (e3) 枝が Singer 仮説 `¬(|W₁|∣p-1)` を保持。
2. **`IsExtraspecial.of_card_eq_prime_cube` (= Coq `p3group_extraspecial`) を実証明** (sorry-free +
   axiom-clean、AxiomsCheck 登録、`OddOrder/GroupTheory/IsExtraspecial.lean`): **非可換 p³ 群は
   extraspecial** (`Z=[G,G]=Φ(G)`, `|Z|=p`)。disjunct 3 で P=O_p(M_F) を extraspecial に格上げする構造ステップ。
   - |Z|=p: `card_center_eq_prime_pow` (|Z|=p^k, k>0) + k=3 排除 (Z=⊤⟹abelian) + k=2 排除
     (G/Z cyclic⟹abelian, `commutative_of_cyclic_center_quotient`)。
   - [G,G]=Z: G/Z 位数 p² ⟹ abelian (`IsPGroup.commutative_of_card_eq_prime_sq`) ⟹ [G,G]≤Z; 非可換ゆえ
     [G,G]≠⊥; |Z|=p prime ⟹ =Z。
   - Φ=Z: Z=[G,G]≤Φ (`commutator_sup_pow_closure_le_frattini`); |Φ|=p² 排除は新 helper Burnside basis。
   - **新 Burnside helper `isCyclic_of_isCyclic_quotient_frattini`** (`FrattiniPGroup.lean`、汎用 finite
     group、sorry-free+axiom-clean+AxiomsCheck): G/Φ cyclic ⟹ G cyclic (`frattini_nongenerating` 経由)。

**インフラ調査結論 (Explore + 手動、disjunct 3 の depth 確定)**:
OddOrder に**既存**: `IsExtraspecial`/`IsCentralProduct`/`IsNarrow` (NarrowPGroup) + narrow 特徴付け
(`S05_NarrowCharacterization`, BG §5 Lem 5.2) + `IsFrobeniusAction`+`card_dvd_sub_one_of_isFrobeniusAction`
(p-1 engine) + GL₂(p) 位数 (`S7A1_JpGL2p`, `card_gl2_zmod_prime`=p(p-1)²(p+1)) + p-群 small-rank 大量
(`S04_PGroupsSmallRank`/`S04d_GorThm415`=`pRank_le_two_of_scn3_empty`/`S04f_Blackburn`)。
**未ポート (Coq のみ、disjunct 3 の真の gate)**:
- **`mFT_rank2_Sylow_cprod`** (BG §10.7b, `coq/BGsection10.v:699`): 非可換 rank≤2 p-群 = extraspecial p³ ∘
  cyclic の中心積。`rank2_coprime_comm_cprod` (BGappendix) に依存。→ **sorry 1 (|P|=p³)** の核。
- **`repr_extraspecial_prime_sdprod_cycle`** (BG §2.5, `coq/BGsection2.v:580`): extraspecial P ⋊ cyclic K
  (prime action C_P(k)=Z(P)) ⟹ |K| ∣ p^n±1。→ **sorry 2 (|K|∣p+1)** の核。
- **`Aut_narrow`** (BGappendix): narrow p-群の coprime odd cyclic 自己同型は r(P)>2 で |K|∣p-1。
  → Coq `rPle2` (r(P)≤2) の gate (¬|K|∣p-1 と矛盾)。

**sorry 2 (|K|∣p+1) の数学的核心 (確定)**: K cyclic が P/Z(P)≅F_p² に prime action (C_P(k)=Z) で作用
⟹ K↪GL₂(p) を FPF (固有値1なし) + **K は交換子形式を保存** (K が Z(P)=Ks を中心化) ⟹ **K≤Sp₂=SL₂(p)**、
かつ既約 (¬|K|∣p-1 ⟹ split torus 排除) ⟹ K≤Singer F_{p²}^*、**SL₂∩Singer=norm-1 部分群=位数 p+1** ⟹ |K|∣p+1。
mathlib に `GaloisField` (F_{p²}) はあるが Singer torus/Schur/non-split torus は未整備 → 要新インフラ。

**残 = disjunct 3 の 2 sorry (genuine multi-week)**: `S16_MainResults.lean` の
`isTypeV_of_isTypeP1_mf_eq_msigma` (e3) 枝、`Nat.card ↥(opiCoreInG {p} (S15.MF M)) = p³` と
`Nat.card ↥data.W1 ∣ p+1`。両者とも上記 3 BG 前提 (appendix Aut_narrow + §2.5 Singer + §10.7b cprod) の
ポートを要する。次の上流ステップ候補: (a) `mFT_rank2_Sylow_cprod` (rank-2 Sylow cprod、narrow 特徴付け
S05 + Blackburn を活用)、(b) SL₂∩Singer divisibility (F_{p²} non-split torus、`p3group_extraspecial` の
extraspecial 構造を入力)。`p3group_extraspecial` は (b) の P-extraspecial 入力を供給する down-payment。

### 2026-06-27⁸ (lane-f): disjunct 3 de-risk — 文献+Coq 精読で scope 大幅縮小 (ユーザー方針: 文献→Coq→必要なら ChatGPT)

ユーザー裁可「まず文献と Coq で確認、gap が埋まらなければ ChatGPT」に従い disjunct 3 の 3 前提を精読。
**「multi-week の §2/§10/appendix 未ポート」評価を訂正** — 主要機構はポート済で scope は大幅縮小:

**重要訂正 1: `Aut_narrow` は appendix でなく BG §5、かつ完全ポート済**。
`solvableAut_of_narrow` (`S05_NarrowAutomorphisms.lean:976` = BG Thm 5.5) が:
- (a) A/O_p(A) abelian p'-群
- **(b) `3 ≤ pRank R p → ∀ a:A, Coprime(orderOf a) p → orderOf a ∣ (p-1)`** ← Coq `rPle2` の核心
- **(c) `(card A).Prime → ¬card A∣p(p-1) → card A ∣ (p+1)/2 ∧ (R=[R,A] ∧ ¬abelian R → card R = p³)`**
を供給。⟹ **rPle2 (r(P)≤2) は Thm 5.5(b) で到達可能** (r(P)>2 ⟹ |K|∣p-1 で ¬|K|∣p-1 と矛盾)。

**重要訂正 2: |P|=p³ は BG §4 Blackburn 部品で到達可能**。`S04f_Blackburn`:
- `card_le_prime_cube_of_pRank_le_two_of_exponent_prime` (rank≤2 + exp p ⟹ card≤p³)
- `omega1_large_card_eq_prime_cube_and_pow_eq_one` (p>3, rank≤2, |Ω₁|>p² ⟹ |Ω₁|=p³)
+ Thm 5.5(c) の `card R = p³`。`mFT_rank2_Sylow_cprod` (Coq §10.7b) も最終ステップで
**`p3group_extraspecial` を使用** (BGsection10.v:717、`have[||[]]:=p3group_extraspecial pS`) = 私の
`of_card_eq_prime_cube` が genuine prerequisite と裏付け。

**残る真の gap = |K|∣p+1 (sorry 2)**: Coq は `repr_extraspecial_prime_sdprod_cycle` (BG §2.5 Thm 2.5,
`BGsection2.v:580`) を使うが、これは **重い matrix 表現論** (`mx_irreducible`/`mx_Maschke`/`rfix_mx`/
quasi-regular cyclic eigenspace Prop 2.4) で faithful ポートは大仕事 (S02_Representations は §2E stub)。
**⟹ 回避ルート (route B) = 初等的 SL₂(p) symplectic torus 経路**:
- P extraspecial p³ ⟹ V=P/Z(P)≅F_p² + 交換子 symplectic form。
- K acts on V (共役)、K が Z(P) を中心化 ⟹ form 保存 ⟹ **K↪Sp₂(p)=SL₂(p)**。
- prime action C_P(k)=Z(P) ⟹ K FPF on V (固有値1なし)。
- K cyclic semisimple (coprime p) ⟹ split/non-split torus。¬|K|∣p-1 ⟹ non-split ⟹ **|K|∣p+1**。
- `S7A1_JpGL2p` (Isaacs Ch07) の GL₂(p) 機構 (`card_gl2_zmod_prime`=p(p-1)²(p+1)、SL₂、`sl2_unique_involution`)
  を活用。SL₂(p) torus 分類 (cyclic abelian ⟹ split∣p-1 / non-split∣p+1) を要形式化。

**⟹ 改訂計画 (上流順、全て gap 埋まる、ChatGPT 不要)**:
1. `IsNarrow p P` 確立 (P=O_p(M_F)、B=X₁×Z0 が p2maxElem rank 2 から) — Thm 5.5 適用の前提。
2. K の P への faithful 作用 (K→MulAut P、C_K(P)=1) setup。
3. rPle2: Thm 5.5(b) で r(P)≤2 (¬|K|∣p-1 contra)。
4. |P|=p³: Blackburn (rank≤2 + nonabelian + |Z|=p) + `of_card_eq_prime_cube` で extraspecial。
5. |K|∣p+1: route B (SL₂(p) symplectic torus、初等)。最大の残工。

これは bounded な assembly + SL₂ torus 論で、「§2.5 repr の multi-week ポート」ではない。

### 2026-06-27⁹ (lane-f): route B の Singer 段は `SingerField.lean` でポート済 — 追加 de-risk

route B (|K|∣p+1) を更に精読。**Singer 機構は `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`
にポート済**で、SL₂ torus 経路が大幅短縮:
- `nonempty_singerFieldData` (SingerField:101): 有限 abelian `C` が elem abelian p-群 `M` に **F_p-既約**
  作用 (`IsSimpleModule (MonoidAlgebra (ZMod p) C) M`) ⟹ M は体 `K`、C は乗法作用 (`μ : C →* Kˣ`, compat)。
- `nonempty_ringEquiv_galoisField` (SingerField:83): |M|=p^n ⟹ K ≅ GF(p^n)。
- `card_K_eq`: |K|=|M|。

⟹ **route B 整理 (上流順、sorry 1 |P|=p³ が前提)**:
1. **|P|=p³ (sorry 1) 先決**: rPle2 (Thm 5.5(b) `solvableAut_of_narrow`) → |P|=p³ (Blackburn §4 +
   `of_card_eq_prime_cube`)。route B の V=P/Z(P)≅F_p² module setup の前提。
2. V=P/Z(P): extraspecial ⟹ |V|=p², elem abelian。K-action (共役)。
3. **既約性**: K cyclic semisimple (coprime p)、FPF (prime action C_P(k)=Z(P))、¬|K|∣p-1 ⟹ V 既約
   (可約なら split torus で |K|∣p-1 矛盾)。= `IsSimpleModule (MonoidAlgebra (ZMod p) K) V`。
4. **Singer**: `nonempty_singerFieldData` + galoisField ⟹ V≅GF(p²)、μ: K↪GF(p²)ˣ (faithful ゆえ injective)。
5. **det 1 ⟹ μ(k)^(p+1)=1**: extraspecial 交換子 ⟹ V に symplectic form、K 保存 (Z(P) 中心化) ⟹
   det(K-action)=1。det = Algebra.norm(μ k) = (μ k)^(1+p) (GF(p²) norm) ⟹ μ(k)^(p+1)=1。
6. **|K|∣p+1**: K cyclic gen g、|K|=orderOf g = orderOf(μ g) (μ inj, `orderOf_injective`)、
   (μ g)^(p+1)=1 ⟹ orderOf(μ g)∣p+1 (`orderOf_dvd_of_pow_eq_one`) ⟹ |K|∣p+1。

**残る genuine 工 (sorry 1 後)**: 既約性判定 (step 3)、symplectic form + det=norm (step 5)。
両者とも mathlib の Representation/Algebra.norm + IsExtraspecial 構造で形式化可能 (multi-session だが
全ピース所在確定、ChatGPT 不要)。**次セッション = sorry 1 (|P|=p³) を Thm 5.5(b) + Blackburn で着手**。

### ✅✅ 2026-06-27¹⁰ (lane-f): disjunct 3 assembly 着手 — rPle2 gate を実証明 (de-risk 検証成功)

de-risk 後、構造 assembly を上流から brick 化。**3 brick landed (全 sorry-free + axiom-clean、
AxiomsCheck 登録)**:
1. `IsExtraspecial.of_card_eq_prime_cube` (p3group_extraspecial、commit `6dadd6bb`)
2. **`isNarrow_opiCore_of_three_le_pRank`** (commit `5e2b0345`): P=O_p(M_F) は pRank≥3 で narrow。
   witness X₁ + hrank3 (E1X rank) を S05 narrow 特徴付けに供給。**Sylow/β plumbing 不要**。
3. **`pRank_opiCore_le_two_of_kappaHall`** (rPle2、commit `85ad96d8`): **当初「appendix Aut_narrow
   未ポート」と誤評価した r(P)≤2 gate を実証明**。by_contra pRank≥3 → IsNarrow → faithful φ:↥K→MulAut↥P
   (A=K 直接、quotient 不要) → Thm 5.5(b) `solvableAut_of_narrow` → |K|∣p-1 矛盾。
   **= de-risk (Thm 5.5 ポート済 → rPle2 到達) の実証**。

**|P|=p³ の構造定理も発見済ポート: `blackburnRankTwoClassification` (S04f, BG Thm 4.16)** —
rank≤2 + [R,A]=R + 非可換 ⟹ central product (extraspecial p³ ∘ cyclic)。A=V (p'-Hall of N_G(P))
で適用。

**rPle2 の唯一の input = faithfulness (K⊓C_G(P)=⊥) は全て導出可能と確定** (次 brick):
- semiprime `centralizer_msigma_kappaElement_eq_kstar` (S16:2488) ✓
- **Kstar=Z**: `kstar_card_prime_of_inputs` (S16, BG Thm C(8), U=⊥⟹|K*| prime) + Z≤Kstar (hZK) +
  |Z|=p ⟹ |Kstar|=p ⟹ Kstar=Z ✓
- **X₁⊄Z**: `isMulCommutative_mf_inf_centralizer_of_not_le` (C_{M_F}(X₁) abelian) + Brick 1 (P 非可換)
  — X₁⊆Z⟹P⊆C_{M_F}(X₁) abelian ⟹ P abelian 矛盾 ✓
- C_K(P) 論法: x∈K⊓C_G(P)# ⟹ X₁≤C_{M_σ}(x)=Kstar=Z、X₁⊓Z=⊥ ⟹ X₁=⊥ 矛盾。

**残 brick (全ピース located)**: (4) faithfulness、(5) |P|=p³ (P=Sylow_p(G) + Thm 4.16 + |Z(P)|=p、
|Z(P)|=p は Z(P)⊆Kstar=Z 経由で coprime_odd_faithful_Ohm1 [K が Ω₁(Z(P))=Z を中心化 ⟹ Z(P) 中心化]
が唯一の未ポート、汎用 coprime-action 事実)、(6) route B (|K|∣p+1、SingerField + symplectic det=1)。

### ✅✅ 2026-06-27¹¹ (lane-f 再開): brick (4) faithfulness + rPle2 (r(P)≤2) + sylP_G を実証明 (3 axiom-clean lemma)

de-risk 後の構造 assembly を上流から 3 brick landing。**全 sorry-free + axiom-clean + AxiomsCheck 登録**
(commits `07005949` + `3724d448`、full build 3884/3872 green)。

1. **brick (4) `kappaHall_inf_centralizer_opiCore_eq_bot`** (Coq `tiKcP`/`defKs`): 型V Singer ケースで
   κ-Hall K が P=O_p(M_F) に faithful 作用 (K ⊓ C_G(P) = ⊥)。nonidentity x∈K⊓C_G(P) は P⊇X₁ を中心化
   ⟹ X₁≤M_σ⊓C_G(x)=K*=Z (`centralizer_msigma_kappaElement_eq_kstar` + `kstar_card_prime_of_inputs`
   で |K*|=p=|Z|)、X₁⊄Z と矛盾。**S15 refactor**: `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`
   の結論に `¬ X₁ ≤ Z` を追加 (q=p は内部 hX₁notZ、q≠p は coprimality で自明)、faithfulness に供給。
2. **rPle2 (r(P)≤2) を (e3) ブランチで実証明**: brick (4) faithfulness + `pRank_opiCore_le_two_of_kappaHall`
   を配線、hpodd/hKp' (κ∩σ=∅ via `kappa_subset_sigmaCompl`)/hKnormP/hZKstar を導出。
   `hrPle2 : pRank (O_p(M_F)) p ≤ 2` を sorry-free 確立。`hPnab` (P 非可換) も `opiCore_singleton_…`。
3. **sylP_G `exists_sylow_eq_opiCore_of_mf_eq_msigma`** (Coq `sylP_G`): M_F=M_σ ∧ p∈σ ⟹
   P=O_p(M_F) は Sylow_p(G)。{p}-Hall of nilpotent M_F (`oPiCore_isHall_of_isNilpotent`、p∤[M_F:P])
   ⟹ |P|=p^{v_p(|M_σ|)}; M_σ σ-Hall・p∈σ (`Msigma_isHall`、p∤[G:M_σ]) ⟹ =p^{v_p(|G|)} ⟹ `Sylow.ofCard`。

⟹ sorry 1 (|P|=p³) を gate `card_opiCore_eq_prime_cube_singer` に縮小 (**r(P)≤2 + P非可換 + P=Sylow_p(G)
が全て discharged の hypothesis**)。残 gate residual + 検証済み次手:

- **真のボトルネック = |Z(P)|=p = Coq `defZP`** ← **`coprime_odd_faithful_Ohm1` (BG Thm 1.11,
  BGsection1.v:429)** の port。これは §3/§4/§11/§13/§15 で多用される汎用 §1 coprime-action 定理だが
  **未ポート、かつ prereq `coprime_cent_prod` (G=C_G(A)·[G,A]) と `abelian_charsimple_special` も
  repo/mathlib に不在** ⟹ **multi-session port** (special group + binomial)。これが gate の本当の gate。
- **mFT_rank2_Sylow_cprod** = Lean `S10.sylow_structure_b` (Cor 10.7b、**private**) に実在。適用には
  (i) de-privatize、(ii) V=p'-Hall of N_G(P) complement 構成 (Schur-Zassenhaus、`sylow_structure_a` 経由)、
  (iii) **rank 変換**: sylow_structure_b は `rank P ≤ 2` を要求するが hrPle2 は `pRank P p ≤ 2`。
  p-群で rank=pRank: **`rank_le_pRank_of_isPGroup` (S09:571、private)** + `pRank_le_rank` で変換可。
  ただし central-product → |P|=p³ 抽出は (i)|Z(P)|=p を要するので、結局 coprime_odd_faithful_Ohm1 待ち。
- **次セッション最優先 = `coprime_odd_faithful_Ohm1` (BG Thm 1.11) の port** (high-value reusable §1
  インフラ、disjunct-3 |P|=p³ の唯一の真の gate)。その後 sylow_structure_b de-privatize + V + 抽出で
  gate 完了、最後に sorry 2 (route B Singer、|P|=p³ 下流)。
