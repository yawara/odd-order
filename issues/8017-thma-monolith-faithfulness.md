---
id: 8017
slug: thma-monolith-faithfulness
title: "BG Theorem A monolith: faithfulness (K-invariant U) + assembly"
created: 2026-06-21
---

# BG Theorem A monolith: faithfulness (K-invariant U) + assembly

## 背景

`theoremA_maximal_structure` (`S16_MainResults:144`, BG Theorem A, sorry) は §16 type-data 構成
(Prop 16.1 の hFI/hP2II/hP1neIIIIV、Theorem B-E) が cite する keystone。lane-b の bridge
(`typePData_W1_hall_coprime` 等) も κ-Hall cyclicity のために cite。

2026-06-21 (issue 8016 完了後) の調査で **忠実性の疑い**を発見:

- BG Theorem A(3) (mmd L4350): 「`KM_σ` は **`K`-invariant** complement `U` を持ち `UM_σ◁M=KUM_σ`,
  `U◁UK`」。U は **K-invariant に選ばれる** (存在主張)。
- BG Theorem A(4) (mmd L4351): 「`C_U(k)=1` for `k∈K#`」— これは A(3) の **K-invariant U** についての主張。
- BG Theorem A(5) (mmd L4352): 「`K*≠1` かつ `K≠1 → C_M(k)=K×K*` for `k∈K#`」。

しかし formalized `theoremA_maximal_structure` は `U` を **任意の (κ∪σ)'-Hall** (hU) として取り、
conjunct 4 (`∀k∈K#, U⊓C(k)=⊥`) と conjunct 7 (`K≠⊥→∀k∈K#, M⊓C(k)=K⊔Kstar`) を主張する。
**`C_U(k)=1` は U の共役の取り方で変わる** (共役不変でない) ので、非 K-invariant な U では偽の可能性大。
⟹ monolith は conjunct 4 (and 5-element) で **任意 U に対し over-strong = 忠実性 bug の疑い**。

(なお A(1)(2)(3-normal=`M≤N(UMσ)`)(5-Kstar)(6)(8) は U 非依存 or 任意 U で OK = 忠実。
`typeP_auxiliary_structure` (S15:1702) がこれら大半を sorry-free で供給:cyclic K / M≤N(UMσ) /
Mσ≤M' / M'=U⊔Mσ structure。A(8) は `theoremA8_structure` (issue 8016, axiom-clean)。)

## ✅ 2026-06-21 (cont.) 忠実性 audit 解決 + element-wise conjunct 4/5 を sorry-free 達成

**忠実性の結論: conjunct 4 (`C_U(k)=1`) は任意 (κ∪σ)'-Hall U で真。K-invariant 限定は不要、monolith
は (conjunct 4 について) 忠実。** 当初の「非 K-invariant U で偽の疑い」は**否定された**:

- **鍵: conjunct 4 (`U⊓C(k)=⊥`) は conjunct 7 (`M⊓C(k)=K⊔K*`) に還元され、conjunct 7 は U に依存しない。**
  `U⊓C_G(k) = U⊓(M⊓C_G(k)) = U⊓(K⊔K*)` (U≤M)、`|U|` は (κ∪σ)'-数、`|K⊔K*|=|K|·|K*|` は (κ∪σ)-数
  (`card_kappaHall_sup_Kstar`) ゆえ互いに素 ⟹ `U⊓(K⊔K*)=⊥`。**U の取り方 (K-invariant か否か) に無関係。**

**landed (S16_MainResults, 両 sorry-free + axiom-clean, AxiomsCheck 登録):**
- **`typeP_centralizer_kappaElement_eq`** (S16:149, conjunct 7 = BG Thm A(5) element form):
  type-P M + cyclic K で `∀k∈K#, M⊓C_G(k)=K⊔K*`。Prop 14.2(b1) (`typeP_structure`, rank-1 X の
  `N(X)⊓M=K⊔K*`) を element-wise に sharpen。Bridge: K cyclic ⟹ `⟨k⟩` の order-p 部分群 X≤K を取り
  `C_G(k)≤C_G(X)≤N_G(X)` ⟹ `M⊓C_G(k)≤N(X)⊓M=K⊔K*`; 逆は K abelian (`Subgroup.le_centralizer`) +
  `K*≤C_G(K)≤C_G(k)`。
- **`typeP_hall_inf_centralizer_kappaElement_eq_bot`** (S16:212, conjunct 4 = BG Thm A(4)):
  type-P M + cyclic K + **U≤M** で `∀k∈K#, U⊓C_G(k)=⊥`。上記還元 + coprimality
  (`coprime_of_isPiGroup_of_isPiGroup_compl`)。**hUM (U≤M) は必須** (conjunct 4 は U≤M なしでは偽)。

## やること (残)

- [x] **忠実性の確認** ✅: conjunct 4 は任意 (κ∪σ)'-Hall U≤M で真 (上記)。restate 不要。
- [x] **assembly conjunct 7** ✅ `typeP_centralizer_kappaElement_eq`。
- [x] **assembly conjunct 4/5** ✅ `typeP_hall_inf_centralizer_kappaElement_eq_bot`。
- [ ] **monolith signature の忠実性 fix (cross-lane, hub/ユーザー裁可)**: 現 `theoremA_maximal_structure`
      (S16:249) は hKM (K≤M)・hUM (U≤M) を欠き、conjunct 3 (`M=K⊔U⊔Msigma`)・conjunct 4 が forces
      する K≤M/U≤M を満たさない ⟹ **as-stated は unprovable (faithfulness bug)**。fix には hKM・hUM
      追加が要るが、**`theoremA_maximal_structure` は Peterfalvi `S12_MaximalIII_IV_V:503` (lane-b) +
      S16:669 が cite** ⟹ signature 変更は cross-lane。`theoremA_ungated_conjuncts`/`theoremB(1)` の
      faithfulness precedent (hKM/hUM 明示) に倣う。**標準 (buggy) monolith に触れず新 faithful 版
      `theoremA_maximal_structure_faithful` (hKM/hUM 明示, 全 conjunct sorry-free) を別建てし、後で
      callers を移行**するのが安全。
- [x] **conjunct 3 (`M = K U M_σ`) standalone** ✅ `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`
      (S16, sorry-free + axiom-clean): type-F via `subgroupESetup_of_isHall_kappa_eq_bot.E_compl_sup`,
      type-P via `typeP_auxiliary_structure` complement (`M'=U M_σ`, `M'` complements `K`) pushed
      `M→G` (`subgroupOf_sup`/`subgroupOf_eq_top`)。⚠ Lean tip: `Msigma M`/`derivedInG M` を含む
      lattice `≤` は `le_antisymm`/`sup_le` で whnf 爆発 → 明示引数 `conv_lhs`/`rw [sup_comm …, ← sup_assoc]`
      の純 AC 書換えで回避。`rw [← hMM']` は `Msigma M` 内の `M` まで書換える → `conv_lhs` で LHS 限定。
- [x] **extended `theoremA_ungated_conjuncts`** ✅: 4→8 conjunct (A(2) cyclic K / A(3) M≤N(UMσ) /
      A(4) C_U(k)=⊥ / A(5)-element C_M(k)=K⊔Kstar 追加、hUM 追加)。
- [ ] **残 = faithful monolith の組立** (新版 `theoremA_maximal_structure_faithful`): conjunct 1-9 は全て
      sorry-free standalone で揃った (上記 + `theoremA8_structure` の A(8))。**唯一の gate = A(7) `M''≤F(M)`**
      = `derivedDerived_le_fittingInAmbient_of_inputs` (S15:6340, **type-P1 chief-factor 入力 Q/Q0/D に
      gated**, type-P1 構造論待ち)。A(7) が landing したら 11-conjunct faithful monolith を組める。
      buggy 標準 monolith (hKM/hUM 欠) は Peterfalvi S12:503 cite ゆえ触らない (cross-lane)。

## 完了条件

`theoremA_maximal_structure` が sorry-free (忠実な statement で)。中間は `theoremA_ungated_conjuncts`
を拡張 (現 4 conjunct → cyclic K / M≤N(UMσ) / A(8) 追加で ~7 conjunct) して available surface を増やす。

## 参照

- issue 8016 (closed): A(8) FittingIsTI axiom-clean = monolith conjunct 8 の供給元。
- `typeP_auxiliary_structure` (S15:1702): conjuncts 2/3-normal/9/M'-structure を供給。
- `theoremA8_structure` (S16:1015, axiom-clean), `theoremA_ungated_conjuncts` (S16:181, sorry-free)。
- `actsRegularlyOn_E23_E1_of_caseTau1` (S14:771): E₁ regular on E₂E₃ (conjunct 4 の E-setup 源)。
- mmd `references/bg/local-analysis.mmd` L4346-4355 (Theorem A statement)。
