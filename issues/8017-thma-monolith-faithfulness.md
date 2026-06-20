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

## やること

- [ ] **忠実性の確認**: conjunct 4 (`C_U(k)=1`) が任意 (κ∪σ)'-Hall U で成り立つか、K-invariant U
      限定かを確定 (math: 共役不変性を精査; 非自明な transfer があるか)。
- [ ] **忠実なら**: conjunct 4/5-element を K-invariant U about に restate (existential
      `∃ K-invariant U, ...` or hypothesis `U◁UK`) → cross-lane (lane-b/Prop16.1 の cite) signature
      影響を要調整 (hub/ユーザー裁可)。
- [ ] **assembly**: 残 gap = conjunct 4 (K regular on U = Prop 14.2(a) deferred 部分、
      `actsRegularlyOn_E23_E1_of_caseTau1` 経由 E-setup で証明可、K*≠Mσ [issue 8016] と同様の機構) +
      conjunct 7 (element-wise `M⊓C(k)=K⊔Kstar`; typeP_structure (b1) は rank-1 X 用、k∈K# への拡張要)。
- [ ] monolith を assemble (available conjuncts は cite、gap を埋める)。

## 完了条件

`theoremA_maximal_structure` が sorry-free (忠実な statement で)。中間は `theoremA_ungated_conjuncts`
を拡張 (現 4 conjunct → cyclic K / M≤N(UMσ) / A(8) 追加で ~7 conjunct) して available surface を増やす。

## 参照

- issue 8016 (closed): A(8) FittingIsTI axiom-clean = monolith conjunct 8 の供給元。
- `typeP_auxiliary_structure` (S15:1702): conjuncts 2/3-normal/9/M'-structure を供給。
- `theoremA8_structure` (S16:1015, axiom-clean), `theoremA_ungated_conjuncts` (S16:181, sorry-free)。
- `actsRegularlyOn_E23_E1_of_caseTau1` (S14:771): E₁ regular on E₂E₃ (conjunct 4 の E-setup 源)。
- mmd `references/bg/local-analysis.mmd` L4346-4355 (Theorem A statement)。
