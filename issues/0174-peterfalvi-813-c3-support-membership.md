---
id: 174
slug: peterfalvi-813-c3-support-membership
title: "Peterfalvi (8.13)(c3): 支持極大 L について x ∈ A(L) − A₁(L)"
created: 2026-08-07
---

# Peterfalvi (8.13)(c3): 支持極大 L について x ∈ A(L) − A₁(L)

## 背景

[issue 0172](0172-peterfalvi-full-formalization.md) ステップ 3 の §8 逐条監査 (2026-08-07) で、
**§8 で唯一未形式化の sub-clause** として検出した。

書籍 (8.13) (p.47) は、極大部分群 `M`、`X = A(M)` または `A₀(M)`、
`D = {x ∈ X | C_G(x) ⊄ M}` に対して:

- (a) `X` の 2 元が `G` 共役なら `M` 共役 — repo: 台別に 3 形 (`S10_MinimalSimpleBasic:560,593,731`)
- (b) `D ⊆ A₁(M)`、`x ∈ D` なら `C_G(x)` は一意の極大部分群に含まれる — repo:
  `S10.escapingCentralizers_control` + 型一律 `escaping_typeA_mem_A1`
- (c) `x ∈ D` と `C_G(x) ⊆ L` なる極大 `L` について:
  - (c1) `L = L_F ⋊ (M ∩ L)` かつ `C_G(x) = C_{L_F}(x) ⋊ C_M(x)` — repo: 同 control 内
  - **(c2)** `\|L_F\|` は全ての `y ∈ X` について `\|C_M(y)\|` と互いに素 — repo:
    `coprime_FT_signalizer_centralizerIn_typeA` (型一律)
  - **(c3)** `x ∈ A(L) − A₁(L)` ← **これが未形式化**
  - (c4) `L` は Type I か II。さらに `L` が Type II なら `M` は核 `M_F` の Frobenius 群 — repo:
    前半 = `escapingCentralizers_control`、後半 = BG Theorem II packaging
    (`S16_MainResults/TamelyImbedded.lean:141` / `TheoremIIPackaging.lean:393`
    = `FrobeniusTypeIWithNonTIFitting M`)

⚠ **repo が (8.18)(a) を別ルートで証明しているので、(c3) は現在どこからも要求されていない** —
書籍は (8.18)(a) を「(8.13.b,c3) より」と導くが、repo の型一律版
`S10_MinimalSimpleStructure.escaping_supported_of_A1_conj_mem_typeA` は
σ-disjointness (`sigma_disjoint_of_nonconjugate`) + (8.12.b) 一意性
(`centralizer_unique_of_mem_typeA`) で直接証明している。よって **consumer 0 だが書籍強度の
被覆としては欠けている** 項目 (CLAUDE.md: consumer 0 は deprioritize の理由にならない)。

## やること

- [ ] 書籍 p.47 の (8.13) の Reference ([BG] §16 Theorem II, Theorem B(5), Theorem D(4)) のうち
      **Theorem D(4)** の rich predicate `Q` (repo: `theoremD_msigma_conjugacy_and_centralizers`
      の第 4 成分、`TaxonomyOutput.lean:452` で 6 成分に分解している) を読み、
      `x ∈ A(N₀) − A₁(N₀)` に相当する成分が既に在るか確認する
- [ ] 在れば Peterfalvi 側の statement (`x ∈ typeA L tauL ∧ x ∉ A1 L tauL`) として取り出す
- [ ] 無ければ BG 側で何を足す必要があるか特定する (signalizer `R(x) = C_{L_F}(x) ≠ 1` から
      `x ∈ C_{L'}(y)^#` for some `y ∈ L_s^#` を得る経路が自然)

## 完了条件

型一律の形 (任意の Peterfalvi 型の `M`、`X = A(M)` または `A₀(M)`) で

```
x ∈ D → C_G(x) ≤ L → L ∈ maximalSubgroups G →
  x ∈ typeA L tauL ∧ x ∉ A1 L tauL
```

が証明され、AxiomsCheck に登録される。census note の §8 表を更新して §8 監査を完了にする。

## 参照

- 監査記録: [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の §8 節
- 書籍: `references/peterfalvi/pages/peterfalvi-p047.png` ((8.13) 全文)
- Coq 併読: `coq/theories/PFsection8.v`
