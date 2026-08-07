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

- [x] **Theorem D(4) の rich predicate を確認 (2026-08-08) — 該当成分は既に在る**。
      `TheoremsAE.theoremD_msigma_conjugacy_and_centralizers` の第 4 連言 (`hD4`) が返す
      `∃! N` の述語は 6 成分で、その **第 4 成分がまさに**

      ```
      x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G)
      ```

      = 書籍の `x ∈ A(N) − M_σ(N)`。`A₁` 側の橋も既存:
      **`BG.Ch4.S16.A1_eq_sigmaSharp hG hM htau : A1 M tau = sigmaSharp M`**
      (`sigmaSharp M = (Msigma M)^#`)。したがって
      `x ∉ Msigma N` ⟹ `x ∉ sigmaSharp N` ⟹ `x ∉ A1 N tauN` が直に出る。

      さらに D(4) の第 3 成分 `S15.MF N = Msigma N` と第 5 成分
      `S14.IsTypeF N ∨ S14.IsTypeP2 N` (→ Prop 16.1 で Type I/II) が
      `mainSubgroup N tauN = maxNilpotentNormalHall N = Msigma N` を保証するので、
      `A1_eq_sigmaSharp` の適用条件も揃う。

- [x] **`x ∈ ASet N ⊤` → `x ∈ typeA N tauN` の橋を解析 (2026-08-08)**。書籍 (8.10) (p.47) の
      定義をページ画像で確定した:

      ```
      M_s = H (= M_F)  if Type I, II, V ;  M'  if Type III, IV
      A₁(M) = M_s^#
      Type I : A(M) = A₀(M) = ⋃_{x ∈ H^#} C_M (x)^#     ← host は M
      type 𝒫 : A(M)          = ⋃_{x ∈ M_s^#} C_{M'}(x)^#  ← host は M'
      ```

      repo の `mainSubgroup` / `supportHost` はこれと**完全一致**している (定義の突合は OK)。

      **Type I は完全に閉じる**: `Msigma N = MF N = H` かつ host が `N` なので
      `hatMsigma N = {a ∈ N | ∃ y ∈ H^#, a ∈ C_G(y)}` と
      `A(N) = {a ∈ N | a ≠ 1 ∧ ∃ y ∈ H^#, a ∈ C_N(y)}` は
      **`A(N) = hatMsigma N ∖ {1}`** で一致する (`a ∈ N` なので `C_N(y) = C_G(y) ∩ N` の差は消える)。
      `a ≠ 1` は D(4) 第 4 成分の `x ∉ Msigma N` から出る (`1 ∈ Msigma N`)。

      ⚠ **Type II にはギャップがある**: host が `N'` なので `x ∈ N'` が別途要る。
      D(4) が返すのは `x ∈ ASet N ⊤ = hatMsigma N` (host は `N`) までで、`x ∈ N'` は含まない。
      `[N,N] = H ⋊ U` (書籍 (8.12)) から `H ≤ N'` は出るが、「`H^#` の元を中心化する `x ∈ N`」が
      `N'` に入る理由は自明でない。

- [ ] **次の作業**: (i) Type I 版を先に landing させる (完全に閉じているので即書ける)。
      (ii) Type II 版の `x ∈ N'` をどこから取るか特定する — 候補は BG Theorem B(5)
      (`A(M) − M_σ` の TI 性) か、書籍 (8.13)(c1) の `C_G(x) = C_{L_F}(x) ⋊ C_M(x)` 分解。
- [ ] 組み立て: `escapingCentralizers_control` と同じ入口
      (`mem_sigmaSharp_of_mem_aSet_of_escape` / `A1_eq_sigmaSharp` で `x ∈ sigmaSharp M`)
      → D(4) → 第 3/4/5 成分 → 結論。`L` の同定は
      `existsUnique_maximal_centralizer_le_typeI_or_typeII` の一意性で行う。
- [ ] AxiomsCheck に登録 + census note §8 表を更新

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
