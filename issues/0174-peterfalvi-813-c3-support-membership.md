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

- [x] **Type I 版を landing (2026-08-08)**。新規 3 定理、すべて axiom-clean:

      ```
      S10_StructureSetup.mem_typeA_of_mem_hatMsigma_of_typeI    hatMsigma M ∖ {1} ⊆ A(M)
      S10_StructureSetup.typeA_eq_hatMsigma_sdiff_one_of_typeI  A(M) = hatMsigma M ∖ {1}
      S10_MinimalSimpleBasic.escaping_mem_typeA_notMem_A1_of_typeI   ← (8.13)(c3) 本体
      ```

      新しい数学は不要で、**BG Theorem D(4) の第 4 成分を Peterfalvi の語彙へ翻訳する**仕事だった。
      `L` の同定は `maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`
      (`ℳ(C_G(x))` の単元性)、`x ∉ A₁(L)` は `A1_eq_sigmaSharp` 経由。

- [ ] **残: Type II 版**。書籍 (8.13)(c1) をページ画像で確定した (2026-08-08):

      > (c1) `L = L_F ⋊ (M ∩ L)` and `C_G(x) = C_{L_F}(x) ⋊ C_M(x)`.

      これで障害が正確に見える:

      - `x ∈ D ⊆ A₁(M) = M_σ^# ⊆ M` かつ `x ∈ C_G(x) ≤ L` なので **`x ∈ M ∩ L`** —
        つまり `x` は (c1) の**補因子側**に居て `L_F` 側ではない。
      - Type II では `[L,L] = L_F ⋊ U_L` (書籍 (8.12))、一方 `L = L_F ⋊ (M ∩ L)`。
        よって `x ∈ L'` ⟺ `x` の `L/L_F ≅ M ∩ L` での像が `L'/L_F ≅ U_L` に入る。
      - D(4) が与える `x ∈ hatMsigma L` は `x ∈ L` までで、この `U_L` 条件は含まない。

      ⟹ 必要なのは「`M ∩ L` の元で `L_F^#` の元を中心化するものは `U_L` 成分だけ」という主張。

- [x] **経路を特定 (2026-08-08): これは BG 側の作業**。repo の Theorem D(4) は第 4 成分を
      **`x ∈ ASet N ⊤ ∖ M_σ(N)`** と記録しているが、`ASet N U = hatMsigma N ∩ (U ⊔ M_σ N)`
      なので `U = ⊤` 版は単に `hatMsigma N` であり、**BG の `A(N)` より弱い**。

      実際 `S10_TypePSupport.typePACore_subset_ASet` が示すとおり、型 `𝒫` の正しい `U₀`
      (matched `(κ∪σ)'`-Hall) では BG Lemma 15.1(b) が `derivedInG N = U₀ ⊔ M_σ N` を与え、
      **`ASet N U₀ = hatMsigma N ∩ N'` = Peterfalvi の `A(N)`** (host `N'`) になる。
      つまり Type II 版に必要なのは

      > Theorem D(4) の第 4 成分を `ASet N ⊤` から **`ASet N U₀`** へ強める

      こと。repo の証明 (`LocalTaxonomy.lean:930`) は `x ∈ N` と `M_σ N ⊓ C_G(x) ≠ ⊥` から
      `⊤` 版を出しており、`x ∈ N'` を出す材料を持っていない。⟹ **BG §16 側の強化が前提**で、
      Peterfalvi 側だけでは閉じない。

      ⚠ repo の D(4) は**主張しているものは証明している** (honest) が、書籍 BG の D(4) より
      弱い可能性がある。BG 原文の D(4) が `A(N)` をどう定義しているかの確認が先。

- [x] **BG 原文で確定 (2026-08-08) — repo の D(4) は BG より弱い**。
      `references/bg/local-analysis.pdftotext.txt`:

      - **Theorem D(4)** (L6532 付近): 「… `R(x) = C_{N_σ}(x)`, `N_σ = N_F`,
        **`x ∈ A(N) − N_σ`**, and `M ∩ N` is a complement of `N_σ` in `N`.」
      - **`A(M)` の定義** (L6852 付近) は Peterfalvi (8.10) と**同一**:

        ```
        Type I        A(M) = A₀(M) = ⋃_{x∈H^#} C_M (x)     ← host M
        Type II       A(M)          = ⋃_{x∈H^#} C_{M'}(x)   ← host M'
        Type III/IV/V A(M)          = (M')^#
        ```

      ⟹ **BG D(4) は型依存の `A(N)` を主張しており、Type II では host が `N'`**。
      repo の `theoremD_msigma_conjugacy_and_centralizers` が記録する
      `x ∈ ASet N ⊤ ∖ M_σ(N)` = `hatMsigma N ∖ M_σ(N)` は host が `N` で、
      **Type II においてのみ BG より弱い** (Type I では一致 — 前 commit で landing 済)。

      ⟹ **これは Peterfalvi 側の債務ではなく BG 側の弱化**。repo の D(4) は主張しているものは
      証明している (honest) が、BG 原文の条項を完全には運んでいない。

- [ ] **次の作業 (BG レーン)**: `LocalTaxonomy.lean:930` の D(4) 第 4 成分を
      `ASet N ⊤` から **型依存の `A(N)`** (Type II なら `ASet N U₀`、`U₀` = matched
      `(κ∪σ)'`-Hall) へ強める。

      **BG 側の証明鎖を特定済 (2026-08-08)**。BG は Theorem D に schematic proof しか付けない
      (mmd L4455):

      > Theorem D — Corollary 15.3(b) → (1) / Lemma 12.17 → (2) /
      > **Theorem 14.4(b), Theorem A(8), Corollary 15.9 → (3)(4)**

      **Corollary 15.9** (mmd L4313、Feit-Thompson 1991 + Sibley の未公刊部分) の証明が
      `x ∈ N'` に必要な構造を出す:

      - `{N} = ℳ(C_G(x))`、`N ∈ ℳ_{𝒫₂}`、`r ∈ τ₂(N) ∩ σ(M)`、`M ∩ N` は `N_σ` の補元 (15.3)
      - `K₁` = `M ∩ N` の `κ(N)`-Hall で **`\|K₁\|` は素数**、`M ∩ N = K₁ ⋉ U₁` で `U₁` は
        可換正規補元、`C_{U₁}(K₁) = 1` (Prop 14.2(g),(a))
      - `R` (`M∩N` の Sylow `r`) について **`R ⊆ U₁`** かつ `N_G(R) ⊆ M` (Cor 12.10(d))
      - `K₁ ∩ M_σ = 1` (`K₁R` が非冪零ゆえ)

      ⟹ `x ∈ M_σ ∩ (M∩N)` が `U₁` に入ること (= `x ∈ N'`) を、この鎖から出すのが本体。
      **repo 側の在庫を実測 (2026-08-08)** — 前提はすべて在るが Cor 15.9 は一部だけ:

      | BG | repo |
      |---|---|
      | Proposition 14.2 | `BG/Ch3_MaximalSubgroups/S14_Prop142Support.lean` ✅ |
      | Corollary 12.10 | `BG/Ch3_MaximalSubgroups/S12_E.lean` ✅ |
      | Theorem 15.7 | `S15_MF/OpicoreCentralizer.lean` / `S16_MainResults/FittingNonTITrichotomy.lean` ✅ |
      | Theorem 15.8 | `S15_MF/OpicoreCentralizer.lean` ✅ |
      | **Corollary 15.9** | `S15_MF/TIFailure.lean:1131` — ⚠ **一部のみ** (`not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le` = 「`F(M)` は TI でない」ステップだけ)。**(15.3) の `M ∩ N` 補元性 / (15.4) の `M∩N = K₁ ⋉ U₁`, `C_{U₁}(K₁)=1` / `R ⊆ U₁` は無い** |

      ⟹ 素朴には「Cor 15.9 の構造部分 ((15.3)+(15.4)+`R ⊆ U₁`) を新規に形式化」だが、

- [x] **より軽い経路を発見 (2026-08-08)** — 商の位数による整除性だけで済む:

      D(4) の第 6 成分が既に **`M ∩ N` は `N_σ` の `N` における補元**を与える
      (`Subgroup.IsComplement' ((M ⊓ N).subgroupOf N) ((Msigma N).subgroupOf N)`)。
      Type II (= `𝒫₂`) では BG Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian`) が
      `N' = U_N ⊔ N_σ` を与え、`U_N` は `M ∩ N` の `κ(N)'`-部分。したがって

      ```
      N / N' ≅ K₁ = (M ∩ N) の κ(N)-Hall     (Prop 14.2(g) より **素数位数** k)
      ```

      一方 `x ∈ M_σ^#` は **`σ(M)`-元**なので `|x|` は `σ(M)`-数。⟹

      > **`k ∉ σ(M)` なら `gcd(|x|, |N/N'|) = 1` となり、`x` の `N/N'` での像は自明 = `x ∈ N'`**

      つまり必要なのは **`κ(N) ∩ σ(M) = ∅` 型の 1 本**だけで、(15.4) の
      `M∩N = K₁ ⋉ U₁` / `C_{U₁}(K₁) = 1` / `R ⊆ U₁` を全部作る必要はない。
      Peterfalvi (8.13)(c2) が同型の coprimality (`coprime_FT_signalizer_centralizerIn_typeA`)
      を既に持つので、そこから引ける可能性が高い。

- [x] **鎖を最小形まで詰めた (2026-08-08)**。`κ(N) ∩ σ(M) = ∅` は**不要**だった
      (実際 BG Cor 15.9 は `r ∈ τ₂(N) ∩ σ(M)` を使うので両者は交わりうる)。正しい鎖は:

      ```
      |K₁| 素数 (= k)                        BG Prop 14.2(g)
      K₁ ⊄ M_σ                              BG Cor 15.9 の (15.2) 経由 (K₁R が非冪零)
        ⟹ K₁ ∩ M_σ = 1                      (|K₁| 素数ゆえ)
        ⟹ M_σ ⊴ M なので M_σ ∩ K₁^g = 1 (∀g)
      x ∈ M_σ の k-部分 ∈ M_σ ∩ (M∩N の Sylow k) ⊆ M_σ ∩ K₁^g = 1
        ⟹ k ∤ |x|
        ⟹ x の N/N' ≅ K₁ (位数 k) での像は自明
        ⟹ x ∈ N'
      ```

      ⟹ **新規に要るのは `K₁ ∩ M_σ = 1` の 1 本だけ**。`|K₁|` 素数は Prop 14.2(g) から、
      `K₁ ⊄ M_σ` は (15.2) から。あとは群論の定型 (正規部分群の元の素数部分・商の位数との互素性)。

- [ ] **次の作業**: (i) repo の `S14_Prop142Support` から `|K₁|` 素数を取り出す。
      (ii) (15.2) (`K₁R` 非冪零) の repo 版を探す/証明して `K₁ ∩ M_σ = 1` を出す。
      (iii) 上の定型で `x ∈ N'` を締める。
      (iv) D(4) 第 4 成分を型依存の `A(N)` へ強め、(8.13)(c3) Type II を Type I と同じ形で出す。
- [ ] 組み立て: `escapingCentralizers_control` と同じ入口
      (`mem_sigmaSharp_of_mem_aSet_of_escape` / `A1_eq_sigmaSharp` で `x ∈ sigmaSharp M`)
      → D(4) → 第 3/4/5 成分 → 結論。`L` の同定は
      `existsUnique_maximal_centralizer_le_typeI_or_typeII` の一意性で行う。
- [ ] AxiomsCheck に登録 + census note §8 表を更新

## 完了条件

**Type I は 2026-08-08 に達成済**。残るは Type II。型一律の形 (任意の Peterfalvi 型の `M`、`X = A(M)` または `A₀(M)`) で

```
x ∈ D → C_G(x) ≤ L → L ∈ maximalSubgroups G →
  x ∈ typeA L tauL ∧ x ∉ A1 L tauL
```

が証明され、AxiomsCheck に登録される。census note の §8 表を更新して §8 監査を完了にする。

## 参照

- 監査記録: [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の §8 節
- 書籍: `references/peterfalvi/pages/peterfalvi-p047.png` ((8.13) 全文)
- Coq 併読: `coq/theories/PFsection8.v`
