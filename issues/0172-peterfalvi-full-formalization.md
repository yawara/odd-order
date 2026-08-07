---
id: 172
slug: peterfalvi-full-formalization
title: "Peterfalvi 完全形式化キャンペーン (次フロンティア)"
created: 2026-08-07
---

# Peterfalvi 完全形式化キャンペーン

**ユーザー裁定 2026-08-07**: Q₈ Brauer–Suzuki 完了 (repo 全体 sorry 0) を受け、
**Peterfalvi *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) の完全形式化を
次のフロンティアに定める**。

⚠ **sorry 0 は「完了」ではない** — 未形式化の番号付き結果は `sorry` を生まない。本キャンペーンは
`sorry` カウントでなく**書籍の番号付き結果を書籍強度で被覆したか**で測る (CLAUDE.md「進捗の測り方」)。

## 実測ベースライン (2026-08-07)

正本 = [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md)。
⚠ 2026-07-16 の 3 冊 survey は**使わない** (降格済 + 3 週間分 stale)。

### Part I (§1–§16 = 書籍 result 番号 (1.x)–(14.x))

書籍テキストから番号を機械抽出 (各章 1..max が**欠番なし**で連続) → **全 169 件**。
repo の docstring cite と突合:

| 層 | 件数 | 内容 |
|---|---|---|
| cite あり | **169 / 169** | 番号または sub-part `(N.M.x)` 形で repo に出現 |
| **cite ゼロ** | **0** | (8.9) は 2026-08-07 に形式化済 (下記ステップ 1) |

### Part II (Suzuki の定理 A) / 補章

Part II は `Proposition N` / `Lemma N` の**章内リセット番号**で、Part I と同じ機械 census が
効かない。補章 (Huppert / Near-Fields / Suzuki 2-Groups / Feit–Sibley) も同様。
**census 第 2 弾として別途実施する** (下記ステップ 2)。

## ⚠ この census が測っていないもの

「cite あり」= **その番号が docstring に現れる**であって、**書籍強度の statement が存在する**
ことではない。実際の残債は次の 3 種で、いずれも番号 grep では検出できない:

1. **特殊化債務** — 書籍より狭い仮説で述べている (2026-07-16 時点で Pf に 26 件と記録)。
2. **部分被覆** — (a)(b)(c) のうち一部だけ形式化、bundled statement が条項を運搬していない
   (実例: BG 15.7 の (b)(e) が `∃ X` decoupling で準恒真だった = issue 3022)。
3. **言及のみ** — 「(8.5) は §14 で使う」のような散文 cite で、statement が無い。

⟹ **本キャンペーンの本体は「番号を埋める」ことでなく、1 件ずつ statement を書籍と逐条照合する
監査**。上流優先 + 文書順 (CLAUDE.md) で (1.1) から順に当たる。

## 作業手順

- **ステップ 1 ✅ 完了 (2026-08-07、commit `39bfc2831`)**: **(8.9)** — 唯一の cite ゼロ。
  `OddOrder/Peterfalvi/S10_Theorem88CaseB.lean` に形式化 (axiom-clean):
  `Theorem88CaseBData.derivedInG_inf_centralizer_W1_eq` (内在形 `C_{S'}(W₁) = W₂`) と
  `Theorem88CaseBData.typePData_W2_eq` (書籍そのままの形)。証明は書籍 pp.46-47 を逐条で追う。

  **副産物 — (8.8.b) の条項欠落を発見・補充**: `Theorem88CaseBData` (旧 `S12_MaximalIII_IV_V`)
  は (b1) の半分と (b2)(b3) しか持たず、(8.9) が要求する (8.4.e)・`S ∩ T = W`・直積性・
  非自明性・(b4) を**欠いていた**。書籍 p.46 と逐条照合して 6 フィールドを追加し、生産側
  2 箇所 (`S14.theorem88_dichotomy` / `FeitThompsonSection16Core`) を実データで充足した
  (仮説への hoist ではない)。これは §2「部分被覆 — bundled statement が条項を運搬していない」
  の実例で、**番号 grep では検出できなかった**。以降の逐条監査で同型を探すこと。

  書籍 p.46:
  > Suppose that case (b) of Theorem (8.8) holds. Then the group denoted by `W₂` in Theorem (8.8)
  > coincides with the group denoted by `W₂` in (8.4.d) with `M = S`.

  証明 (書籍 pp.46–47): `W₂ ⊆ W ⊆ S`、`W` cyclic ゆえ `|W₁|` と `|W₂|` は互いに素 ⟹ `W₂ ⊆ S'`。
  よって `W₂ ⊆ C_{S'}(W₁)`。(8.4.d) を `M = S` に適用して `W₁C_{S'}(W₁)` は可換 ⟹
  `C_{S'}(W₁) ⊆ C(W)`。`W` は (8.4.e) を満たすので `C_{S'}(W₁) ⊆ W`、ゆえに `C_{S'}(W₁) = W₂`。

  Coq 対応 = **`typeP_pairW`** (`coq/theories/PFsection8.v:466`、`of_typeP` 述語で述べる形)。
  (8.8)+(8.9) の合成 `FTtypeP_pair_witness` が同ファイル :712 にある。

- **ステップ 2 ✅ 完了 (2026-08-08)**: Part II + 補章の census。書籍テキストを節境界つきで
  走査し **全 115 件**を列挙 (Part II Introduction 1 / Ch.I 19 / Ch.II 18 / Ch.III 16 /
  Ch.IV 41 / App.I-IV 16)。**cite ゼロは無し** (Part I の 169/169 と同じ状況)。
  - Part II は Part I と番号体系がまったく違う: (1) 章をまたぐ固有名 Theorem A/B/C、
    (2) **節ごとにリセット**する `Proposition N`/`Lemma N` + 無番号の `Proposition.`/`Lemma.`/
    `Corollary.`、(3) 証明内の連番ステップ `(N)` (書籍が本文から参照するので実質的に結果)。
    ⟹ Part I の機械 census (番号 grep) は原理的に効かない。
  - ⚠ 初回の機械 census は **11 件を偽の「cite ゼロ」と誤判定**した (すべて repo の引用表記の差)。
    対応表を census note §4.2 に残した。
  - **補章ラベルの不統一を是正**: repo が BG の補章 letter (`Appendix B`/`C`/`E`) を Peterfalvi
    側に流用しており grep が混線していた → 書籍どおり `Appendix I`/`II`/`IV` へ統一。
  - **ページ画像を全ページ揃えた** (pp.97-114 / 135-143 を追加 → pp.5-92 / 97-150 が完備)。
- **ステップ 4 (Part II 逐条監査)** — 上流優先 + 文書順で進行中。
  - **Ch.I §1 監査完了 (2026-08-08)**: 7 件 (Prop 1-6 + 無番号 Lemma) 全件に書籍強度の実体。
    **補充 2 件**:
    - **Prop 4(c) の特殊化債務** — 書籍の §1 は **(A1) だけ**を仮定する (p.100) のに repo の
      `Hypothesis` は (A1)+(A2)+(A3) を束ねていたため、`N = ⋂_x H^x = C_D(Q) ⊆ C_D(t)` 等が
      **(A2) の下で `N = 1` により恒真**に潰れていた。書籍は §3 Prop 1(a)/1(c) の証明で
      **(A1) のみの一般形**を 2 度使う (`L = C_G(X)` の `Ω_X` 上の作用は一般に非忠実) ため、
      repo は §3 で同じ内容を独立に再証明していた。`Hypothesis extends HypothesisA1` に変更し
      §1 全体を `HypothesisA1` へ移送、5 条項を一般形で証明 (すべて axiom-clean)。
      ⚠ (A2)/(A3) の実使用は §1 全体で 2 箇所だけだったので**証明本体は無変更**で済んだ。
    - **Lemma (a) の第 2 全単射** — 書籍は `(y,z) ↦ yz` と `(y,z) ↦ zy` の**両方**が全単射と
      主張するが repo は前者だけ。§3 Prop 1(b) が回り道をしていた → `invertedProdEquiv'` を追加。
  - **Ch.I §2 監査完了 (2026-08-08、補充ゼロ)**: 4 件 (Prop 1(a)-(c) / Prop 2 / Corollary /
    Prop 3) すべてに書籍強度の実体。Prop 3 は `semilinearGroup F A = (F₊ ⋊ Fˣ) ⋊ A` が書籍の
    `𝓛(F,A)` そのもので、3 つの同定と "In particular `V/W` is cyclic" まで揃う。
    ⚠ census の件数を **111 → 110** に訂正 (§2 の `Lemma` 3 箇所は**§1 の Lemma への参照**で
    そこに新 statement は無い — ページ画像で確認)。
  - **Ch.I §3 監査完了 (2026-08-08、補充ゼロ)**: 7 件 (Lemma 1 / Prop 1(a)(b)(c) / Prop 2 /
    Lemma 2-5) すべてに書籍強度の実体。複数条項の結果はいずれも**束ねた形**で在る
    (Lemma 1 = `TheoremAConclusion.Q_and_residual` / Lemma 3 =
    `stronglyReal_normalForm_and_centralizer_odd` / Lemma 5 = `lemmaFive_of_orderThree`)。
    §1 Prop 4(c) の一般形は Prop 1(a) の `normalCore_cH_*` が消費する形で実在。
  - **Ch.II 監査完了 (2026-08-08、補充 1 件)**: 18 件 ((B1)(B2) + Theorem B + step (1)-(17))。
    **補充 = step (11) の第 3 条項 `T ⋊ C_Q(P) ≅ F ⋊ F*`** — 書籍 p.111 は 4 条項を主張するが
    repo は半直積同型だけ `StepEleven.lean` の file docstring に散文で書かれているだけで
    定理が無かった (census note §2 の失敗様式 3 =「言及のみ」の実例)。新 leaf
    `FirstCase/StepElevenSemidirect.lean` で `fieldCoord`/`sInvertedTEquivField`/
    `fieldCoord_conj` を証明 (全て axiom-clean)。
    清掃: `char_eq_p` の「model の sorry を継承するので未登録」注記が stale → 訂正 + 登録。
    stale docstring 2 件 (`StepElevenComplement` の「in subsequent commits」等) も訂正。
    ⚠ ページ画像が必須だった — pdftotext は (4)(6)(8)(10) の式を壊す
    (`|Q| = |C_Q(P)|^p = |F*|^p` が `|0| = |Cg(P)|'= |Fr-`)。
  - **Ch.III 監査完了 (2026-08-08、補充ゼロ)**: 16 件。Theorem C は書籍そのままの形
    (`isPGroup_two_Q`)、§1 Proposition は 3 分岐を束ねた `WNeBot.trichotomy` (書籍より強く
    case (b)(c) に位数情報も付く)、§2 Proposition は `typeASubgroup` を `Subgroup G` として
    構成 (=「部分群である」の内容そのもの)、§3 Proposition は `exists_standardModel` が
    書籍の全条項 (φ の双加法性・scaling 則・anisotropy・`K₁W₁` の作用) を持つ。
  - **Ch.IV 監査完了 (2026-08-08、補充ゼロ)**: **46 件** (§1 = 7 / §2 = 21 / §3 = 8 / §4 = 10)。
    §1 の (H1)-(H6) は `GroupTheory/RankOneBNPair.lean`、§1 Lemma は `RankOneBNPairRigidity`、
    §3 Corollary 1 (`O^{2'}(G) ≅ PSU(3,q)`) は `exists_mulEquiv_standardPermGroup` +
    `TheoremAConclusion` インスタンス。
    ⚠ **(H3)/(H4)/(H6) の指数は `a^t`/`a^{-t}`/`h(y)^t`** で `a^{-1}` 等ではない —
    pdftotext は完全に潰すのでページ画像を拡大クロップして確定した (repo 側は元から正しい)。
    ⚠ **§4 のステップは (1)-(10)** — 素の `^\(N\)` grep が表示式内の (6)-(9) を取りこぼして
    いた。census を Ch.IV 41 → 46、総数 110 → **115** に訂正。
  - ⟹ **Part II 本体 (Ch.I-IV) の逐条監査完了**。補充は通算 3 件
    (Ch.I §1 の Prop 4(c) 一般形 / Ch.I §1 Lemma (a) の第 2 全単射 / Ch.II step (11) の半直積同型)。
  - **補章 4 本 監査完了 (2026-08-08、補充 1 件)**: 16 件 (App.I = 3 / II = 2 / III = 8 / IV = 3)。
    **補充 = App.I Prop 1 の `[IsSolvable D]` 削除** — 書籍は「odd order」しか仮定しないが
    repo は可解性も要求していた。奇数位数 ⟹ 可解は **本リポジトリが証明済の Feit–Thompson**
    なので `feitThompson` を内部で使い仮説を書籍どおりに戻した (import cycle なし)。
    これは Part I の失敗様式リストに無かった型 (**失敗様式 7 = 書籍が暗黙にしている定理を
    repo が仮説で受ける**) で census note に記録。
    stale docstring 訂正 1 件 (App.III hub の「Theorem (e) forward direction」— 逆向きも実在)。

- **⟹ ステップ 4 (Part II 逐条監査) 完了 (2026-08-08)**。Part II 全 115 件
  (Theorem A + Ch.I 19 + Ch.II 18 + Ch.III 16 + Ch.IV 46 + 補章 16) に書籍強度の実体あり、
  **未形式化ゼロ**。**補充は通算 4 件**:
  1. Ch.I §1 Prop 4(c) の (A1)-only 一般形 (`Hypothesis extends HypothesisA1` へ再編)
  2. Ch.I §1 Lemma (a) の第 2 全単射 `(y,z) ↦ zy` (`invertedProdEquiv'`)
  3. Ch.II step (11) の `T ⋊ C_Q(P) ≅ F ⋊ F*` (新 leaf `StepElevenSemidirect.lean`)
  4. App.I Prop 1 の `[IsSolvable D]` 削除 (Feit–Thompson で discharge)
  すべて axiom-clean。**新たに見つけた失敗様式 2 型** (7 = 書籍が暗黙にする定理を仮説で受ける /
  8 = file docstring の散文が定理の代わりをしている) を census note §4.6 に記録。

- **次の入口 = 残件の消化 (上流優先 + 文書順)**:
  1. ~~**(1.7)(b)**~~ — **2026-08-08 に「未形式化」判定を撤回**。実体は
     `RepresentationTheory/InducedInvariantConstituent.lean` に landing 済で書籍の 3 条項を
     すべて持つ (`induce_smul_eq_sum_induce_mul_of_invariant_inertia` /
     `card_induce_constituents_eq_index_div_sq_of_invariant` /
     `induce_invariant_constituent_apply_one_eq`)。docstring が `(1.7.b)` と書いており
     `(1.7)(b)` の番号 grep が 0 hit だったのが誤判定の原因。6 定理を AxiomsCheck に登録
     (全て axiom-clean)。⟹ **Part I の未形式化もゼロ**。
  2. [issue 0174](0174-peterfalvi-813-c3-support-membership.md) — (8.13)(c3)。
     **Type I は 2026-08-08 に landing** (`escaping_mem_typeA_notMem_A1_of_typeI`、axiom-clean)。
     **Type II は BG 側の作業**と判明: Theorem D(4) の第 4 成分 `x ∈ ASet N ⊤` を
     `ASet N U₀` (正しい `(κ∪σ)'`-Hall) へ強める必要がある。Peterfalvi 側だけでは閉じない。
  3. [issue 0175](0175-pf-911-section9-casea-descent.md) — (9.11) の type-free 化。
     **2026-08-08 に依存を実測して scope を再評価**: `hnoV` の使用は 1 箇所だが、型固有の
     実体は §15 補題 9 本で、§9 counterpart が在るのは 1 本のみ。「4 箇所を差し替える」ではなく
     **~520 行の証明の移植 (複数 session 規模)**。
  4. 低優先繰延 2 件: (3.8) の packaging 差 / (5.6) の書籍仮説 (b)(c) ⟹ 分解存在 の橋渡し

## 現況サマリ (2026-08-08)

| 層 | 状態 |
|---|---|
| Part I (169 件) | **逐条監査完了・未形式化ゼロ** ((1.7)(b) の誤判定は 2026-08-08 に撤回) |
| Part II (115 件) | **逐条監査完了・未形式化ゼロ**、補充 4 件すべて landing |
| 条件付き 2 件 | (8.13)(c3) Type II = **BG 側前提** / (9.11) type-free = **複数 session の移植** |
| 低優先繰延 | (3.8) packaging / (5.6) 橋渡し |

⟹ **Peterfalvi 全 284 件の番号付き結果に書籍強度の実体があり、未形式化はゼロ**。
残るのは「条件付き 2 件の仮説解消」と「低優先繰延 2 件」のみ。
- **ステップ 3 ✅ 完了 (2026-08-08)**: Part I (§1-§14) の逐条監査を (1.1) から文書順に完了。1 章ぶん終えるごとに census note を更新した。
  - **2026-08-07 時点: §1-§6 完了 (全 63 件)**。
    正本 = [census note](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の各表。
  - **§6 の補充 3 件 (2026-08-07)**:
    - **(6.7) の第 1 結論 `ψ(z) ∈ ℤ`** — 書籍 p.32 の結論は 2 つだが repo は合同側のみで、整数性は
      「consumer が別途知っている」と file docstring が自認していた。
      `RepresentationTheory.exists_int_character_of_constant_on_nonidentity` を追加
      (`Z^#` 上定数 ⟹ `ψ(z)` は有理数 ⟹ 代数的整数ゆえ整数; TI/Sylow/奇数位数を使わない)。
      併せて `peterfalvi_67_int_dvd_of_odd` (両結論 + ℤ 整除形) と `int_dvd_of_cong_intCast`。
    - **(6.8)(b) の `τ = Ind_L^G`** — 書籍は「`τ` は `Ind_L^G` の `ℤ[𝒮,L^#]` への制限」だが repo の
      `tau` は §4 Dade 写像だった。`SibleyDadeHypothesis.tau_apply_eq_induce` で同定
      (TI ⟹ 局所部分群自明 ⟹ 同じ点ごとの規則; §15 (13.2.e) の §8 版)。
    - **(6.8)(b) の格子** — `CoherenceTarget` の `A` が `H^#` で書籍は `L^#`。
      `zSupportedSpan_ne_one_eq_sharp` (`Ind_H^L θ` は正規 `H` の外で消える) +
      `CoherenceTarget.toBookForm` で capstone を書籍形へ移送。
  - **stale 注記の訂正 2 件**: `six_three_of_imageData` の「repo は `H` 冪零を取る」(issue 0173 で
    解消済) と `six_two_of_imageData` の `B < K` の誤った正当化 (実際は**書籍 statement の修理**;
    `B = K` では書籍 (6.2) は偽)。
  - **§1-§9 監査完了 (2026-08-07)**。未形式化/条件付きは **3 件のみ**:
    1. ~~**(1.7)(b)**~~ — **2026-08-08 撤回: 形式化済** (`InducedInvariantConstituent.lean`)
    2. **(8.13)(c3)** — `x ∈ A(L) − A₁(L)` → [issue 0174](0174-peterfalvi-813-c3-support-membership.md)
    3. **(9.11) の type-free 化** — types III/IV は閉、type II 込みの版は case (a) の 2 仮説が残る
       → [issue 0175](0175-pf-911-section9-casea-descent.md) (descent 作業、未解決数学ではない)
  - **§6 の補充 3 件・§8 の補充 1 件は landed** (下記)。**次の入口 = §10 (書籍 pp.58-63、repo `S12`)**
    — census note に下調べ (cite 密度・監査手順) を記録済。
  - **§7 監査完了 (2026-08-07)**: 全 11 件 ((7.1)-(7.11)) で未形式化ゼロ・補充ゼロ。
    carrier の「証明書 field」((7.7.a)/(7.8.c.i)/(7.8.a)/(7.8.b)) は 4 つとも producer が
    discharge 済 (`hypothesis76OfFamily` / `hypothesis78OfDade` / `betaDecompOfFacts` /
    `normEstimates_of_source_orthogonal`)。(7.1) の `IsDadeIsometry` も書籍 (2.6) =
    `S04.Hypothesis.fullDadeIsometryData` が (2.2) だけから構成するので導出可能。
  - **§8 監査完了 (2026-08-07)**: 18 件中 17 件被覆。補充 = `S12.typeII_centralizer_le_of_mem_A0`
    ((8.13) の `X` 範囲を type II で完成 — (8.16) より escaping set が空になる退化)。
    型定義 ((8.1)(8.3)(8.4)(8.6)(8.7)) は条項一致で、3 つの設計差 (Hall 条項が field でない /
    `fitting_eq` が (8.5)(a) 形 / (8.6.a) の TI が `M_F^#` 版) はいずれも別途定理で被覆済。
    ⚠ `S10_StructureSetup:910` の「(8.16) RETIRED (false-as-stated)」注記は **`A(M) = (M')^#` と
    誤読した版**についてのもの — 書籍の (8.16) は type II の honest な `A(S)` で成立し証明済。
  - **§9 監査完了 (2026-08-07)**: 11 件 + sub-part 8 件。(9.1) の指数 `|E|`・(9.8)(b) の
    `μ_j ∈ 𝒮(H₀C)` はいずれも pdftotext が壊す箇所で、ページ画像で確定した。
  - **§10 監査完了 (2026-08-07)**: 15 件 ((10.1)-(10.11) + (10.10.1)-(10.10.4)) すべてに
    書籍強度の実体あり。**補充 2 件**:
    - **(10.9) を書籍の形へ** — repo は直交条項だけ (`residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2`、
      (11.9.b) 消費側の形) と **coherence を仮定した**特殊化 (`orthogonality_of_w1_lt_w2`) しか持たず、
      書籍の `χ ∈ ℤ[Irr G]` と `‖χ‖² = 1` が statement に無かった。
      `S12.exists_residual_of_w1_lt_w2` を新設 (Hypothesis (10.1) のみ、axiom-clean)。
    - **(10.10.2) の `|𝒮₁|`** — statement は `8 ≤ |𝒮₁|` だけで、書籍の `|𝒮₁| = (p²−1)/w₁` は
      証明内部に埋もれていた。`w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube` (`w₁·|𝒮₁|+1 = p²`) と
      `SHCcount_eq_of_card_eq_prime_cube` (`|𝒮₁| = 4(w₁−1)`) を新設、`eight_le_…` はその系に。
    清掃 2 件: `CharacterParameters` の未消費 opaque `Prop` フィールド 2 本を削除 /
    `tau_muColumnZero_sub_zeta_eq` の「(10.6)(b)」誤ラベルを (10.6)(a) 第 2 文へ訂正。
    設計差 2 件 (いずれも被覆済): (10.1) の「(5.2) も成立」は独立 carrier でなく Dade datum 経由 /
    (10.7) は `TypesIIIIIIVSetup` を受けるが `maximal + IsTypeII` から構成可能。
  - **§11 監査完了 (2026-08-07)**: 15 件 ((11.1)-(11.9) + (11.8.1)-(11.8.6)) すべてに実体あり。
    **補充 = 無条件化 6 件**: 書籍は (11.4)-(11.9) を Hypothesis (11.2) だけの下で述べるが、repo は
    **(11.3) の非coherence `hnc` をパラメータで受けた形**しか持たなかった (無条件の (11.3)
    `S_H0C_not_coherent_unconditional` は Theorem (10.8) 経由ゆえ (11.5)-(11.7) を証明する
    ファイルより下流、という層順の都合)。両側を import する `S13_NonGaloisExclusion` で
    一度だけ discharge:
    (11.4) `coherent_quotient_bound` / (11.5) `secondDerived_eq_HC` /
    (11.6) `core_structure_unconditional` / (11.7) `H_elementaryAbelian_unconditional` /
    (11.8) `zeta_residual_not_orthogonal_unconditional` (書籍の `∀ ζ ∈ 𝒮(HC)` 形) /
    (11.9.a) `inner_tau_muColumnZero_sub_zeta_rowZero_unconditional`。循環なし。
    清掃 1 件: §13 `Hypothesis` の未消費 opaque `Prop` フィールド 3 本を削除 +
    構造 docstring を書籍 (11.2) の条項列挙に差し替え。
  - **§12 監査完了 (2026-08-07)**: 17 件 ((12.1)-(12.17)) すべてに実体あり。
    **補充 1 件** = (12.7) を書籍そのままの形へ (`S14.typeI_isFrobenius_kernel_maxNilpotentNormalHall`):
    旧 `typeI_frobenius` は (i) Type-V 排除 `hnoV` を仮説で受けていた (書籍に無い; (10.10) で
    discharge 可能、循環しない)、(ii) 結論の第 2 連言が `Prop` 値データフィールド
    `data.kernel_eq_MF` で producer が `True` を入れていた (**強度が producer 依存** — 別 producer
    は本物の `typeF.H = M_F` を入れる)。新形は核を `maxNilpotentNormalHall M` と名指しし無条件。
    清掃 2 件: `DadeNotation` の未消費 `Prop` フィールド 3 本を削除 /
    `witness_value_norm_package` の「Genuinely still-missing」docstring が stale だったので訂正
    (7 連言すべて名前つき補題で discharge 済・axiom-clean)。
  - **opaque-`Prop` フィールドの棚卸し (§10-§12 で 4 例)**: `S12.CharacterParameters` (2 本) /
    `S13.Hypothesis` (3 本) / `S14.TypeIFrobeniusData.kernel_eq_MF` (1 本、**消費者あり・強度可変**) /
    `S14.DadeNotation` (3 本)。**残 1 件**: `S15_SAndTGrid.lean:39` の `e_eq_index : Prop`
    (同ファイル :137 に本物版がある) → §13 監査で扱う。
  - **§13 監査に着手 (2026-08-07)**: 22 件 ((13.1)-(13.19) + (13.10.1)-(13.10.3))、番号 grep では
    全件に実体。**(13.19) は突合済 = 書籍の全条項が `S15.TypeIOrthogonalityGridData` に在る**
    (`betaL_eq` で `β_L` を Dade 像に pin / (c) 第 1 条項の `j` 非依存 / (c1)(c2) とも**両条項**)。
    ⚠ 同ファイルの**旧** carrier `TypeIOrthogonalityData` は opaque `Prop` を case ラベルに使い、
    implication field が (c1) の次数評価・(c2) の parity しか投影しない **lossy adapter**
    (§16 `BetaVanishing` が消費)。producer は grid 版から本物を入れているので**証明は忠実**だが
    statement 単体では条項が読めない (失敗様式 2 に近い形)。**被覆漏れではない**ので補充不要と判断。
    §12 の宿題だった `S15_SAndTGrid.lean:39` の `e_eq_index : Prop` はこの旧 carrier のもの。
  - **§13 の (13.1)(13.2) 突合済 (2026-08-07)**。(13.1) carrier は条項一致。
    **(13.2)(e) を書籍の形へ補充** (`S15.Hypothesis.A0S_normedTI`): 書籍「`A₀(S)` は正規化群 `S` を
    持つ TI-部分集合、かつ `τ = Ind_S^G`」の 2 条項。両半分の honest 定理
    (`isTISubset_typePACore` / `sInstance_dade_eq_induce`) は既存だったが、carrier
    `BasicStructureGated`/`BasicStructureData` は (13.2.e) を **`Prop` 値データフィールド**
    `A0S_TI`/`tauS_eq_induction` としてしか露出せず、producer が **`True`** を入れていたため
    **headline `basic_structure` の結論の最終連言が空**だった。`basic_structure` の結論も本物の
    `IsTISubset` へ差し替え。Type-V 排除は (10.10) で discharge (書籍にその仮説は無い)。
    stale docstring 訂正 1 件 (closed issue 3001 への「未解決」参照)。
  - **§13 監査完了 (2026-08-08)**: 22 件 ((13.1)-(13.19) + (13.10.1)-(13.10.3)) すべてに
    書籍強度の実体あり。**補充 3 件**:
    - **(13.2)(e)** `S15.Hypothesis.A0S_normedTI` — carrier が `Prop` 値フィールドで `True` を
      入れており headline `basic_structure` の結論の最終連言が空だった (5 例目の opaque-Prop、
      最も実害大)。`basic_structure` の結論も本物の `IsTISubset` へ差し替え。
    - **(13.10)** `Hypothesis.analytic_inequality_of_lambdaCluster` — Core endpoint は書籍が
      λ から導く 3 入力 (`hD`/`hv` = (13.4)、`hQcomm` = (13.2.b)-at-`T`) を仮説で受けていた。
    - **(13.11)** `Hypothesis.numeric_bounds_of_lambdaCluster` — 同上の 3 条項版。
    設計差の記録: (13.4) の「case (9.7.b) holds for `M = T`」は数値署名で表現 (定性形は
    `clifford_dichotomy` に在る) / (13.16) は `hTTypeII`/`hDbot` を仮説で受ける (discharge 可) /
    (13.19) の旧 carrier `TypeIOrthogonalityData` は lossy adapter (書籍強度は grid 版)。
    stale docstring 訂正 1 件 (closed issue 3001)。
  - **§14 監査完了 (2026-08-08) ⟹ ステップ 3 (Part I §1-§14 の逐条監査) 完了**:
    20 件 ((14.1)-(14.16) + (14.11.1)-(14.11.4)) すべてに書籍強度の実体あり、**補充ゼロ**。
    (14.2) = `S16.FieldNormalizerData` が (a)(b) の条項一致 ((a) `σ` 経由の体モデル同定 +
    condition (A)、(b) `Q` の可換 `p'` 性 + `W₂` の正規化)。総組み立て
    `S16.field_normalizer_structure` は書籍の結び「By (14.12), (14.16) and (14.7), the proof
    of Theorem (14.2) is complete」を**そのまま**写した分岐構造で、`feitThompson` まで axiom-clean。
  - **次の入口**: ステップ 2 = Part II (Suzuki の定理 A、書籍 pp.97-134) + 補章 (Huppert /
    Near-Fields / Suzuki 2-Groups / Feit–Sibley) の census。章内リセット番号なので手作業寄り。
  - **監査手順の正本** = memory `textbook-coverage-audit-failure-modes`。
    **(1) AxiomsCheck の番号コメント → (2) 書籍ページ画像 → (3) 結論の突合** の順。
    🚨「実体が見つからない」を結論にしない (本セッションで 3 回誤判定しかけた)。
  - **未形式化として残るもの**: **なし** (2026-08-08 に (1.7)(b) の判定を撤回 — 上記)。
  - **低優先の繰延 2 件**: (3.8) の packaging 差 / (5.6) の書籍仮説 (b)(c) ⟹ 分解存在 の橋渡し。

## 完了条件

Peterfalvi の全番号付き結果 (Part I 169 + Part II + 補章) が**書籍強度**の Lean statement を
持ち、特殊化債務ゼロ。各章の監査結果を census note に記録する。

## 参照

- census 正本: `notes/peterfalvi/full_formalization_census_2026_08_07.md`
- 書籍テキスト: `references/peterfalvi/pdftotext/*.txt` (⚠ 数式は OCR 崩れ → `pages/*.png` を読む)
- Coq 併読: `coq/theories/PFsection<N>.v` (N = 書籍 result 章番号)
