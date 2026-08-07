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

- **ステップ 2**: Part II + 補章の census (章内リセット番号なので手作業寄り)。
- **ステップ 3 (進行中)**: Part I の逐条監査を (1.1) から文書順に。1 章ぶん終えるごとに census note を更新。
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
    1. **(1.7)(b)** — 重複度 `e` 付き一般形 (可換 inertia 商への拡張定理が前提。巡回版は済)
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
  - **次の入口**: §12 = 書籍 pp.69-74「Maximal Subgroups of Type I」(repo `S14`)。
  - **監査手順の正本** = memory `textbook-coverage-audit-failure-modes`。
    **(1) AxiomsCheck の番号コメント → (2) 書籍ページ画像 → (3) 結論の突合** の順。
    🚨「実体が見つからない」を結論にしない (本セッションで 3 回誤判定しかけた)。
  - **未形式化として残るもの**: **(1.7)(b)** (重複度 `e` 付き一般形。可換 inertia 商への
    拡張定理が前提で、巡回版は済・合成列に沿う反復が未実施) の 1 件のみ。
  - **低優先の繰延 2 件**: (3.8) の packaging 差 / (5.6) の書籍仮説 (b)(c) ⟹ 分解存在 の橋渡し。

## 完了条件

Peterfalvi の全番号付き結果 (Part I 169 + Part II + 補章) が**書籍強度**の Lean statement を
持ち、特殊化債務ゼロ。各章の監査結果を census note に記録する。

## 参照

- census 正本: `notes/peterfalvi/full_formalization_census_2026_08_07.md`
- 書籍テキスト: `references/peterfalvi/pdftotext/*.txt` (⚠ 数式は OCR 崩れ → `pages/*.png` を読む)
- Coq 併読: `coq/theories/PFsection<N>.v` (N = 書籍 result 章番号)
