---
id: 175
slug: pf-911-section9-casea-descent
title: "Peterfalvi (9.11) case-(a) の §9 descent: CaseASevenEightRefutation の type-free producer"
created: 2026-08-07
---

# Peterfalvi (9.11) case-(a) の §9 descent

## 背景

[issue 0172](0172-peterfalvi-full-formalization.md) ステップ 3 の §9 逐条監査 (2026-08-07) で、
**§9 で唯一の条件付き結果**として検出した。

書籍 (9.11) (p.54) は「`𝒮(H₀C′)` は `τ` について coherent」を **Hypothesis (9.5) の下で**
主張する。(9.5) は (9.2) 経由で **Type II / III / IV** を覆う。repo の状況:

- **types III/IV**: `S13.coherent_sOf_H0Cprime` が閉じている (FT の live path)。
- **type-free (§9 level)**: `S11.sOf_nineEleven_coherent`
  (`S11_NineElevenSubcoherentBridge.lean:1322`) は Clifford 二分律の両枝を通すが、
  **case (a) 側で 2 つの入力を仮説として受ける**:
  - `h2 : ∀ caseA, 2 ≤ #{degree-qa irreducibles in 𝒮(H₀C′)}` (degree-`qa` base coherence)
  - `hrefuteEq : ∀ caseA, CaseAEqualityRefutation caseA …` (maximality refuter)

  実体としては、[closed issue 1045](closed/1045-pf-9-11-section9-level.md) の消化記録が
  「**開いた carrier はちょうど 1 本 = `CaseASevenEightRefutation`** と §9 dictionary
  パラメータに還元された」と結論している。

## なぜ「未解決数学ではない」のか (issue 1045 の調査結果)

§13 側の対応物が **sorry-free で証明済** (projection-budget 論法)。その証明が type 情報を使うのは
`hncH0C` / `htype` の 4 箇所だけで、**4 つとも type-free な §9 counterpart が既に在る**:

> ⚠ **2026-08-08 の参照訂正**: 上の「`S13.nineElevenSevenEightRefutation`
> (`S11_NineElevenPairAdjoin.lean:893`)」は **stale** (当該ファイルは 224 行しかない)。
> 実体は **`OddOrder/Peterfalvi/S15_NineElevenSevenEight.lean`** (563 行) の
> `S15.Hypothesis.nineElevenSevenEightRefutationS` (:45) と
> `...RefutationT` (AxiomsCheck :11659 に登録済)。
> ⚠ さらにこの S15 版は `hyp : S15.Hypothesis` と `hnoV` (Type-V 排除) を仮説に取り、
> **§13 の S-and-T 設定に強く依存**する。descent は「4 箇所を差し替える」より重い可能性があり、
> 着手時に依存の実測 (どのフィールドが実使用か) を先にやること
> — memory `generalize-by-measuring-which-carrier-fields-are-used` の手順。

- `caseA_nineElevenTwo_tiWitness`
- `caseA_two_summand_inertia_inputs`
- `caseA_nineElevenThree_count_inputs`
- `C_eq_cSub_of_noncoherent` (§9 では定義的)

⟹ **§13 の証明を type-free counterpart 4 本に載せ替える descent**。

## やること

- [x] **依存を実測 (2026-08-08)**。`S15.Hypothesis.nineElevenSevenEightRefutationS`
      (`S15_NineElevenSevenEight.lean:45`、本体 ~520 行) の実使用:

      - **`hnoV` は 1 箇所だけ** (:266、`sSet_coherent_extension_cross_orthogonal` へ渡す)。
      - `hyp` の大半は**記法**: `toTypesIIIIIIVSetupS` 65 回 / `dadeHypS` 59 回 / `S` 33 回。
        これらは setup・Dade 仮説・群のアクセサで、型固有の事実ではない。
      - 型固有の実体は **9 本の名前つき §15 補題**:
        `sSet_scaledDiff_support` (2) / `sSet_member_conjDiff_supported` /
        `sSet_eq_sOf_H0Cprime` / `sSet_coherent_extension_cross_orthogonal` /
        `sOf_H0Uprime_subset_sSet` / `oddCardS` / `nineElevenSTwoExtractionS` /
        `nineElevenFourNormInputsS` / `finiteG`。

      **§9 counterpart の実在**: 本 issue が挙げる 4 本
      (`caseA_nineElevenTwo_tiWitness` / `caseA_two_summand_inertia_inputs` /
      `caseA_nineElevenThree_count_inputs` / `C_eq_cSub_of_noncoherent`) は**全部実在**し
      AxiomsCheck 登録済 (`S11_NineElevenCaseA.lean` / `S11_NineElevenSubcoherentBridge.lean`)。
      しかし上の 9 本のうち §11 に同名/対応が見つかるのは `nineElevenSTwoExtraction` **1 本だけ**。

      ⟹ **scope の再評価**: 「4 箇所を差し替える」ではなく「~520 行の証明を、§15 固有の
      6 本程度を §9 レベルの事実へ載せ替えながら移植する」作業。**複数 session 規模**。
      (CLAUDE.md: 規模は着手可否の基準でないが、見積もりは正確にしておく。)
- [x] **⚠ 2026-08-08: 本 issue の前提が誤りだったと判明 — descent は 2026-07-20 に完了済**。

      実測すると `S11_NineElevenCaseAResidual.lean` に §9 レベルの producer が**全部揃っている**:

      | repo (すべて AxiomsCheck 登録済 = axiom-clean) | 内容 |
      |---|---|
      | `S11.caseA_sevenEightRefutation` (:445) | `CaseASevenEightRefutation` の §9 producer。docstring 明記「**No type hypothesis remains.**」 |
      | `S11.caseA_normBound` (:838) | (9.11.4)-(9.11.8) の norm bound、`h78` 供給済 |
      | `S11.caseA_equalityRefutation` (:853) | `CaseAEqualityRefutation` = `hrefuteEq` |
      | **`S11.nineEleven_coherent` (:886)** | **endpoint** — `sOf_nineEleven_coherent` に `h2` = `caseA_irrCut_two_le_ncard`、`hrefuteEq` = `caseA_equalityRefutation` を渡して**両仮説を消している** |
      | `S11.typeII_nineEleven_coherent` (:922) | type II 版 (Hypothesis (9.2) を `TypeIIData` から直接構成) |
      | `S11.nineEleven_coherent_A0` | `A₀` レベル版 |

      landing は **2026-07-20 の commit `9b3b2bc95`**
      (「⭐ (9.11) の §9 版が case (9.7.a) 込みで完全証明に — 最後の producer を降ろした」)。
      ⟹ **本 issue は 2026-08-07 の起票時点で既に stale**。

      **誤判定の原因** (2 段重ね):
      1. `sOf_nineEleven_coherent` を endpoint と取り違えた。これは Clifford 二分律の
         **branch-level assembly** で、case (a)/(b) の残差を分岐データごとに量化して露出する
         のが役目。endpoint はその下流の `nineEleven_coherent`。
      2. 2026-08-08 の「参照訂正」で `S15.Hypothesis.nineElevenSevenEightRefutationS` を
         descent 対象と特定したのも誤り。あれは **§13/§15 の S-instance** (FT spine 側) 用で、
         §9 レベルの `CaseASevenEightRefutation` とは別物。~520 行の移植見積もりは
         **存在しない作業**の見積もりだった。

      ⟹ memory [[textbook-coverage-audit-failure-modes]] に既出の様式そのもの
      (「engine 止まり」の逆 = **assembly を endpoint と誤認**)。本セッションだけで
      「未形式化と記録されていたが既に在った」が 8 件目。

- [x] **AxiomsCheck の (9.11) block の stale コメントを修正 (2026-08-08)**。
      `sOf_nineEleven_coherent` の注記から「the remaining item of issue 1045」を外し、
      **下流の `nineEleven_coherent` が両残差を discharge している**ことへの forward pointer に
      置き換えた (この文言自体が誤判定を招いた)。
- [x] census note の §9 表を更新 (2026-08-08)

## 完了条件

**達成済 (実体は 2026-07-20、判定は 2026-08-08)**。完了条件は

> `S11.sOf_nineEleven_coherent` (**または後継**) が Hypothesis (9.5) 相当のデータのみを取り
> `𝒮(H₀C′)` の coherence を返す (case-(a) の 2 仮説が消える)。full build green + AxiomsCheck OK。

で、**後継 = `S11.nineEleven_coherent`** がこれを満たしている。残る parametric 入力は
(4.6)/(8.15) の Dade データ (`h46` / `dd` とその pin) のみで、これは (9.5) が前提とする
Dade 等長そのもの — open mathematics ではない。

## 参照

- 監査記録: [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の §9 節
- 前段の調査: [closed issue 1045](closed/1045-pf-9-11-section9-level.md)
- landing commit: `9b3b2bc95` (2026-07-20)
- 書籍: `references/peterfalvi/pages/peterfalvi-p054..p057.png` ((9.11) と (9.11.1)-(9.11.8))
- Coq 併読: `coq/theories/PFsection9.v`
