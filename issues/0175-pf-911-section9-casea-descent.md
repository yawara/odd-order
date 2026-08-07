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

- [ ] `S15.Hypothesis.nineElevenSevenEightRefutationS` (`S15_NineElevenSevenEight.lean:45`) の
      証明を読み、`hyp`/`hnoV` の**実使用箇所を数える** (docstring の「4 箇所」は未検証)
- [ ] 各点を上記 type-free counterpart に置換して `CaseASevenEightRefutation` の §9 producer を作る
- [ ] その producer で `sOf_nineEleven_coherent` の `h2`/`hrefuteEq` を discharge し、
      **Hypothesis (9.5) だけから (9.11) が出る**形にする
- [ ] AxiomsCheck の (9.11) block のコメント (「case (a) still needs …, the remaining item of
      issue 1045」) を更新する (issue 1045 は closed なので現状 stale)
- [ ] census note の §9 表を更新

## 完了条件

`S11.sOf_nineEleven_coherent` (または後継) が **Hypothesis (9.5) 相当のデータのみ**を取り
`𝒮(H₀C′)` の coherence を返す (case-(a) の 2 仮説が消える)。full build green + AxiomsCheck OK。

## 参照

- 監査記録: [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の §9 節
- 前段の調査: [closed issue 1045](closed/1045-pf-9-11-section9-level.md) (「次の自然な frontier」節)
- 書籍: `references/peterfalvi/pages/peterfalvi-p054..p057.png` ((9.11) と (9.11.1)-(9.11.8))
- Coq 併読: `coq/theories/PFsection9.v`
