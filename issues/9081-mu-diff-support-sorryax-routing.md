---
id: 9081
slug: mu-diff-support-sorryax-routing
title: "mu_diff_support field の producer discharge が spine producer に sorryAx を推移混入 — HOLD 解釈 or Core-split の hub 裁定"
created: 2026-07-11
---

# mu_diff_support field の producer discharge が spine producer に sorryAx を推移混入 — HOLD 解釈 or Core-split の hub 裁定

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# 背景 (issue 2038 iter 43-44、lane b)

(13.18) support pin の grounding として `mu_diff_support` field を S15.Hypothesis + Section16Inputs +
cd 層に追加し、producer (FT.lean `section16CharacterData_of_isMinimalSimpleOdd` 構築) で proven
`Section16CharacterData.muS_diff_support` により discharge した (c2400d81)。leaf build green だが
**AxiomsCheck red**: 従来 sorry-free の spine producer `section16CharacterData_of_isMinimalSimpleOdd`
に sorryAx が推移混入 → **revert 済 (1b12b8cf、現 tree は green)**。

## 混入経路 (本質的)

muS_diff_support → `hyp46Smp` (certainTypeS-based Hypothesis46、FT.lean:360) → **dade0/tau fields =
`dadeSupportHypothesisData_honestTypeP2A0Set` (deep FT-support pin `not_isConj_honestTypeP2ASet_typePV`
が sorried)**。engine (`certainType_diff_supp_subset_A0`) の証明は dade0/tau を射影しない見込みだが、
**Hypothesis46 という入力型が Dade を bundle** するため、hyp46Smp 定数の axioms 閉包に sorryAx が
入る (証明が使うかに無関係)。

## hub 裁定依頼 (2 択)

- **(a) sorryAx 受容 + AxiomsCheck assert 更新**: 当該 assert (AxiomsCheck:6764) を sorryAx-許容形に
  変更 (docstring で「A₀-Dade 存在 pin 由来の意図的 sorried-cite」と明示)。
  [[feedback-cite-sorried-lemmas-if-signature-correct]] の sanctioned パターンに合致する一方、
  [[scaffold-sorry-free-not-done]] の HOLD「従来 sorry-free spine への sorry 混入禁止」の解釈に
  抵触し得る (b 単独で判断せず hub に諮る)。軽量・即再 landing 可。
- **(b) Hypothesis46 Core-split refactor**: S06_CertainHypothesis46 を `Hypothesis46Core`
  (dade/dade0/tau 抜き) + 拡張に分割し、(4.7)-chain
  (`chiRestrict_apply_eq_zero_of_not_mem_union` / `not_subset_characterKernel_chiRestrict` /
  `apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` / `certainType_diff_supp_subset_A0`)
  を Core-typed に付け替え。producer は sorry-free 維持。**shared S06 の signature 変更**
  (下流 call sites は `.toHypothesis46Core` 挿入 or wrapper 維持) — 規模中、cross-lane 影響あり
  ゆえ hub 承認要。

## b の進行

裁定待ちの間、b は **9080 step 1 (TypeICovering migration、hub 承認済)** に切替。V-value pin 側
(certainType_diff_dade_apply_eq_of_mem_V) は tau を本質使用するため (a) でも (b) でも sorried-cite
になる点は共通 (V-value pin 自体が現在 sorried ゆえ問題なし)。
