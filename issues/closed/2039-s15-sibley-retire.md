---
id: 2039
slug: s15-sibley-retire
title: "b-3: retire consumer-zero S-side Sibley placeholders"
created: 2026-07-15
---

# b-3: retire consumer-zero S-side Sibley placeholders

## 背景

Issue 0118 b-3 は、2026-07-02 hub 裁定で do-not-complete とされた
`sibleyTarget_S` / `S_coherent` を W-side に restate するか retire するよう割り当てている。
両宣言は `Hypothesis.tauS` / `Sset` / `A0S` を使う S-side maximal-coherent Dade route だが、
FT spine の carrier では `tauS = 0` が placeholder であり、Lean 上の外部 consumer は 0。

実際の spine は `eta = tau3 ∘ omega` の W-side grid を使い、`eta_eq_tau_omega`、
`coherentIndS_image_inner_eta_eq_zero`、`T_typeIII_coherent_image_inner_eta_eq_zero` などの
直交・coherence API が既に実装されている。したがって新しい wrapper / restatement は重複となる。

## やること

- [x] `sibleyTarget_S` と、その唯一の consumer `S_coherent` を同時に retire
- [x] repo-wide grep で Lean consumer 0 を再確認
- [x] `HypothesisBasics` leaf build と full build を実行

## 完了条件

- W-side の既存 spine API を変更せず、上記 2 宣言だけが削除されている。
- `lake build OddOrder` が green で、AxiomsCheck が不変。

## 結果

- `rg "sibleyTarget_S|S_coherent" OddOrder` は該当 0。
- `lake build OddOrder.Peterfalvi.S15_SAndT_Setup.HypothesisBasics` green (4111 jobs)。
- `lake build OddOrder` green (4228 jobs、AxiomsCheck OK)。
- W-side の `eta` grid / coherent-image API は非変更。新しい wrapper は追加していない。

## 参照

- issues/0118 b-3
- issues/closed/1004、issues/closed/4014
- notes/peterfalvi/s16_w4_char_cascade.md (2026-07-02 hub ruling)
