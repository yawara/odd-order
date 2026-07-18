---
id: 2041
slug: centralizer-induction-a
title: "Peterfalvi Ch I section 3 Proposition 1(a) centralizer induction"
created: 2026-07-18
---

# Peterfalvi Ch I section 3 Proposition 1(a) centralizer induction

## 背景

Peterfalvi Part II, Chapter I §3 Proposition 1 begins the induction on
centralizers. For `1 ≠ X ≤ V`, it sets `L = C_G(X)` and lets `L` act on
`Ω_X`. Part (a) asserts that this action satisfies the full source hypothesis
(A1), and that its intrinsic normal core is
`𝒩(L) = C_{L ∩ D}(L ∩ Q) ≤ L ∩ V`. Section 1 Proposition 6 already proves
the required double transitivity elementwise, but the induced action, A1-only
carrier, and nonfaithful normal-core statement are not yet bundled. Issue 9129
and commit `cea5e4055` complete the preceding §3 Lemma 1 frontier.

## やること

- [x] Construct the `C_G(X)` action on `Ω_X` and prove the three fixed points
  `H`, `H^t`, and `H^{ts}` in the left-action convention.
- [x] Add an honest `HypothesisA1` carrier containing every source (A1) field,
  without importing faithfulness (A2) or 2-rank (A3), and construct it for the
  restricted action.
- [x] Identify `(L ∩ H).normalCore` with the restricted action kernel and with
  `C_{L ∩ D}(L ∩ Q)`, intrinsically in `L = C_G(X)`.
- [x] Prove the source inclusion `𝒩(L) ≤ L ∩ V`.
- [x] Wire the leaf into the Suzuki hub and `AxiomsCheck`, update the frontier,
  and pass strict, module, audit, and full builds.

## 完了条件

Chapter I §3 Proposition 1(a) is represented at book strength by constructed
A1 data and the intrinsic restricted normal-core formula. No full `Hypothesis`
is fabricated for the generally nonfaithful action; there is no opaque Prop
field, `sorry`, new axiom, or weakening of a source conclusion.

## 参照

Text: `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
lines 167--193 (printed pp. 105--106). Upstream Lean:
`FixedPointCentralizer.lean`, `CentralizerStructure.lean`,
`DistinguishedInvolution.lean`, and `InductionHypothesis*.lean`. Survey row:
`notes/meta/three_books_full_survey_2026_07_16.md` (I.3 Prop 1).

## 実装記録

- `CentralizerInduction.lean` に `C_G(X)` の `Ω_X` 上の誘導作用と、
  source (A1) の全データだけを保持する `HypothesisA1` を構成した。
- Peterfalvi の右作用 `H^{ts}` は Lean の左作用で `s • (t • H)` と翻訳した。
  restricted action は一般に faithful でないため、ambient `Hypothesis` の
  `normalCore_H_eq_bot` は使用していない。
- intrinsic core を restricted action kernel と同定し、
  `𝒩(L) = C_{L ∩ D}(L ∩ Q) ≤ L ∩ V` を証明した。
- Suzuki hub と `AxiomsCheck` に接続し、strict leaf、module build
  (2802 jobs)、`OddOrder.AxiomsCheck` (4366 jobs)、full `OddOrder`
  (4422 jobs) が成功した。新しい `sorry`・`axiom` はない。
