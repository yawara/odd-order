---
id: 1030
slug: nu-grid-canonical-threading
title: "Canonical Section 16 hypothesis へ pure ν-grid bundle を thread する"
created: 2026-07-14
---

# Canonical Section 16 hypothesis へ pure ν-grid bundle を thread する

## 背景

Issue 9096 の hub 裁定に従い、lane-b が `NuGridSupplyData` から post-(14.9) の
構造事実 `V_commutative` を分離した後、lane-a が canonical `nuT` の純粋な
§4/§6 grid facts を FT-layer carrier に載せる。

最終定義 `sectionSixteenHypothesis_of_isMinimalSimpleOdd` を直接包むだけの producer は、
定理の型が巨大な canonical hypothesis を展開するため、個々の `nuT_*` 定理が
axiom-clean でも `#print axioms` で `sorryAx` を拾う。したがって genuine carrier
threading (`Section16CharacterData` → `Section16Inputs`) を行い、inputs を引数に取る
producer を axiom-clean な境界とする。

## やること

- [x] `Section16CharacterData` に pure ν-grid proof fields 10項目を追加し、canonical
      `nuT_*` 定理で producer を充足する
- [x] `Section16Inputs` に同じ fields を thread する
- [x] `sectionSixteenHypothesis_of_inputs` に対する `NuGridSupplyData` producer を追加する
- [x] leaf/full build と `#print axioms` で検証する
- [x] issue 9096 に lane-b consumer rewiring の残作業を handoff する

## 完了条件

Canonical `nuT` の全 pure grid facts が explicit carrier data として inputs まで到達し、
`sectionSixteenHypothesis_of_inputs` の base に対する `NuGridSupplyData` を `sorry` なしで
構成できること。producer の axiom audit が `sorryAx`-free で、`lake build OddOrder` が通ること。

## 結果

- `OddOrder.sectionSixteenNuGridSupplyData_of_inputs` が、named inputs の 10 個の
  pure ν-grid fields から `NuGridSupplyData` を構成する。
- `#print axioms` の結果は `[propext, Classical.choice, Quot.sound]`。新しい
  `#assert_only_allowed_axioms` も通過した。
- `lake build OddOrder.FeitThompson OddOrder.AxiomsCheck` は 4189 jobs で成功した。
- canonical final hypothesis を直接包む producer は、型に未完成の巨大 constructor を
  展開して `sorryAx` を継承するため不採用。clean boundary は named inputs のまま保った。
- generic `S15.Hypothesis.nuGridSupply` は row-translation gap により証明不能なので、
  downstream の explicit-pins rewiring を issue 9096 に記録した。

## 参照

- `issues/9096-b-frontier-gated-direction.md`
- `issues/1029-nu-grid-supply.md`
- `OddOrder/FeitThompsonNuGrid.lean`
- `OddOrder/FeitThompsonSetup.lean`
- `OddOrder/FeitThompson.lean`
