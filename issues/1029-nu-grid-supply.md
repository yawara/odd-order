---
id: 1029
slug: nu-grid-supply
title: "Peterfalvi T-side ν-grid supply を canonical certain-type data から構成する"
created: 2026-07-14
---

# Peterfalvi T-side ν-grid supply を canonical certain-type data から構成する

## 背景

issue 9096 が、S15 の `deltaPrime_eq_one_T` と
`tSide_theta_package_of_not_caseB_core` の共通 gate を
`Hypothesis.nuGridSupply`（Peterfalvi (4.3)--(4.9) の T-side certain-type grid）へ
局所化した。供給元となる canonical grid は A 所有の
`Section16CharacterData.nuT` / `deltaPrimeT` と `mp.certainTypeT` に既に構成済みである。

ただし現行 theorem

```lean
Hypothesis.nuGridSupply (hG) (hyp : Hypothesis G) : NuGridSupplyData hyp
```

は generic `hyp` に対して強すぎる。`Hypothesis` の `nu` を各 row ごとに同じ class
function だけ平行移動しても、唯一の拘束 `nu_definition` は差分なので保存される一方、
`nu_irreducible` などは保存されない。したがって canonical proof package の構築と、
S15 carrier/API の正しい threading は分けて扱う。後者は b-owned signature に関わるため、
無断変更しない。

## やること

- [x] `FeitThompsonNuGrid.lean` へ canonical `nuT` 定義群を topic leaf として抽出する
- [x] irreducibility / row injectivity / orthonormality / degree congruence / base sign を証明する
- [x] row-sum induction / reducible dichotomy / support / value を T-side で証明する
- [x] conjugation を T-side で証明する
- [x] V-side commutativity の供給可能性を監査する（post-(14.9) fact と確定、無条件供給は棄却）
- [x] AxiomsCheck tripwire と full build を通す
- [x] generic carrier の row-base gap と必要な cross-lane API 修正を issue 9096 に報告する

## Carrier 監査結果

canonical `nuT` の grid field はすべて構成できたが、現行 `NuGridSupplyData` の
`V_commutative` は grid property ではない。`V` は general type-P では `T_F` の nilpotent
complement にすぎず、可換性は `IsTypeII T`（Peterfalvi (14.9)）の後に
`S15.isMulCommutative_V` から得る事実である。したがって `V_commutative` を前段 bundle に
無条件で要求して A 側から埋めることはしない。row-translation で generic `hyp.nu` 自体も
canonical grid に固定されない問題と合わせ、正しい signature 分割を issue 9096 に報告した。
## 完了条件

canonical certain-Type-T の全 **grid field** が sorry-free / allowed-axiom-only で揃い、
`lake build OddOrder` が成功すること。post-(14.9) の `V_commutative` と generic
`Hypothesis` への threading は、正しい carrier 契約が hub/b 側で裁定・実装されるまでは
本 issue の completion に含めない。

## 参照

- `issues/9096-b-frontier-gated-direction.md`
- `issues/2035-char-degree-analysis-producer.md`
- `OddOrder/FeitThompson.lean`
- `OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisSwap.lean`
