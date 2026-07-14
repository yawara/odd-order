---
id: 1034
slug: casea-ambient-sylow
title: "Construct the ambient Sylow carrier for Peterfalvi (14.6)"
created: 2026-07-14
---

# Construct the ambient Sylow carrier for Peterfalvi (14.6)

## 背景

Peterfalvi (14.6) は `R₀ ∈ Syl_r(U)` を、(14.3) の Fitting kernel
`H = L_F ≥ U` の Sylow `r`-部分群 `R` へ拡張してから `Z(R)` を調べる。issue 1033 は
`R₀` の非巡回性から `x ∈ R₀#` かつ `P ⊓ C_G(x) ≠ 1` を構成した。本 issue はこの
centralizer witness を保持したまま、任意の ambient subgroup `K ≥ U` における Sylow
extension を実構成する。

## やること

- [x] `R₀` の `K` への像が `r`-group であることを示す。
- [x] `IsPGroup.exists_le_sylow` で、その像を含む `R ∈ Syl_r(K)` を構成する。
- [x] issue 1033 の centralizer witness と同じ existential carrier に束ねる。
- [x] leaf / AxiomsCheck / full build を通す。

## 完了条件

上記 assembly theorem が新 axiom / sorry なしで実装され、AxiomsCheck と
`lake build OddOrder` が green。

## 結果

`exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic` を実装した。
`R₀.map (Subgroup.inclusion hUK)` の `IsPGroup` 証明から ambient Sylow `R` を構成し、
issue 1033 の非自明な centralizer witness を同じ existential carrier に保持する。

- leaf build: 4118 jobs
- `OddOrder.AxiomsCheck`: 4204 jobs（allowlist 内の既存 3 公理のみ）
- full `OddOrder`: 4219 jobs

## 参照

- Peterfalvi §14, (14.6); `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `galS`
- issue 1033 (`caseA-centralizer-witness`)
- issue 0115 (`OrderDetermination.lean` lane-a carve-out)
