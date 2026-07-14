---
id: 1038
slug: case-a-final-arithmetic-contradiction
title: "Peterfalvi (14.6): close case A by the final prime contradiction"
created: 2026-07-15
---

# Peterfalvi (14.6): close case A by the final prime contradiction

## 背景

issue 1037 / commit `342b4736` までで、case (9.7.a) の ambient Sylow subgroup
`R` に対する `R₁ = Ω₁(Z(R))` の位数が `r` または `r²` であり、(14.5) の
Frobenius complement 内の `W₂^y` から `p ∣ r² - 1` が従うことを証明した。

Peterfalvi (14.6) の残りは、`r ∣ (p - 1) / 2` なる素数を選ぶと、前者から
`r < p`、後者から odd-prime comparison により `p < r` が従うという最終矛盾である。
Coq `PFsection14.v` の `m12` から節末の divisibility contradiction に対応する。

issue 0116 の relayer 境界を守るため、解析的に生産される
`c = 1`, `q = 3`, `u = (p - 1)² / 4` は capstone の明示仮定とし、
hidden-sorry producer `analytic_inequality` を参照しない。

## やること

- [x] `r ∣ (p - 1) / 2` と `p ∣ r² - 1` の odd-prime 矛盾を証明する
- [x] case A の非巡回 Sylow、中心 trapping、`Ω₁` 位数、Frobenius count を合成する
- [x] leaf / AxiomsCheck / full build と axiom audit を通す

## 完了条件

明示パラメータ版の case-A contradiction が `sorry` なしで成立し、標準 allowlist
三公理だけに依存すること。

## 実施結果

- `S15_CaseAContradiction.lean` を新設し、odd primes `p`, `r` に対する純算術補題
  `false_of_odd_primes_dvd_half_and_sq_sub_one` を証明した。
- `caseA_false_of_parameters_and_typeIOverNormalizerData` で、素数 `r` の選択、
  `R₀ ∈ Syl_r(U)` の非巡回性、ambient Sylow の中心 trapping、
  `|Ω₁(Z(R))| = r ∨ r²`、(14.5) の fixed-point-free count を合成した。
- `r ∣ |R₀| ∣ |U| ∣ |G|` を実証して `r` の奇性を得ており、追加仮定はない。
- `c = 1`, `q = 3`, `u = (p - 1)² / 4` は明示引数のまま保ち、
  `analytic_inequality` および無条件 parameter producer は参照していない。
- `lake build OddOrder.Peterfalvi.S15_CaseAContradiction`: 4133 jobs green。
- `lake build OddOrder.AxiomsCheck`: 4208 jobs green。新規二定理は allowlist 三公理のみ。
- `lake build OddOrder`: 4223 jobs green。

## 参照

- Peterfalvi (14.6), `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `m12` から節末
- issues/0116, 1035, 1036, 1037
