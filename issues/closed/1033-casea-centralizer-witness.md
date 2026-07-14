---
id: 1033
slug: casea-centralizer-witness
title: "Construct the case-A centralizer witness from a noncyclic Sylow subgroup"
created: 2026-07-14
---

# Construct the case-A centralizer witness from a noncyclic Sylow subgroup

## 背景

Peterfalvi (14.6) の case (9.7.a) 排除では、`r ∣ (p - 1) / 2` に対する
`R₀ ∈ Syl_r(U)` の非巡回性から BG Prop. 1.16 を適用し、
`x ∈ R₀#` かつ `P ∩ C_G(x) ≠ 1` を得る。issue 1032 は sharp parameters と
block-scalar embedding から `R₀` の非巡回性までを構成済み。本 issue は Sylow を
ambient `G` の部分群へ写し、Prop. 1.16 の全仮定を実際の §15 carrier から証明する。

## やること

- [x] `R₀ : Sylow r U` の ambient image `B ≤ G` が非巡回かつ可換であることを示す。
- [x] `B ≤ N_G(P)`、`(|B|, |P|) = 1`、`P ≠ 1` を `Sdata` と `|P| = p^q` から示す。
- [x] BG Prop. 1.16 を適用して `x ∈ B#` と `P ⊓ C_G(x) ≠ ⊥` を構成する。
- [x] sharp-parameter consumer と接続し、AxiomsCheck / leaf build / full build を通す。

## 完了条件

上記 witness theorem が新 axiom / sorry なしで実装され、issue 1032 の非巡回性 producer
と接続される。AxiomsCheck と `lake build OddOrder` が green。

## 結果

- `exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic` が `R₀` の ambient imageを
  実構成し、可換性・normalizer包含・異素数位数・`P ≠ 1` を carrier から証明して
  BG Prop. 1.16 の witness を返す。
- `caseA_exists_sylow_mem_inf_centralizer_ne_bot_of_parameters` が issue 1032 の
  sharp-parameter Sylow 非巡回性と上記一般定理を接続する。既存 `caseA_parameters` を
  経由する無条件 consumer とは公理境界を分離した。
- `lake build OddOrder.Peterfalvi.S15_SAndT_Setup.OrderDetermination`: 4118 jobs green。
- `lake build OddOrder.AxiomsCheck`: 4204 jobs green。新規2定理はいずれも allowlist の
  `propext`, `Classical.choice`, `Quot.sound` のみに依存。
- `lake build OddOrder`: 4219 jobs green。

## 参照

- Peterfalvi §14, (14.6); `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `galS`
- BG Prop. 1.16: `OddOrder.BG.Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic`
- issue 1032 (`caseA_sylow_U_not_isCyclic`)
- issue 0115 (`OrderDetermination.lean` lane-a carve-out)
