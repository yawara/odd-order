---
id: 1037
slug: case-a-omega-fixed-point-free
title: "Peterfalvi (14.6): count the fixed-point-free action on Omega_1(Z(R))"
created: 2026-07-15
---

# Peterfalvi (14.6): count the fixed-point-free action on Omega_1(Z(R))

## 背景

issue 1036 / commit `aecc7341` までで、case (9.7.a) の ambient Sylow subgroup
`R` に対し `R₁ = Ω₁(Z(R))` の位数が `r` または `r²` であることを証明した。
Peterfalvi (14.6) の次の段は、(14.5) の `y` が与える Frobenius complement 内の
`W₂^y` が `R₁` を fixed-point-free に作用することから
`p ∣ |R₁| - 1`、従って `p ∣ r² - 1` を得る部分である。

Coq `PFsection14.v` の `chR1H` / `nR1W2y` / `regR1W2y` に対応して、Lean では
`H = L_F` の nilpotence により Sylow `R` を characteristic にし、さらに
`N_G(R) ≤ N_G(Ω₁(Z(R)))` を使う。固定点自由性と合同は既存の ambient Frobenius
counting API `IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient` が担う。

## やること

- [x] Frobenius kernel 内の `Ω₁(Z(R))` に対する汎用合同を証明する
- [x] `TypeIOverNormalizerData` の (14.5) complement witness から仮定を放電する
- [x] `p ∣ r² - 1` を公開する
- [x] leaf / AxiomsCheck / full build と axiom audit を通す

## 完了条件

上記 theorem が `sorry` なしで成立し、標準 allowlist 三公理だけに依存すること。

## 実施結果

- `S15_CaseAOmegaFixedPointFree.lean` を新設し、ambient Frobenius kernel の
  `Ω₁(Z(R))` に対する合同と `p ∣ r² - 1` を証明した。
- (14.5) の `W₂^y` について、補群との所属から `W₂^y ⊓ H = ⊥` を実証し、
  `H = L_F` の nilpotenceから Sylow `R` の characteristic 性を構成した。
- `lake build OddOrder.Peterfalvi.S15_CaseAOmegaFixedPointFree`: 4132 jobs green。
- `lake build OddOrder.AxiomsCheck`: 4207 jobs green。新規二定理は allowlist 三公理のみ。
- `lake build OddOrder`: 4222 jobs green。

## 参照

- Peterfalvi (14.6), `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `chR1H`, `nR1W2y`, `regR1W2y`
- issues/0116, 1036
