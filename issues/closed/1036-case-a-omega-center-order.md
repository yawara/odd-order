---
id: 1036
slug: case-a-omega-center-order
title: "Peterfalvi (14.6): determine the order of Omega_1(Z(R))"
created: 2026-07-15
---

# Peterfalvi (14.6): determine the order of Omega_1(Z(R))

## 背景

issue 1035 / commit `b4e95807` までで、case (9.7.a) の非巡回
`R₀ ∈ Syl_r(U)` を ambient Sylow `R` に延長し、`Z(R) ≤ R₀` を証明した。
Peterfalvi (14.6) の次の段は `R₁ = Ω₁(Z(R))` が非自明 elementary abelian
`r`-subgroup であり、`U` の二つの cyclic scalar coordinates による rank 上界から
`|R₁| = r` または `r²` とする部分である。

Case A では (13.12) の `c = 1` により `U` の chief-factor action の kernel が自明になる。
従って (9.7.a) の block-scalar embedding は quotient image だけでなく実際の `U` を
`((ZMod p)ˣ)^2` に埋め込み、`rank U ≤ 2` を与える。

`c_eq_one` / `caseA_parameters` の現行 producer は (13.10) の legacy
`analytic_inequality` を経由して `sorryAx` を含む。この layer inversion は hub issue 0116 が
b #22 rebase 後に full flip する裁定済みである。本 leaf はその所有域に触れず、`c = 1` と
`q = 3` を明示入力にした axiom-clean な数学を公開する。0116 完了後の consumer はこの theorem に
clean producer を直接渡せばよく、legacy wrapper は追加しない。

## やること

- [x] 二つの cyclic coordinates の積の BG-rank が高々 2 であることを証明する
- [x] `c = 1` と `cSub = C` から Case A の actual `U` の scalar embedding を単射化する
- [x] `rank U ≤ 2` を公開する
- [x] `Ω₁(Z(R))` の非自明性・elementary abelian 性・`R₀` への包含を組み合わせる
- [x] `|Ω₁(Z(R))| = r ∨ |Ω₁(Z(R))| = r²` を証明する
- [x] leaf / AxiomsCheck / full build と axiom audit を通す

## 完了条件

上記 theorem が `sorry` なしで成立し、標準 allowlist 三公理だけに依存すること。

## 実施結果

- `S15_CaseAOmegaCenter.lean` を新設し、二座標 cyclic product の rank bound、actual `U` の
  faithful scalar embedding、ambient `Ω₁(Z(R))` の位数二択を証明した。
- `c = 1` / `q = 3` は明示入力として、hub issue 0116 の relayer 所有境界を保持した。
- `lake build OddOrder.Peterfalvi.S15_CaseAOmegaCenter`: 4131 jobs green。
- `lake build OddOrder.AxiomsCheck`: 4206 jobs green。新規三定理はいずれも allowlist 三公理のみ。
- `lake build OddOrder`: 4221 jobs green。

## 参照

- Peterfalvi (14.6), `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `R1 := 'Ohm_1('Z(R))`, `m12`
- issues/0115, 1035, 9087
