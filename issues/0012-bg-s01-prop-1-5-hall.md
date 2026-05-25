---
id: 12
slug: bg-s01-prop-1-5-hall
title: "BG §1 Prop 1.5 A-invariant Hall framework を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.5 A-invariant Hall framework を形式化する

## 背景

BG Prop 1.5 は §1 の中心で、A-invariant Hall π-subgroup の存在・包含・共役・商の固定点・
commutator containment をまとめる。`notes/bg/s01_solvable.md` では後続 25 回程度の引用があり、
Peterfalvi 04.11 でも Prop 1.5(d) が繰り返し使われる。

現状は Sylow p 版の coprime action machinery が Ch.4 にあり、Prop 1.5(d) 相当は
`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient` として利用可能。Hall π 一般版と
Prop 1.5(e) の正確な statement が残る。

## やること

- [ ] BG Prop 1.5(a)-(e) の statement を mmd で再確認する。
- [ ] 既存の `exists_aInvariant_sylow`, `aInvariant_sylow_conj`,
      `aInvariant_pSubgroup_le_aInvariant_sylow`, `coprime_fixedPoints_quotient` との対応を確定する。
- [ ] Hall π 一般版の existence / containment / conjugacy を実装する。
- [ ] Prop 1.5(d) は no-wrapper 方針に従い、必要なら section docstring で直接対応を明示する。
- [ ] Prop 1.5(e) の仮定を精密化し、実装または別 issue へ分割する。

## 完了条件

- BG Prop 1.5(a)-(e) について、Lean theorem または no-wrapper 対応表のどちらかが明確。
- 新規 theorem は sorry-free。
- `notes/bg/s01_solvable.md` の Prop 1.5 未解決欄が更新される。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`
- `references/bg/local-analysis.mmd` L400-L414 付近
