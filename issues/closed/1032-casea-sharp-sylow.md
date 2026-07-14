---
id: 1032
slug: casea-sharp-sylow
title: "Instantiate the sharp case-A Sylow bridge for the Section 11 action image"
created: 2026-07-14
---

# Instantiate the sharp case-A Sylow bridge for the Section 11 action image

## 背景

Peterfalvi (14.6) の case (9.7.a) 排除では、(13.13) の sharp parameters
`q = 3`, `u = ((p - 1) / 2)^2` と §9.7(a) の 2 座標 block-scalar 埋め込みから、
`r ∣ (p - 1) / 2` に対する `U` の Sylow `r`-部分群が非巡回であることを使う。
issue 9101 で一般表現論 bridge は構築済み。本 issue はこれを §11 action image、元の
`TypesIIIIIIVSetup.U`、最後に §13/§14 の実際の `Hypothesis.U` へ接続する。

## やること

- [x] §9.7(a) の block-scalar ratio embedding と sharp parameters から、作用像の全 Sylow
      `r`-部分群の非巡回性を証明する。
- [x] action hom の range 全射を使い、元の `TypesIIIIIIVSetup.U` の全 Sylow
      `r`-部分群へ非巡回性を持ち上げる。
- [x] sharp parameters と `Sdata_U_eq` を用い、実際の `Hypothesis.U` に対する honest な
      Peterfalvi (14.6) bridge を証明する。
- [x] 既存の `caseA_parameters` を cite する無条件 consumer を配線する。
- [x] honest bridge 群の AxiomsCheck / leaf build / full build を通し、新 axiom・sorry が
      無いことを確認する。

## 実施結果

- `S11_CaseAOddPartBound.lean` に action-image 版と original-`U` 版を実装。
- original-`U` 版は action kernel の自明性を仮定しない。全射像で Sylow と巡回性が保たれる
  向きだけを使うため、§11 の一般 setup で成立する。
- `OrderDetermination.lean` に (13.13) の値を正規化し、`Sdata_U_eq` で named `U` へ輸送する
  axiom-clean な `caseA_sylow_U_not_isCyclic_of_parameters` を実装。
- 無条件 `caseA_sylow_U_not_isCyclic` は既存の `caseA_parameters` を cite する downstream
  wiring。後者は現在 transitive に既存 `sorryAx` を含むため AxiomsCheck 対象にはせず、
  本 issue の honest bridge と上流パラメータ決定の境界を明示した。
- build 実測: S11 leaf 4037 jobs、S15 leaf 4118 jobs、AxiomsCheck 4204 jobs、
  `lake build OddOrder` 4219 jobs。すべて green。

## 完了条件

上記 3 段の sharp-parameter bridge が sorry-free で実装され、AxiomsCheck と full build が
green。既存の (13.13) parameter producer を cite する consumer も配線済み。

## 参照

- Peterfalvi §14, (14.6); `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `galS`
- issue 9101 (`BlockScalarSylow.lean`)
- issue 0115 (`OrderDetermination.lean` lane-a carve-out)
