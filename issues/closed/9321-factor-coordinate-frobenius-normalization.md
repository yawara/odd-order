---
id: 9321
slug: factor-coordinate-frobenius-normalization
title: "FactorCoordinateData の Frobenius half-range normalization API"
created: 2026-07-23
---

# FactorCoordinateData の Frobenius half-range normalization API

## claim

- owner: lane b
- claimed: 2026-07-23
- consumer: Higman Lemma 13 p.92 restricted-factor B/C normal forms
- shared target:
  `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/CaseDispatch.lean`
- downstream compatibility check:
  `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/Assembly.lean`

## 背景

`Assembly.lean` と `TypeBRecognition.lean` は同じ local `normalize` helper を
重複しており、commutative branch は `theta = 1`、noncommutative branch は
`exists_flip_frobenius_le_half` で `0 < r`、`2*r ≤ n` に正規化している。
Lemma 13 でも共通 `ePhi` と `nu` を動かさず同じ操作が必要なので、
`FactorCoordinateData` の public API として抽出する。

## やること

- [x] inclusive `FactorCoordinateData` の normalization theorem を追加
- [x] prescribed kernel coordinate と `nu` の index を保持
- [x] CaseDispatch と Assembly の targeted build
- [x] warning ratchet
- [x] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。CaseDispatch と Assembly の targeted build green。

## 2026-07-23 完了

commit `e4f91c289` で
`FactorCoordinateData.exists_normalized_frobenius_le_half` を追加した。
commutative branch は同じ coordinate data と `theta = 1` を返し、
noncommutative branch は既存の coordinate flip により `0 < r`、
`2*r ≤ n` を満たす Frobenius power を返す。型 index の `c`、`ePhi`、`nu`
は両 branch で不変。

検証:

- `lake build OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch`
- `lake build OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly`
- `bin/check-warnings OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch`
  — 非 sorry 警告 21、全件 baseline 内
- `bin/check-warnings OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly`
  — 非 sorry 警告 31、全件 baseline 内
