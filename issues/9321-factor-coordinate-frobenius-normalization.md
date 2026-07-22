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

- [ ] inclusive `FactorCoordinateData` の normalization theorem を追加
- [ ] prescribed kernel coordinate と `nu` の index を保持
- [ ] CaseDispatch と Assembly の targeted build
- [ ] warning ratchet
- [ ] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。CaseDispatch と Assembly の targeted build green。
