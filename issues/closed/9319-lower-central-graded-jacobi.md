---
id: 9319
slug: lower-central-graded-jacobi
title: "Lower-central associated-graded Jacobi identity"
created: 2026-07-23
---

# Lower-central associated-graded Jacobi identity

## claim

- owner: lane b
- claimed: 2026-07-23
- consumer: Higman Lemma 13 p.92 exponent-four Jacobi/eigenweight step
- shared targets: `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralGraded.lean`,
  `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralDegreeThree.lean`
- downstream compatibility check:
  `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/Assembly.lean`

## 背景

既存の `lowerCentralTripleCommutatorTrilinear` は実際の `[[x,y],z]` を
`L₃` に落とすが、Hall–Witt から従う associated-graded Jacobi
`T x y z + T y z x + T z x y = 0` が未実装。
Lemma 13 の `[[y_k,x_i],x_j]=[[y_k,x_j],x_i]` はこの Jacobi と
`lowerCentralCommutatorBilinear x_i x_j = 0` の直接 consumer。

## やること

- [x] `lowerCentralTripleCommutatorTrilinear_jacobi`
- [x] zero bracket からの swap-last corollary
- [x] targeted build + warning ratchet
- [x] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。`HigmanLowerCentralDegreeThree` targeted build green。

## 2026-07-23 完了

commit `180916adb` で Hall--Witt 恒等式から associated-graded Jacobi
`T x y z + T y z x + T z x y = 0` を証明し、zero degree-two bracket から
`T z x y = T z y x` を導く consumer-facing corollary を追加した。
既存の `lowerCentralCommutatorBilinear_comm` は依存方向を正すため
`HigmanLemmaTwelve/Assembly.lean` から shared `HigmanLowerCentralGraded.lean`
へ同名移設し、既存 consumer も変更なしで通した。

検証:

- `lake build OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree`
- `lake build OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly`
- `bin/check-warnings OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree`
  — 非 sorry 警告 0
- `bin/check-warnings OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly`
  — 非 sorry 警告 31、全件 baseline 内
