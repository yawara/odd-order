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
- shared target: `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralDegreeThree.lean`

## 背景

既存の `lowerCentralTripleCommutatorTrilinear` は実際の `[[x,y],z]` を
`L₃` に落とすが、Hall–Witt から従う associated-graded Jacobi
`T x y z + T y z x + T z x y = 0` が未実装。
Lemma 13 の `[[y_k,x_i],x_j]=[[y_k,x_j],x_i]` はこの Jacobi と
`lowerCentralCommutatorBilinear x_i x_j = 0` の直接 consumer。

## やること

- [ ] `lowerCentralTripleCommutatorTrilinear_jacobi`
- [ ] zero bracket からの swap-last corollary
- [ ] targeted build + warning ratchet
- [ ] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。`HigmanLowerCentralDegreeThree` targeted build green。
