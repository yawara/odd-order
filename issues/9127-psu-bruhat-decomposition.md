---
id: 9127
slug: psu-bruhat-decomposition
title: "claim: PSU(3,q) Bruhat decomposition (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) Bruhat decomposition (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 uses the standard `PSU(3,q)`
structure, while Chapter IV §3 identifies the reciprocal Weyl coordinates and
the cubic Hua parameter. Issue 9126 and commit `609fdea4f` constructed the
faithful determinant-one root--torus Borel. No open 9000-series claim owns the
next upstream layer: the nontrivial Weyl--root relation, two Bruhat cells,
point-stabilizer equality, and exact full group order.

## 作用規約の裁定（2026-07-18）

Peterfalvi は右作用を用い、Chapter IV §3 の reciprocal を
`F(a,b) = (a/b, 1/b)` と書く。Lean 側は `MulAction` に合わせた左作用と
左 root translation を採用するため、affine 座標を root inversion
`J(u) = u⁻¹` で移送する。したがって標準 Weyl 写像は
`J ∘ F ∘ J(a,b) = (a/star(b), 1/b)` である。これは同じ作用の共役表示で
あり、原文の `F` 自体を変更するものではない。ユーザー承認により左作用を
維持するこの設計を採用した。これに伴い Hua parameter は
`b / star(b)^2`、Bruhat relation の左右 root はそれぞれ `J F J(u)` と
`F(u)` になる。

## やること

- [ ] Construct the determinant-one Hua/Bruhat torus parameter from the nonzero
  second root coordinate and prove its underlying value is `b / star(b)^2`.
- [ ] Use `weylReciprocal u` as the left root and Peterfalvi's `reciprocal u` as
  the right root, and prove the coordinate identities needed for the nontrivial
  relation `w R(u) w = b₁ w b₂`.
- [ ] Prove the Weyl--root relation as equality of concrete unital permutations,
  including pole, origin, and generic affine cases.
- [ ] Prove inverse closure of the standard generators and use closure induction to
  obtain the honest two-cell cover `G = B ∪ B w B` for `0 < n`.
- [ ] Deduce `standardBorel = stabilizer infinity` and the exact group order
  `q^3 * (q^3 + 1) * ((q^2 - 1) / gcd(q + 1, 3))`.
- [ ] Wire the Bruhat leaves into the project and axiom audit; update the
  Peterfalvi frontier after strict, module, audit, and full builds pass.

## 完了条件

The concrete standard permutation group has an honestly proved two-cell Bruhat
decomposition. The standard Borel is identified with the infinity stabilizer and
the full PSU order is derived from the action. The Hua parameter is constructed
in `PSUTorusParameter`; no `sorry`, new `axiom`, PGU substitution, or opaque
Weyl--root relation is introduced.

## 参照

Upstream: issue 9126, commit `609fdea4f`,
`ProjectiveUnitary/Borel.lean`. Architecture reference:
`SpecificGroups/Suzuki/Bruhat.lean`. Text reference: Peterfalvi Part II,
Chapter IV §3 Proposition and Corollary 2 (pp. 129-132). Next consumer: the
exact PSU simplicity and induction-hypothesis target.
