---
id: 9128
slug: psu-simplicity
title: "claim: PSU(3,q) simplicity for q > 2 (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) simplicity for q > 2 (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 uses simplicity of the standard
`PSU(3,q)` target, citing [H], Kapitel II, Satz 10.13 rather than proving it.
Theorem A assumes `q > 2`; with the repository model `q = 2^n`, the exact
nonexceptional hypothesis is `1 < n` (`n = 1` has group order 72). Issues
9122--9127 constructed the honest Hermitian unital action, Borel, Bruhat
decomposition, and exact order. No open 9000-series claim owns simplicity.

## やること

- [x] Add `GroupTheory/SpecificGroups/ProjectiveUnitary/Simplicity.lean`.
- [x] Prove fixed-point-free root scaling for torus weight not equal to one,
  construct such a parameter for `1 < n`, and obtain every root generator as
  a commutator.
- [x] Use the central-root Bruhat relation to put the Weyl generator in the
  derived subgroup.
- [x] Prove the Bruhat torus parameter is surjective and then put every
  determinant-one torus generator in the derived subgroup.
- [x] Prove the standard group is perfect and its standard Borel is solvable.
- [x] Apply the existing perfect/quasiprimitive/solvable-stabilizer criterion to
  prove `IsSimpleGroup (standardPermGroup n)` for `1 < n`.
- [x] Wire public endpoints into `OddOrder.lean` and `AxiomsCheck`, update the
  frontier note, and pass strict, module, audit, and full builds.

## 完了条件

The concrete PSU permutation group is honestly proved simple for exactly the
source range `q = 2^n > 2`, with no opaque simplicity hypothesis, `sorry`, new
axiom, or false extension to the exceptional `q = 2` case.

## 参照

Upstream: issue 9127, commits `33e6a7a85` and `6d2c80245`,
`ProjectiveUnitary/Bruhat.lean`. Architecture reference:
`SpecificGroups/Suzuki/Simplicity.lean` and
`GroupAction/PerfectQuasiprimitive.lean`. Text reference: Peterfalvi Part II,
Theorem A and Chapter I §3 Lemma 1 (pp. 97--107). Next consumer:
`Peterfalvi/Appendices/Suzuki/InductionHypothesisPSU.lean`.

## 実施結果 (2026-07-18)

`ProjectiveUnitary/Simplicity.lean` proves a nontrivial Hermitian norm weight
for `1 < n`, fixed-point-free root displacement, Bruhat-torus surjectivity,
and root, Weyl, then torus generator membership in the derived subgroup. It
therefore proves perfectness; the root-by-abelian-torus Borel is solvable, so
the existing primitive-action criterion gives
`standardPermGroup_isSimpleGroup (hn : 1 < n)`. The exceptional `n = 1` case
is intentionally excluded exactly as Peterfalvi Theorem A requires.

Strict elaboration, the leaf module build (2057 jobs), `OddOrder.AxiomsCheck`
(4363 jobs), and the full `lake build OddOrder` (4420 jobs) all passed. Every
public endpoint is audited, and no `sorry`, `admit`, or new axiom was introduced.
