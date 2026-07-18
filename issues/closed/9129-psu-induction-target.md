---
id: 9129
slug: psu-induction-target
title: "claim: Peterfalvi Ch I section 3 Lemma 1 PSU target (lane b)"
created: 2026-07-18
---

# claim: Peterfalvi Ch I section 3 Lemma 1 PSU target (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 uses exactly two facts about the
standard `PSU(3,q)` target: the action degree minus one is a power of two, and
the target is simple. Issues 9122--9128 now provide the concrete unital of
degree `q^3 + 1` and simplicity for the exact source range `q = 2^n > 2`. No
open 9000-series claim owns the remaining transport into the common Lemma 1
core.

## やること

- [x] Add `Peterfalvi/Appendices/Suzuki/InductionHypothesisPSU.lean`.
- [x] Transport `Unital.natCard = 2^(3*n)+1` across the equivariant bijection to
  prove the degree-minus-one power-of-two input.
- [x] Transport `ProjectiveUnitary.standardPermGroup_isSimpleGroup` across the
  target isomorphism for `1 < n`.
- [x] Apply `simple_normal_oddIndex_Q_core` to prove that `Q` is a `2`-group and
  identify `L` with both `O^{2′}(G)` and the join of the conjugates of `Q`.
- [x] Wire the leaf into the Suzuki hub and `AxiomsCheck`, update the frontier,
  and pass strict, module, audit, and full builds.

## 完了条件

The complete PSU branch of Peterfalvi Chapter I §3 Lemma 1 is proved from a
concrete target isomorphism and equivariant bijection, with no opaque target
hypothesis, `sorry`, new axiom, or weakening of `q > 2`.

## 参照

Upstream: issue 9128 and commit `e9155d64c`;
`ProjectiveUnitary/RootGroup.lean`, `ProjectiveUnitary/Simplicity.lean`, and
`Peterfalvi/Appendices/Suzuki/InductionHypothesis.lean`. Architecture:
`InductionHypothesisSuzuki.lean`. Text: Peterfalvi Part II, Chapter I §3
Lemma 1 (p. 105), citing [H] II.10.12--10.13 for the PSU degree and simplicity.

## 実装記録 (2026-07-18)

- `psu3_degree_twoPower` transports the concrete unital degree with the exact
  nondegenerate range `0 < n` and exponent `3 * n`.
- `psu3_target_simple` transports the constructed standard-group simplicity
  theorem with the exact range `q = 2^n > 2`, i.e. `1 < n`.
- `Q_and_residual_of_psu3_target` supplies both inputs to the common conditional
  core, without an opaque target hypothesis.
- Strict leaf elaboration passed; module build passed (2830 jobs),
  `AxiomsCheck` passed (4364 jobs), and `lake build OddOrder` passed (4421 jobs).
  The placeholder scan found no `sorry`, `admit`, or new `axiom` declaration.
