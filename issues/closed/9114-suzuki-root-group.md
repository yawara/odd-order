---
id: 9114
slug: suzuki-root-group
title: "claim: SpecificGroups/Suzuki/RootGroup — construct S(q,theta) (lane b)"
created: 2026-07-18
---

# claim: SpecificGroups/Suzuki/RootGroup — construct S(q,theta) (lane b)

## 背景

The completed Tits-twist leaf is the first layer of the concrete `Sz(q)` target
required by Peterfalvi Part II, Chapter I section 3, Lemma 1. The next upstream
object is the standard nonabelian root group `S(q,theta)` on two field coordinates.
Repository and open-claim searches found no existing construction.

## やること

- [x] Add `OddOrder/GroupTheory/SpecificGroups/Suzuki/RootGroup.lean`.
- [x] Construct the ovoid-coordinate group law `(x,y)*(u,v) = (x+u,y+v+u*theta(x))`.
- [x] Prove explicit one, multiplication, inverse, square, and fourth-power formulas.
- [x] Construct the central involution line and prove its structural API.
- [x] Prove the exact cardinality and the `2`-group instance/theorem.
- [x] Wire the leaf into `OddOrder.lean` and `OddOrder.AxiomsCheck`.

## 完了条件

The leaf is warning-clean and contains no `sorry` or new `axiom`; all listed group
identities, the central line, cardinality, and `2`-group result are explicit and pass
`OddOrder.AxiomsCheck`. The issue is then moved to `issues/closed/`.

## 参照

Upstream: `OddOrder/GroupTheory/SpecificGroups/Suzuki/Field.lean`.
Consumers: the standard Suzuki root matrices, ovoid action, and Peterfalvi Lemma 1
target leaf. Frontier note: `notes/peterfalvi/suzuki_ch1.md`, item 9.
