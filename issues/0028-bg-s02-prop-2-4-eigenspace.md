---
id: 28
slug: bg-s02-prop-2-4-eigenspace
title: "BG §2 Prop 2.4 eigenspace decomposition package"
created: 2026-05-26
---

# BG §2 Prop 2.4 eigenspace decomposition package

## 背景

BG §2 Prop 2.4 is the eigenspace decomposition and dimension-counting package
used by Thm 2.5.  The §2 note marks Thm 2.6 as closed and routes the next work
to Prop 2.4.

## やること

- [ ] Add `OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction`
      with BG notation for the spaces `V_i`, dimensions `n_i`, and the
      endomorphism spaces used in Prop 2.4.
- [ ] Prove the first reusable facts sorry-free, starting with membership and
      periodicity of `V_i` under a primitive root of unity.
- [ ] Keep the public BG §2 file as the traceability surface by importing the
      shared module and updating `notes/bg/s02_representations.md`.
- [ ] Later split out the heavier direct-sum and arithmetic parts (Prop 2.4
      (c)-(k)) into separate commits or issues if needed.

## 完了条件

- Prop 2.4 has a Lean helper package with the needed `V_i`, `E_i`, and
  `E_{i,t}` APIs.
- The package builds without actual `sorry`.
- `lake build OddOrder.BG.Ch1_Preliminary.S02_Representations` and
  `lake build OddOrder.AxiomsCheck` pass at integration points.
- This issue is moved to `issues/closed/` when the Prop 2.4 package is complete
  or the remaining heavy pieces are split into narrower issues.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`
- `notes/bg/s02_representations.md`
- `references/bg/local-analysis.mmd` lines 671-714
