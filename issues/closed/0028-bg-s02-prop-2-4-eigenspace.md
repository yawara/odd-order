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

- [x] Add `OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction`
      with BG notation for the spaces `V_i`, dimensions `n_i`, and the
      endomorphism spaces used in Prop 2.4.
- [x] Prove the first reusable facts sorry-free, starting with membership and
      periodicity of `V_i` under a primitive root of unity.
- [x] Keep the public BG §2 file as the traceability surface by importing the
      shared module and updating `notes/bg/s02_representations.md`.
- [ ] Later split out the heavier direct-sum and arithmetic parts (Prop 2.4
      (c)-(k)) into separate commits or issues if needed.

## 進捗

- 2026-05-26: `V_i`, `n_i`, finite-indexed `V_i`, and periodicity
  `V_{i+h}=V_i`, `n_{i+h}=n_i` added.
- 2026-05-26: `E_i` / `E_{i,t}` entrypoints added as
  `cyclicEndConjEigenspace` and `cyclicHomBlockFin`.  The Prop 2.4(e)
  conjugation calculation is available in scalar-multiplied pointwise form and
  in a span-based map-level form.
- 2026-05-26: Added the inclusion bridge
  `cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_ratio`, plus the
  non-wrapping `t = i + m` specialization.  The remaining Prop 2.4(e)
  work is modular-index bookkeeping and the Prop 2.4(a) span/direct-sum input.
- 2026-05-26: Added modular-index bookkeeping
  `cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_modEq`.  A congruence
  `i + m ≡ t (mod h)` plus `epsilon^h = 1` now feeds the ratio bridge and
  gives the theorem-facing inclusion `E_{i,t} ≤ E_m`.  Remaining work for the
  full Prop. 2.4 package is the Prop. 2.4(a) span/direct-sum input and the
  later direct-sum/dimension identities.
- 2026-05-26: Added the directness half of Prop. 2.4(a) as
  `cyclicEigenspaceFin_iSupIndep`.  The proof combines primitive-root
  injectivity of the eigenvalues with mathlib's eigenspace independence
  theorem; it is not a thin rename.  The remaining Prop. 2.4(a) input is
  span/diagonalization from the finite-order hypothesis on `g`.
- 2026-05-26: Added the span/supremum bridge
  `span_cyclicEigenspaceFinUnion_eq_iSup` and its top-iff form.  Existing block
  calculations use `span (⋃ V_i) = ⊤`, while direct-sum work naturally uses
  `⨆ i, V_i = ⊤`; the two Prop. 2.4(a) spanning inputs are now connected.
  The remaining heavy input is diagonalization from the finite-order hypothesis
  on `g`.
- 2026-05-26: Added the finite-spectrum bridge
  `eigenvalue_eq_power_of_primitiveRoot_of_pow_eq_one`, plus
  `cyclicEigenspaceFin_iSup_eq_top_of_iSup_eigenspace_eq_top_of_pow_eq_one`
  and the span form.  Once a diagonalization argument gives
  `⨆ μ, eigenspace g μ = ⊤`, finite order `g^h = 1` and the primitive root now
  restrict that top span to the displayed BG family `V_0, ..., V_{h-1}`.
  Remaining work is to produce the all-eigenspace top span from the finite-order
  / split-polynomial hypothesis.
- 2026-05-26: Closed the finite-order span input directly as
  `cyclicEigenspaceFin_iSup_eq_top_of_pow_eq_one` and
  `span_cyclicEigenspaceFinUnion_eq_top_of_pow_eq_one`.  The proof factors
  `X^h - 1` as `∏ (X - ε^i)` using the primitive root, then uses coprime
  kernel decomposition for `aeval g`; this replaces the previous placeholder
  "diagonalization" input for Prop. 2.4(a)'s spanning half.
- 2026-05-26: Packaged Prop. 2.4(a) in theorem-facing internal direct-sum form
  as `cyclicEigenspaceFin_isInternal_of_pow_eq_one`.  This combines the
  primitive-root eigenspace independence and the finite-order span theorem via
  mathlib's `DirectSum.IsInternal` API, so downstream block/dimension work can
  consume the displayed decomposition directly.
- 2026-05-26: Started the Prop. 2.4(c)(d) block-matrix layer with
  `cyclicHomBlockFinOfHom`.  Given the internal decomposition from Prop. 2.4(a),
  a linear map `V_i → V_t` is extended by zero on all other displayed
  eigenspaces, and `cyclicHomBlockFinOfHom_mem` proves the resulting
  endomorphism lies in `E_{i,t}`.
- 2026-05-26: Completed the restriction side of the block package:
  `cyclicHomBlockFinToHom`, `cyclicHomBlockFinOfHomLinear`, and
  `cyclicHomBlockFinLinearEquiv` identify `E_{i,t}` with
  `Hom_F(V_i,V_t)` under the internal decomposition.  The dimension statement
  `finrank_cyclicHomBlockFin` now gives Prop. 2.4(d)'s block formula
  `dim E_{i,t} = n_i n_t` for finite-dimensional `V`.  Remaining work for
  Prop. 2.4(c) is the global direct-sum decomposition of `End_F(V)` over all
  `(i,t)` blocks.
- 2026-05-26: Added the block projection entrypoints
  `cyclicHomBlockFinProjectionHom` and `cyclicHomBlockFinProjection`.  For any
  endomorphism `e`, these take the `V_i → V_t` matrix coefficient relative to
  the internal decomposition and extend it back to an element of `E_{i,t}`.
  The apply lemmas on source eigenspaces are in place; the next Prop. 2.4(c)
  step is the reconstruction formula summing these projections over all
  `(i,t)`.

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

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

Prop 2.4 一式 landed: `EigenspaceUnderCyclicAction.lean` + `EigenspaceBlockDecomp.lean` とも実 sorry 0
(検証 2026-07-02)、Thm 2.5 側で消費済。
