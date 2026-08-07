/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.TwistedProductComparison
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.UnitaryCoordinates
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.FieldModel
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ModelCenters
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SplitUniqueness
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SquareCosetFiber
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.KSubgroupOrbit
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ActualQuotientAction
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ConjugateSummandSplit
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuotientPlaneModel
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AutomorphismInducedMaps
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AutomorphismClassification
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.TypeBIsomorphicSplit

/-!
# Peterfalvi Appendix III: On Suzuki 2-Groups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, pp. 139--143.

This file is the pure re-export hub for the appendix.  The honest coverage:

* **Definition 1** (Suzuki 2-group) — `OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group`
  (regular cyclic automorphism action on the involutions);
* **Lemma 1(b)** (group from a quadratic map) — `QuadraticExtensions.lean`
  (`QuadraticExtension`);
* **Definitions 2--3** (types A and B) — `Types.lean` (`TypeAData` / `TypeBData`
  with the concrete `TypeAModel` / `TypeBModel` carriers);
* **Higman's theorem** (classification) — proved in
  `OddOrder.Higman.Suzuki2Groups` (`higmanClassification` and the bundled
  `higmanClassification_of_isSuzuki2Group`); per the 2026-07-19 ruling
  (issue 0127 ③) no thin Peterfalvi wrapper is re-stated here — cite the
  Higman theorem directly.  Parts (d)--(e) are represented by the concrete
  invariant two-summand data (`InvariantSummands.lean`, `SplitUniqueness.lean`,
  `QuotientPlaneModel.lean`).

Formalized honestly in the 2026-07-24 campaign (issue 0148; the former
opaque-`Prop` placeholders were deleted as logically vacuous — issue
0127 ②): **Lemma 1(a)** (`QuadraticExtensions.lean`), **Lemma 1(c)/(d)**
(`GroupTheory/CentralExtensionAutomorphisms.lean`), **Lemma 2(a)-(c)**
(`GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`, with the
bundled 2(b) basis and the 2(c) spanning theorem;
`Algebra/QuadraticMapCoordinates.lean` supplies the dimension count),
**Proposition 1** (`FieldModel.lean`), **Proposition 2**
(`AutomorphismInducedMaps.lean` + `AutomorphismClassification.lean`), and
**both directions of the Theorem's part (e)** — the forward implication
"type B ⟹ `P/Z` splits into two isomorphic `𝔽₂[K]`-modules" in
`TypeBIsomorphicSplit.lean` (`IsTypeB.exists_isomorphicOrderQModuleSplit`,
issue 2052), and the converse in
`OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TypeBRecognition`
(`isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube`), which is what
Part II Ch. I §3 Lemma 5 consumes.  With these, every numbered statement of
Appendix III is formalized.
-/
