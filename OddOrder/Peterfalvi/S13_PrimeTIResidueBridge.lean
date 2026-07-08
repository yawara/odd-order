/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core
import OddOrder.GroupTheory.RepresentationTheory.PrimeTIResidue

/-!
# The `S`-side prime-TI residue grid of the `(13.1)` hypothesis (Peterfalvi §13, issues 9014/9076)

Peterfalvi's §13 `μ`-grid `μ_{ij} ∈ Irr(S)` (the field `S15.Hypothesis.mu`) is, mathematically, the
**prime-TI residue grid** of `S` — the constituents `mu2_ i j` of the cyclic-TI isometry images,
whose theory is ported (constructor-complete, `sorry`-free) in
`OddOrder.GroupTheory.RepresentationTheory.PrimeTIResidue` (`PrimeTIResidueData`,
`PrimeTIResidueData.ofS06Hypothesis`).

The `(13.18)` cross-column facts that `S15_HonestTypeP2A0` isolates as prime-TI pins
(`mu_row0_ne` = row-`0` distinctness, `tauS_mu_row0_diff_support`, `tauS_mu_row0_vanish_on_V`) are
consequences of this residue grid — **not** of the §12 `Hypothesis.muGrid` (which is nominally
gated on the type-III/IV/V = `IsTypeP1` Dade datum, whereas `S` is type-`P2`).  The resolution
recorded here: the residue grid `mu2 = (columnFamily χ₂).mu` is built purely from the certain-type
`S06.Hypothesis` (the `.toHypothesis` part of the §6/§10 machinery), which is **type-uniform** — it
needs only `TypePData S`, `S ∈ maximalSubgroups G`, `IsTypeP S` (which `S` has via `S_typeP2`), and
the Hall coprimality.  So the same `columnFamily.mu` grid that §12 uses for type-`P1` maximals is
available for the type-`P2` group `S`, via `typePData_toS06Hypothesis`, with **no** `IsTypeP1` need.

## Contents

* `Hypothesis.s06S` — the certain-type `S06.Hypothesis ↥S` built from `hyp.Sdata` (type-uniform).
* `Hypothesis.residueS` — the prime-TI residue datum `PrimeTIResidueData ↥S S' q p` for `S`, via
  the `sorry`-free constructor `PrimeTIResidueData.ofS06Hypothesis`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §4 (4.3)/(4.5).
* Coq: `PFsection4.v` (`primeTIred`, `prTIres_irr_cases`), `PFsection13.v` (`S1cases`).
* `issues/9014-primeti-residue-api.md`, `issues/9076-cyclicti-rigidity-dade-crossrel.md`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.RepresentationTheory
open scoped BigOperators

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The certain-type `S06.Hypothesis` of the `S`-side (type-uniform).**  From the type-`P` datum
`hyp.Sdata : TypePData S` and `S`'s maximality + type-`P` status (`IsTypeP S`, obtained from the
type-`P2` field `S_typeP2` — no `IsTypeP1` needed), `typePData_toS06Hypothesis` supplies the §6
certain-type Hypothesis on `↥S`.  This is the common source of the `μ`-grid (`columnFamily.mu`)
that §12 uses for type-`P1` maximals, here made available for the type-`P2` group `S`. -/
noncomputable def Hypothesis.s06S [Finite G] (hyp : Hypothesis (G := G))
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.S :=
  OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis hyp.Sdata hG.odd
    (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hyp.S_maximal
      (OddOrder.BG.Ch4.S14.isTypeP_of_isTypeP2 hyp.S_typeP2) hyp.Sdata)

open scoped FiniteInduce in
/-- **The `S`-side prime-TI residue datum** (Peterfalvi (4.3.b)/(4.5.a), §13 `μ`-grid).  The
residue grid `PrimeTIResidueData ↥S S' |W₁| |W₂|` of `S`, assembled by the `sorry`-free constructor
`PrimeTIResidueData.ofS06Hypothesis` from the type-uniform certain-type Hypothesis `hyp.s06S hG`.
Its `mu2 i j = (columnFamily χ₂).mu i` is exactly the object §12 calls `muGrid` — here for the
type-`P2` group `S`, with no `IsTypeP1` requirement.  The kernel-family subgroup is taken to be `⊤`
(the whole `S'`); every residue `chi_ j` (`j ≠ 0`) is then non-trivial, which is all the downstream
`(13.18)` facts (distinctness, difference support, `V`-value) use.

The `↥S`- and `S'`-side `Fintype`/`Invertible`/`NeZero` data are taken as instance binders (the
standard repo pattern for `↥S`-level character theory, cf. `mkSection11CharacterDataS_honest`);
every one holds unconditionally for the finite group `↥S` and its subgroups, and callers discharge
them by `Fintype.ofFinite`/`invertibleOfNonzero`/`Nat.card_pos.ne'`. -/
noncomputable def Hypothesis.residueS [Finite G] (hyp : Hypothesis (G := G))
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)]
    [Fintype ↥(hyp.s06S hG).K] [Invertible (Nat.card ↥(hyp.s06S hG).K : ℂ)]
    [NeZero (Nat.card ↥(hyp.s06S hG).W1)] [NeZero (Nat.card ↥(hyp.s06S hG).W2)] :
    PrimeTIResidueData ↥hyp.S (hyp.s06S hG).K
      (Nat.card ↥(hyp.s06S hG).W1) (Nat.card ↥(hyp.s06S hG).W2) := by
  haveI : Fintype ↥((hyp.s06S hG).W1 ⊔ (hyp.s06S hG).W2) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥((hyp.s06S hG).W1 ⊔ (hyp.s06S hG).W2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact PrimeTIResidueData.ofS06Hypothesis (hyp.s06S hG) ⊤ le_top

end OddOrder.Peterfalvi.S15
