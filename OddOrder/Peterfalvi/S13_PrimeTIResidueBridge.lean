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

/-! ## Support-set relation: honest `A(S)` `⊆` the deprecated `typePA` over-claim (issue 9008)

The `(13.18)` support pin `S15.Hypothesis.tauS_mu_row0_diff_support` places the `μ`-column difference
support inside `honestTypeP2A0Set = honestTypeP2ASet ∪ V^S`, whose `A`-part
`honestTypeP2ASet = centralizerSupport (M_σ^#) S'` is the **honest** Peterfalvi (8.10)/(13.2.e)
type-`P₂` support (indexed over the *core* `M_σ^#`; issue 9008 Option A).  The old
`typePA = centralizerSupport S^# S' = (S')^#` is the **over-claim** (issue 9008 phantom): it wrongly
includes the Frobenius-complement points `U^#` (where `C_{S_σ} = 1`).

**The pin's support target is therefore correct, and the `(13.18)` route is clean**: the S06
certain-type bound `certainTypeDiffSupported : SupportedClassFunctions (A ∪ V^S) L` is **parametric
in the Hypothesis46 support `A`** — so a `Hypothesis46 (honestTypeP2ASet S) ↥S` (built with lane-c's
`dadeHypS0`, whose support is exactly `honestTypeP2A0Set`) delivers the pin's honest support
`honestTypeP2A0Set` *directly*, with no `typePA0` over-claim in the way.  The remaining pin-2/3
assembly is thus the type-`P₂` `Hypothesis46`-for-`S` (`A = honestTypeP2ASet`, `dade0 = dadeHypS0`),
which lives in lane-c's `S15_HonestTypeP2A0` (it consumes `dadeHypS0`); cf. issue 9076.

The lemma below just records the containment `honest ⊆ over-claim` (immediate from `M_σ ≤ S` and
`centralizerSupport` monotonicity in its source), a sanity check on the two support notions. -/
theorem honestTypeP2ASet_subset_typePA {M : Subgroup G}
    (data : OddOrder.GroupTheory.TypePData M) :
    honestTypeP2ASet M ⊆ OddOrder.GroupTheory.typePA M data := by
  intro y hy
  rw [mem_honestTypeP2ASet] at hy
  obtain ⟨hyM', hy1, x, hx, hxcent⟩ := hy
  simp only [OddOrder.GroupTheory.typePA, OddOrder.GroupTheory.centralizerSupport,
    Set.mem_setOf_eq]
  rw [OddOrder.GroupTheory.sharpSubgroup, Set.mem_diff_singleton] at hx
  exact ⟨hyM', hy1, x, by
    rw [OddOrder.GroupTheory.sharpSubgroup, Set.mem_diff_singleton]
    exact ⟨OddOrder.BG.Ch3.S10.Msigma_le M hx.1, hx.2⟩, hxcent⟩

/-! ## A type-`P₂`-usable `Hypothesis46` constructor (issue 9076, char-endgame shared infra)

`§12.Hypothesis.toHypothesis46` (S12_Core:1088) builds a §6 `Hypothesis46 (typePA M) M` **only from a
`S12.Hypothesis M`**, which requires the type-III/IV/V (`IsTypeP1`) Dade datum — unavailable for a
type-`P₂` maximal.  `hypothesis46OfTypePData` below is the type-uniform version: it takes the Dade
datum (the `A₀`-Dade `dade0` and its `HConjInvariant`) and the (4.6.c) kernel-family subgroup `subH`
**as parameters**, and assembles the `Hypothesis46` from any `TypePData M` (structural `tic`/`W₁`/`W₂`
reconciliation done here, type-uniformly).  A type-`P₂` caller (e.g. lane-c's `S15_HonestTypeP2A0`)
instantiates it with `A = honestTypeP2ASet M`, `dade0 = dadeHypS0`, `subH = M_σ` (for which `A_covers`
holds, `honestTypeP2ASet = ⋃_{z∈M_σ#} C_{S'}(z)#`), unblocking the (13.18) `certainTypeDiffSupported`
/ `certainType_diff_dade_eq` residue facts.  Mirrors `toHypothesis46` field-for-field, with the Dade
and `subH` hoisted to parameters. -/
open scoped FiniteInduce in
noncomputable def hypothesis46OfTypePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (data : OddOrder.GroupTheory.TypePData M) (hodd : Odd (Nat.card G)) (A : Set G)
    (dade0 : OddOrder.Peterfalvi.S04.Hypothesis G
      (A ∪ OddOrder.GroupTheory.conjClassSetIn M
        (OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis data hodd).V) M)
    (hconj : dade0.HConjInvariant)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (subH : Subgroup ↥M) (subH_normal : subH.Normal)
    (W2_le_subH : (data.W2.subgroupOf M) ≤ subH)
    (subH_le_K : subH ≤ (OddOrder.GroupTheory.derivedInG M).subgroupOf M)
    (A_covers : ∀ (hh : ↥M), hh ∈ subH → hh ≠ 1 →
      ∀ (x : ↥M), x ∈ Subgroup.centralizer ({hh} : Set ↥M) ⊓
          (OddOrder.GroupTheory.derivedInG M).subgroupOf M →
        x ≠ 1 → (M.subtype x) ∈ A) :
    OddOrder.Peterfalvi.S06.Hypothesis46 A M :=
  { toHypothesis := OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis data hodd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hM hP data)
    dade := dade0.restrict Set.subset_union_left hAnorm
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis data hodd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le data.W1_le).symm
    tic_W2 :=
      (Subgroup.map_subgroupOf_eq_of_le (OddOrder.Peterfalvi.S12.typePData_W2_le_self data)).symm
    tic_V := rfl
    subH := subH
    subH_normal := subH_normal
    W2_le_subH := W2_le_subH
    subH_le_K := subH_le_K
    A_covers := A_covers
    dade0 := dade0
    tau := dade0.fullDadeIsometryData hconj }

end OddOrder.Peterfalvi.S15
