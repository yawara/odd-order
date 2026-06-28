/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.RepresentationTheory.Irreducible

/-!
# Peterfalvi Section 14: Maximal Subgroups of Type I

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 14, pp. 69--74.

This section proves that every maximal subgroup of type I is a Frobenius group
with kernel `M_F`.  The proof first sets up the Dade isometry attached to a
type-I maximal subgroup, proves orthogonality and constancy properties for the
families `R(chi)`, and then excludes a minimal counterexample with a non-cyclic
Sylow subgroup in `M / M_F`.

The scaffold records the named endpoints (12.1)--(12.17).  The detailed
character decompositions, rho maps, and integer congruence calculations are kept
as proposition fields until the lower-level Dade/rho API is ready for this
maximal-subgroup layer.
-/

namespace OddOrder.Peterfalvi.S14
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (12.1): the type-I hypothesis -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1)**: setup for a maximal subgroup `L` of type I.

`G` is finite (carried as the instance field `finiteG`, the `S12`/`S15`
`FiniteInduce` pattern), so the *genuine* Dade isometry `tau`, the induced family
`Sset = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (`H = L_F`), and the support `A = A(L)`
are honest projections (`Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A`)
rather than unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis
for `A(L)` (supplied by `S10.dadeSupportHypotheses_typeI`), and `hconj` is its
`L`-conjugation invariance; together they build the Dade isometry relative to
`(A(L), L, G)` (Peterfalvi (12.1)). -/
structure Hypothesis (L : Subgroup G) where
  [finiteG : Finite G]
  maximal : L ∈ maximalSubgroups G
  typeI : TypeIData L
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData L (typeIA L typeI)
  hconj : dadeData.dade.HConjInvariant

namespace Hypothesis

/-- Peterfalvi's `H = L_F`. -/
def H {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  hyp.typeI.typeF.H

/-- Peterfalvi's `H'`, represented as an ambient subgroup. -/
def Hprime {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  derivedInG hyp.H

/-- Peterfalvi's ambient `A(L)` set from Definition (8.3). -/
def ambientA {L : Subgroup G} (hyp : Hypothesis L) : Set G :=
  typeIA L hyp.typeI

/-- Peterfalvi's support `A(L)` restricted to `L` (the `supportInSubgroup` of the
ambient `A(L)`), the genuine support of the Dade isometry, no longer an
unconstrained field. -/
def A {L : Subgroup G} (hyp : Hypothesis L) : Set ↥L :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's family `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` of (12.1),
`H = L_F`, induced via the canonical `ClassFunction.induce`.  No longer an
unconstrained field. -/
noncomputable def Sset {L : Subgroup G} (hyp : Hypothesis L) :
    Set (ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  { χ | ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      χ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) }

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A(L), L, G)` of (12.1), pinned to
the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data `dadeData`.
No longer an unconstrained field. -/
noncomputable def tau {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)

end Hypothesis

/-- Conjugation transports the centralizer of a singleton:
`g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)` (S14-local copy of the S12 helper; pure group theory). -/
private theorem conj_smul_centralizer_singleton (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group

/-- **Peterfalvi (8.14)/(8.15)**: the support kernel `R(x)` is `M`-conjugation equivariant
(S14-local copy of the S12 helper).  `supportKernel M M X (g x g⁻¹) = g · supportKernel M M X x`
for `g ∈ M` and `X` an `M`-invariant set. -/
private theorem supportKernel_conj_invariant {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    supportKernel M M X (g * x * g⁻¹) = MulAut.conj g • supportKernel M M X x := by
  have hMfix : MulAut.conj g • maxNilpotentNormalHall M = maxNilpotentNormalHall M :=
    conj_smul_eq_self_of_mem_normalizer
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hg)
  have hMself : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← hMself]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  have hescape : (g * x * g⁻¹ ∈ escapingCentralizerSet M X)
      ↔ (x ∈ escapingCentralizerSet M X) := by
    simp only [escapingCentralizerSet, Set.mem_setOf_eq, hmem, hcent]
  unfold supportKernel
  by_cases hx : x ∈ escapingCentralizerSet M X
  · rw [if_pos (hescape.mpr hx), if_pos hx, Subgroup.smul_inf, hMfix,
        conj_smul_centralizer_singleton]
  · rw [if_neg (fun h => hx (hescape.mp h)), if_neg hx, Subgroup.smul_bot]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1), existence**: every type-I maximal subgroup `L` carries the
(12.1) Hypothesis.  The Dade isometry, induced family, and support are the genuine
`S07.dadeIntegralCharacterMap`, `Sset`, and `A(L)`; the only inputs are the (8.15)
Dade support data (`S10.dadeSupportHypotheses_typeI`) and the conjugation
invariance `hconj` of the support kernels (a (8.14)/(8.15) fact).  Mirrors
`S12.exists_hypothesis_of_typeIIIorIVorV`. -/
theorem exists_typeI_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (hType : IsTypeI L) :
    Nonempty (Hypothesis L) := by
  obtain ⟨data⟩ := hType
  obtain ⟨dadeData⟩ :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeI hG hL data).1
  -- (8.14)/(8.15): the support kernels `R(a)` are `L`-conjugation invariant.
  have hconj : dadeData.dade.HConjInvariant := by
    intro a l
    simp only [dadeData.H_eq_supportKernel]
    refine supportKernel_conj_invariant l.2 ?_
    exact ⟨fun h => by simpa using dadeData.dade.L_normalizes_A l⁻¹ h,
      fun h => dadeData.dade.L_normalizes_A l h⟩
  exact ⟨{ maximal := hL, typeI := data, dadeData := dadeData, hconj := hconj }⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The type-I family `S = {Ind_H^L θ}` is closed under complex conjugation**
(Peterfalvi §12, the `χ̄ ∈ S` input to (12.2.b)): for `χ = Ind_H^L θ ∈ S` with
`θ ∈ Irr H`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_H^L θ̄` (`ClassFunction.induce_conj`),
and `θ̄` is again a non-trivial irreducible of `H = L_F`. -/
theorem Sset_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Sset := by
  classical
  intro φ hφ
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

/-! ## (12.2): character decomposition and Dade domain -/

/-- **Peterfalvi (12.2)**, genuine carrier: the constituent decomposition of `χ ∈ S`.
`S(χ) = constituents` is the (finite, nonempty) set of irreducible constituents of `χ`, all of
equal degree ((12.2.a)), each non-real (so `φ ≠ φ̄`) and supported in `A(L) ∪ {1}` (so the
differences `φ − φ̄` lie in the Dade domain `A(L)`, feeding (12.2.b) `R1`/`Rset`). -/
structure CharacterDecompositionData {L : Subgroup G} (hyp : Hypothesis L)
    (chi : ClassFunction ↥L ℂ) where
  chi_mem : chi ∈ hyp.Sset
  /-- `S(χ)`: the irreducible constituents of `χ`. -/
  constituents : Finset (IrreducibleCharacter ↥L)
  constituents_nonempty : constituents.Nonempty
  /-- (12.2.a): `χ` is the multiplicity-one sum of its constituents. -/
  decomp : chi = ∑ φ ∈ constituents, (φ : ClassFunction ↥L ℂ)
  /-- (12.2.a): the constituents share a common degree. -/
  equal_degree : ∀ φ ∈ constituents, ∀ φ' ∈ constituents,
    ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
  /-- Each constituent is non-real, so `φ ≠ φ̄` and `φ − φ̄ ≠ 0` ((12.2.b)). -/
  not_real : ∀ φ ∈ constituents, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)
  /-- (12.2.a): each constituent is supported in `A(L) ∪ {1}` (`H ⊄ Ker φ` (1.5.a), then (1.2)),
  so each difference `φ − φ̄` is supported in the Dade domain `A(L)`. -/
  supported : ∀ φ ∈ constituents, (φ : ClassFunction ↥L ℂ).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}

/-- **Type-`F` induced-character constituent structure** (Peterfalvi (8.2.c) + (1.2)/(1.5.a) +
(1.7.c) + Clifford; a faithful §8 obligation — the deep content is type-`F` character theory living
in §8, not §12).  For a type-I maximal `L` and `χ = Ind_H^L θ ∈ S` (`θ ∈ Irr H ∖ {1}`), `χ` is the
multiplicity-one sum of a nonempty finite set of equal-degree, non-real irreducible constituents,
each supported in `A(L) ∪ {1}`.  Body = §8 type-`F` Clifford theory: (8.2.c) `I(θ) ∩ U ⊆ U₁` +
induced-degree (1.7.c) for the equal degree, `(Res_H φ, 1_H) = 0` (1.5.a) + (1.2) for the support. -/
theorem typeI_induced_char_constituents [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ S : Finset (IrreducibleCharacter ↥L), S.Nonempty ∧
      chi = ∑ φ ∈ S, (φ : ClassFunction ↥L ℂ) ∧
      (∀ φ ∈ S, ∀ φ' ∈ S, ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
        = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1) ∧
      (∀ φ ∈ S, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)) ∧
      (∀ φ ∈ S, (φ : ClassFunction ↥L ℂ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}) := by
  sorry

/-- **Peterfalvi (12.2.a)**: each `χ ∈ S` decomposes (multiplicity one) into irreducible
constituents of equal degree, each non-real and supported in `A(L) ∪ {1}`.  The §12 assembly:
unpack the type-`F` constituent structure (`typeI_induced_char_constituents`) into the genuine
`CharacterDecompositionData` carrier — whose R(χ) blocks of (12.2.b) then come from `R1`/`Rset`.  The deep type-`F` Clifford content ((8.2.c) inertia +
(1.7.c)/(1.5.a)/(1.2)) is isolated in the obligation, keeping this assembly `sorry`-free. -/
theorem character_decomposition_and_dade_domain [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi, data.chi_mem = hchi := by
  obtain ⟨S, hne, hdecomp, hdeg, hreal, hsupp⟩ := typeI_induced_char_constituents hyp hchi
  exact ⟨⟨hchi, S, hne, hdecomp, hdeg, hreal, hsupp⟩, rfl⟩

/-! ## (12.2.b): the orthonormal Dade-image families `R₁(φ)` and `R(χ)` -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The constituent difference `φ̄ − φ` (`φ ∈ S(χ)`) is supported in the Dade domain
`A(L) = supportInSubgroup (A(L)) L`: `φ` is supported in `A(L) ∪ {1}` (`data.supported`), `φ̄` has
the same support (conjugation preserves it), and the value at `1` cancels (`φ̄(1) = φ(1)`, the
degree being a real natural number).  Feeds the difference-support constructor
`S07.dadeOrthonormalCharacterImageFamilyOfDiff` for the orthonormal block `R₁(φ)`. -/
theorem R1_diffsupp {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  haveI := hyp.finiteG
  have hsupp_eq : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)) x ≠ 0 := hx
  have hxsupp : x ∈ (φ : ClassFunction ↥L ℂ).support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases data.supported φ hφ hxsupp with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
    exact hx0 (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hd, star_natCast, sub_self])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the underlying difference image `{μ_φ, ν_φ, ε}` of `R₁(φ)`.**  The Dade
`CharacterDifferenceImage` of the constituent `φ ∈ S(χ)`: `(φ − φ̄)^τ = ε·(μ_φ − ν_φ)`.  `R1` is its
`toOrthonormalImage`; the raw `{μ_φ, ν_φ}` data is what the cross-`L` (4.1) orthogonality of (12.3)
consumes (`S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across`). -/
noncomputable def R1cdi {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    hyp.dadeData.dade hyp.hconj φ (data.not_real φ hφ) (R1_diffsupp data hφ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the orthonormal block `R₁(φ)`**: for a constituent `φ ∈ S(χ)`, the
orthonormal Dade-image family of `φ − φ̄`, "an orthonormal subset of `ℤ[Irr G]` of cardinality 2"
with `(φ − φ̄)^τ = ∑_{α ∈ R₁(φ)} α` (the `image_eq` field).  The `toOrthonormalImage` of the
difference image `R1cdi`.  This is the `imageFamily` the `CharacterPsiDecomposition` engine of
(12.4)/(12.5) consumes; its underlying `{μ, ν}` feeds the (12.3) cross-`L` orthogonality. -/
noncomputable def R1 {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  (R1cdi data hφ).toOrthonormalImage

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b)**: `R(χ) = ⋃_{φ ∈ S(χ)} R₁(φ)`, the union of the two-element orthonormal
Dade-image blocks `R₁(φ) = (R1 data hφ).imageSet` of the constituents.  A class function `ψ` is
"orthogonal to `R(χ)`" iff `⟨ψ, α⟩ = 0` for every `α ∈ R₁(φ)`, `φ ∈ S(χ)` ((12.4)/(12.5)). -/
noncomputable def Rset {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) : Set (ClassFunction G ℂ) :=
  haveI := hyp.finiteG
  {α | ∃ (φ : IrreducibleCharacter ↥L) (_hφ : φ ∈ data.constituents),
    α ∈ (R1 data _hφ).imageSet}

/-! ## (12.3)--(12.5): orthogonality and rho-constancy -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3), the geometric obligation** ((8.18.c) + (5.9) + Dade support).  For
non-conjugate type-I maximal subgroups `L₁, L₂` and constituents `φ₁ ∈ S(χ₁)`, `φ₂ ∈ S(χ₂)`, the
Dade difference-images `(φ₁−φ̄₁)^{τ₁}` and `(φ₂−φ̄₂)^{τ₂}` are orthogonal: their supports lie in the
disjoint thickened Dade domains `Ã(L₁)`, `Ã₁(L₂)` (Peterfalvi (8.18.c),
`S10.support_mutual_exclusion`).  A faithful §8/§10 obligation — the thickened-support theory and
its mutual-exclusion are §10 (lane-d/f) territory; (12.3) cites this as the geometric input to the
(4.1) assembly. -/
theorem nonconjugate_diffImage_inner_zero {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (_hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (_hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups `L₁, L₂`, the families
`R(χ₁) = Rset data1` and `R(χ₂) = Rset data2` are mutually orthogonal.

Proof: a member `α ∈ R(χ₁)` lies in `R₁(φ₁) = (R1cdi data1 hφ₁).toOrthonormalImage` for some
constituent `φ₁`, and likewise `β ∈ R₁(φ₂)`.  The cross-`L` (4.1) orthogonality
`toOrthonormalImage_inner_eq_zero_across` reduces `⟨α, β⟩ = 0` to the orthogonality of the signed
differences `⟨(φ₁−φ̄₁)^{τ₁}, (φ₂−φ̄₂)^{τ₂}⟩ = 0` (`image_eq_signedDifference`), which is the geometric
obligation `nonconjugate_diffImage_inner_zero` ((8.18.c): the supports lie in disjoint `Ã(L₁)`,
`Ã₁(L₂)`). -/
theorem nonconjugate_typeI_R_orthogonal {L1 L2 : Subgroup G} [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ∀ α ∈ Rset data1, ∀ β ∈ Rset data2, ClassFunction.inner α β = 0 := by
  intro α hαm β hβm
  obtain ⟨φ1, hφ1, hα⟩ := hαm
  obtain ⟨φ2, hφ2, hβ⟩ := hβm
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ1) (R1cdi data2 hφ2) ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ1),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference (R1cdi data2 hφ2)]
  exact nonconjugate_diffImage_inner_zero hyp1 hyp2 hnot_conj data1 hφ1 data2 hφ2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)/(12.5) input**: each member `χ = Ind_H^L θ` of `S` vanishes on `L − H`.
`H = L_F` is normal in `L` (`maxNilpotentNormalHall_subgroupOf_normal`, the Fitting subgroup `L_F`),
so the induced character is supported on `H` (`ClassFunction.induce_eq_zero_of_not_mem_normal`).  This
is the "the elements of `S` vanish on `L − H`" step of the constant-on-coset conclusions of
(12.4)/(12.5) (`ψ(xh) = β(xh) + γ(xh) = γ(x)`, the `β ∈ ℂ[S]` part vanishing off `H`). -/
theorem Sset_vanishes_off_H {L : Subgroup G} (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.Sset) {x : ↥L} (hxH : (x : G) ∉ hyp.H) : χ x = 0 := by
  haveI := hyp.finiteG
  obtain ⟨θ, _, hχ_eq⟩ := hχ
  haveI hnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  have hxmem : x ∉ (hyp.typeI.typeF.H).subgroupOf L :=
    fun hcon => hxH (Subgroup.mem_subgroupOf.mp hcon)
  rw [hχ_eq]
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hxmem

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (a)** (coherence): for constituents `φ₁, φ₂ ∈ S(χ)`, the Dade image
`(φ₁ − φ₂)^τ` lies in `ℤ[R(χ)]`.  By (1.4) the four-element set `{φ₁, φ₂, φ̄₁, φ̄₂}` is coherent, so
`τ` maps its difference lattice into the integral span of `R(χ) = ⋃ R₁(φ)`.  A faithful §5/§1
obligation (the coherence-extension content of (1.4)/(5.x), char-theory). -/
theorem constituent_diff_tau_mem_span {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (_h₁ : φ₁ ∈ dχ.constituents) (_h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) ∈
      Submodule.span ℤ (Rset dχ) := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (b)** ([Is] 7.7 + (8.12.c) + [Is] 6.2): for constituents `φ₁, φ₂ ∈ S(χ)`,
the Dade isometry acts as induction on the difference, `(φ₁ − φ₂)^τ = Ind_L^G(φ₁ − φ₂)`.  By [Is] 6.2
`Res_H φᵢ` is the conjugate-sum of `θ`, so `Supp(φ₁ − φ₂) ⊆ A(L) − H^#`, a TI-subset of `G` with
normalizer `L` by (8.12.c); on a TI-supported function the Dade isometry coincides with `Ind_L^G`
([Is] 7.7).  A faithful §8/[Is] obligation. -/
theorem constituent_diff_tau_eq_induce {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (_h₁ : φ₁ ∈ dχ.constituents) (_h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) =
      ClassFunction.induce L ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), coherence → coefficient-equality bridge** (genuine).  If `ψ ⊥ R(χ)`, then
`Res_L ψ` has the *same* coefficient on every constituent of `χ`: `⟨Res_L ψ, φ₁⟩ = ⟨Res_L ψ, φ₂⟩`
for `φ₁, φ₂ ∈ S(χ)`.  Proof: `⟨Res_L ψ, φ₁ − φ₂⟩ = ⟨ψ, Ind_L^G(φ₁ − φ₂)⟩ = ⟨ψ, (φ₁ − φ₂)^τ⟩`
(Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry + pin (b)), and this is `0` because
`(φ₁ − φ₂)^τ ∈ ℤ[R(χ)]` (pin (a)) and `ψ ⊥ R(χ)` (`inner_eq_zero_of_mem_zSpan`).  This is the genuine
content by which `ψ ⊥ R(χ)` forces the `∪S(χ)`-part of `Res_L ψ` to be `β = ∑_χ c_χ·χ ∈ ℂ[S]`. -/
theorem Sset_coeff_equal {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {psi : ClassFunction G ℂ} (horth : ∀ α ∈ Rset dχ, ClassFunction.inner psi α = 0)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.inner (ClassFunction.restrict L psi) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₂ : ClassFunction ↥L ℂ) := by
  haveI := hyp.finiteG
  set f : ClassFunction ↥L ℂ :=
    (φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ) with hf
  -- `⟨ψ, τ f⟩ = 0`: `τ f ∈ ℤ[R(χ)]` (pin a) and `ψ ⊥ R(χ)`.
  have hψτ : ClassFunction.inner psi (hyp.tau f) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan horth
      (constituent_diff_tau_mem_span hyp dχ h₁ h₂)
  -- `⟨f, Res_L ψ⟩ = ⟨Ind_L^G f, ψ⟩ = ⟨τ f, ψ⟩ = star⟨ψ, τ f⟩ = 0`.
  have hfres : ClassFunction.inner f (ClassFunction.restrict L psi) = 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict L f psi,
      ← constituent_diff_tau_eq_induce hyp dχ h₁ h₂,
      inner_conj_symm psi (hyp.tau f), hψτ, star_zero]
  -- `⟨Res_L ψ, f⟩ = star⟨f, Res_L ψ⟩ = 0`, then split the difference.
  have hresf : ClassFunction.inner (ClassFunction.restrict L psi) f = 0 := by
    rw [inner_conj_symm f (ClassFunction.restrict L psi), hfres, star_zero]
  rw [hf, ClassFunction.inner_sub_right] at hresf
  exact sub_eq_zero.mp hresf

/-- Evaluation of a finite sum of class functions at a point (the eval map is additive). -/
private theorem classFunction_sum_apply {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) (g : H) : (∑ i ∈ s, F i) g = ∑ i ∈ s, (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

/-- The "`H ⊆ ker φ`" predicate: the Fitting subgroup `H = L_F` lies in the character kernel of the
irreducible character `φ` of `L`.  The `γ`-components of `Res_L ψ` in (12.4) are exactly those `φ`
with `InHKernel`; they are constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`). -/
def InHKernel {L : Subgroup G} (hyp : Hypothesis L) (φ : IrreducibleCharacter ↥L) : Prop :=
  ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) ⊆
    OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (c)** ([Is] 6.2 capturing + (1.5.a)/(1.2)): the off-kernel irreducible
characters `{φ : H ⊄ ker φ}` partition into the constituent-sets `S(χ)`, `χ ∈ S`.  By [Is] 6.2,
`H ⊄ ker φ ⟹ Res_H φ` has a non-trivial constituent `θ`, so `φ ∈ S(Ind_H^L θ)`; the orbit `θ`
determines `χ = Ind θ` uniquely ((1.5.a)/(1.2)), so the `S(χ)` are pairwise disjoint and cover the
off-kernel irreducibles.  This is the genuine cross-section content (the [Is] 6.2 partition); the
`β`-vanishing regroup `Sset_offKernel_vanishes_off_H` is proved from it. -/
theorem exists_offKernel_constituent_partition {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) :
    ∃ parts : Finset {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset},
      Finset.univ.filter (fun φ => ¬ InHKernel hyp φ) =
        parts.biUnion (fun χ => (data χ.1 χ.2).constituents) ∧
      (↑parts : Set {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset}).PairwiseDisjoint
        (fun χ => (data χ.1 χ.2).constituents) := by
  sorry

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the off-kernel direction** (genuine): every constituent `φ ∈ S(χ)` of a
member `χ = Ind_H^L θ ∈ S` (`θ ≠ 1_H`) is off-kernel, `H ⊄ ker φ`.  If `H ⊆ ker φ` then `Res_H φ` is
constant `= φ(1)` on `H` (`= φ(1)·1_H`), so by Frobenius `⟨χ, φ⟩ = ⟨θ, Res_H φ⟩ = star(φ(1))·⟨θ, 1_H⟩
= 0` (`θ ≠ 1_H`); but `φ` a constituent of `χ` gives `⟨χ, φ⟩ = 1`.  This is the `⊇` inclusion
`S(χ) ⊆ {φ : H ⊄ ker φ}` of the partition `exists_offKernel_constituent_partition`. -/
theorem constituents_not_inHKernel {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hχ : chi ∈ hyp.Sset) (dχ : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ dχ.constituents) : ¬ InHKernel hyp φ := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := hχ
  intro hker
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  -- `Res_K φ = φ(1) · 1_K` (since `H ⊆ ker φ`, `φ` is constant `= φ(1)` on `K`).
  have hrestrict : ClassFunction.restrict K (φ : ClassFunction ↥L ℂ)
      = OddOrder.Peterfalvi.S03.characterDegree (φ : ClassFunction ↥L ℂ) •
        (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    ext k
    rw [ClassFunction.restrict_apply, ClassFunction.smul_apply]
    have hmem : (↑k : ↥L) ∈ OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ) :=
      hker k.2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
    simp only [hmem, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply, mul_one]
  -- `⟨χ, φ⟩ = ⟨θ, Res_K φ⟩ = star(φ(1)) · ⟨θ, 1_K⟩ = 0` (`θ ≠ 1_K`).
  have hzero : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 0 := by
    rw [hchi_eq, ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
      OddOrder.RepresentationTheory.inner_smul_right, irreducibleCharacter_inner, if_neg hθ_ne,
      mul_zero]
  -- `⟨χ, φ⟩ = 1` (multiplicity-one constituent), contradiction.
  have hone : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 1 := by
    rw [dχ.decomp, inner_sum_left,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg hne]),
      irreducibleCharacter_inner, if_pos rfl]
  rw [hone] at hzero
  exact one_ne_zero hzero

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the capturing direction** (genuine): every off-kernel irreducible `φ`
(`H ⊄ ker φ`) is a constituent of some `χ ∈ S`.  By `exists_constituent_not_subset_characterKernel`
([Is] 6.5 / constituent transitivity), `Res_H φ` has a constituent `θ ≠ 1_H`; then `χ := Ind_H^L θ ∈ S`
and `⟨φ, χ⟩ = ⟨Res_H φ, θ⟩ ≠ 0` (Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry), so
`φ ∈ S(χ)`.  This is the `⊆` inclusion `{φ : H ⊄ ker φ} ⊆ ⋃ S(χ)` of the partition
`exists_offKernel_constituent_partition`. -/
theorem not_inHKernel_imp_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} (hφ : ¬ InHKernel hyp φ) :
    ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hlo, hθker⟩ :=
    exists_constituent_not_subset_characterKernel
      (le_refl ((hyp.typeI.typeF.H).subgroupOf L)) φ hφ
  -- `θ ≠ 1`: else `K = K.subgroupOf K ⊆ ker θ = univ`, contradicting `hθker`.
  have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rintro rfl
    exact hθker (by
      simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction, Set.subset_univ])
  -- `θ` is a genuine constituent of `Res_K φ`.
  have hlo' : ClassFunction.inner
      (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ≠ 0 := by
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  -- `⟨φ, Ind_K θ⟩ = ⟨Res_K φ, θ⟩ ≠ 0` (Frobenius + conjugate symmetry).
  have hinner_ne : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    exact hlo'
  by_contra hnotin
  apply hinner_ne
  rw [(data _ ⟨θ, hθ_ne, rfl⟩).decomp, inner_sum_right]
  refine Finset.sum_eq_zero fun φ' hφ' => ?_
  have hne : φ ≠ φ' := by rintro rfl; exact hnotin hφ'
  rw [irreducibleCharacter_inner, if_neg hne]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the off-kernel regroup** (genuine, from the [Is] 6.2 partition pin): the
off-kernel Fourier part `β = ∑_{φ : H ⊄ ker φ} ⟨Res_L ψ, φ⟩·φ` of `Res_L ψ` vanishes on `L − H`.
Regroup the off-kernel irreducibles by the partition into `S(χ)`
(`exists_offKernel_constituent_partition`); on each `S(χ)` the coefficient `⟨Res_L ψ, φ⟩` is constant
(`Sset_coeff_equal`, from `ψ ⊥ R(χ)`), so the `S(χ)`-block is `c_χ·∑_{φ ∈ S(χ)} φ = c_χ·χ`
(`decomp`), which vanishes at `g ∈ L − H` (`Sset_vanishes_off_H`). -/
theorem Sset_offKernel_vanishes_off_H {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {g : ↥L} (hg : (g : G) ∉ hyp.H) :
    (∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
      ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g = 0 := by
  obtain ⟨parts, hpart, hdisj⟩ := exists_offKernel_constituent_partition hyp data
  rw [classFunction_sum_apply, hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun χ _ => ?_
  -- The `S(χ)`-block: `∑_{φ ∈ S(χ)} ⟨Res_L ψ, φ⟩ · φ(g) = c_χ · χ(g) = 0`.
  obtain ⟨φ₀, hφ₀⟩ := (data χ.1 χ.2).constituents_nonempty
  have hblock : ∑ φ ∈ (data χ.1 χ.2).constituents,
      (ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₀ : ClassFunction ↥L ℂ) *
        ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply,
      Sset_coeff_equal hyp (data χ.1 χ.2) (horth χ.1 χ.2) hφ hφ₀]
  have hdecomp : ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g = χ.1 g := by
    rw [← classFunction_sum_apply, ← (data χ.1 χ.2).decomp]
  rw [hblock, hdecomp, Sset_vanishes_off_H hyp χ.2 hg, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)**: a class function `ψ` orthogonal to every type-I family `R(χ)` (`χ ∈ S`) is
constant on each coset `xH` with `x ∈ L − H`.

Proof: write `Res_L ψ = γ + β` by the Fourier expansion (`sum_inner_irreducibleCharacter_smul`),
splitting `Irr L` into `{H ⊆ ker φ}` (= `γ`) and `{H ⊄ ker φ}` (= `β`).  The kernel part `γ` is
constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`, each `φ` with `H ⊆ ker φ`); the
off-kernel part `β` vanishes on `L − H` (`Sset_offKernel_vanishes_off_H`: by [Is] 6.2 + the
coefficient bridge `Sset_coeff_equal`, `β ∈ ℂ[S]` vanishes off `H`).  Hence
`ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`. -/
theorem orthogonal_character_constant_on_coset {L : Subgroup G} [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  haveI := hyp.finiteG
  classical
  intro h hh
  have hhL : h ∈ L := hyp.typeI.typeF.H_le hh
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  set hL : ↥L := ⟨h, hhL⟩ with hhLdef
  set gf : ClassFunction ↥L ℂ := ClassFunction.restrict L psi with hgf
  -- Fourier split of `Res_L ψ = γ + β`.
  set γ : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hγ
  set β : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hβ
  have hsplit : gf = γ + β := by
    rw [hγ, hβ, Finset.sum_filter_add_sum_filter_not]
    exact (sum_inner_irreducibleCharacter_smul gf).symm
  -- `hL` lies in `H` (as a subgroup of `L`).
  have hLmem : hL ∈ ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) :=
    Subgroup.mem_subgroupOf.mpr hh
  -- `γ` is constant on the `H`-coset `xL · hL`.
  have hγconst : γ (xL * hL) = γ xL := by
    rw [hγ, classFunction_sum_apply, classFunction_sum_apply]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply,
      apply_mul_eq_of_mem_characterKernel φ.isIrreducible
        ((Finset.mem_filter.mp hφ).2 hLmem) xL]
  -- `β` vanishes on `L − H` (off-kernel part is in `ℂ[S]`).
  have hxhH : x * h ∉ hyp.H := fun hcon => hxH (by
    have hmem : x * h * h⁻¹ ∈ hyp.H := mul_mem hcon (inv_mem hh)
    rwa [mul_inv_cancel_right] at hmem)
  have hβxh : β (xL * hL) = 0 := by
    rw [hβ]
    exact Sset_offKernel_vanishes_off_H hyp data horth (g := xL * hL)
      (by rw [Subgroup.coe_mul]; exact hxhH)
  have hβx : β xL = 0 := by
    rw [hβ]; exact Sset_offKernel_vanishes_off_H hyp data horth (g := xL) hxH
  -- Assemble: `ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`.
  have key : gf (xL * hL) = gf xL := by
    simp only [hsplit, ClassFunction.add_apply, hγconst, hβxh, hβx, add_zero]
  have hgxh : gf (xL * hL) = psi (x * h) := by
    rw [hgf, ClassFunction.restrict_apply, Subgroup.coe_mul]
  have hgx : gf xL = psi x := by rw [hgf, ClassFunction.restrict_apply]
  rw [← hgxh, ← hgx]; exact key

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5)**: after the rho-reduction, a class function `ψ` orthogonal
to every type-I family `R(χ)` is constant on `H − H'`.  The orthogonality hypothesis
is the genuine `⟨ψ, α⟩ = 0` for `α ∈ R(χ)`, no longer an opaque field. -/
theorem rho_constant_on_H_minus_Hprime {L : Subgroup G} [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0) :
    ∀ h : G, h ∈ hyp.H → h ∉ hyp.Hprime → psi h = psi 1 := by
  sorry

/-! ## (12.6)--(12.7): type-I Frobenius structure -/

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Structural input for Peterfalvi (12.6) — Frobenius case.**

When `L` is already Frobenius with kernel `H`, the Sibley Dade setup of (6.8) takes its
case-(c1) (Frobenius) branch, so a `SibleyTarget` for `(τ, S, A)` is available.  Exhibiting it
is the remaining structural obligation; once it lands, and once lane B supplies the (6.8) proof
body of `S08.sibleySetup_is_coherent`, `frobenius_typeI_coherent` is unconditional. -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := sorry

/-- **Peterfalvi (12.6)**: if `L` is already Frobenius with kernel `H`, then the
family `S` is coherent.

Wired to the (6.8) capstone through the coherence-wiring bridge: given the Frobenius-case
structural witness `sibleyTarget_frobI`, coherence is exactly (6.8).  The proof carries no
`sorry` of its own; its gaps are `sibleyTarget_frobI` (Frobenius structure) and (6.8) (lane B). -/
theorem frobenius_typeI_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) :=
  CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hfrob)

/-- **Frobenius realization bridge for type `F`** (the (8.2.b) consumer behind (12.10)/(12.16)).
A type-`F` maximal `M` whose complement `U` is a **Z-group** (every Sylow subgroup cyclic) is a
Frobenius group with kernel `M_F`.  By `IsZGroup.exponent_eq_card`, `|U| = exp(U)`, so Peterfalvi
(8.2.b) (`S10.typeF_frobenius_of_card_eq_exponent`) applies.  `sorry`-free + axiom-clean. -/
theorem typeF_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hZ : _root_.IsZGroup ↥data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  haveI := hZ
  exact OddOrder.Peterfalvi.S10.typeF_frobenius_of_card_eq_exponent data
    (_root_.IsZGroup.exponent_eq_card (G := ↥data.U)).symm

/-- **Frobenius realization bridge for type I** (the `kernel = M_F` form consumed by (12.10)).
A type-I maximal `M` whose complement `U = M/M_F` is a **Z-group** is a Frobenius group with kernel
`M_F = typeF.H`.  Wraps `typeF_frobenius_of_isZGroup_complement` on `data.typeF`. -/
theorem typeI_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeIData M) (hZ : _root_.IsZGroup ↥data.typeF.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) :=
  typeF_frobenius_of_isZGroup_complement data.typeF hZ

/-! The headline **(12.7)** (`typeI_frobenius`: every type-I maximal is a Frobenius group with
kernel `M_F`) is proved at the end of this section, after the minimal-counterexample machinery
(12.8)–(12.16) on which it depends: the `π = ∅` case is the easy direction
`typeI_frobenius_of_pi_empty`, and `π = ∅` itself (`pi_empty`) is the content of (12.16). -/

/-! ## (12.8)--(12.12): minimal counterexample analysis -/

/-- **Peterfalvi (12.8), the prime set `π`**: `q ∈ π` when some type-`I` maximal subgroup `M'`
has a **noncyclic Sylow `q`-subgroup in `M' / M'_F`**.  Encoded by a Sylow `q`-subgroup `P ≤ M'`
(`q`-group with `q ∤ [M' : P]`) that is noncyclic and satisfies `q ∣ [M' : M'_F]` — so `P` is not
contained in `M'_F` and its image in `M'/M'_F` is a noncyclic Sylow `q`-subgroup. -/
def InPi (q : ℕ) : Prop :=
  ∃ M' : Subgroup G, M' ∈ maximalSubgroups G ∧ IsTypeI M' ∧
    ∃ P : Subgroup G, P ≤ M' ∧ IsPGroup q ↥P ∧ ¬ q ∣ P.relIndex M' ∧
      ¬ IsCyclic ↥P ∧ q ∣ (maxNilpotentNormalHall M').relIndex M'

/-- **Peterfalvi (12.7), the `π = ∅` case** (the first sentence of the proof of (12.16)): if the
prime set `π` of (12.8) is empty, every type-I maximal `M` is a Frobenius group with kernel `M_F`.

`M_F = H` is a normal Hall subgroup (8.11), so its complement `U` has `|U| = [M : M_F]` coprime
to `|M_F|`; hence every Sylow `q`-subgroup `P` of `U` has full `q`-order in `M`.  Were `P`
noncyclic, its `M`-image `P.map U.subtype` would be a noncyclic Sylow `q`-subgroup of `M` with
`q ∣ [M : M_F]`, i.e. `q ∈ π` — contradicting `π = ∅`.  So `U` is a Z-group and the bridge
`typeI_frobenius_of_isZGroup_complement` applies.  Its only gap is the (8.11) Hall input. -/
theorem typeI_frobenius_of_pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hpi : ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) := by
  classical
  refine typeI_frobenius_of_isZGroup_complement data ?_
  set H := data.typeF.H with hHdef
  set U := data.typeF.U with hUdef
  have hUM : U ≤ M := data.typeF.U_le
  -- `[M : H] = |U|` (complement) and `|M| = |H| * |U|`.
  have hrel : H.relIndex M = Nat.card ↥U := by
    rw [Subgroup.relIndex, data.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hMcard : Nat.card ↥M = Nat.card ↥H * Nat.card ↥U := by
    rw [← (H.subgroupOf M).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv,
      ← Subgroup.relIndex, hrel]
  -- `H = M_F` is Hall in `G` (8.11), so `|H|` is coprime to `[M : H] = |U|`.
  have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hM
    (tau := PeterfalviType.I) ⟨data⟩).1
  rw [← data.typeF.H_eq] at hHall
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥U) :=
    hHall.coprime_index.coprime_dvd_right
      (hrel ▸ Subgroup.relIndex_dvd_index_of_le data.typeF.H_le)
  -- Every Sylow `q`-subgroup `P` of `U` is cyclic.
  refine ⟨fun q hq P => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hnc
  -- `P ≠ ⊥`, so `q ∣ |U|`, and `|H|` has no `q`.
  have hPcard : Nat.card ↥(P : Subgroup ↥U) = q ^ (Nat.card ↥U).factorization q :=
    P.card_eq_multiplicity
  have hPne : (P : Subgroup ↥U) ≠ ⊥ := fun h => hnc (h ▸ inferInstance)
  have hfacU_pos : 0 < (Nat.card ↥U).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥U).factorization q) with h0 | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hPcard, h0, pow_zero])) hPne
    · exact h
  have hqU : q ∣ Nat.card ↥U := Nat.dvd_of_factorization_pos hfacU_pos.ne'
  have hHfac0 : (Nat.card ↥H).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_right hqU).symm)
  have hMfac : (Nat.card ↥M).factorization q = (Nat.card ↥U).factorization q := by
    rw [hMcard, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
      (Nat.card_pos (α := ↥U)).ne', Finsupp.add_apply, hHfac0, zero_add]
  -- `Pm = P.map U.subtype`: a noncyclic `q`-subgroup of `M` of full `q`-order.
  set Pm := (P : Subgroup ↥U).map U.subtype with hPmdef
  have hPmM : Pm ≤ M := (Subgroup.map_subtype_le _).trans hUM
  have hPmcard : Nat.card ↥Pm = q ^ (Nat.card ↥M).factorization q := by
    rw [hPmdef, Subgroup.card_map_of_injective U.subtype_injective, hPcard, hMfac]
  have hPmsub : Nat.card ↥(Pm.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmM).toEquiv, hPmcard]
  have hPmP : IsPGroup q ↥Pm := (IsPGroup.iff_card).mpr ⟨_, hPmcard⟩
  refine hpi q hq ⟨M, hM, ⟨data⟩, Pm, hPmM, hPmP, ?_, ?_, ?_⟩
  · -- `¬ q ∣ Pm.relIndex M`: `Pm` has the full `q`-part of `|M|`.
    rw [Subgroup.relIndex]
    intro hdvd
    have hsplit : (Nat.card ↥M).factorization q
        = (Nat.card ↥(Pm.subgroupOf M)).factorization q
          + ((Pm.subgroupOf M).index).factorization q := by
      conv_lhs => rw [← (Pm.subgroupOf M).card_mul_index]
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥(Pm.subgroupOf M))).ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply]
    rw [hPmsub, hq.factorization_pow, Finsupp.single_eq_same] at hsplit
    exact absurd (Nat.Prime.factorization_pos_of_dvd hq Subgroup.index_ne_zero_of_finite hdvd)
      (by omega)
  · -- `¬ IsCyclic ↥Pm`: `Pm ≃* P` and `P` is noncyclic.
    intro hc
    haveI := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.surjective)
  · -- `q ∣ (maxNilpotentNormalHall M).relIndex M = [M : H] = |U|`.
    rw [← data.typeF.H_eq, hrel]; exact hqU

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7).

`M` is a type-`I` maximal subgroup whose Fitting kernel is `K = M_F` (`K' = [K, K]`), and `P₀`
is a Sylow `p`-subgroup of `M` that is noncyclic with `p ∣ [M : M_F]` (so the image of `P₀` in
`M/M_F` is a noncyclic Sylow `p`-subgroup, i.e. `p ∈ π`); `p` is the smallest element of `π`. -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInG K
  P0_le_M : P0 ≤ M
  /-- `P₀` is a `p`-group… -/
  P0_pGroup : IsPGroup p ↥P0
  /-- …and a Sylow `p`-subgroup of `M` (`p ∤ [M : P₀]`). -/
  P0_sylow : ¬ p ∣ P0.relIndex M
  /-- The Sylow `p`-subgroup of `M/M_F` is noncyclic (so `P₀` is noncyclic). -/
  P0_noncyclic : ¬ IsCyclic ↥P0
  /-- …and `p ∣ [M : M_F]` (so `P₀ ⊄ M_F`; together with the Hall property this gives `p ∤ |M_F|`). -/
  p_dvd_index : p ∣ K.relIndex M
  /-- `p` is the smallest prime in `π`. -/
  minimal_p : ∀ q : ℕ, q.Prime → InPi (G := G) q → p ≤ q

/-- **Peterfalvi (12.8), existence of the minimal counterexample.**  If the prime set `π` of
(12.8) is nonempty, its least element `p = Nat.find` yields a `CounterexampleHypothesis`: the
`InPi` witness for `p` supplies a type-`I` maximal `M'` with a noncyclic Sylow `p`-subgroup `P₀`
that has `p ∣ [M' : M'_F]`, and `Nat.find_min'` records that `p` is the smallest prime in `π`.

This is the well-ordering step that opens the minimal-counterexample analysis of (12.7); it is
`§8`-free and unconditional (its only input is `InPi` for some prime). -/
theorem exists_counterexampleHypothesis [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (h : ∃ q : ℕ, q.Prime ∧ InPi (G := G) q) :
    Nonempty (CounterexampleHypothesis (G := G)) := by
  classical
  obtain ⟨hp_prime, M', hM', hM'I, P, hPle, hPpg, hPsyl, hPnc, hqdvd⟩ := Nat.find_spec h
  exact ⟨{
    p := Nat.find h
    p_prime := hp_prime
    M := M'
    K := maxNilpotentNormalHall M'
    Kprime := derivedInG (maxNilpotentNormalHall M')
    P0 := P
    M_maximal := hM'
    M_typeI := hM'I
    K_eq_MF := rfl
    Kprime_eq := rfl
    P0_le_M := hPle
    P0_pGroup := hPpg
    P0_sylow := hPsyl
    P0_noncyclic := hPnc
    p_dvd_index := hqdvd
    minimal_p := fun q hq hqInPi => Nat.find_min' h ⟨hq, hqInPi⟩ }⟩

/-- The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully.

`L` is the second maximal subgroup with `P₀ ⊆ L_s` (`L_s = mainSubgroup L L_type`); `x` is the
order-`p` element of `Ω₁(P₀)^#` whose centralizer in `K = M_F` escapes `K'`, controls `N_G(⟨x⟩)`,
and escapes `L`. -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  /-- Peterfalvi's type attached to `L` (so `L_s = mainSubgroup L L_type`). -/
  L_type : PeterfalviType
  L_hasType : HasPeterfalviType L_type L
  /-- `P₀ ⊆ L_s`. -/
  P0_le_Ls : ctr.P0 ≤ mainSubgroup L L_type
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  /-- `x ∈ Ω₁(P₀)^#`: `x` has order dividing `p`. -/
  x_mem_omega1 : x ^ ctr.p = 1
  /-- `C_K(x) ⊄ K'` (equivalently `C_{K/K'}(x) ≠ 1`). -/
  CKx_not_le_Kprime : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)
  /-- `N_G(⟨x⟩) ⊆ M`. -/
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  /-- `C_G(x) ⊄ L`. -/
  centralizer_x_not_le_L : ¬ (Subgroup.centralizer ({x} : Set G) ≤ L)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Group-theoretic core of Peterfalvi (12.9)** (fully general, `§8`-independent).

If a **noncyclic abelian** group `A` acts **coprimely** on a finite group `K` whose
abelianization is nontrivial (`[K, K] ≠ K`), then some **nontrivial** `a ∈ A` has a fixed
subgroup `C_K(a)` that is *not* contained in the derived subgroup `[K, K]`.

This is the abstract content of the centralizer step of (12.9): there Peterfalvi takes
`A = Ω₁(P₀)` (elementary abelian of rank `2`, hence noncyclic) acting by conjugation on
`K = M_F`, with `[K, K] = K'`, and concludes `∃ x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`
(equivalently `C_{K/K'}(x) ≠ 1`).

Proof.  `[K, K]` is characteristic, hence `A`-invariant, so `A` acts on the quotient
`K / [K, K]`.  By **BG Proposition 1.16(1)** (Isaacs 6.21,
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) applied to that quotient action,
`K / [K, K] = ⟨ C_{K/[K,K]}(a) ∣ a ≠ 1 ⟩`.  Since `K / [K, K]` is nontrivial, some
`a ≠ 1` has `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset lifts, by the coprime fixed-point
lifting (**Isaacs Cor 3.28**, `coprime_fixedPoints_quotient`), to an element of `C_K(a)`
outside `[K, K]`. -/
theorem exists_ne_one_actionFixedBy_not_le_commutator
    {A K : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hCop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hSolv : IsSolvable A ∨ IsSolvable K) (hNC : ¬ IsCyclic A)
    (hK' : commutator K ≠ ⊤) :
    ∃ a : A, a ≠ 1 ∧ ¬ (Ch06.actionFixedBy φ a ≤ commutator K) := by
  classical
  -- `[K, K]` is characteristic, hence `A`-invariant; let `ψ` be the induced quotient action.
  have hN_inv : Ch03.IsAInvariant φ (commutator K) := Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  -- Coprimality on the quotient: `|K / [K,K]|` divides `|K|`.
  have hCopQ : Nat.Coprime (Nat.card A) (Nat.card (K ⧸ commutator K)) :=
    hCop.coprime_dvd_right (commutator K).card_quotient_dvd_card
  -- BG 1.16(1) on the quotient action: the nontrivial fixed-point closure is everything.
  have htop : Ch06.nontrivialActionFixedByClosure ψ = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic' ψ hCopQ hNC
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a, a ≠ 1 → C_K(a) ≤ [K, K]`.  Show the quotient closure is `⊥`.
  have hquot_bot : Ch06.nontrivialActionFixedByClosure ψ ≤ ⊥ := by
    rw [Ch06.nontrivialActionFixedByClosure_le_iff]
    intro a ha q hq
    -- `q ∈ C_{K/K'}(a)`: `q` is fixed by every element of `⟨a⟩`.
    have hq_zp : q ∈ Ch06.actionFixedPoints ψ (Subgroup.zpowers a) := by
      rw [← Ch06.actionFixedBy_eq_actionFixedPoints_zpowers]; exact hq
    -- Lift `q = mk' g` and assemble the coset-fixed hypothesis on `⟨a⟩`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) q
    have hg_fix : ∀ b : ↥(Subgroup.zpowers a), ∃ n ∈ commutator K, φ (b : A) g = g * n := by
      intro b
      have hb := (Ch06.mem_actionFixedPoints.mp hq_zp) b
      rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
      exact ⟨g⁻¹ * φ (b : A) g, by simpa using (commutator K).inv_mem hb, by group⟩
    -- Coprime fixed-point lifting (Isaacs Cor 3.28) on the cyclic group `⟨a⟩`.
    have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card K) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hSolv' : IsSolvable ↥(Subgroup.zpowers a) ∨ IsSolvable K := by
      rcases hSolv with hA | hK
      · haveI := hA; exact Or.inl inferInstance
      · exact Or.inr hK
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      Ch04.coprime_fixedPoints_quotient hCop' hSolv'
        (Ch03.IsAInvariant.of_characteristic (φ.comp (Subgroup.zpowers a).subtype)) hg_fix
    -- `c` is fixed by `a`, hence `c ∈ C_K(a) ≤ [K, K]` by `hcon`.
    have hca : φ a c = c := hc_fix ⟨a, Subgroup.mem_zpowers a⟩
    have hc_mem : c ∈ commutator K := hcon a ha (Ch06.mem_actionFixedBy.mpr hca)
    -- Then `g = c * n⁻¹ ∈ [K, K]`, so the coset `q = mk' g` is trivial.
    have hg_mem : g ∈ commutator K := by
      have : g = c * n⁻¹ := by rw [hcn]; group
      rw [this]; exact (commutator K).mul_mem hc_mem ((commutator K).inv_mem hn)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg_mem
  -- `⊤ ≤ ⊥` forces `K / [K, K]` trivial, i.e. `[K, K] = ⊤`, contradicting `hK'`.
  have hbot : (⊤ : Subgroup (K ⧸ commutator K)) = ⊥ := le_bot_iff.mp (htop ▸ hquot_bot)
  apply hK'
  rw [Subgroup.eq_top_iff']
  intro k
  have hk1 : QuotientGroup.mk' (commutator K) k ∈ (⊥ : Subgroup (K ⧸ commutator K)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact hk1

/-- **Conjugation form of the (12.9) centralizer core** (ambient subgroups, directly the
form consumed by (12.9)).  If a **noncyclic abelian** subgroup `A ≤ G` normalizes a finite
subgroup `K` of **coprime** order whose abelianization is nontrivial (`⁅K, K⁆ ≠ K`), then
some `x ∈ A`, `x ≠ 1`, has `C_K(x) = C_G(x) ⊓ K` **not** contained in `⁅K, K⁆`.

Specialization of `exists_ne_one_actionFixedBy_not_le_commutator` to the conjugation action
`A → MulAut K` (`Subgroup.normalizerMonoidHom`): the abstract fixed subgroup `C_K(a)` becomes
`C_G(a) ⊓ K` and `commutator ↥K` maps to `⁅K, K⁆` under `K.subtype`. -/
theorem exists_mem_centralizer_inf_not_le_commutator
    {A K : Subgroup G} [Finite ↥A] [IsMulCommutative ↥A] [Finite ↥K]
    (hAK : A ≤ Subgroup.normalizer K) (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K))
    (hSolv : IsSolvable ↥A ∨ IsSolvable ↥K) (hNC : ¬ IsCyclic ↥A) (hK' : ⁅K, K⁆ ≠ K) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 ∧ ¬ (Subgroup.centralizer {x} ⊓ K ≤ ⁅K, K⁆) := by
  classical
  -- The conjugation action `φ : A → MulAut K` and the `K.subtype`-image of `[↥K, ↥K]`.
  set φ : ↥A →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hAK)
    with hφ
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hg; exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, htop_map]
  -- `[↥K, ↥K] ≠ ⊤`: else its `K.subtype`-image would be `⁅K, K⁆ = K`.
  have hKtop : commutator ↥K ≠ ⊤ := by
    intro h; exact hK' (by rw [← hmap, h, htop_map])
  obtain ⟨a, ha_ne, hnle⟩ :=
    exists_ne_one_actionFixedBy_not_le_commutator φ hCop hSolv hNC hKtop
  -- Translate the abstract conclusion to ambient subgroups.
  obtain ⟨n, hn_fix, hn_out⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨(a : G), a.2, fun h => ha_ne (Subtype.ext h), SetLike.not_le_iff_exists.mpr
    ⟨(n : G), ?_, ?_⟩⟩
  · -- `n ∈ C_G(a) ⊓ K`: `a` conjugates `n` to itself, and `n ∈ K`.
    rw [Ch06.mem_actionFixedBy] at hn_fix
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      congrArg (Subtype.val) hn_fix
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, n.2⟩
    rintro y rfl
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `n ∉ ⁅K, K⁆`: else `n ∈ [↥K, ↥K]`, contradicting `hn_out`.
    rw [← hmap]
    intro hmem
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hmem
    exact hn_out (by rw [show n = m from Subtype.ext hmn.symm]; exact hm)

/-- **Peterfalvi (12.9), the order-`p` centralizer witness** (the genuine, `§8`-free heart of
(12.9)).  Given the counterexample data with `P₀` abelian, coprime to `K = M_F`, normalizing `K`,
and `K` not perfect, there is an element `x ∈ Ω₁(P₀)^#` (order dividing `p`) with `C_K(x) ⊄ K'`.

Proof: apply the centralizer core `exists_mem_centralizer_inf_not_le_commutator` to the abelian
noncyclic `P₀` acting by conjugation on `K`, yielding `y ∈ P₀^#` with `C_K(y) ⊄ K'`; then pass to
the order-`p` power `x = y ^ (|y| / p)` — its centralizer contains `C_K(y)`, so still escapes `K'`. -/
theorem exists_orderP_centralizer_witness [Finite G]
    (ctr : CounterexampleHypothesis (G := G))
    (habelian : IsMulCommutative ↥ctr.P0)
    (hcoprime : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K))
    (hP0_norm : ctr.P0 ≤ Subgroup.normalizer ctr.K)
    (hKperfect : ⁅ctr.K, ctr.K⁆ ≠ ctr.K) :
    ∃ x : G, x ∈ ctr.P0 ∧ x ≠ 1 ∧ x ^ ctr.p = 1 ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI := habelian
  haveI : Group.IsNilpotent ↥ctr.P0 := ctr.P0_pGroup.isNilpotent
  -- `K' = ⁅K, K⁆`.
  have hKprime : ctr.Kprime = ⁅ctr.K, ctr.K⁆ :=
    ctr.Kprime_eq.trans (Subgroup.map_subtype_commutator ctr.K)
  -- Centralizer core (A = P₀, abelian noncyclic, coprime, normalizing K, K not perfect).
  obtain ⟨y, hyP0, hy_ne, hy_cent⟩ :=
    exists_mem_centralizer_inf_not_le_commutator (A := ctr.P0) (K := ctr.K)
      hP0_norm hcoprime (Or.inl inferInstance) ctr.P0_noncyclic hKperfect
  -- `y` has `p`-power order `p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ctr.P0_pGroup) ⟨y, hyP0⟩
  have hoy : orderOf y = ctr.p ^ k :=
    (orderOf_injective ctr.P0.subtype ctr.P0.subtype_injective ⟨y, hyP0⟩).trans hk
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hoy; exact absurd hoy hy_ne
    · exact h
  have hp_dvd : ctr.p ∣ orderOf y := hoy ▸ dvd_pow_self ctr.p (by omega)
  have hord_pos : 0 < orderOf y := hoy ▸ pow_pos ctr.p_prime.pos k
  -- The order-`p` power `x = y ^ (|y| / p)`.
  set n := orderOf y / ctr.p with hn
  have hnp : n * ctr.p = orderOf y := Nat.div_mul_cancel hp_dvd
  have hn_pos : 0 < n := by
    rw [hn]; exact Nat.div_pos (Nat.le_of_dvd hord_pos hp_dvd) ctr.p_prime.pos
  have hn_lt : n < orderOf y := by
    rw [hn]; exact Nat.div_lt_self hord_pos ctr.p_prime.one_lt
  refine ⟨y ^ n, ctr.P0.pow_mem hyP0 n, ?_, ?_, ?_⟩
  · -- `y ^ n ≠ 1`: else `|y| ∣ n < |y|`, impossible.
    rw [Ne, ← orderOf_dvd_iff_pow_eq_one]
    exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  · -- `(y ^ n) ^ p = y ^ (n * p) = y ^ |y| = 1`.
    rw [← pow_mul, hnp, pow_orderOf_eq_one]
  · -- `C_K(y ^ n) ⊇ C_K(y) ⊄ K'`.
    rw [hKprime]
    intro hle
    apply hy_cent
    refine le_trans (inf_le_inf_right ctr.K ?_) hle
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro z rfl
    exact Commute.pow_left (hg y rfl) n

/-- **Peterfalvi (12.9), the `(κ ∪ σ)ᶜ`-Hall complement obligation** — the precise BG §16
(Proposition 16.1) bridge behind `(8.12.a)`.  For the type-`I` minimal-counterexample `M`, the
Sylow `p`-subgroup `P₀` (with `p ∣ [M : M_F]`, hence `p ∤ |M_F|` as `M_F` is Hall) lies in a
`(κ(M) ∪ σ(M))ᶜ`-Hall subgroup `U ≤ M`.

*Why this is the gate (and not `(8.12.a)` itself).*  BG Theorem B(1)
(`theoremB_U_sylow_abelian_rank_le_two`, already **proved** in the repo) says every Sylow of such
a `U` is abelian of rank `≤ 2`; the only missing input is producing the complement `U`.  The
type-`I` complement of `M_F` is `π(M_F)ᶜ`-Hall (immediate from `M_F` being a normal Hall
subgroup), and Proposition 16.1's type-`I` classification (`κ(M) = ∅` and `M_F = M_σ`)
identifies `π(M_F)ᶜ` with `(κ ∪ σ)ᶜ`.

**Proof (issue 2016).**  Write `M = ctr.M`, `p = ctr.p`.  Proposition 16.1 (clause (a)) gives
`κ(M) = ∅` for the type-`I` `M`, and (clause (f)) gives `M_F = M_σ`.  Since `M_F` is `π(M_F)`-Hall
in `M` (`maxNilpotentNormalHall_isHall`) and `p ∣ [M : M_F]`, we have `p ∤ |M_F| = |M_σ|`.  As
`M_σ` is `σ(M)`-Hall in `G` (`S10.isHall_Msigma_Malpha`), `p ∤ |M_σ|` forces `p ∉ σ(M)` (else
`p` would divide the `σ`-part `|M_σ|` of `|G|`).  With `κ(M) = ∅` this gives `p ∈ (κ ∪ σ)ᶜ`, so
the `p`-group `P₀` is a `(κ ∪ σ)ᶜ`-subgroup of the solvable `M` and Hall's theorem D
(`Ch03.hall_D`) places it in a `(κ ∪ σ)ᶜ`-Hall subgroup `U` of `M`.  The only `§16`-gated inputs
are the cited Proposition 16.1 type-`I` clauses (lane-f frontier, issue 8015). -/
theorem exists_sigmaKappaCompl_hall_ge_P0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ U : Subgroup G, ctr.P0 ≤ U ∧ U ≤ ctr.M ∧
      Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ)
        (U.subgroupOf ctr.M) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI hMsolv : IsSolvable ↥ctr.M := hG.solvable_of_mem_maximalSubgroups ctr.M_maximal
  -- κ(M) = ∅ (Type I ⟹ Type F, Prop 16.1 clause (a)).
  have hκ : OddOrder.BG.Ch4.S14.kappa ctr.M = ∅ :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).1.mp ctr.M_typeI
  -- M_F = M_σ (Prop 16.1 clause (f)).
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  -- `p ∤ |M_F|`: `M_F` is `π(M_F)`-Hall in `M` and `p ∣ [M : M_F]`.
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  -- `p ∣ |G|` (`p ∣ [M : M_F] ∣ |M| ∣ |G|`).
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  -- `p ∉ σ(M)`: `M_σ` is `σ(M)`-Hall in `G`, and `p ∤ |M_σ|` with `p ∣ |G| = |M_σ|·[G:M_σ]`.
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  have hp_not_sigma : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
    intro hpσ
    refine hp_not_dvd_Mσ ?_
    have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
        * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
      rw [Subgroup.card_mul_index]; exact hp_dvd_G
    rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
    · exact h
    · exact absurd hpσ (hσHall.index_no_pi ctr.p
        (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))
  -- `p ∈ (κ ∪ σ)ᶜ`.
  have hp_compl : ctr.p ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M
      ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hκ ▸ Set.notMem_empty ctr.p, hp_not_sigma⟩
  -- Every prime divisor of `|P₀|` (a `p`-power) is `p ∈ (κ ∪ σ)ᶜ`; place `P₀` via Hall D.
  have hcond : ∀ q ∈ (Nat.card ↥(ctr.P0.subgroupOf ctr.M)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ctr.P0_pGroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv, hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hp_compl
  obtain ⟨V, hVhall, hPV⟩ := Ch03.hall_D (G := ↥ctr.M) hcond
  refine ⟨V.map ctr.M.subtype, ?_, Subgroup.map_subtype_le V, ?_⟩
  · rw [show ctr.P0 = (ctr.P0.subgroupOf ctr.M).map ctr.M.subtype from
      (Subgroup.map_subgroupOf_eq_of_le ctr.P0_le_M).symm]
    exact Subgroup.map_mono hPV
  · have hUeq : (V.map ctr.M.subtype).subgroupOf ctr.M = V :=
      Subgroup.comap_map_eq_self_of_injective ctr.M.subtype_injective V
    rw [hUeq]; exact hVhall

/-- **Peterfalvi (12.9), the rank-two structure for `P₀`** = `(8.12.a)`.

Every Sylow subgroup of the type-`I` complement `U` (`M = M_F ⋊ U`) is abelian of rank `≤ 2`
(BG **Theorem B(1)**, `theoremB_U_sylow_abelian_rank_le_two`, **proved**); applied to the Sylow
`p`-subgroup `P₀ ≤ U` and combined with `P₀` noncyclic (Hypothesis `(12.8)`, `ctr.P0_noncyclic`,
giving `2 ≤ rank P₀` via `two_le_rank_of_noncyclic_pSubgroup`), this forces `P₀` abelian of rank
exactly `2`.

The substantive content (Theorem B(1) + the rank lower bound) is therefore **wired and
load-bearing**; the only remaining gap is the `(κ ∪ σ)ᶜ`-Hall complement obligation
`exists_sigmaKappaCompl_hall_ge_P0` (the BG §16 / Proposition 16.1 bridge, lane-f).

(The other structural inputs `P₀` coprime to `K`, `P₀ ≤ N_G(K)`, `⁅K, K⁆ ≠ K` are discharged in
`exists_rankTwoWitness` from `(8.11)` [`M_F` Hall] and `M_F ◁ M` nilpotent + nontrivial.) -/
theorem counterexample_P0_K_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨U, hP0U, hUM, hU⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  obtain ⟨hrank_le, habelian⟩ :=
    OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two hG ctr.M_maximal hUM hU
      ctr.p ctr.p_prime ctr.P0 hP0U ctr.P0_pGroup
  exact ⟨habelian, le_antisymm hrank_le
    (OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup ctr.P0_noncyclic)⟩

/-- A `p`-Hall subgroup `H` (its order having only `p`-primary divisors among `π = π(|H|)`) with
`p ∣ |H|` contains a Sylow `p`-subgroup of the ambient group `G`.

A Sylow `p`-subgroup `R` of `↥H` maps to a subgroup `R.map H.subtype ≤ H` of `G` of the same
order `p ^ v_p(|H|)`.  Since `H` is Hall, `p ∤ [G : H]`, so `v_p(|H|) = v_p(|G|)`; hence
`R.map H.subtype` is a Sylow `p`-subgroup of `G` contained in `H`. -/
theorem exists_sylow_le_of_hall [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H) (hp : p ∣ Nat.card ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  -- A Sylow `p`-subgroup `R` of `↥H`.
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥H))
  -- The `p`-multiplicity of `|H|` equals that of `|G|`, because `H` is Hall and `p ∣ |H|`.
  have hfact : (Nat.card ↥H).factorization p = (Nat.card G).factorization p := by
    have hcop : Nat.Coprime (Nat.card ↥H) H.index := hHall.coprime_index
    have hp_notdvd : ¬ p ∣ H.index :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hp)
    have hidx0 : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_notdvd
    have hsplit : (Nat.card G).factorization p =
        (Nat.card ↥H).factorization p + H.index.factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
        Subgroup.index_ne_zero_of_finite]
      rfl
    rw [hsplit, hidx0, add_zero]
  -- `R.map H.subtype` is a `p ^ v_p(|G|)`-subgroup of `G`, i.e. a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(R : Subgroup ↥H) = p ^ (Nat.card G).factorization p := by
    rw [R.card_eq_multiplicity, hfact]
  have hcardQ : Nat.card ↥((R : Subgroup ↥H).map H.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardR]
  exact ⟨Sylow.ofCard ((R : Subgroup ↥H).map H.subtype) hcardQ,
    by rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi (12.9), existence of the second maximal `L`** — a §8 obligation
(`(8.17.a)` `bgTheoremE_cover_data`: `p ∈ π(G)` is covered by some `π((M_i)_s)`, giving a maximal
`L` with `p ∣ |L_s|`; then `(8.11)`/`L_s ⊇ Sylow_p(G)` and Sylow conjugation place `P₀ ⊆ L_s`). -/
theorem exists_second_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ (L : Subgroup G) (Lt : PeterfalviType), L ∈ maximalSubgroups G ∧ L ≠ ctr.M ∧
      HasPeterfalviType Lt L ∧ ctr.P0 ≤ mainSubgroup L Lt := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∈ π(G)`: `p ∣ [M : M_F] ∣ |M| ∣ |G|`.
  have hp_in_G : ctr.p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨ctr.p_prime, ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ctr.p_dvd_index (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card ctr.M))
    exact Subgroup.relIndex_dvd_card (H := ctr.K) (K := ctr.M)
  -- `p ∤ |M_F| = |K|`: `(8.11)` makes `M_F` Hall, and `p ∣ [M : M_F] ∣ [G : M_F]`.
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hpK : ¬ ctr.p ∣ Nat.card ↥ctr.K := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    exact ctr.p_prime.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm)
  -- BG Theorem E cover data: `p ∈ π((M_i)_s)` for some representative `M_i = L₀`.  Repackage the
  -- representative as genuine local variables `L₀, Lt` (so we may later `cases` on the type label).
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨i, hi⟩ := (data.primeFactors_cover ctr.p ctr.p_prime).mp hp_in_G
  obtain ⟨L₀, Lt, hL₀max, hL₀typed, hi'⟩ :
      ∃ (L₀ : Subgroup G) (Lt : PeterfalviType), L₀ ∈ maximalSubgroups G ∧
        HasPeterfalviType Lt L₀ ∧
        ctr.p ∈ (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors :=
    ⟨data.reps i, data.tau i, data.maximal i, data.typed i, hi⟩
  have hp_Ls : ctr.p ∣ Nat.card ↥(mainSubgroup L₀ Lt) := (Nat.mem_primeFactors.mp hi').2.1
  -- `(8.11)`: `(L₀)_s` is Hall, hence contains a Sylow `p`-subgroup `Q` of `G`.
  have hLsHall : Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors
      (mainSubgroup L₀ Lt) :=
    (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hL₀max hL₀typed).2
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_hall hLsHall hp_Ls
  -- A Sylow `p`-subgroup `Q'` of `G` over `P₀`, then conjugate `Q` to `Q'`.
  obtain ⟨Q', hQ'le⟩ := ctr.P0_pGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  -- `P₀ ≤ Q' = ↑(g • Q) = conj g • ↑Q ≤ conj g • (L₀)_s`.
  have hP0_le : ctr.P0 ≤ MulAut.conj g • mainSubgroup L₀ Lt := by
    refine hQ'le.trans ?_
    have hQ'eq : (Q' : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [hQ'eq]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQle
  -- Assemble: `L = conj g • L₀`, type `Lt`, with `P₀ ⊆ (conj g • L₀)_s`.
  refine ⟨MulAut.conj g • L₀, Lt, mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL₀max)), ?_,
    hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed, ?_⟩
  · -- `conj g • L₀ ≠ M`: else `M` has type `Lt`; if `Lt = I` then `p ∣ |K|` (false), else `M` is
    -- both type I and non-I (false).
    rintro hEq
    have hMtype : HasPeterfalviType Lt ctr.M :=
      hEq ▸ hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed
    -- transport the divisibility `p ∣ |(L₀)_s|` to `p ∣ |M_s|`.
    have hp_Ms : ctr.p ∣ Nat.card ↥(mainSubgroup ctr.M Lt) := by
      have hcard : Nat.card ↥(mainSubgroup ctr.M Lt) = Nat.card ↥(mainSubgroup L₀ Lt) := by
        rw [← hEq, ← mainSubgroup_pointwise_smul, card_pointwise_smul]
      rw [hcard]; exact hp_Ls
    -- `ctr.M` has type `Lt` and type I.  Type `I` forces `p ∣ |K|` (false); any non-I label
    -- makes `ctr.M` non-I, contradicting type I via `not_isTypeI_of_isTypeNonI`.
    have hMnotNonI : ¬ IsTypeNonI ctr.M := fun h =>
      OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG ctr.M_maximal h ctr.M_typeI
    cases Lt with
    | I => exact hpK (by rw [ctr.K_eq_MF]; exact hp_Ms)
    | II => exact hMnotNonI (Or.inl hMtype)
    | III => exact hMnotNonI (Or.inr (Or.inl hMtype))
    | IV => exact hMnotNonI (Or.inr (Or.inr (Or.inl hMtype)))
    | V => exact hMnotNonI (Or.inr (Or.inr (Or.inr hMtype)))
  · -- `P₀ ⊆ mainSubgroup (conj g • L₀) Lt`.
    rw [← mainSubgroup_pointwise_smul]; exact hP0_le

/-- **Peterfalvi (12.9), centralizer control** — **discharged** from `(8.12.b)`
(`typeI_or_typeII_centralizer_unique`) + `G` simple.

Applying `(8.12.b)` with `U = M` and `X = {x}` (`x ∈ M^#`, and `C_K(x) ⊄ K'` gives
`M_F ⊓ C_G(x) ≠ 1`) yields `C_G(x) ≤ M` together with `IsUniquelyMaximal (C_G(x))` — `M` is the
*unique* maximal subgroup over `C_G(x)`.  Hence: `N_G(⟨x⟩) ⊇ C_G(x)` is a proper subgroup
(`⟨x⟩` is a proper nontrivial subgroup of the nonabelian simple `G`, so not normal), so it lies
in a maximal subgroup over `C_G(x)`, which must be `M`; and any maximal `L ≠ M` cannot contain
`C_G(x)`. -/
theorem centralizer_control_of_CKx [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ ctr.M)
    {Lt : PeterfalviType} (hLt : HasPeterfalviType Lt L) (hPL : ctr.P0 ≤ mainSubgroup L Lt)
    {x : G} (hx : x ∈ ctr.P0) (hxne : x ≠ 1)
    (hCKx : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)) :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ≤ L) := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  have hMcoatom : IsCoatom ctr.M := ctr.M_maximal
  have hLcoatom : IsCoatom L := hL
  have hxM : x ∈ ctr.M := ctr.P0_le_M hx
  -- `M_F ⊓ C_G(x) ≠ ⊥` from `C_K(x) ⊄ K'`.
  have hCKne : maxNilpotentNormalHall ctr.M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot; apply hCKx; rw [ctr.K_eq_MF, inf_comm, hbot]; exact bot_le
  have hxsharp : ({x} : Set G) ⊆ sharpSubgroup ctr.M := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨hxM, fun h => hxne (Set.mem_singleton_iff.mp h)⟩
  -- (8.12.b): `C_G(x) ≤ M` and uniquely maximal.
  obtain ⟨hCxleM, huniq⟩ := OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique hG
    ctr.M_maximal (Or.inl ctr.M_typeI) (le_refl ctr.M) ({x} : Set G) (Set.singleton_nonempty x)
    hxsharp hCKne
  refine ⟨?_, fun hCxleL => hLM (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hLcoatom hCxleL).symm⟩
  -- `N_G(⟨x⟩) ⊆ M`.
  have hCx_le_Nx : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure]; exact Subgroup.centralizer_le_normalizer _
  have hcl_le_M : Subgroup.closure ({x} : Set G) ≤ ctr.M := Subgroup.closure_le _ |>.mpr (by
    simpa using hxM)
  have hNx_lt : Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
    · exact hxne (by simpa [hb] using Subgroup.subset_closure (Set.mem_singleton x))
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hcl_le_M))
  obtain ⟨N, hNco, hNx_le_N⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNx_lt
  exact hNx_le_N.trans (le_of_eq
    (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hNco (hCx_le_Nx.trans hNx_le_N)).symm)

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup.

Honest assembly: the structural inputs `(8.12.a)`/`(8.11)` (`counterexample_P0_K_structure`) give
`P₀` abelian of rank `2`, coprime to `K`, normalizing `K`, with `K` not perfect; the genuine
`§8`-free `exists_orderP_centralizer_witness` then produces the order-`p` element `x` with
`C_K(x) ⊄ K'`; `(8.17.a)` (`exists_second_maximal`) supplies `L`; and `(8.12.b)`
(`centralizer_control_of_CKx`) the centralizer conditions. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr) := by
  obtain ⟨hab, hrank⟩ := counterexample_P0_K_structure hG ctr
  refine ⟨hab, hrank, ?_⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `P₀` coprime to `K`: `(8.11)` makes `M_F` Hall (`p ∤ |M_F|` from `p ∣ [M : M_F] ∣ [G : M_F]`).
  have hcop : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K) := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    have hcop_p : Nat.Coprime ctr.p (Nat.card ↥ctr.K) :=
      Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn]; exact hcop_p.pow_left n
  -- `P₀ ≤ N_G(K)` from `M_F ◁ M` (`maxNilpotentNormalHall_le_normalizer`).
  have hnorm : ctr.P0 ≤ Subgroup.normalizer ctr.K := by
    rw [ctr.K_eq_MF]
    exact ctr.P0_le_M.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M)
  -- `⁅K, K⁆ ≠ K`: `K = M_F` is nilpotent and nontrivial, hence not perfect.
  have hperf : ⁅ctr.K, ctr.K⁆ ≠ ctr.K := by
    obtain ⟨tiData⟩ := ctr.M_typeI
    have hKH : ctr.K = tiData.typeF.H := ctr.K_eq_MF.trans tiData.typeF.H_eq.symm
    haveI : Nontrivial ↥ctr.K :=
      ctr.K.nontrivial_iff_ne_bot.mpr (hKH ▸ tiData.typeF.H_nontrivial)
    haveI : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hlt : commutator ↥ctr.K < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ctr.K)
    intro hEq
    have htop_map : (⊤ : Subgroup ↥ctr.K).map ctr.K.subtype = ctr.K := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    exact hlt.ne (Subgroup.map_injective ctr.K.subtype_injective
      (by rw [Subgroup.map_subtype_commutator, hEq, htop_map]))
  obtain ⟨x, hxP0, hxne, hxp, hCKx⟩ := exists_orderP_centralizer_witness ctr hab hcop hnorm hperf
  obtain ⟨L, Lt, hLmax, hLne, hLt, hPL⟩ := exists_second_maximal hG ctr
  obtain ⟨hNx, hCx⟩ := centralizer_control_of_CKx hG ctr hLmax hLne hLt hPL hxP0 hxne hCKx
  exact ⟨{ L := L, L_maximal := hLmax, L_type := Lt, L_hasType := hLt, P0_le_Ls := hPL,
           x := x, x_mem_P0 := hxP0, x_ne_one := hxne, x_mem_omega1 := hxp,
           CKx_not_le_Kprime := hCKx, normalizer_closure_x_le_M := hNx,
           centralizer_x_not_le_L := hCx }⟩

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is
Frobenius with kernel `L_F`. -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  sorry

/-- **Peterfalvi (12.11)**: `M inter L` complements `K` in `M` and lies in the
Fitting kernel `H` of the witness subgroup `L`. -/
theorem intersection_complement_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  sorry

/-- **(12.12) Case A core.**  A finite group `E` acting faithfully on a one-dimensional
`𝔽_p`-space `V` is cyclic, with `|E| ∣ |V| - 1 = p - 1`.  This is the reducible / rank-one case
of Peterfalvi (12.12): `End_{𝔽_p}(V) ≅ 𝔽_p` (every endomorphism of a line is a homothety), so
`E ↪ End(V)ˣ ≅ (ℤ/p)ˣ`, a cyclic group of order `p - 1`. -/
theorem isCyclic_and_card_dvd_of_faithful_one_dim
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `End_{𝔽_p}(V) ≅ 𝔽_p` via `algebraMap` (bijective in dimension one: every endo is `c • id`).
  have hsurj : Function.Surjective (algebraMap (ZMod p) (Module.End (ZMod p) V)) := by
    intro u
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) V)) :=
    (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective
  let eRing : ZMod p ≃+* Module.End (ZMod p) V := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  -- `E ↪ End(V)ˣ ≃ (ℤ/p)ˣ`.
  let φ : E →* (ZMod p)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).symm.toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hfaith
    have h1 : (MonoidHom.toHomUnits ρ) a = (MonoidHom.toHomUnits ρ) b :=
      (Units.mapEquiv eRing.toMulEquiv).symm.injective (by simpa [φ] using hab)
    simpa using congrArg (Units.val) h1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : IsCyclic φ.range := inferInstance
  have hcardV : Nat.card V = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, pow_one, Nat.card_eq_fintype_card,
      ZMod.card]
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
      (MonoidHom.ofInjective hφinj).symm.surjective, ?_⟩
  rw [hcardV]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

/-- **(12.12) irreducible-case core.**  An odd-order group `E` acting faithfully and
irreducibly on a two-dimensional `𝔽_p`-space `V` (with `p ∤ |E|`) is cyclic, with
`|E| ∣ |V| - 1 = p² - 1`.  This is the rank-two irreducible case of Peterfalvi (12.12):
BG Theorem 2.6(a) (`odd_two_dim_abelian`) abelianizes `E`, and the commutativity-free Singer
mechanism (`isCyclic_and_card_dvd_of_faithful_irreducible_comm`) then realizes `E` inside the
units of the Singer field `𝔽_p[E] ⧸ I ≅ 𝔽_{p²}`. -/
theorem isCyclic_and_card_dvd_of_odd_two_dim_irreducible
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- BG 2.6(a): a faithful odd two-dimensional representation has abelian image.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  -- Give `V` the `𝔽_p[E]`-module structure of the representation *directly* (this is
  -- definitionally `ρ.asModule`'s instance, but stated on `V` so that instance synthesis does
  -- not choke on the `ρ.asModule` notation — which it does once `IsIrreducible ρ` is around).
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  exact isCyclic_and_card_dvd_of_faithful_irreducible_comm (M := V) hcomm hfaith'

/-- **(12.12) rep-theory core (combined).**  A finite odd-order group `E` (`p ∤ |E|`) acting
**fixed-point-freely** (no nonzero vector is fixed by a nontrivial element) on an `𝔽_p`-space `V`
of dimension `1` or `2` is **cyclic**, with `|E| ∣ |V| - 1`.  Dispatches the two (12.12) cores:
dim 1 (or dim 2 with an `E`-invariant line) ⟹ Case A (`isCyclic_and_card_dvd_of_faithful_one_dim`);
dim 2 irreducible ⟹ Case B (`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`).  The FPF
hypothesis makes `E` faithful on every nonzero invariant subspace. -/
theorem isCyclic_and_card_dvd_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- Step 1: the FPF hypothesis makes `ρ` faithful.
  -- `V` is nontrivial because `finrank V ≥ 1`, so it has a nonzero vector; a nontrivial element in
  -- the kernel would fix that vector, contradicting `hfpf`.
  haveI hVnt : Nontrivial V := by
    rcases hdim with h | h
    · exact Module.nontrivial_of_finrank_eq_succ h
    · exact Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [h])
  have hfaith : Function.Injective ρ := by
    intro a b hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (hfpf (b⁻¹ * a) hba v ?_)
    rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rcases hdim with hd1 | hd2
  · -- dim 1: Case A.
    exact isCyclic_and_card_dvd_of_faithful_one_dim ρ hfaith hd1
  · -- dim 2.
    by_cases hirr : Representation.IsIrreducible ρ
    · -- irreducible: Case B.
      exact isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hd2 hp_ndvd
    · -- reducible: a proper nonzero invariant line `W` exists; apply Case A to `W.toRepresentation`,
      -- then lift `|E| ∣ p - 1` to `|E| ∣ p² - 1` via `p - 1 ∣ p² - 1`.
      -- `¬ IsSimpleOrder` plus nontriviality (`⊥ ≠ ⊤` since `V` is nontrivial) yields a proper
      -- nonzero subrepresentation `W`.
      have hbnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
        bot_ne_top (congrArg Subrepresentation.toSubmodule h)
      haveI : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
      have hnotall : ¬ ∀ W : Subrepresentation ρ, W = ⊥ ∨ W = ⊤ := fun H =>
        hirr { eq_bot_or_eq_top := H }
      push_neg at hnotall
      obtain ⟨W, hWbot, hWtop⟩ := hnotall
      -- `W` is a proper nonzero subrepresentation; its submodule has `finrank = 1`.
      have hWsub_bot : W.toSubmodule ≠ ⊥ := fun h =>
        hWbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      have hWsub_top : W.toSubmodule ≠ ⊤ := fun h =>
        hWtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      haveI : Finite ↥W.toSubmodule := Subtype.finite
      haveI : Module.Finite (ZMod p) ↥W.toSubmodule := Module.Finite.of_finite
      have hpos : 0 < Module.finrank (ZMod p) ↥W.toSubmodule := by
        have := Submodule.finrank_lt_finrank_of_lt (s := (⊥ : Submodule (ZMod p) V))
          (t := W.toSubmodule) (lt_of_le_of_ne bot_le (Ne.symm hWsub_bot))
        simpa using this
      have hlt : Module.finrank (ZMod p) ↥W.toSubmodule < Module.finrank (ZMod p) V :=
        Submodule.finrank_lt hWsub_top
      have hWdim : Module.finrank (ZMod p) ↥W.toSubmodule = 1 := by
        rw [hd2] at hlt; omega
      -- faithfulness of `W.toRepresentation` from `hfpf` restricted to `W`.
      have hfaithW : Function.Injective W.toRepresentation := by
        intro a b hab
        by_contra hne
        have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
        -- every element of `W` is fixed by `ρ (b⁻¹ a)`, hence is `0` by `hfpf`; so `W = ⊥`.
        apply hWsub_bot
        rw [Submodule.eq_bot_iff]
        intro w hw
        have hfix : W.toRepresentation (b⁻¹ * a) ⟨w, hw⟩ = ⟨w, hw⟩ := by
          rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
            inv_mul_cancel, map_one, Module.End.one_apply]
        have hfixV : ρ (b⁻¹ * a) w = w := by
          have := congrArg Subtype.val hfix
          simpa [Subrepresentation.toRepresentation, LinearMap.restrict_coe_apply] using this
        exact hfpf (b⁻¹ * a) hba w hfixV
      -- Case A on `W.toRepresentation` gives `IsCyclic E ∧ |E| ∣ p - 1`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_faithful_one_dim W.toRepresentation hfaithW hWdim
      refine ⟨hcyc, ?_⟩
      -- `Nat.card ↥W.toSubmodule = p`, `Nat.card V = p²`.
      have hcardW : Nat.card ↥W.toSubmodule = p := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hWdim, pow_one, Nat.card_eq_fintype_card,
          ZMod.card]
      have hcardV : Nat.card V = p ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
      rw [hcardW] at hdvd
      rw [hcardV]
      -- `|E| ∣ p - 1 ∣ p² - 1`, via `p² - 1 = (p - 1) * (p + 1)`.
      refine hdvd.trans ?_
      have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      refine ⟨k + 2, ?_⟩
      have hsq : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
      rw [hsq, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form).**  A finite odd-order group
`E` (`p ∤ |E|`) acting **fixed-point-freely** on an elementary abelian `p`-group `M` — encoded by
a `ZMod p`-module structure on `Additive M` — of `𝔽_p`-dimension `1` or `2` is **cyclic**, with
`|E| ∣ |M| - 1`.

This lifts `isCyclic_and_card_dvd_of_fpf_dim_le_two` from an abstract `Representation` to a
`MulDistribMulAction` (via `Representation.ofDistribMulAction`), which is the form that a
conjugation action of `E` on an elementary abelian subgroup supplies. -/
theorem isCyclic_and_card_dvd_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The fixed-point-free hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    -- `e • v = Additive.ofMul (e • v.toMul)` definitionally; pass to the multiplicative action.
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  exact ⟨hcyc, by rwa [Nat.card_congr (Additive.toMul (α := M))] at hdvd⟩

/-- **(12.12) rep-theory bridge (conjugation form).**  Let a finite group `E` normalize an
elementary abelian `p`-subgroup `T` of order `p` or `p²` of `G`, with `|E|` odd and coprime to `p`,
and let `E` act **fixed-point-freely on `T` by conjugation** (no nontrivial element of `T` is fixed
by a nontrivial element of `E`).  Then `E` is **cyclic** and `|E|` divides `p - 1` or `p² - 1`.

This is the `§8`-free structural core of Peterfalvi (12.12): there `T = Ω₁(Z(O_p(H)))` is the
rank `≤ 2` elementary abelian subgroup and `E` the Frobenius complement of `L`, acting FPF on `T`
by (12.10).  The `p + 1` refinement of (12.12) is separate (it consumes (12.9)/(12.11)). -/
theorem isCyclic_and_card_dvd_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p ^ 2 - 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpf' : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_of_fpf_mulDistribMulAction hodd hp_ndvd hdim hfpf'
  refine ⟨hcyc, ?_⟩
  rcases hT_card with h | h
  · exact Or.inl (by rwa [h] at hdvd)
  · exact Or.inr (by rwa [h] at hdvd)

/-- **Peterfalvi (12.12)**: the Frobenius complement in the witness subgroup is
cyclic, with order dividing `p - 1` or `p + 1`. -/
theorem complement_cyclic_order_dvd [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (frob : TypeIFrobeniusData L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  sorry

/-! ## (12.13)--(12.16): Dade notation and contradiction -/

/-- **Peterfalvi (12.13)**: notation for the final Dade calculation in the
minimal counterexample. -/
structure DadeNotation {L : Subgroup G} (hyp : Hypothesis L) where
  e : ℕ
  e_eq_index : Prop
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  chi : ClassFunction ↥L ℂ
  chi_mem : chi ∈ hyp.Sset
  chi_degree_eq_e : chi 1 = (e : ℂ)
  psi : ClassFunction G ℂ
  psi_eq_tau1_chi : psi = tau1 chi
  rhoFormula : Prop
  rhoMFormula : Prop

/-- **Peterfalvi (12.14)**: the character `psi` is constant on the coset `xK`. -/
theorem psi_constant_on_xK [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (hyp : Hypothesis L) (witness : RankTwoWitnessData ctr)
    (dade : DadeNotation hyp) :
    ∀ g : G, g ∈ ctr.K → dade.psi (witness.x * g) = dade.psi witness.x := by
  sorry

/-- **Peterfalvi (12.15)**: the rho image is unchanged on `K#`, constant on
`K - K'`, and has integer values there. -/
theorem rhoM_integer_values [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    {hyp : Hypothesis L} (dade : DadeNotation hyp) :
    dade.rhoMFormula ∧
      (∀ g : G, g ∈ ctr.K → g ∉ ctr.Kprime → ∃ z : ℤ, dade.psi g = (z : ℂ)) := by
  sorry

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  sorry

/-- **Peterfalvi (12.7), `π = ∅`** (the headline consequence of (12.16)): no prime lies in the
set `π` of (12.8).  Were `π` nonempty, (12.8) (`exists_counterexampleHypothesis`) would build a
minimal counterexample, contradicting (12.16) (`counterexample_contradiction`). -/
theorem pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q := by
  by_contra h
  push_neg at h
  obtain ⟨ctr⟩ := exists_counterexampleHypothesis hG h
  exact counterexample_contradiction hG ctr

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with kernel `M_F`.

Since `π = ∅` by (12.16) (`pi_empty`), the easy direction `typeI_frobenius_of_pi_empty` applies
and gives the Frobenius decomposition with kernel `M_F = typeF.H` and complement `typeF.U`.  (The
`kernel_eq_MF` carrier is vacuous here: the `frobenius` field already names `typeF.H = M_F` as the
kernel, so the identification holds definitionally.) -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  obtain ⟨data⟩ := hType
  exact ⟨{ typeI := data
           complement := data.typeF.U.subgroupOf M
           kernel_eq_MF := True
           kernel_eq_MF_holds := trivial
           frobenius := typeI_frobenius_of_pi_empty hG (pi_empty hG) hM data }, trivial⟩

/-! ## (12.17): forcing case (b) of Theorem (8.8) — the all-type-I non-existence argument

Peterfalvi (12.17) shows that case (a) of Theorem (8.8) — *every* maximal subgroup of `G` being of
type I — is impossible.  The argument assembles the type-I maximals into a Frobenius family in the
sense of (7.10) (`S09.FrobeniusFamily`) and derives the contradiction from (7.11)
(`S09.not_trivial_G0`).  Combined with the (8.8) dichotomy (`theorem88_dichotomy`, BG §16), this
forces the case-(b) pairing data `Theorem88CaseBData`, which the Feit–Thompson endgame consumes.

The genuinely group-theoretic content of the family — the Frobenius structure (from (12.7)) and the
self-normalizing identity `L = N_G(L_F)` — is proved here.  The remaining §8/§10 covering inputs
(TI sharp-sets via (8.13.c1), coprime kernels and the `G#` cover via (8.17)) are isolated in the
faithful carrier `TypeICovering`. -/

section Theorem1217

variable [Finite G]

/-- **Normalizer bridge for Peterfalvi (12.17)**: a maximal subgroup `L` of a minimal simple group
of odd order is the normalizer of its maximal nilpotent normal Hall subgroup `L_F`, as soon as
`L_F ≠ ⊥`.

`L ≤ N_G(L_F)` is `maxNilpotentNormalHall_le_normalizer`.  If `N_G(L_F) = ⊤` then `L_F ⊴ G`, so by
simplicity `L_F = ⊥` or `⊤`; both are excluded (`L_F ≠ ⊥` by hypothesis, `L_F ≤ L < ⊤`).  Hence
`L ≤ N_G(L_F) < ⊤`, and `L` being a coatom upgrades the containment to equality. -/
theorem maximalSubgroup_eq_normalizer_maxNilpotentNormalHall
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hne : maxNilpotentNormalHall L ≠ ⊥) :
    L = Subgroup.normalizer (maxNilpotentNormalHall L : Set G) := by
  have hco : IsCoatom L := hL
  have hLleN : L ≤ Subgroup.normalizer (maxNilpotentNormalHall L : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L
  refine le_antisymm hLleN ?_
  rcases hLleN.lt_or_eq with hlt | heq
  · -- `L < N_G(L_F)` would force `N_G(L_F) = ⊤`, making `L_F ⊴ G`, which simplicity excludes.
    exfalso
    have hNtop : Subgroup.normalizer (maxNilpotentNormalHall L : Set G) = ⊤ := hco.2 _ hlt
    haveI hHnormal : (maxNilpotentNormalHall L).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall L) hHnormal with hb | ht
    · exact hne hb
    · have hle : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
      rw [ht] at hle
      exact hco.1 (top_le_iff.mp hle)
  · exact heq.ge

/-- **§8/§10 covering inputs to Peterfalvi (12.17)** — the all-type-I case of Theorem (8.8).

When every maximal subgroup of `G` is of type I, the §8 covering theory (BG Theorem E, (8.17), and
the escaping-centralizer control (8.13.c1)) supplies a finite family of conjugacy-class
representatives `reps i` whose maximal nilpotent normal Hall subgroups `(reps i)_F`:
* number at least two (`two_le`);
* have TI sharp-sets `((reps i)_F)#` (`isTI`, via (8.13.c1)+(2.3));
* are pairwise of coprime order (`coprime`, via the (8.17) prime partition);
* cover `G#` up to conjugacy (`covers`, the (8.17.a) type-I covering).

These are exactly the inputs the (12.17) argument feeds to (7.11), beyond the genuinely
group-theoretic family facts (Frobenius structure, `reps i = N_G((reps i)_F)`) discharged in
`not_all_maximal_typeI`. -/
structure TypeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) where
  /-- Number of conjugacy classes of maximal subgroups. -/
  k : ℕ
  /-- Conjugacy-class representatives of the maximal subgroups. -/
  reps : Fin k → Subgroup G
  /-- Each representative is maximal. -/
  reps_maximal : ∀ i, reps i ∈ maximalSubgroups G
  /-- (7.10): at least two members. -/
  two_le : 2 ≤ k
  /-- (8.13.c1)+(2.3): each kernel sharp-set is a TI-subset. -/
  isTI : ∀ i, IsTISubset ((maxNilpotentNormalHall (reps i) : Set G) \ {1}) (reps i)
  /-- (8.17): the kernels have pairwise-coprime order. -/
  coprime : ∀ ⦃i j⦄, i ≠ j →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (reps i)))
      (Nat.card ↥(maxNilpotentNormalHall (reps j)))
  /-- (8.17.a): the conjugates of the kernels cover every nonidentity element. -/
  covers : ∀ x : G, x ≠ 1 →
    ∃ i, ∃ g : G, g * x * g⁻¹ ∈ (maxNilpotentNormalHall (reps i) : Set G) \ {1}

omit [Finite G] in
/-- **§8 thickening kernel containment.**  The subgroup `R(x) = supportKernel L M X x` of
Peterfalvi (8.14) is always contained in `L_F = maxNilpotentNormalHall L`: on the
escaping-centralizer set it is `L_F ⊓ C_G(x) ≤ L_F`, and elsewhere it is `⊥`. -/
theorem supportKernel_le_maxNilpotentNormalHall (L M : Subgroup G) (X : Set G) (x : G) :
    supportKernel L M X x ≤ maxNilpotentNormalHall L := by
  classical
  unfold supportKernel
  split
  · exact inf_le_left
  · exact bot_le

/-- **The type-I thickened cover lands in `L_F`-conjugates.**  If a support set `X` is contained in
`L_F = maxNilpotentNormalHall L`, then every element of the thickened support
`⋃_{z ∈ X} (z R(z))^G` (`thickenedSupport L M X`) is conjugate to an element of `L_F`: the coset
factor `z ∈ X ⊆ L_F` and the kernel factor `r ∈ R(z) ⊆ L_F`
(`supportKernel_le_maxNilpotentNormalHall`) multiply into `L_F`, which `𝒞_G` saturates.

This is the structural heart of the (12.17) type-I covering: the thickening `R(z)` never escapes
`L_F`, so the `A_1(L) = (L_F)#` cover by thickened sets is, up to conjugacy, a cover by `L_F`. -/
theorem thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall
    {L M : Subgroup G} {X : Set G} (hX : X ⊆ (maxNilpotentNormalHall L : Set G)) :
    thickenedSupport L M X ⊆ conjClassSet (maxNilpotentNormalHall L : Set G) := by
  rintro y ⟨z, hz, hyz⟩
  obtain ⟨w, hw, g, hgwy⟩ := hyz
  obtain ⟨r, hr, hzrw⟩ := hw
  have hzMF : z ∈ maxNilpotentNormalHall L := hX hz
  have hrMF : r ∈ maxNilpotentNormalHall L :=
    supportKernel_le_maxNilpotentNormalHall L M X z (SetLike.mem_coe.mp hr)
  have hwMF : w ∈ maxNilpotentNormalHall L := hzrw ▸ mul_mem hzMF hrMF
  exact ⟨w, SetLike.mem_coe.mpr hwMF, g, hgwy⟩

/-- **Peterfalvi (8.17)/(8.13.c1), all-type-I case**: the §8 covering inputs of (12.17) exist.

Built as an honest reduction from BG Theorem E (`S10.bgTheoremE_cover_data`): in the all-type-I case
every representative `M_i` has `data.tau i = .I` (type exclusivity, `not_isTypeI_of_isTypeNonI`), so
`mainSubgroup (M_i) (τ_i) = (M_i)_F`.  The `reps`/`reps_maximal` plumbing, `coprime` (the (8.17)
prime-factor partition is disjoint, hence the kernels are coprime), `two_le` (a single class would
make `|G#| = (|M_s|-1)|G:M| < |G|-1 = |G#|`), and `covers` (the thickened cover lands in
`(M_i)_F`-conjugates, `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`) are all
discharged.  Two upstream facts remain isolated as residual sorries: `isTI`, the escaping-centralizer
control (8.13.c1)+(2.3) making each kernel sharp-set a TI-subset; and the selection of the type-I
cover branch under `hall`, the (8.8.a) dichotomy (BG §16, parallel to `theorem88_dichotomy`). -/
theorem exists_typeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by
  classical
  -- `BGTheoremECoverData.ι : Type*` is universe-polymorphic; pin the index type to `Type 0`.
  obtain ⟨data, hcover⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  haveI : Fintype data.ι := data.finite_index
  -- **Every representative is type I**, so `data.tau i = .I` and hence
  -- `mainSubgroup (M_i) (τ_i) = (M_i)_F`.  Type exclusivity is
  -- `not_isTypeI_of_isTypeNonI` (BG §16): a type-`P` (= non-type-I) maximal is not type I.
  have hMF : ∀ i, mainSubgroup (data.reps i) (data.tau i)
      = maxNilpotentNormalHall (data.reps i) := by
    intro i
    have hI : IsTypeI (data.reps i) := hall _ (data.maximal i)
    have htau := data.typed i
    have htauI : data.tau i = PeterfalviType.I := by
      by_contra hne
      have hNonI : IsTypeNonI (data.reps i) := by
        cases hc : data.tau i with
        | I => exact absurd hc hne
        | II => rw [hc] at htau; exact Or.inl htau
        | III => rw [hc] at htau; exact Or.inr (Or.inl htau)
        | IV => rw [hc] at htau; exact Or.inr (Or.inr (Or.inl htau))
        | V => rw [hc] at htau; exact Or.inr (Or.inr (Or.inr htau))
      exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG (data.maximal i) hNonI hI
    simp only [htauI, mainSubgroup]
  -- The `Fin k`-indexing of the representatives (`e : data.ι ≃ Fin k`).
  set e := Fintype.equivFin data.ι with he
  rcases hcover with hTypeI | hNonTypeI
  · -- **(8.8.a) type-I cover branch.**
    refine ⟨{
      k := Fintype.card data.ι
      reps := fun j => data.reps (e.symm j)
      reps_maximal := fun j => data.maximal (e.symm j)
      two_le := ?_
      isTI := ?_
      coprime := ?_
      covers := ?_ }⟩
    · -- **`two_le`** (discharged): at least two conjugacy classes of maximal subgroups (7.10).
      -- A single class would force `|G#| = |thickenedA1(M)| = (|M_s| - 1)|G : M|`; but
      -- `(|M_s| - 1)|G : M| ≤ (|M| - 1)|G : M| = |G| - |G : M| ≤ |G| - 2 < |G| - 1 = |G#|`, and an
      -- empty class would force `|G#| = 0`, both impossible.  No counting of disjoint unions is
      -- needed: a one-element index makes the cover `⋃ᵢ thickenedA1(Mᵢ)` equal to a single
      -- `thickenedA1(M)`, whose cardinality is strictly below `|G#|`.
      haveI : Nontrivial G := hG.simple.toNontrivial
      by_contra hlt
      rw [Nat.not_le] at hlt
      have hcard01 : Fintype.card data.ι = 0 ∨ Fintype.card data.ι = 1 := by omega
      rcases hcard01 with h0 | h1
      · -- empty index: the cover is empty, but `G#` contains a nonidentity element.
        rw [Fintype.card_eq_zero_iff] at h0
        have hempty : (⋃ i, thickenedA1 (data.reps i) (data.reps i) (data.tau i)) = ∅ :=
          Set.iUnion_of_empty _
        rw [← hTypeI.cover_nonidentity] at hempty
        obtain ⟨b, hb⟩ := exists_ne (1 : G)
        have hbmem : b ∈ sharpSubgroup (⊤ : Subgroup G) := by
          simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_diff, Set.mem_univ, true_and,
            Set.mem_singleton_iff]
          exact hb
        rw [hempty] at hbmem
        exact hbmem.elim
      · -- one class: `⋃ᵢ thickenedA1(Mᵢ) = thickenedA1(M)`, of cardinality `< |G#|`.
        obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
        have hunion : (⋃ i, thickenedA1 (data.reps i) (data.reps i) (data.tau i))
            = thickenedA1 (data.reps i₀) (data.reps i₀) (data.tau i₀) := by
          ext x
          simp only [Set.mem_iUnion]
          exact ⟨fun ⟨i, hi⟩ => by rwa [hi₀ i] at hi, fun hx => ⟨i₀, hx⟩⟩
        rw [← hTypeI.cover_nonidentity] at hunion
        have hcard_eq : Nat.card ↥(thickenedA1 (data.reps i₀) (data.reps i₀) (data.tau i₀))
            = Nat.card G - 1 := by
          rw [Nat.card_coe_set_eq, ← hunion]
          show ((↑(⊤ : Subgroup G) : Set G) \ {1}).ncard = Nat.card G - 1
          rw [Subgroup.coe_top, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
        rw [data.thickenedA1_card i₀] at hcard_eq
        -- Arithmetic contradiction.
        have hmain_le : mainSubgroup (data.reps i₀) (data.tau i₀) ≤ data.reps i₀ :=
          (hMF i₀).le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (data.reps i₀))
        have ham : Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀))
            ≤ Nat.card ↥(data.reps i₀) := Subgroup.card_le_of_le hmain_le
        have hidx0 : (data.reps i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hidx1 : (data.reps i₀).index ≠ 1 :=
          fun h => (data.maximal i₀).1 (Subgroup.index_eq_one.mp h)
        have hidx : 2 ≤ (data.reps i₀).index := by omega
        have hmidx : Nat.card ↥(data.reps i₀) * (data.reps i₀).index = Nat.card G :=
          Subgroup.card_mul_index (data.reps i₀)
        have hm_pos : 0 < Nat.card ↥(data.reps i₀) := Nat.card_pos
        have hG2 : 2 ≤ Nat.card G :=
          le_trans hidx (hmidx ▸ Nat.le_mul_of_pos_left (data.reps i₀).index hm_pos)
        have hb1 : (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
            * (data.reps i₀).index
            ≤ (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ham 1)
        have hrhs : (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index
            = Nat.card G - (data.reps i₀).index := by rw [Nat.sub_one_mul, hmidx]
        rw [hrhs] at hb1
        -- `hcard_eq : P = |G| - 1`, `hb1 : P ≤ |G| - idx`, `idx ≥ 2`, `|G| ≥ 2` ⟹ `False`.
        set P := (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
          * (data.reps i₀).index with hP
        omega
    · -- `isTI`: each kernel sharp-set `((M_i)_F)#` is a TI-subset, by (8.13.c1)+(2.3).
      -- Escaping-centralizer §8 residual.
      intro j
      sorry
    · -- **`coprime`** (discharged): the kernels have pairwise-coprime order because the (8.17)
      -- partition makes their prime-factor sets disjoint.
      intro j j' hjj'
      have hne : e.symm j ≠ e.symm j' := fun h => hjj' (e.symm.injective h)
      have hdisj := data.primeFactors_disjoint (e.symm j) (e.symm j') hne
      simp only [hMF] at hdisj
      have hcard1 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j))) ≠ 0 :=
        Nat.card_pos.ne'
      have hcard2 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j'))) ≠ 0 :=
        Nat.card_pos.ne'
      exact (Nat.disjoint_primeFactors hcard1 hcard2).mp hdisj
    · -- **`covers`** (discharged): the genuine type-I covering.  Every nonidentity `x` lies in
      -- some thickened `A_1(M_i)` (the (8.17.a) cover), and that thickened set lands in the
      -- conjugates of `(M_i)_F#` because the §8 thickening kernel `R(z) ≤ (M_i)_F`
      -- (`thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`).
      intro x hx1
      have hxsharp : x ∈ sharpSubgroup (⊤ : Subgroup G) := by
        simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_diff, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        exact hx1
      rw [hTypeI.cover_nonidentity] at hxsharp
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxsharp
      have hX : A1 (data.reps i) (data.tau i)
          ⊆ (maxNilpotentNormalHall (data.reps i) : Set G) := by
        show sharpSubgroup (mainSubgroup (data.reps i) (data.tau i))
          ⊆ (maxNilpotentNormalHall (data.reps i) : Set G)
        rw [hMF i]
        exact Set.diff_subset
      have hxconj : x ∈ conjClassSet (maxNilpotentNormalHall (data.reps i) : Set G) :=
        thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall hX hxi
      obtain ⟨t, htMF, g, hgtx⟩ := hxconj
      refine ⟨e i, g⁻¹, ?_⟩
      have hreps : data.reps (e.symm (e i)) = data.reps i := by rw [Equiv.symm_apply_apply]
      have hconj : g⁻¹ * x * (g⁻¹)⁻¹ = t := by rw [inv_inv, ← hgtx]; group
      simp only [hreps, hconj, Set.mem_diff, Set.mem_singleton_iff]
      refine ⟨htMF, ?_⟩
      intro ht1
      exact hx1 (by rw [← hgtx, ht1]; group)
  · -- **(8.8.b) non-type-I cover branch**: ruled out when every maximal subgroup is type I.
    -- This is the all-type-I case of the (8.8) dichotomy (`theorem88_dichotomy`); under `hall`
    -- BG Theorem E returns the type-I cover, never the two-exceptional-subgroup case (the
    -- exceptional `W` of `hNonTypeI` is the normalizer of a non-type-I maximal).  Isolating that
    -- is the BG §16 (8.8.a) residual.
    exfalso
    sorry

/-- **Peterfalvi (12.17), non-existence half**: in a minimal simple group of odd order, not every
maximal subgroup is of type I.

*Proof.*  Assume otherwise.  The §8 covering theory (`exists_typeICovering`) provides the family of
conjugacy-class representatives `reps i` of the maximal subgroups, whose kernels `(reps i)_F` are
pairwise-coprime TI-subsets covering `G#`.  Each `reps i` is a Frobenius group with kernel
`(reps i)_F` by (12.7) (`typeI_frobenius`) and equals its own `N_G((reps i)_F)`
(`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`), so these data assemble into a Frobenius
family in the sense of (7.10) (`S09.FrobeniusFamily`).  The covering makes `G₀ = {1}`, contradicting
(7.11) (`S09.not_trivial_G0`). -/
theorem not_all_maximal_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) := by
  intro hall
  obtain ⟨cov⟩ := exists_typeICovering hG hall
  let F : OddOrder.Peterfalvi.S09.FrobeniusFamily G cov.k :=
    { L := cov.reps
      H := fun i => maxNilpotentNormalHall (cov.reps i)
      two_le := cov.two_le
      kernel_le := fun i => OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (cov.reps i)
      isFrobenius := fun i => by
        obtain ⟨fd, -⟩ := typeI_frobenius hG (cov.reps_maximal i) (hall _ (cov.reps_maximal i))
        refine ⟨fd.complement, ?_⟩
        rw [← fd.typeI.typeF.H_eq]
        exact fd.frobenius
      normalizer_eq := fun i =>
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG (cov.reps_maximal i) (by
          obtain ⟨td⟩ := hall _ (cov.reps_maximal i)
          rw [← td.typeF.H_eq]
          exact td.typeF.H_nontrivial)
      isTI := cov.isTI
      coprime_kernel := cov.coprime }
  have hG0 : F.G0 = {(1 : G)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨F.one_mem_G0, fun x hx => ?_⟩
    by_contra hx1
    obtain ⟨i, g, hg⟩ := cov.covers x hx1
    exact (F.mem_G0_iff.mp hx) i ⟨g, hg⟩
  exact OddOrder.Peterfalvi.S09.not_trivial_G0 F hG.odd hG0

end Theorem1217

/-! ## (12.17) → (8.8): the case-(b) dichotomy -/

/-- **Type-`P` ⟹ non-Type-I** (Proposition 16.1(b)(c)(d)): a type-`P` maximal subgroup of a minimal
simple group of odd order is one of the Types II–V.  Split `κ(M)` against `π(M) - σ(M)`: equal gives
`P₁`, which is Type V (`M_F = M_σ`) or Type III/IV (`M_F ≠ M_σ`); unequal gives `P₂` = Type II.  This
is the local `typeP_imp_nonI` of BG Theorem I's dichotomy proof, isolated here for
`theorem88_dichotomy`. -/
private theorem isTypeNonI_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP N) : IsTypeNonI N := by
  obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
  by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
  · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
    by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
    · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
    · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
      · exact Or.inr (Or.inl hIII)
      · exact Or.inr (Or.inr (Or.inl hIV))
  · exact Or.inl (hbII.mpr ⟨hP, hk⟩)

/-- **Theorem (8.8) dichotomy** (BG §16): for a minimal simple group of odd order, either every
maximal subgroup is of type I, or the case-(b) pairing data `Theorem88CaseBData` exists.

*Proof.*  If some maximal `S` is not type I, then it is type `P` (Proposition 16.1(a): `TypeI ⟺
TypeF`, and `TypeF ⟺ κ(S) = ∅`).  BG Theorem 14.7 duality (`typeP_duality`) applied to `S` with a
`κ(S)`-Hall subgroup `K` produces the complement `S = S' ⋊ K` (first conjunct), the dual maximal
`T = M*`, the cyclic factor `W = K ⊔ K*`, the type-II witness, and the `κ(M*)`-Hall `K*`.  Applying
the duality again at `M*` gives the second complement `T = T' ⋊ K*`.  The `κ`-Hall complement `K`
plays the role of the case-(b) factor `W₁` (both `K` and the type-`P` `W₁` complement `S'`, Peterfalvi
(8.8.b1)).  Cites the merged BG §16 `typeP_duality` and `proposition_type_classification`; the
remaining hard content lives in their (issue-8015) residuals. -/
theorem theorem88_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  classical
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · exact Or.inl hall
  · refine Or.inr ?_
    push_neg at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
    -- `S` not type I ⟹ `S` type `P` (Prop 16.1(a): `TypeI ⟺ TypeF`, `TypeF ⟺ κ(S) = ∅`).
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP S := by
      have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).1
      have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF S := fun hF => hSnotI (hiff.mpr hF)
      rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- A `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- BG Theorem 14.7 duality at `S`: `S = S' ⋊ K` (`hScompl`), the dual `M*`, its data.
    obtain ⟨hScompl, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
    -- Apply duality again at `M*` with its `κ`-Hall `K*`: `M* = (M*)' ⋊ K*` (`hTcompl`).
    obtain ⟨hTcompl, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq
    exact ⟨{
      S := S, T := Mstar, W1 := K, W2 := Kstar, W := K ⊔ Kstar
      S_maximal := hS, T_maximal := hMstarMem
      S_ne_T := by
        intro hST
        rw [hST] at hSnconjMstar
        exact hSnconjMstar (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
      W_eq := rfl, W_cyclic := hcyc
      S_nonI := isTypeNonI_of_isTypeP hG hS hSP
      T_nonI := isTypeNonI_of_isTypeP hG hMstarMem hMstarP
      one_typeII := hP2disj.imp
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr h)
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr h)
      W1_le_S := Subgroup.map_subtype_le K'
      W2_le_T := hKstarMstar
      S_compl := hScompl
      T_compl := hTcompl }⟩

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible, so the case-(b)
data of (8.8) exists.  Immediate from the (8.8) dichotomy (`theorem88_dichotomy`) and the
non-existence half `not_all_maximal_typeI`. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) :=
  (theorem88_dichotomy hG).resolve_left (not_all_maximal_typeI hG)

end OddOrder.Peterfalvi.S14
