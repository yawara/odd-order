import OddOrder.Peterfalvi.S16_NonExistenceG.TSideTypeP
import OddOrder.Peterfalvi.S13_PrimeTIResidueBridge
import OddOrder.GroupTheory.RepresentationTheory.InducedDegreeSum

/-!
# Peterfalvi (14.9): the T-side prime-TI anchor

Construction of the reducible prime-TI character `ν₀ = primeTIred 0` used in
`βT0 = ν₀ - ζ`.  This is the `primeTIred ptiWT 0` of Coq `PFsection14.v`, not the
two-dimensional §13 `nu` grid.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), T-side prime-TI anchor.**  If `T` is type III, its certain-type
prime-TI residue datum constructs `ν₀ = primeTIred 0`.  It is a real virtual character,
is induced from `T'` and hence supported there, and has degree
`[T:T'] = |W₁(T)| = p`.

These are precisely the source-side inputs for the supported Dade difference
`βT0 = ν₀ - ζ`; no S-side gap or cross-maximal relation is used. -/
theorem exists_typeIII_primeTIredZero_with_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
            Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 := by
  classical
  let td : OddOrder.GroupTheory.TypeIIIData hyp.base.T := hIII.some
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII hG hyp.base.T_maximal hIII
  let s06 : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.base.T :=
    OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis td.typeP hG.odd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime
        hG hyp.base.T_maximal hP td.typeP)
  letI : NeZero (Nat.card ↥s06.W1) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card ↥s06.W2) := ⟨Nat.card_pos.ne'⟩
  let residue : PrimeTIResidueData ↥hyp.base.T s06.K
      (Nat.card ↥s06.W1) (Nat.card ↥s06.W2) :=
    PrimeTIResidueData.ofS06Hypothesis s06 ⊤ le_top
  refine ⟨residue.primeTIred 0, residue.prTIred_mem_ZIrr 0, ?_, ?_, ?_, ?_⟩
  · change (residue.primeTIred 0).conj = residue.primeTIred 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.induce_conj, trivialClassFunction_isReal]
  · haveI : s06.K.Normal := s06.K_normal
    change (residue.primeTIred 0).support ⊆ (s06.K : Set ↥hyp.base.T)
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact ClassFunction.support_induce_subset_of_normal s06.K
      (trivialClassFunction ↥s06.K)
  · calc
      residue.primeTIred 0 1 =
          (Nat.card ↥s06.W1 : ℂ) := by
        rw [← residue.cfInd_prTIres 0, residue.prTIres0,
          ClassFunction.induce_apply_one, s06.index_K_eq,
          trivialClassFunction_apply, mul_one]
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by
        rw [T_typeIII_card_W1 hyp td]
  · change ClassFunction.inner (residue.primeTIred 0)
        (trivialClassFunction ↥hyp.base.T) = 1
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    have hconst :
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T =
          trivialClassFunction ↥hyp.base.T := by
      ext t
      simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
    rw [← hconst]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one s06.K

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), source data for the T-side projection.**
The concrete prime-TI anchor `ν₀ = Ind_{T'}^T 1_{T'}` has self-inner-product `p`
and is orthogonal to every `Ind_{T'}^T θ` with `θ ≠ 1`.

These are Coq's `cfnorm_prTIred` and `omuS1` inputs in the norm-rigidity proof of
`FTtype34_structure`. Keeping the universal induced-family orthogonality alongside
the concrete anchor avoids replacing the (11.9)(a) projection by an opaque coefficient
assumption downstream. -/
theorem exists_typeIII_primeTIredZero_with_projectionData_and_galois [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0 ν0 = (hyp.base.p : ℂ) ∧
        (∀ θ : IrreducibleCharacter
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T),
          θ ≠ trivialIrreducibleCharacter _ →
          ClassFunction.inner ν0
            (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
              θ.toClassFunction) = 0) ∧
        ∀ sigma : ℂ ≃+* ℂ,
          ClassFunction.mapRingEquiv sigma ν0 = ν0 := by
  classical
  let td : OddOrder.GroupTheory.TypeIIIData hyp.base.T := hIII.some
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII hG hyp.base.T_maximal hIII
  let s06 : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.base.T :=
    OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis td.typeP hG.odd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime
        hG hyp.base.T_maximal hP td.typeP)
  letI : NeZero (Nat.card ↥s06.W1) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card ↥s06.W2) := ⟨Nat.card_pos.ne'⟩
  let residue : PrimeTIResidueData ↥hyp.base.T s06.K
      (Nat.card ↥s06.W1) (Nat.card ↥s06.W2) :=
    PrimeTIResidueData.ofS06Hypothesis s06 ⊤ le_top
  refine ⟨residue.primeTIred 0, residue.prTIred_mem_ZIrr 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (residue.primeTIred 0).conj = residue.primeTIred 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.induce_conj, trivialClassFunction_isReal]
  · haveI : s06.K.Normal := s06.K_normal
    change (residue.primeTIred 0).support ⊆ (s06.K : Set ↥hyp.base.T)
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact ClassFunction.support_induce_subset_of_normal s06.K
      (trivialClassFunction ↥s06.K)
  · calc
      residue.primeTIred 0 1 = (Nat.card ↥s06.W1 : ℂ) := by
        rw [← residue.cfInd_prTIres 0, residue.prTIres0,
          ClassFunction.induce_apply_one, s06.index_K_eq,
          trivialClassFunction_apply, mul_one]
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by rw [T_typeIII_card_W1 hyp td]
  · change ClassFunction.inner (residue.primeTIred 0)
        (trivialClassFunction ↥hyp.base.T) = 1
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    have hconst :
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T =
          trivialClassFunction ↥hyp.base.T := by
      ext t
      simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
    rw [← hconst]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one s06.K
  · calc
      ClassFunction.inner (residue.primeTIred 0) (residue.primeTIred 0) =
          (Nat.card ↥s06.W1 : ℂ) := residue.cfnorm_prTIred 0
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by rw [T_typeIII_card_W1 hyp td]
  · intro θ hθ
    change ClassFunction.inner (residue.primeTIred 0)
        (ClassFunction.induce s06.K θ.toClassFunction) = 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact OddOrder.RepresentationTheory.inner_induce_trivial_induce_eq_zero hθ
  · intro sigma
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.mapRingEquiv_induce]
    congr 1
    ext x
    simp [ClassFunction.mapRingEquiv_apply, trivialClassFunction_apply]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The projection data of the canonical T-side prime-TI anchor, with its
coefficient-Galois fixedness projected away for existing consumers. -/
theorem exists_typeIII_primeTIredZero_with_projectionData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0 ν0 = (hyp.base.p : ℂ) ∧
        ∀ θ : IrreducibleCharacter
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T),
          θ ≠ trivialIrreducibleCharacter _ →
          ClassFunction.inner ν0
            (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
              θ.toClassFunction) = 0 := by
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth, _⟩ :=
    exists_typeIII_primeTIredZero_with_projectionData_and_galois hG hyp hIII
  exact ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the prime-TI anchor is orthogonal to a conjugate pair.**
For a nonprincipal irreducible source `θ` of `T'`, retain the universal projection data of
`ν₀ = Ind_{T'}^T 1` together with its two specialisations
`ν₀ ⟂ Ind θ` and `ν₀ ⟂ (Ind θ)̄ = Ind θ̄`.

The conjugate source is still nonprincipal: if `θ̄ = 1`, conjugating once more gives `θ = 1`.
This is the exact source-pair input used to show
`⟨ν₀ - Ind θ, Ind θ - (Ind θ)̄⟩ = -1`. -/
theorem exists_typeIII_primeTIredZero_with_conjugateProjectionData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0 ν0 = (hyp.base.p : ℂ) ∧
        (∀ ξ : IrreducibleCharacter
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T),
          ξ ≠ trivialIrreducibleCharacter _ →
          ClassFunction.inner ν0
            (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
              ξ.toClassFunction) = 0) ∧
        ClassFunction.inner ν0
          (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
            θ.toClassFunction) = 0 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
            θ.toClassFunction).conj = 0 := by
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth⟩ :=
    exists_typeIII_primeTIredZero_with_projectionData hG hyp hIII
  let θc : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    ⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩
  have hθcne : θc ≠ trivialIrreducibleCharacter _ :=
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.irreducibleCharacter_conj_ne_trivial
      hθne
  refine ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth,
    hνorth θ hθne, ?_⟩
  rw [ClassFunction.induce_conj
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)]
  exact hνorth θc hθcne

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), norm of the T-side bridge source.**
For a nonprincipal irreducible source `θ` of `T'`, the bridge
`β_{T,0} = ν₀ - Ind_{T'}^T θ` has norm `p + 1`.

This is the source-side equality used in Coq's `normX_le_q`: the anchor has
norm `p`, the induced member has norm `1`, and the two cross terms vanish
by `omuS1`. -/
theorem exists_typeIII_primeTIDifference_induced_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) := by
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνθ⟩ :=
    exists_typeIII_primeTIredZero_with_projectionData hG hyp hIII
  have hθν : ClassFunction.inner
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ν0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hνθ θ hθne, star_zero]
  refine ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, ?_⟩
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hνnorm, hνθ θ hθne, hθν,
    hζirr.inner_self_eq_one]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The T-side prime-TI anchor, with the Frobenius-reciprocity coefficient
projected away for consumers that only need support and degree. -/
theorem exists_typeIII_primeTIredZero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
            Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) := by
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, _⟩ :=
    exists_typeIII_primeTIredZero_with_inner hG hyp hIII
  exact ⟨ν0, hνZ, hνR, hνsupp, hν1⟩

open scoped Classical in
/-- **Peterfalvi (2.7), specialised to the T-side Dade map.**  A class function
supported on `A₁(T) = supportInSubgroup (sigmaSharp T) T` has the same
trivial-character multiplicity before and after applying `τ_T`. -/
theorem tSideDadeMap_inner_trivial [Finite G]
    (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφ : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ) (trivialClassFunction G) =
      ClassFunction.inner φ (trivialClassFunction ↥hyp.base.T) := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hmem : φ ∈ ClassFunction.supportedSubmodule
      (G := ↥hyp.base.T) (k := ℂ)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :=
    (ClassFunction.mem_supportedSubmodule).mpr hφ
  have he : tSideDadeMap hyp hG φ =
      side.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩ := by
    change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData side.hconj) φ =
      side.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      side.dade _ hφ]
  have hψ : ∀ a : {a : G //
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T},
      (trivialClassFunction ↥hyp.base.T)
          ⟨a.1, side.dade.subset_L a.2⟩ =
        OddOrder.Peterfalvi.S04.adjointAverageFun side.dade
          (trivialClassFunction G) ⟨a.1, side.dade.subset_L a.2⟩ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.adjointAverageFun, dif_pos a.2]
    simp only [trivialClassFunction_apply, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  rw [he]
  exact OddOrder.Peterfalvi.S04.adjoint_formula side.dade
    side.dade.dadeMap
    (side.dade.isDadeMap_dadeMap (k := ℂ)) side.hconj
    ⟨φ, hmem⟩ (trivialClassFunction G)
    (trivialClassFunction ↥hyp.base.T) hψ

open scoped Classical in
/-- **Peterfalvi (14.9): the supported T-side difference
`βT0 = ν₀ - ζ`.**  If `ζ` is a degree-`p` virtual character supported on
`T'`, the concrete prime-TI anchor `ν₀` gives an integral difference
supported on `(T')^# = A₁(T)`.  Consequently its genuine T-side Dade image is
again a virtual character and vanishes at the identity. -/
theorem exists_typeIII_primeTIDifference_with_anchor_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [fintypeT : Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζZ : ζ ∈ ZIrr ↥hyp.base.T)
    (hζsupp : ζ.support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
        Set ↥hyp.base.T))
    (hζ1 : ζ 1 = (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ζ) ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ζ).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G ∧
        tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 ∧
        (ν0 - ζ).conj = ν0 - ζ.conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 := by
  have hfintypeT : fintypeT =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype hyp.base.T :=
    Subsingleton.elim _ _
  subst fintypeT
  have hinvertibleT : invertibleT =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC hyp.base.T :=
    Subsingleton.elim _ _
  subst invertibleT
  letI : Invertible (Nat.card ↥hyp.base.T : ℂ) :=
    OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC hyp.base.T
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνinner⟩ :=
    exists_typeIII_primeTIredZero_with_inner hG hyp hIII
  have hβZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T :=
    (ZIrr ↥hyp.base.T).sub_mem hνZ hζZ
  have hA :
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
        (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro x hx
    have hxK : x ∈
        (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      rcases ClassFunction.support_sub_subset ν0 ζ hx with hx | hx
      · exact hνsupp hx
      · exact hζsupp hx
    have hx1 : x ≠ 1 := by
      intro he
      apply ClassFunction.mem_support.mp hx
      rw [he, ClassFunction.sub_apply, hν1, hζ1, sub_self]
    exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hA x).2 ⟨hxK, hx1⟩
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτZ : tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        side.dade side.hconj hβsupp hβZ)
  have hτ1 : tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        side.dade side.hconj hβsupp)
  refine ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, ?_, hνinner⟩
  rw [ClassFunction.conj_sub, hνR]

open scoped Classical in
/-- The supported T-side difference with the anchor's principal coefficient
projected away for existing consumers. -/
theorem exists_typeIII_primeTIDifference [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζZ : ζ ∈ ZIrr ↥hyp.base.T)
    (hζsupp : ζ.support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
        Set ↥hyp.base.T))
    (hζ1 : ζ 1 = (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ζ) ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ζ).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G ∧
        tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 ∧
        (ν0 - ζ).conj = ν0 - ζ.conj := by
  obtain ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, hβconj, _⟩ :=
    exists_typeIII_primeTIDifference_with_anchor_inner hG hyp hIII
      hζZ hζsupp hζ1
  exact ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, hβconj⟩

open scoped Classical in
/-- A `calT1` source induced from the normal subgroup `T'` is supported on `T'`. -/
theorem typeIII_induced_source_support [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T]
    [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) :
    (ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction).support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
        Set ↥hyp.base.T) := by
  haveI : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  intro x hx
  by_contra h
  apply ClassFunction.mem_support.mp hx
  exact ClassFunction.induce_eq_zero_of_not_mem_normal θ.toClassFunction h

open scoped Classical in
/-- A linear `calT1` source induces to degree `[T:T'] = p`. -/
theorem typeIII_induced_source_degree [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T]
    [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθ1 : (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1) :
    ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction 1 = (hyp.base.p : ℂ) := by
  rw [ClassFunction.induce_apply_one, T_derived_index_eq_p hyp,
    hθ1, mul_one]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), full T-side bridge datum with its norm.**
For a nonprincipal irreducible source `θ` of `T'`, construct the same concrete
`ν₀` used by `exists_typeIII_primeTIDifference_with_anchor_inner`, but retain the
source norm `‖ν₀ - Ind θ‖² = p + 1` and its Dade-image norm.

The latter is not a new character hypothesis: it follows from the supported Dade
isometry on `A₁(T) = (T')#`. This packages exactly the norm input used by the
`FTtype34_structure` projection rigidity. -/
theorem exists_typeIII_induced_primeTIDifference_with_norm [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [fintypeT : Fintype ↥hyp.base.T]
    [fintypeK : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [invertibleK :
      Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
    (hζ1 : ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction 1 =
        (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ∈ ZIrr G ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) 1 = 0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj =
            ν0 - (ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ClassFunction.inner
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) =
          ((hyp.base.p : ℕ) + 1 : ℂ) := by
  have hfg : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hft : fintypeT =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype hyp.base.T :=
    Subsingleton.elim _ _
  subst fintypeT
  have hfk : fintypeK =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Subsingleton.elim _ _
  subst fintypeK
  have hig : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hit : invertibleT =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC hyp.base.T :=
    Subsingleton.elim _ _
  subst invertibleT
  have hik : invertibleK =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Subsingleton.elim _ _
  subst invertibleK
  let ζ := ClassFunction.induce
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
  change IsIrreducibleCharacter ζ at hζirr
  change ζ 1 = (hyp.base.p : ℂ) at hζ1
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hβnorm⟩ :=
    exists_typeIII_primeTIDifference_induced_inner_self hG hyp hIII θ hθne hζirr
  change ClassFunction.inner (ν0 - ζ) (ν0 - ζ) =
    ((hyp.base.p : ℕ) + 1 : ℂ) at hβnorm
  have hζsupp : ζ.support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) :=
    typeIII_induced_source_support hyp θ
  have hβZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T :=
    (ZIrr ↥hyp.base.T).sub_mem hνZ hζirr.mem_ZIrr
  have hA : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro x hx
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      rcases ClassFunction.support_sub_subset ν0 ζ hx with hx | hx
      · exact hνsupp hx
      · exact hζsupp hx
    have hx1 : x ≠ 1 := by
      intro he
      apply ClassFunction.mem_support.mp hx
      rw [he, ClassFunction.sub_apply, hν1, show ζ 1 = (hyp.base.p : ℂ) from hζ1, sub_self]
    exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hA x).2 ⟨hxK, hx1⟩
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτZ : tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        side.dade side.hconj hβsupp hβZ)
  have hτ1 : tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        side.dade side.hconj hβsupp)
  have hτnorm : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
      (tSideDadeMap hyp hG (ν0 - ζ)) = ((hyp.base.p : ℕ) + 1 : ℂ) := by
    have hS : ∀ s ∈ ({ν0 - ζ} : Set (ClassFunction ↥hyp.base.T ℂ)),
        s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hβsupp
    rw [show tSideDadeMap hyp hG =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData side.hconj) from rfl]
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      side.dade side.hconj hS
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ)))
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ))), hβnorm]
  refine ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, ?_, hνone, hβnorm, hτnorm⟩
  rw [ClassFunction.conj_sub, hνR]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the normed bridge retains anchor orthogonality.**
This is the projection-ready form of
`exists_typeIII_induced_primeTIDifference_with_norm`: the same canonical prime-TI
anchor is kept orthogonal to the induced source and its conjugate. -/
theorem exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
    [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [fintypeT : Fintype ↥hyp.base.T]
    [fintypeK : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [invertibleK :
      Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
    (hζ1 : ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction 1 =
        (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ∈ ZIrr G ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) 1 = 0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj =
            ν0 - (ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) = 0 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj = 0 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ClassFunction.inner
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ∀ sigma : ℂ ≃+* ℂ,
          ClassFunction.mapRingEquiv sigma ν0 = ν0 := by
  have hfg : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hft : fintypeT =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype hyp.base.T :=
    Subsingleton.elim _ _
  subst fintypeT
  have hfk : fintypeK =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Subsingleton.elim _ _
  subst fintypeK
  have hig : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hit : invertibleT =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC hyp.base.T :=
    Subsingleton.elim _ _
  subst invertibleT
  have hik : invertibleK =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Subsingleton.elim _ _
  subst invertibleK
  let ζ := ClassFunction.induce
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
  change IsIrreducibleCharacter ζ at hζirr
  change ζ 1 = (hyp.base.p : ℂ) at hζ1
  obtain ⟨ν0, hνZ, hνR, hνsupp, hν1, hνone, hνnorm, hνorth, hνfixed⟩ :=
    exists_typeIII_primeTIredZero_with_projectionData_and_galois hG hyp hIII
  let θc : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    ⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩
  have hθcne : θc ≠ trivialIrreducibleCharacter _ :=
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.irreducibleCharacter_conj_ne_trivial
      hθne
  have hνζ : ClassFunction.inner ν0 ζ = 0 := hνorth θ hθne
  have hνζc : ClassFunction.inner ν0 ζ.conj = 0 := by
    rw [ClassFunction.induce_conj
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
      (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)]
    exact hνorth θc hθcne
  have hζsupp : ζ.support ⊆
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T : Set ↥hyp.base.T) :=
    typeIII_induced_source_support hyp θ
  have hβZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T :=
    (ZIrr ↥hyp.base.T).sub_mem hνZ hζirr.mem_ZIrr
  have hA : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro x hx
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      rcases ClassFunction.support_sub_subset ν0 ζ hx with hx | hx
      · exact hνsupp hx
      · exact hζsupp hx
    have hx1 : x ≠ 1 := by
      intro he
      apply ClassFunction.mem_support.mp hx
      rw [he, ClassFunction.sub_apply, hν1, hζ1, sub_self]
    exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hA x).2 ⟨hxK, hx1⟩
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτZ : tSideDadeMap hyp hG (ν0 - ζ) ∈ ZIrr G := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        side.dade side.hconj hβsupp hβZ)
  have hτ1 : tSideDadeMap hyp hG (ν0 - ζ) 1 = 0 := by
    simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        side.dade side.hconj hβsupp)
  have hζν : ClassFunction.inner ζ ν0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hνζ, star_zero]
  have hβnorm : ClassFunction.inner (ν0 - ζ) (ν0 - ζ) =
      ((hyp.base.p : ℕ) + 1 : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hνnorm, hνζ, hζν, hζirr.inner_self_eq_one]
    ring
  have hτnorm : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
      (tSideDadeMap hyp hG (ν0 - ζ)) = ((hyp.base.p : ℕ) + 1 : ℂ) := by
    have hS : ∀ s ∈ ({ν0 - ζ} : Set (ClassFunction ↥hyp.base.T ℂ)),
        s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hβsupp
    rw [show tSideDadeMap hyp hG =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData side.hconj) from rfl]
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      side.dade side.hconj hS
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ)))
      (Submodule.subset_span (Set.mem_singleton (ν0 - ζ))), hβnorm]
  refine ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, ?_, hνone,
    hνζ, hνζc, hβnorm, hτnorm, hνfixed⟩
  rw [ClassFunction.conj_sub, hνR]

/-- The normed T-side prime-TI bridge with the canonical anchor's Galois
fixedness projected away for existing consumers. -/
theorem exists_typeIII_induced_primeTIDifference_with_norm_and_anchor_orthogonality
    [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [fintypeT : Fintype ↥hyp.base.T]
    [fintypeK : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [invertibleT : Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [invertibleK :
      Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθne : θ ≠ trivialIrreducibleCharacter _)
    (hζirr : IsIrreducibleCharacter
      (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
    (hζ1 : ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction 1 =
        (hyp.base.p : ℂ)) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            ∈ ZIrr ↥hyp.base.T ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) ∈ ZIrr G ∧
        tSideDadeMap hyp hG
          (ν0 - ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) 1 = 0 ∧
        (ν0 - ClassFunction.induce
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj =
            ν0 - (ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj ∧
        ClassFunction.inner ν0 (trivialClassFunction ↥hyp.base.T) = 1 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) = 0 ∧
        ClassFunction.inner ν0
          (ClassFunction.induce
            ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction).conj = 0 ∧
        ClassFunction.inner
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)
            (ν0 - ClassFunction.induce
              ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) =
          ((hyp.base.p : ℕ) + 1 : ℂ) ∧
        ClassFunction.inner
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))
            (tSideDadeMap hyp hG
              (ν0 - ClassFunction.induce
                ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) =
          ((hyp.base.p : ℕ) + 1 : ℂ) := by
  obtain ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, hβconj, hνone,
      hνζ, hνζc, hβnorm, hτnorm, _⟩ :=
    exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
      hG hyp hIII θ hθne hζirr hζ1
  exact ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτZ, hτ1, hβconj, hνone,
    hνζ, hνζc, hβnorm, hτnorm⟩

end OddOrder.Peterfalvi.S16
