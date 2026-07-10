import OddOrder.Peterfalvi.S16_NonExistenceG.TGapPrimeTI
import OddOrder.Peterfalvi.S13_Orthogonality

/-!
# Peterfalvi (14.9): the T-side residual character

Coherence consequences used for
`Δ = τ_T (ν₀ - ζ) - 1_G + τ₁ ζ`: first, every coherent image of a
nonprincipal conjugate-paired source is orthogonal to the trivial character.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (7.8.a), specialised to the T-side coherent extension.**
If `ζ` and `ζ̄` are distinct orthonormal members of the T-side family, their
difference is `A₁(T)`-supported, and `ζ ⟂ 1_T`, then the coherent image
`τ₁ ζ` is orthogonal to `1_G`.

The proof combines the genuine T-side (2.7) adjoint identity with the generic
equal-degree coherent-pair argument; no cross-maximal input is used. -/
theorem tSideCoherentExtension_inner_trivial [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ClassFunction.inner ζ (trivialClassFunction ↥hyp.base.T) = 0)
    (hsupp : (ζ.conj - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (coh.extension ζ) (trivialClassFunction G) = 0 := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥hyp.base.T ℂ),
      tSideDadeMap hyp hG (c • x) = c • tSideDadeMap hyp hG x := by
    intro c x
    simpa only [tSideDadeMap] using
      (OddOrder.Peterfalvi.S09.Cert.dadeIntegralCharacterMap_smul_complex
        side.dade (side.dade.fullDadeIsometryData side.hconj) c x)
  have hconstG :
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G =
        trivialClassFunction G := by
    ext g
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
  have hconstT :
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T =
        trivialClassFunction ↥hyp.base.T := by
    ext t
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
  have htau1 : ∀ φ : ClassFunction ↥hyp.base.T ℂ,
      φ.support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T →
        ClassFunction.inner (tSideDadeMap hyp hG φ)
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) =
          ClassFunction.inner φ
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T) := by
    intro φ hφ
    rw [hconstG, hconstT]
    exact tSideDadeMap_inner_trivial hyp hG hφ
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hζne : ζ ≠ ζ.conj := hyp07.ne_conj hζ
  have hζc1 : ClassFunction.inner ζ.conj
      (trivialClassFunction ↥hyp.base.T) = 0 := by
    rw [← trivialClassFunction_isReal,
      OddOrder.RepresentationTheory.inner_conj_conj, hζ1, star_zero]
  have h :=
    OddOrder.Peterfalvi.S09.Cert.coherence_extension_orthogonal_constOne
      coh hτ_smul htau1 hζ hζc hζirr.inner_self_eq_one
      hζirr.conj.inner_self_eq_one
      (hyp07.pairwise_orthogonal hζ hζc hζne) hsupp
      (by rw [hconstT]; exact hζ1)
      (by rw [hconstT]; exact hζc1)
  rwa [hconstG] at h

open scoped Classical in
/-- The genuine T-side Dade map commutes with complex conjugation on its
supported domain. -/
theorem tSideDadeMap_conj_of_support [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφ : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    (tSideDadeMap hyp hG φ).conj = tSideDadeMap hyp hG φ.conj := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  have hbridgeT : ∀ X : ClassFunction ↥hyp.base.T ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext t
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  change (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
      (side.dade.fullDadeIsometryData side.hconj) φ).conj =
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
      (side.dade.fullDadeIsometryData side.hconj) φ.conj
  rw [hbridgeG, hbridgeT]
  exact (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    side.dade (side.dade.fullDadeIsometryData side.hconj)
    Complex.conjAe.toRingEquiv hφ).symm

open scoped Classical in
/-- **Peterfalvi (5.9.a), specialised to the type-III T-side family.**
The coherent extension of the degree-`p` family induced from `T'` commutes
with complex conjugation.

The substantive support input is derived rather than assumed: the family is
contained in `inducedKernelFamily T' bot`, so every element of its integral
span that vanishes at `1` is supported on `(T')# = A₁(T)`. -/
theorem tSideCoherentExtension_conj [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (S : Set (ClassFunction ↥hyp.base.T ℂ))
    (hS : S = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    {ζ : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S) :
    (coh.extension ζ).conj = coh.extension ζ.conj := by
  let K := (derivedInG hyp.base.T).subgroupOf hyp.base.T
  haveI : K.Normal := T_derivedSubgroupOf_normal hyp
  have hSsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily K ⊥ := by
    intro φ hφ
    rw [hS, Finset.mem_coe, Finset.mem_image] at hφ
    obtain ⟨θ, hθ, rfl⟩ := hφ
    refine ⟨θ, hne θ hθ, ?_, rfl⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hAsharp : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hKsupp : ∀ x : ↥hyp.base.T, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro x hx hx1
    exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAsharp x).2 ⟨hx, hx1⟩
  have hspan : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan S, φ 1 = 0 →
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro φ hφ hφ1
    exact OddOrder.Peterfalvi.S13.inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hKsupp (Submodule.span_mono hSsub hφ) hφ1
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  have hbridgeT : ∀ X : ClassFunction ↥hyp.base.T ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext t
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  rw [hbridgeG (coh.extension ζ), hbridgeT ζ]
  exact coh.extension_mapRingEquiv_comm subset_rfl
    (fun χ hχ => mem_irreducibleCharacters.mpr (hirr χ hχ)) hspan
    Complex.conjAe.toRingEquiv
    (fun χ hχ => by rw [← hbridgeT χ]; exact hyp07.conjugate_closed hχ)
    (fun χ hχ => coh.extension_mem_ZIrr χ (Submodule.subset_span hχ)) hζ
    ⟨ζ.conj, hyp07.conjugate_closed hζ, (hyp07.ne_conj hζ).symm⟩

open scoped Classical in
/-- **Peterfalvi (14.9): reality of the T-side residual**
`Δ = τ_T(ν₀ - ζ) - 1_G + τ₁ζ`.

The Dade image commutes with conjugation, while coherence identifies the
supported difference `τ_T(ζ - ζ̄)` with `τ₁ζ - τ₁ζ̄`; these two differences
cancel in `Δ̄ - Δ`. -/
theorem tSideDelta_isReal [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζc : ζ.conj ∈ S)
    (hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hdiffSupp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hβconj : (ν0 - ζ).conj = ν0 - ζ.conj)
    (hExtConj : (coh.extension ζ).conj = coh.extension ζ.conj) :
    ClassFunction.IsReal
      (tSideDadeMap hyp hG (ν0 - ζ) -
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        coh.extension ζ) := by
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), hdiffSupp⟩
  have hagree : tSideDadeMap hyp hG (ζ - ζ.conj) =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  have hτconjSub : (tSideDadeMap hyp hG (ν0 - ζ)).conj -
        tSideDadeMap hyp hG (ν0 - ζ) =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [tSideDadeMap_conj_of_support hyp hG hβsupp]
    calc
      tSideDadeMap hyp hG (ν0 - ζ).conj - tSideDadeMap hyp hG (ν0 - ζ) =
          tSideDadeMap hyp hG ((ν0 - ζ).conj - (ν0 - ζ)) :=
        (map_sub (tSideDadeMap hyp hG) (ν0 - ζ).conj (ν0 - ζ)).symm
      _ = tSideDadeMap hyp hG (ζ - ζ.conj) := by
        congr 1
        rw [hβconj]
        abel
      _ = coh.extension ζ - coh.extension ζ.conj := hagree
  have hτconjEq : (tSideDadeMap hyp hG (ν0 - ζ)).conj =
      (coh.extension ζ - coh.extension ζ.conj) + tSideDadeMap hyp hG (ν0 - ζ) :=
    (sub_eq_iff_eq_add).mp hτconjSub
  rw [ClassFunction.IsReal, ClassFunction.conj_add, ClassFunction.conj_sub,
    hExtConj, hτconjEq]
  have hOneReal :
      (trivialIrreducibleCharacter G : ClassFunction G ℂ).conj =
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) :=
    trivialClassFunction_isReal
  rw [hOneReal]
  abel

end OddOrder.Peterfalvi.S16
