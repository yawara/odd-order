/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TTypeIICoherence

/-!
# Peterfalvi (11.9)(a): nonzero T-side eta-projection residual

The coherent correction to a T-side Dade bridge is orthogonal to the shared eta-grid.
Together with the supported Dade isometry, a nonzero source pairing therefore witnesses
that the bridge's perpendicular eta-grid residual is nonzero.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the perpendicular T-side residual is nonzero.**
Let `ζ` belong to the coherent T-side family and let `φ` be supported on `A₁(T)`.
If `φ` is not orthogonal to `ζ - ζ̄`, then the Dade image of this difference is a test
virtual character which:

* is not orthogonal to the Dade image of `φ`, by the supported Dade isometry;
* is orthogonal to every eta-grid character, because coherence identifies it with
  `τ₁ζ - τ₁ζ̄` and both coherent images are eta-orthogonal.

Hence no eta-grid projection of the Dade image of `φ` can equal the whole image. -/
theorem tSide_etaGridProjection_residual_ne_zero_of_coherent_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hsupp : ∀ ξ ∈ S, (ξ - ξ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {ζ φ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ)
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hφpair : ClassFunction.inner φ (ζ - ζ.conj) ≠ 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ) :
    tSideDadeMap hyp hG φ - etaGridProjection hyp.base m ≠ 0 := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  let theta : ClassFunction ↥hyp.base.T ℂ := ζ - ζ.conj
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hthetaSupp : theta.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    simpa [theta] using hsupp ζ hζ
  have hthetaSupported : theta ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
    refine ⟨?_, hthetaSupp⟩
    exact Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hcorr : tSideDadeMap hyp hG theta =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [← coh.extends_on_supported theta hthetaSupported, map_sub]
  have hpair :
      ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG theta) ≠ 0 := by
    simp only [tSideDadeMap]
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (tSideDadeSupport_nonempty hG hyp).some.dade
      (tSideDadeSupport_nonempty hG hyp).some.hconj hφsupp hthetaSupp]
    simpa [theta] using hφpair
  have hζeta := T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
    hyp07.conjugate_closed hyp07.no_real_characters hsupp coh hζ hζirr
  have hζceta := T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
    hyp07.conjugate_closed hyp07.no_real_characters hsupp coh hζc hζirr.conj
  apply etaGrid_projection_residual_ne_zero_of_inner hyp.base
    (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG theta) m hpair
  intro i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hcorr,
    ClassFunction.inner_sub_left, hζeta i j, hζceta i j, sub_zero, star_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Specialise the coherent-pair residual witness to the bridge source `ν₀ - ζ`.
It is enough that the prime-TI anchor `ν₀` be orthogonal to both `ζ` and `ζ̄`;
the coherent family supplies `ζ ⟂ ζ̄` and irreducibility supplies `‖ζ‖² = 1`,
so `⟨ν₀-ζ, ζ-ζ̄⟩ = -1`. -/
theorem tSide_etaGridProjection_residual_ne_zero_of_anchor_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hsupp : ∀ ξ ∈ S, (ξ - ξ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hνζ : ClassFunction.inner ν0 ζ = 0)
    (hνζc : ClassFunction.inner ν0 ζ.conj = 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ) :
    tSideDadeMap hyp hG (ν0 - ζ) - etaGridProjection hyp.base m ≠ 0 := by
  apply tSide_etaGridProjection_residual_ne_zero_of_coherent_pair
    hG hyp hIII hyp07 coh hsupp hζ hζirr hbridgeSupp ?_ m
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hζne : ζ ≠ ζ.conj := hyp07.ne_conj hζ
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 :=
    hyp07.pairwise_orthogonal hζ hζc hζne
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hνζ, hνζc, hζirr.inner_self_eq_one, hζζc]
  norm_num

end OddOrder.Peterfalvi.S16
