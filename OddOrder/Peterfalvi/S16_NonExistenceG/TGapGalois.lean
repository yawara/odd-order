/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapProjectionResidual
import OddOrder.Peterfalvi.S07_CoherenceGalois
import OddOrder.Algebra.GaloisRationalInteger

/-!
# Peterfalvi (11.9)(a): Galois transport of the T-side bridge

The Galois transform of a Dade bridge differs from the original bridge by the
Dade image of the source-character correction.  This is Coq `FTtype34_structure`
lemma `aut_phi`, isolated before the cyclotomic transitivity argument.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory


/-- A coefficient automorphism preserves the inner product of two virtual characters.
Unlike `ClassFunction.mapRingEquiv_inner`, no global commutation with complex conjugation is
needed: virtual-character values satisfy `chi(g^-1) = star (chi(g))`, and the common inner
product is a rational integer. -/
theorem inner_mapRingEquiv_eq_of_mem_ZIrr
    {L : Type*} [Group L] [Finite L] [Fintype L]
    [Invertible (Nat.card L : Complex)]
    (sigma : Complex ≃+* Complex) {phi eta : ClassFunction L Complex}
    (hphi : phi ∈ ZIrr L) (heta : eta ∈ ZIrr L) :
    ClassFunction.inner (ClassFunction.mapRingEquiv sigma phi)
        (ClassFunction.mapRingEquiv sigma eta) =
      ClassFunction.inner phi eta := by
  have hstar (g : L) :
      star (ClassFunction.mapRingEquiv sigma eta g) = sigma (star (eta g)) := by
    rw [← OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr
      (ClassFunction.mapRingEquiv_mem_ZIrr sigma heta) g,
      ClassFunction.mapRingEquiv_apply,
      OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr heta g]
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hphi heta
  have hsum :
      ClassFunction.innerSum (ClassFunction.mapRingEquiv sigma phi)
          (ClassFunction.mapRingEquiv sigma eta) =
        sigma (ClassFunction.innerSum phi eta) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    change sigma (phi g) * star (sigma (eta g)) =
      sigma (phi g * star (eta g))
    have hg := hstar g
    change star (sigma (eta g)) = sigma (star (eta g)) at hg
    rw [hg, map_mul]
  calc
    ClassFunction.inner (ClassFunction.mapRingEquiv sigma phi)
        (ClassFunction.mapRingEquiv sigma eta) =
        sigma (ClassFunction.inner phi eta) := by
      rw [ClassFunction.inner, ClassFunction.inner, hsum]
      have hcoef : sigma (⅟(Nat.card L : Complex)) = ⅟(Nat.card L : Complex) := by
        simp [invOf_eq_inv, map_inv₀, map_natCast]
      calc
        ⅟(Nat.card L : Complex) * sigma (ClassFunction.innerSum phi eta) =
            sigma (⅟(Nat.card L : Complex)) *
              sigma (ClassFunction.innerSum phi eta) := by rw [hcoef]
        _ = sigma (⅟(Nat.card L : Complex) *
              ClassFunction.innerSum phi eta) := (map_mul sigma _ _).symm
    _ = ClassFunction.inner phi eta := by rw [hm]; simp

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The canonical prime-TI anchor `primeTIred 0 = Ind 1` is fixed by every
coefficient automorphism.  This is the source-side fixed point used in
Peterfalvi Galois transport identity. -/
theorem primeTIred_zero_mapRingEquiv
    {S : Type*} [Group S] [Fintype S]
    {PU : Subgroup S} [Fintype PU] [Invertible (Nat.card PU : Complex)]
    {q p : Nat} [NeZero q] [NeZero p]
    (D : PrimeTIResidueData S PU q p) (sigma : RingEquiv Complex Complex) :
    ClassFunction.mapRingEquiv sigma (D.primeTIred 0) = D.primeTIred 0 := by
  rw [(D.cfInd_prTIres 0).symm, D.prTIres0, ClassFunction.mapRingEquiv_induce]
  congr 1
  ext x
  simp [ClassFunction.mapRingEquiv_apply, trivialClassFunction_apply]

/-- If a Galois transport changes `φ` only by a correction orthogonal to the
transported test function, then every integral coefficient of `φ` is unchanged. -/
theorem inner_eq_intCast_of_mapRingEquiv_eq_add
    {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {φ η η' correction : ClassFunction L ℂ} (m : ℤ)
    (hφZ : φ ∈ ZIrr L) (hηZ : η ∈ ZIrr L)
    (hφ : ClassFunction.mapRingEquiv σc φ = φ + correction)
    (hη : ClassFunction.mapRingEquiv σc η = η')
    (hm : ClassFunction.inner φ η = (m : ℂ))
    (hcorrection : ClassFunction.inner correction η' = 0) :
    ClassFunction.inner φ η' = (m : ℂ) := by
  have htransport := inner_mapRingEquiv_eq_of_mem_ZIrr σc hφZ hηZ
  rw [hφ, hη, ClassFunction.inner_add_left, hcorrection, add_zero, hm] at htransport
  simpa using htransport

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), Galois bridge decomposition** (Coq `aut_phi`).
If the prime-TI anchor `ν₀` is fixed by a coefficient automorphism `σ`, then

`σ(τ_T(ν₀ - ζ)) = τ_T(ν₀ - ζ) + τ_T(ζ - σζ)`.

The only character-theoretic input is the supportedness of `ν₀ - ζ`: it lets
the explicit Dade map commute with `σ`.  The remaining identity is linearity. -/
theorem tSideDadeMap_mapRingEquiv_bridge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hν0 : ClassFunction.mapRingEquiv σc ν0 = ν0)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.mapRingEquiv σc (tSideDadeMap hyp hG (ν0 - ζ)) =
      tSideDadeMap hyp hG (ν0 - ζ) +
        tSideDadeMap hyp hG (ζ - ClassFunction.mapRingEquiv σc ζ) := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  change ClassFunction.mapRingEquiv σc
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData side.hconj) (ν0 - ζ)) = _
  rw [← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    side.dade (side.dade.fullDadeIsometryData side.hconj) σc hbridgeSupp]
  change tSideDadeMap hyp hG (ClassFunction.mapRingEquiv σc (ν0 - ζ)) = _
  rw [← map_add]
  congr 1
  rw [ClassFunction.mapRingEquiv_sub, hν0]
  abel

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- A supported difference of two coherent-family members has Dade image
orthogonal to every test function orthogonal to the two coherent images. -/
theorem tSideDadeMap_inner_eq_zero_of_coherent_difference [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ ζ' : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S) (hζ' : ζ' ∈ S)
    (hdiffSupp : (ζ - ζ').support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {η : ClassFunction G ℂ}
    (horth : ∀ ξ ∈ S, ClassFunction.inner (coh.extension ξ) η = 0) :
    ClassFunction.inner (tSideDadeMap hyp hG (ζ - ζ')) η = 0 := by
  have hdiffSupported : ζ - ζ' ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hζ)
      (Submodule.subset_span hζ'), hdiffSupp⟩
  rw [← coh.extends_on_supported (ζ - ζ') hdiffSupported, map_sub,
    ClassFunction.inner_sub_left, horth ζ hζ, horth ζ' hζ', sub_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral coefficient transport** (Coq `a_aut`).
The Galois bridge identity and coherent-difference orthogonality force an
integral eta coefficient to be constant along the chosen Galois transport. -/
theorem tSideDadeMap_inner_galois_eq_intCast [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    {η η' : ClassFunction G ℂ} (m : ℤ)
    (hν0 : ClassFunction.mapRingEquiv σc ν0 = ν0)
    (hbridgeZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hη : ClassFunction.mapRingEquiv σc η = η')
    (hηZ : η ∈ ZIrr G)
    (hm : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ)) η = (m : ℂ))
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hζ : ζ ∈ S) (hσζ : ClassFunction.mapRingEquiv σc ζ ∈ S)
    (hcorrSupp : (ζ - ClassFunction.mapRingEquiv σc ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (horth : ∀ ξ ∈ S, ClassFunction.inner (coh.extension ξ) η' = 0) :
    ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ)) η' = (m : ℂ) := by
  apply inner_eq_intCast_of_mapRingEquiv_eq_add σc m
  · simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (tSideDadeSupport_nonempty hG hyp).some.dade
        (tSideDadeSupport_nonempty hG hyp).some.hconj hbridgeSupp hbridgeZ)
  · exact hηZ
  · exact tSideDadeMap_mapRingEquiv_bridge hG hyp σc hν0 hbridgeSupp
  · exact hη
  · exact hm
  · exact tSideDadeMap_inner_eq_zero_of_coherent_difference hG hyp coh
      hζ hσζ hcorrSupp horth

end OddOrder.Peterfalvi.S16
