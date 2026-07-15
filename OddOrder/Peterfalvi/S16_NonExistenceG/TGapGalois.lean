/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapProjectionResidual
import OddOrder.Peterfalvi.S07_CoherenceGalois
import OddOrder.GroupTheory.RepresentationTheory.GaloisInnerTransport

/-!
# Peterfalvi (11.9)(a): Galois transport of the T-side bridge

The Galois transform of a Dade bridge differs from the original bridge by the
Dade image of the source-character correction.  This is Coq `FTtype34_structure`
lemma `aut_phi`, isolated before the cyclotomic transitivity argument.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory



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
  apply ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add σc m
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


open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), Galois constancy on the two eta axes.**
Assume the nonprincipal row and column eta characters are coefficient-Galois conjugate to
`eta_10` and `eta_01`.  Galois closure of the coherent source family, supportedness of all
family differences, and coherent-image orthogonality then turn `a_aut` into equality of the
integer projection coefficients along each axis.  This is the character-theoretic input of
`etaGrid_coefficients_eq_column_or_row`. -/
theorem tSideDadeMap_eta_axis_coefficients_constant [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {nu0 zeta : ClassFunction ↥hyp.base.T ℂ}
    (hbridgeZ : nu0 - zeta ∈ ZIrr ↥hyp.base.T)
    (hbridgeSupp : (nu0 - zeta).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hzeta : zeta ∈ S)
    (hgalois : ∀ (sigma : ℂ ≃+* ℂ) xi, xi ∈ S →
      ClassFunction.mapRingEquiv sigma xi ∈ S)
    (hdiffSupp : ∀ xi ∈ S, ∀ xi' ∈ S, (xi - xi').support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (horth : ∀ xi ∈ S, ∀ i : Fin hyp.base.q, ∀ j : Fin hyp.base.p,
      ClassFunction.inner (coh.extension xi) (hyp.base.eta i j) = 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hm : ∀ i j, ClassFunction.inner (tSideDadeMap hyp hG (nu0 - zeta))
      (hyp.base.eta i j) = (m i j : ℂ))
    (hnu0 : ∀ sigma : ℂ ≃+* ℂ, ClassFunction.mapRingEquiv sigma nu0 = nu0)
    (hrowOrbit : ∀ i : Fin hyp.base.q, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (hyp.base.eta ⟨1, hyp.base.q_prime.one_lt⟩
              ⟨0, hyp.base.p_prime.pos⟩) =
          hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)
    (hcolumnOrbit : ∀ j : Fin hyp.base.p, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
              ⟨1, hyp.base.p_prime.one_lt⟩) =
          hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :
    (∀ i : Fin hyp.base.q, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      m i ⟨0, hyp.base.p_prime.pos⟩ =
        m ⟨1, hyp.base.q_prime.one_lt⟩ ⟨0, hyp.base.p_prime.pos⟩) ∧
    (∀ j : Fin hyp.base.p, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      m ⟨0, hyp.base.q_prime.pos⟩ j =
        m ⟨0, hyp.base.q_prime.pos⟩ ⟨1, hyp.base.p_prime.one_lt⟩) := by
  constructor
  · intro i hi
    obtain ⟨sigma, hsigma⟩ := hrowOrbit i hi
    have hsigmaZ := hgalois sigma zeta hzeta
    have htransport := tSideDadeMap_inner_galois_eq_intCast hG hyp sigma
      (m ⟨1, hyp.base.q_prime.one_lt⟩ ⟨0, hyp.base.p_prime.pos⟩)
      (hnu0 sigma) hbridgeZ hbridgeSupp hsigma
      (eta_mem_ZIrr hyp.base _ _) (hm _ _) coh hzeta hsigmaZ
      (hdiffSupp zeta hzeta _ hsigmaZ)
      (fun xi hxi => horth xi hxi i ⟨0, hyp.base.p_prime.pos⟩)
    exact Int.cast_injective ((hm i ⟨0, hyp.base.p_prime.pos⟩).symm.trans htransport)
  · intro j hj
    obtain ⟨sigma, hsigma⟩ := hcolumnOrbit j hj
    have hsigmaZ := hgalois sigma zeta hzeta
    have htransport := tSideDadeMap_inner_galois_eq_intCast hG hyp sigma
      (m ⟨0, hyp.base.q_prime.pos⟩ ⟨1, hyp.base.p_prime.one_lt⟩)
      (hnu0 sigma) hbridgeZ hbridgeSupp hsigma
      (eta_mem_ZIrr hyp.base _ _) (hm _ _) coh hzeta hsigmaZ
      (hdiffSupp zeta hzeta _ hsigmaZ)
      (fun xi hxi => horth xi hxi ⟨0, hyp.base.q_prime.pos⟩ j)
    exact Int.cast_injective ((hm ⟨0, hyp.base.q_prime.pos⟩ j).symm.trans htransport)

/-- **Peterfalvi (3.9.b), the threaded full Galois orbits in eta-grid notation.**
The Section 16 carrier stores the producer equalities in their canonical form
`mapRingEquiv u (tau3 (omega ...)) = tau3 (omega ...)`; the defining identity
`eta = tau3 ∘ omega` turns them into the exact row/column orbit pair consumed by
`tSideDadeMap_eta_axis_coefficients_constant`. -/
theorem eta_axis_galois_orbits_of_hypothesis
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (∀ i : Fin base.q, i ≠ ⟨0, base.q_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (base.eta ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩) =
          base.eta i ⟨0, base.p_prime.pos⟩) ∧
    (∀ j : Fin base.p, j ≠ ⟨0, base.p_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (base.eta ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩) =
          base.eta ⟨0, base.q_prime.pos⟩ j) := by
  constructor
  · intro i hi
    obtain ⟨sigma, hsigma⟩ := base.eta_row_galois_orbit i hi
    refine ⟨sigma, ?_⟩
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega]
    exact hsigma
  · intro j hj
    obtain ⟨sigma, hsigma⟩ := base.eta_column_galois_orbit j hj
    refine ⟨sigma, ?_⟩
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega]
    exact hsigma

end OddOrder.Peterfalvi.S16
