import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core.CharacterParameters
import OddOrder.Peterfalvi.S13_MaximalIII_IVBasic
import OddOrder.Peterfalvi.S13_Orthogonality
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapCross

/-!
# Peterfalvi (11.8): T-side non-orthogonality inputs

Producer-level bridges needed to apply the Section 11 non-orthogonality
calculation to each member of the T-side coherent family, rather than to a
freshly reselected distinguished character.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Peterfalvi (10.1), the Section 12 carrier with a specified type-`P`
decomposition.**  The standard existence theorem chooses an unspecified
`TypePData`.  For cross-construction comparisons we must retain the already
reconciled `W₁,W₂` factors; the faithful type-`P₁` Dade producer works for that
specified datum verbatim. -/
noncomputable def s12HypothesisOfTypePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.Peterfalvi.S12.Hypothesis M := by
  let dadeData :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
      hG hM data hP1).some
  exact
    { maximal := hM
      typeP := data
      type_alt := htype
      dadeData := dadeData
      hconj := dadeData.hconj }

open scoped Classical in
/-- **Peterfalvi (4.4)--(4.5), the Section 12 zero column is the prime-TI
anchor.**  The column-`0` dual is trivial, so its distinguished constituent
restricts to `1_{M'}`.  Summing the whole column and applying (4.5.a) therefore
gives exactly `Ind_{M'}^M 1`, independently of every enumeration choice.

This is the source-side identification needed to compare the Section 11
residual with `primeTIred 0` in the T-side (11.9.a) projection. -/
theorem s12_muGrid_zeroColumn_sum_eq_induce_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
      ClassFunction.induce ((derivedInG M).subgroupOf M)
        (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let chi2 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  have hchi2 : chi2 = 1 := by
    dsimp only [chi2]
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by
      apply Fin.ext
      simp, OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  have hsum : ClassFunction.induce h.K
        (ClassFunction.restrict h.K
          ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ)) =
      ∑ i : Fin (Nat.card h.W1),
        ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) :=
    h.induce_restrict_certainType_eq chi2
  have hsource : ClassFunction.restrict h.K
        ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ) =
      trivialClassFunction ↥h.K := by
    rw [hchi2, h.certainType_zero_column_anchor.2]
    ext x
    simp
  rw [hsource] at hsum
  calc
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
        ∑ i : Fin (Nat.card h.W1),
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) := by
      rw [← Equiv.sum_comp (finCongr hcardW1.symm)
        (fun i : Fin (Nat.card h.W1) =>
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ))]
      exact Finset.sum_congr rfl (fun i _ => by
        unfold OddOrder.Peterfalvi.S12.Hypothesis.muGrid
        rfl)
    _ = ClassFunction.induce h.K (trivialClassFunction ↥h.K) := hsum.symm
    _ = ClassFunction.induce ((derivedInG M).subgroupOf M)
          (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := rfl

open scoped Classical in
/-- **Peterfalvi (2.11)/(11.8), the Section 12 residual uses the T-side
Dade map.**  For the specified type-`P₁` datum, the Section 12 full `A₀(T)`
map restricts to the canonical `A₁(T)` map.  Together with the zero-column
anchor above, this identifies the complete source term used by (11.8) with
the `τ_T(ν₀-ζ)` term of (11.9.a). -/
theorem s12Tau_zeroColumn_sub_eq_tSideDadeMap [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (side : Hypothesis (G := G))
    (dataT : TypePData side.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 side.base.T)
    (hIII : IsTypeIII side.base.T)
    (zeta nu0 : ClassFunction ↥side.base.T ℂ)
    (hnu0 : nu0 = ClassFunction.induce
      ((derivedInG side.base.T).subgroupOf side.base.T)
      (trivialClassFunction
        ↥((derivedInG side.base.T).subgroupOf side.base.T)))
    (hsupp : (nu0 - zeta).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp side.base.T) side.base.T) :
    let hyp12 := s12HypothesisOfTypePData hG side.base.T_maximal dataT
      (Or.inl hIII) hP1
    hyp12.tau
        ((∑ i : Fin hyp12.w1, hyp12.muGrid hG hG.odd i 0) - zeta) =
      tSideDadeMap side hG (nu0 - zeta) := by
  let hyp12 := s12HypothesisOfTypePData hG side.base.T_maximal dataT
    (Or.inl hIII) hP1
  have hanchor := s12_muGrid_zeroColumn_sum_eq_induce_trivial hG hyp12
  have hmap := tSideDadeMap_eq_full_typeP1DadeMap_of_support
    hG side dataT hP1 hsupp
  change hyp12.tau
      ((∑ i : Fin hyp12.w1, hyp12.muGrid hG hG.odd i 0) - zeta) =
    tSideDadeMap side hG (nu0 - zeta)
  rw [hanchor, ← hnu0]
  simpa only [hyp12, s12HypothesisOfTypePData,
    OddOrder.Peterfalvi.S12.Hypothesis.tau] using hmap.symm

open scoped Classical in
/-- **Peterfalvi (11.8.6), grid-parametric column assembly.**
The opening identity is purely linear and does not depend on how the
`omegaSigma` grid was constructed.  Given the rowwise `alpha` images and the
normalized zero-column image for any grid, it assembles
`tau (mu_j - d*zeta) = sum_i grid_ij - d*zeta^tau1`.

This is the arbitrary-σ counterpart of
`S12.Hypothesis.tau_muColumnSum_sub_zeta_eq_of_alphaImage`; it is needed for
the S15 `eta` grid, whose σ-isometry is valid but not definitionally the
canonical S12 choice. -/
theorem tau_muColumnSum_sub_zeta_eq_of_grid_alphaImage [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (j : Fin hyp.w2) {zeta : ClassFunction ↥M ℂ} {d n : ℕ}
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (halpha : ∀ i : Fin hyp.w1,
      hyp.tau
          (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i 0 -
            (n : ℂ) • zeta) =
        grid i j - grid i 0 - (n : ℂ) • coh.extension zeta)
    (hzero : hyp.tau
        ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - zeta) =
      (∑ i : Fin hyp.w1, grid i 0) - coh.extension zeta) :
    hyp.tau
        ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (d : ℂ) • zeta) =
      (∑ i : Fin hyp.w1, grid i j) - (d : ℂ) • coh.extension zeta := by
  have hMlevel :
      ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (d : ℂ) • zeta) =
        ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - zeta) +
          ∑ i : Fin hyp.w1,
            (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i 0 -
              (n : ℂ) • zeta) := by
    have hsum :
        (∑ i : Fin hyp.w1,
          (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i 0 -
            (n : ℂ) • zeta)) =
          (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) -
            (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) -
              ((hyp.w1 : ℂ) * (n : ℂ)) • zeta := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
    rw [hsum, hd]
    module
  rw [hMlevel, map_add, hzero, map_sum,
    Finset.sum_congr rfl (fun i _ => halpha i)]
  have hsum :
      (∑ i : Fin hyp.w1,
        (grid i j - grid i 0 - (n : ℂ) • coh.extension zeta)) =
        (∑ i : Fin hyp.w1, grid i j) -
          (∑ i : Fin hyp.w1, grid i 0) -
            ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension zeta := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
  rw [hsum, hd]
  module

/-- **Peterfalvi (10.2)--(10.3), character parameters based at a specified
family member.**  The arithmetic data `d`, `delta`, and `n` depend only on the
maximal subgroup.  Hence the standard parameter construction can retain any
specified degree-`w₁` irreducible member `zeta` instead of discarding it and
choosing a new distinguished character.

This is the producer needed by the arbitrary-member form of the (11.8)
non-orthogonality calculation used in (11.9.a). -/
theorem exists_charParameters_full_for_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ∃ params : OddOrder.Peterfalvi.S12.CharacterParameters hyp,
      params.zeta = zeta ∧
      params.mu = hyp.muGrid hG hG.odd ∧
      params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd ∧
      params.zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
      params.zeta 1 = (hyp.w1 : ℂ) ∧
      params.zeta.conj ≠ params.zeta ∧
      (params.delta = 1 ∨ params.delta = -1) ∧
      ∀ j : Fin hyp.w2, j ≠ 0 →
        hyp.muColumnSign hG hG.odd j = params.delta := by
  haveI := hyp.finiteG
  classical
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hdelta⟩ :=
    hyp.exists_charParamArith hG hG.odd
  let params : OddOrder.Peterfalvi.S12.CharacterParameters hyp :=
    { zeta := zeta
      zeta_mem_S := hzetaS
      zeta_irreducible := hzetairr
      d := d
      delta := delta
      n := n
      w2_prime := hyp.w2_prime hG
      d_gt_one := hd1
      mu := hyp.muGrid hG hG.odd
      omegaSigma := hyp.alignedOmegaSigmaGrid hG hG.odd
      degree_independent := hdi
      n_formula := hnf
      two_le_n := hn2
      alpha_support := fun i j hj =>
        hyp.muGrid_alpha_support hG hG.odd hj hzetaS (hdi i j hj)
          (hyp.muGrid_zero_column_apply_one hG hG.odd i) hzeta1 hnf (hdelta j hj)
      typeV_parameter_formula := True
      typeV_coherence_formula := True }
  refine ⟨params, rfl, rfl, rfl, hzetaS, hzeta1, ?_, ?_, hdelta⟩
  · exact hyp.inducedFamily_degree_w1_conj_ne hG hzetairr hzeta1
  · have hw2 : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
    have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by simp [Fin.ext_iff]
    have hde := hdelta ⟨1, by omega⟩ hj
    have hs := hyp.muColumnSign_eq_one_or_neg_one hG hG.odd ⟨1, by omega⟩
    rw [hde] at hs
    exact hs

/-- **Peterfalvi (11.1)--(11.7), the Section 13 carrier based at a specified
family member.**  This is the member-preserving form of
`S13.exists_hypothesis_of_isTypeIIIorIV`; it uses the same concrete subgroup
and chief-factor data, but retains the supplied `zeta` through the character
parameter field. -/
theorem exists_s13Hypothesis_for_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ∃ s13 : OddOrder.Peterfalvi.S13.Hypothesis M,
      s13.base = hyp ∧ s13.params.zeta = zeta := by
  haveI := hyp.finiteG
  classical
  have hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.typeP :=
    OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨params, hparams, hmu, _, hzmem, hzdeg, _, hdeltaPm, hdeltaSign⟩ :=
    exists_charParameters_full_for_member hG hyp zeta hzetaS hzetairr hzeta1
  refine ⟨{
    base := hyp
    params := params
    params_mu_eq := fun _ _ => hmu
    params_delta_sign := fun _ _ j hj => hdeltaSign j hj
    params_delta_pm := hdeltaPm
    params_zeta_mem := hzmem
    params_zeta_degree := hzdeg
    type_alt := htype
    s11Setup := hyp.toTypesIIIIIIVSetup htype hnt
    chief := (OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.toTypesIIIIIIVSetup htype hnt)).choose
    setup_typeP_eq := rfl
    C := hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)
    C_le_U := inf_le_left
    C_eq_centralizer := rfl
    C_normalized_by_M :=
      OddOrder.Peterfalvi.S12.typePData_C_normalized_by_M hyp.typeP hnt.1
    Hprime := derivedInG hyp.typeP.H
    Hprime_eq := rfl
    Uprime := derivedInG hyp.typeP.U
    Uprime_eq := rfl
    SOf := fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (X.subgroupOf M)
    SOf_eq := fun _ => rfl
    notOrthogonalFormula := fun _ => True
    finalOrthogonalityFormula := fun _ => True
    caseB_of_97 := True }, rfl, hparams⟩

/-- **Peterfalvi (11.8), residual non-orthogonality for a specified family
member.**  This is the arbitrary-member strengthening of
`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`.  Its proof is the
same (11.8.1)--(11.8.6) chain, with the member-preserving parameter and
Section 13 producers above preventing the distinguished character from being
reselected. -/
theorem member_residual_not_orthogonal_H0C_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M =
      hyp.typeP.H ⊔
        (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - zeta)) -
          ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  obtain ⟨s13hyp, hbase, hparams⟩ :=
    exists_s13Hypothesis_for_member hG hyp htype zeta hzetaS hzetairr hzeta1
  rw [← hbase] at hM2 hHcard ⊢
  rw [← hparams]
  intro horth
  let params := s13hyp.params
  have hmu : params.mu = s13hyp.base.muGrid hG hG.odd :=
    s13hyp.params_mu_eq hG hG.odd
  have hzS : params.zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M :=
    s13hyp.params_zeta_mem
  have hz1 : params.zeta 1 = (s13hyp.base.w1 : ℂ) :=
    s13hyp.params_zeta_degree
  have hdeltaPm : params.delta = 1 ∨ params.delta = -1 :=
    s13hyp.params_delta_pm
  have hdeltaSign : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.muColumnSign hG hG.odd j = params.delta :=
    s13hyp.params_delta_sign hG hG.odd
  have hdelta1 : params.delta = 1 :=
    s13hyp.base.charParam_delta_eq_one hG htype params hmu hdeltaPm
  obtain ⟨nu, hnuConj, h114⟩ :=
    s13hyp.base.exists_coherent_extension_h114_of_orthogonal hG hG.odd hzS
      params.zeta_irreducible hz1 horth
  obtain ⟨R, hZ, hRorth, hRmem, hRrev, hRcard⟩ :=
    s13hyp.base.exists_coherentImage_SHC nu
  have hRn : R.card = params.n :=
    hRcard.trans
      (s13hyp.base.card_SHCSet_filter_eq_charParam_n
        hG htype params hmu hdeltaPm hM2 hHcard)
  have hnf : (params.n : ℤ) * (s13hyp.base.w1 : ℤ) =
      (params.d : ℤ) - 1 := by
    rw [← hdelta1]
    exact params.n_formula
  have hd : (params.d : ℂ) =
      (s13hyp.base.w1 : ℂ) * (params.n : ℂ) + 1 := by
    have h : (params.n : ℂ) * (s13hyp.base.w1 : ℂ) =
        (params.d : ℂ) - 1 := by
      exact_mod_cast hnf
    linear_combination -h
  have hmu0 : ∀ i : Fin s13hyp.base.w1,
      s13hyp.base.muGrid hG hG.odd i 0 1 = 1 :=
    fun i => s13hyp.base.muGrid_zero_column_apply_one hG hG.odd i
  have hcol : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.tau
          ((∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) -
            (params.d : ℂ) • params.zeta) =
        (∑ i : Fin s13hyp.base.w1,
            s13hyp.base.alignedOmegaSigmaGrid hG hG.odd i j) -
          (params.d : ℂ) • nu.extension params.zeta := by
    intro j hj
    have hdeg : ∀ i : Fin s13hyp.base.w1,
        s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    have hsign : s13hyp.base.muColumnSign hG hG.odd j = 1 :=
      (hdeltaSign j hj).trans hdelta1
    exact s13hyp.base.tau_muColumnSum_sub_dzeta_eq_of_residualData
      hG nu hnuConj hG.odd hj hzS params.zeta_irreducible hz1 params.w2_prime
      hd hnf hdeg hmu0 hsign params.two_le_n hRn hZ hRorth hRmem hRrev h114
  have hzHC : params.zeta ∈ s13hyp.SOf s13hyp.HC := by
    rw [← OddOrder.Peterfalvi.S13.secondDerived_eq_HC hG s13hyp,
      s13hyp.SOf_secondDerived_eq hG]
    exact ⟨hzS, params.zeta_irreducible, hz1⟩
  have hzdeg : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      (∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) 1 =
        (params.d : ℂ) * params.zeta 1 := by
    intro j hj
    have hall : ∀ i : Fin s13hyp.base.w1,
        s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    rw [ClassFunction.finset_sum_apply]
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hz1]
    ring
  haveI : NeZero
      (Nat.card ↥(s13hyp.base.toHypothesis46 hG hG.odd).W1) :=
    ⟨by
      have hw := (s13hyp.base.toHypothesis46 hG hG.odd).one_lt_card_W1
      omega⟩
  exact hrefute s13hyp
    (OddOrder.Peterfalvi.S13.coherent_SOf_H0C_of_column_identities hG s13hyp
      (OddOrder.Peterfalvi.S13.isCoherent_of_subset nu
        (OddOrder.Peterfalvi.S13.SOf_HC_subset_SHCSet hG s13hyp)
        (OddOrder.Peterfalvi.S13.coherent_SOf_HC hG s13hyp).some.nonzero)
      hzS hzHC hzdeg hcol)

/-- **Peterfalvi (11.8), transport to a transposed T-side grid.**
The Section 12 calculation is indexed by `W₁ × W₂`, whereas the shared
Section 16 grid writes the T-side factors in the transposed order `q × p`.
Once the two cardinal identifications, the Dade image, and each grid entry
are identified, non-orthogonality transports without any further character
theory.  The hypotheses below are equalities of the concrete producers, not
new mathematical assumptions hidden in a carrier. -/
theorem member_residual_not_orthogonal_of_transposed_alignment [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M =
      hyp.typeP.H ⊔
        (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ))
    {p q : ℕ} [NeZero p] [NeZero q]
    (hp : hyp.w1 = p) (hq : hyp.w2 = q)
    (tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (nu0 : ClassFunction ↥M ℂ)
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (himage : hyp.tau
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - zeta) =
      tauT (nu0 - zeta))
    (hgrid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      hyp.alignedOmegaSigmaGrid hG hG.odd i j =
        eta (finCongr hq j) (finCongr hp i)) :
    ¬ ∀ (i : Fin q) (j : Fin p),
      ClassFunction.inner
        (tauT (nu0 - zeta) - ∑ j' : Fin p, eta 0 j')
        (eta i j) = 0 := by
  have hnot := member_residual_not_orthogonal_H0C_of_refuter
    hG hyp htype hM2 hHcard hrefute zeta hzetaS hzetairr hzeta1
  intro horth
  apply hnot
  intro i j
  have hsum :
      (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0) =
        ∑ j' : Fin p, eta 0 j' := by
    calc
      (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0) =
          ∑ i' : Fin hyp.w1, eta 0 (finCongr hp i') := by
        apply Finset.sum_congr rfl
        intro i' _
        simpa using hgrid i' 0
      _ = ∑ j' : Fin p, eta 0 j' := by
        simpa using Equiv.sum_comp (finCongr hp) (fun j' : Fin p => eta 0 j')
  rw [himage, hsum, hgrid]
  exact horth (finCongr hq j) (finCongr hp i)

/-- Reindex a non-orthogonal rectangular residual after transposing its two
axes.  Unlike `finCongr`, the equivalences may encode the independent
enumeration choices made by two concrete character-grid producers; preserving
the distinguished column-zero index is exactly what identifies the subtracted
base row. -/
theorem residual_not_orthogonal_of_transposed_reindexing
    [Fintype G] {w1 w2 p q : ℕ}
    [NeZero w1] [NeZero w2] [NeZero p] [NeZero q]
    (source : ClassFunction G ℂ)
    (grid : Fin w1 → Fin w2 → ClassFunction G ℂ)
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (rowEquiv : Fin w1 ≃ Fin p) (colEquiv : Fin w2 ≃ Fin q)
    (hcol0 : colEquiv 0 = 0)
    (hgrid : ∀ i j, grid i j = eta (colEquiv j) (rowEquiv i))
    (hnot : ¬ ∀ (i : Fin w1) (j : Fin w2),
      ClassFunction.inner
        (source - ∑ i' : Fin w1, grid i' 0) (grid i j) = 0) :
    ¬ ∀ (i : Fin q) (j : Fin p),
      ClassFunction.inner
        (source - ∑ j' : Fin p, eta 0 j') (eta i j) = 0 := by
  intro horth
  apply hnot
  intro i j
  have hsum : (∑ i' : Fin w1, grid i' 0) = ∑ j' : Fin p, eta 0 j' := by
    calc
      (∑ i' : Fin w1, grid i' 0) =
          ∑ i' : Fin w1, eta 0 (rowEquiv i') := by
        apply Finset.sum_congr rfl
        intro i' _
        rw [hgrid, hcol0]
      _ = ∑ j' : Fin p, eta 0 j' := by
        simpa using Equiv.sum_comp rowEquiv (fun j' : Fin p => eta 0 j')
  rw [hsum, hgrid]
  exact horth (colEquiv j) (rowEquiv i)

end OddOrder.Peterfalvi.S16

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), arbitrary-grid dichotomy.**  The norm and integral-lattice
argument producing the normalized coherent extension uses only two properties of the chosen
`sigma`-grid: orthonormality and orthogonality of every degree-`w1` coherent image to its
zero-column sum.  Thus the canonical `alignedOmegaSigmaGrid` can be replaced by any grid with
those properties, in particular the independently constructed T-side grid.
This is the grid-parametric form of `tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`. -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_grid_orthogonal [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {lam : ClassFunction ↥M ℂ},
      lam ∈ inducedFamily M → IsIrreducibleCharacter lam → lam 1 = (hyp.w1 : ℂ) →
      lam.conj ≠ lam →
      ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, grid r 0) = 0)
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) -
          ∑ i' : Fin hyp.w1, grid i' 0)
        (grid i j) = 0) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) - (hyp.SHC_isCoherent hG).extension ζ ∨
      ((∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
          lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) ∧
        hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
          (∑ r : Fin hyp.w1, grid r 0) +
            (hyp.SHC_isCoherent hG).extension ζ.conj) := by
  haveI := hyp.finiteG
  classical
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  -- generic unit-norm integral-lattice toolkit: the Cauchy–Schwarz bound `m² ≤ 1` and the
  -- positive-definiteness equalities `⟨A, θ⟩ = ±1 → A = ±θ` for unit-norm `A`, `θ`.
  have hbound : ∀ (A θ : ClassFunction G ℂ) (m : ℤ),
      ClassFunction.inner A A = 1 → ClassFunction.inner A θ = (m : ℂ) →
      ClassFunction.inner θ θ = 1 → m * m ≤ 1 := by
    intro A θ m hA hm hθ
    have hθA : ClassFunction.inner θ A = (m : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hm, star_intCast]
    have hval : ClassFunction.inner (A - (m : ℂ) • θ) (A - (m : ℂ) • θ)
        = ((1 - m * m : ℤ) : ℂ) := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hA, hm, hθA, hθ,
        star_intCast]
      push_cast
      ring
    have hre := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - (m : ℂ) • θ)
    rw [hval] at hre
    have h1 : (0 : ℝ) ≤ ((1 - m * m : ℤ) : ℝ) := by simpa using hre
    have h2 : (0 : ℤ) ≤ 1 - m * m := by exact_mod_cast h1
    linarith
  have heq : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = 1 → ClassFunction.inner θ θ = 1 → A = θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ, star_one]
    have hz : ClassFunction.inner (A - θ) (A - θ) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A - θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact sub_eq_zero.mp h0
  have heqneg : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = -1 → ClassFunction.inner θ θ = 1 → A = -θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = -1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ]
      simp
    have hz : ClassFunction.inner (A + θ) (A + θ) = 0 := by
      rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_add_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A + θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact add_eq_zero_iff_eq_neg.mp h0
  -- conjugate-family facts for `ζ`
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
  have hζcmem : ζ.conj ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζcirr
  -- supports
  have hsupp : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hsuppd : (ζ - ζ.conj).support ⊆ hyp.A0 := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  -- `ψ = (μ₀ − ζ)^τ ∈ ZIrr G`
  have hμ0Z : (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr
  have hψZ : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp hdiffZ
  have heζZ : (hyp.SHC_isCoherent hG).extension ζ ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have heζcZ : (hyp.SHC_isCoherent hG).extension ζ.conj ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ.conj
      (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  -- `M`-side orthogonality facts
  have hμζ : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζ1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hμζc : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ.conj = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζcirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζc1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [irr_cf_inner hζmem hζmem, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [irr_cf_inner hζmem hζcmem, if_neg hζne.symm]
  -- `G`-side norm bookkeeping under the orthogonality hypothesis
  have hΩr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (∑ r' : Fin hyp.w1, grid r' 0)
        (grid r 0) = 1 := by
    intro r
    rw [inner_sum_left, Finset.sum_eq_single r]
    · rw [hgridInner r 0 r 0, if_pos ⟨rfl, rfl⟩]
    · intro r' _ hne
      rw [hgridInner r' 0 r 0, if_neg fun h => hne h.1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hψr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (grid r 0) = 1 := by
    intro r
    have h := horth r 0
    rw [ClassFunction.inner_sub_left, sub_eq_zero] at h
    exact h.trans (hΩr r)
  have hψΩ : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ r : Fin hyp.w1, grid r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hψr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hΩψ : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩnorm : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      (∑ r : Fin hyp.w1, grid r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hΩr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψnorm : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- `χ = ∑_r ω_{r0}^σ − (μ₀ − ζ)^τ` has norm `1`
  have hχnorm : ClassFunction.inner
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hΩnorm, hΩψ, hψΩ, hψnorm]
    push_cast
    ring
  -- the (5.3.b) orthogonalities `⟨∑_r ω_{r0}^σ, λ^{τ₁}⟩ = 0`
  have heΩ : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      (∑ r : Fin hyp.w1, grid r 0) = 0 :=
    hgridExtensionOrth hζS hζirr hζ1 hζne
  have hΩe : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      ((hyp.SHC_isCoherent hG).extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩ, star_zero]
  have hζcne : (ζ.conj).conj ≠ ζ.conj := by
    rw [ClassFunction.conj_conj]
    exact hζne.symm
  have heΩc : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      (∑ r : Fin hyp.w1, grid r 0) = 0 :=
    hgridExtensionOrth hζcS hζcirr hζc1 hζcne
  have hΩec : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩc, star_zero]
  -- the integer coefficients `s = ⟨ψ, ζ^{τ₁}⟩`, `t = ⟨ψ, ζ̄^{τ₁}⟩` with `s − t = −1`
  obtain ⟨s, hs⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζZ
  obtain ⟨t, ht⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζcZ
  have hGside : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau (ζ - ζ.conj)) = -1 := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsuppd, ClassFunction.inner_sub_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hμζ, hμζc, hζζ, hζζc]
    ring
  rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1,
    ClassFunction.inner_sub_right, hs, ht] at hGside
  have hstz : s - t = -1 := by exact_mod_cast hGside
  -- Cauchy–Schwarz bounds and the integer dichotomy `s = −1 ∨ t = 1`
  have hee : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      ((hyp.SHC_isCoherent hG).extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζS hζirr hζ1
  have heec : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1
  have hmA : ClassFunction.inner
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ) = ((-s : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩe, hs]
    push_cast
    ring
  have hmAc : ClassFunction.inner
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = ((-t : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩec, ht]
    push_cast
    ring
  have hs2 : s * s ≤ 1 := by
    have h := hbound _ _ (-s) hχnorm hmA hee
    have h' : s * s = -s * -s := by ring
    rw [h']
    exact h
  have ht2 : t * t ≤ 1 := by
    have h := hbound _ _ (-t) hχnorm hmAc heec
    have h' : t * t = -t * -t := by ring
    rw [h']
    exact h
  have hsle : s ≤ 1 := by nlinarith [mul_self_nonneg (s - 1)]
  have hsge : -1 ≤ s := by nlinarith [mul_self_nonneg (s + 1)]
  have htle : t ≤ 1 := by nlinarith [mul_self_nonneg (t - 1)]
  have htge : -1 ≤ t := by nlinarith [mul_self_nonneg (t + 1)]
  have hcase : s = -1 ∨ t = 1 := by omega
  rcases hcase with hsval | htval
  · -- `⟨χ, ζ^{τ₁}⟩ = 1`: `χ = ζ^{τ₁}`, the normalized (11.8.4) form
    left
    have hAe : ClassFunction.inner
        ((∑ r : Fin hyp.w1, grid r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ) = 1 := by
      rw [ClassFunction.inner_sub_left, hΩe, hs, hsval]
      push_cast
      ring
    have hχe := heq _ _ hχnorm hAe hee
    rw [← hχe]
    abel
  · -- `⟨χ, ζ̄^{τ₁}⟩ = −1`: `χ = −ζ̄^{τ₁}` and `S₁ = {ζ, ζ̄}`
    right
    have hAec : ClassFunction.inner
        ((∑ r : Fin hyp.w1, grid r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ.conj) = -1 := by
      rw [ClassFunction.inner_sub_left, hΩec, ht, htval]
      push_cast
      ring
    have hχec := heqneg _ _ hχnorm hAec heec
    have hψeq : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, grid r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [sub_eq_iff_eq_add] at hχec
      rw [hχec]
      abel
    refine ⟨fun lam hlamS hlamirr hlam1 => ?_, hψeq⟩
    by_contra hboth
    rw [not_or] at hboth
    obtain ⟨hlamzeta, hlamzetac⟩ := hboth
    have hlamne : lam.conj ≠ lam := hyp.inducedFamily_degree_w1_conj_ne hG hlamirr hlam1
    have hmulam : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) lam = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hlamirr ?_
      rw [hyp.muGrid_zero_column_apply_one hG hodd i, hlam1]
      intro he
      have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
      omega
    have hlammem : lam ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hlamirr
    have hzetalam : ClassFunction.inner ζ lam = 0 := by
      rw [irr_cf_inner hζmem hlammem, if_neg (Ne.symm hlamzeta)]
    have hsupplam : (lam - ζ).support ⊆ hyp.A0 :=
      hyp.inducedFamily_sub_support hlamS hζS (by rw [hlam1, hζ1])
    have hGlam : ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.tau (lam - ζ)) = 1 := by
      rw [hyp.tau_inner_eq_of_supported hsupp hsupplam, ClassFunction.inner_sub_left,
        ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hmulam, hμζ, hzetalam, hζζ]
      ring
    have hspanlam : lam ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hlamS, hlamirr, hlam1⟩
    have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
    have hmemsupp : (lam - ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
      ⟨Submodule.sub_mem _ hspanlam hspanζ, hsupplam⟩
    have htaulam : hyp.tau (lam - ζ) = (hyp.SHC_isCoherent hG).extension lam
        - (hyp.SHC_isCoherent hG).extension ζ := by
      rw [← (hyp.SHC_isCoherent hG).extends_on_supported _ hmemsupp, map_sub]
    have heOmegalam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, grid r 0) = 0 :=
      hgridExtensionOrth hlamS hlamirr hlam1 hlamne
    have hOmegalam : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, heOmegalam, star_zero]
    have heclam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hlamS hlamirr hlam1 (Ne.symm hlamzetac)
    have hece : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension ζ) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hζS hζirr hζ1 hζne
    rw [htaulam, ClassFunction.inner_sub_right, hψeq, ClassFunction.inner_add_left,
      ClassFunction.inner_add_left, hOmegalam, heclam, hΩe, hece] at hGlam
    norm_num at hGlam

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), arbitrary-grid branch-2 normalization.**
The conjugate-swap changes only the coherent extension, so the textbook's
`sum grid + extension zeta.conj` branch normalizes for every chosen grid. -/
theorem Hypothesis.SHC_swap_grid_h114 [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M →
      IsIrreducibleCharacter lam → lam 1 = (hyp.w1 : ℂ) →
      lam = ζ ∨ lam = ζ.conj)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hbranch2 :
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) +
          (hyp.SHC_isCoherent hG).extension ζ.conj) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
      (∑ r : Fin hyp.w1, grid r 0) -
        (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ := by
  haveI := hyp.finiteG
  classical
  have hswapζ :
      (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ =
        -((hyp.SHC_isCoherent hG).extension ζ.conj) := by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M)
        Complex.conjAe.toRingEquiv))) ζ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply,
      ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ = ζ.conj from by
        ext g
        rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
        rfl]
  rw [hswapζ, sub_neg_eq_add, hbranch2]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), arbitrary-grid h114 producer.**
Under the contradiction orthogonality for any orthonormal sigma-grid whose
zero column is orthogonal to the coherent family, one may choose a coherent
extension satisfying the normalized h114 identity for that same grid. -/
theorem Hypothesis.exists_coherent_extension_h114_of_grid_orthogonal [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {lam : ClassFunction ↥M ℂ},
      lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam.conj ≠ lam →
      ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, grid r 0) = 0)
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) -
          ∑ i' : Fin hyp.w1, grid i' 0)
        (grid i j) = 0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0,
      (∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M →
        IsIrreducibleCharacter χ → χ 1 = (hyp.w1 : ℂ) →
        (ν.extension χ).conj = ν.extension χ.conj) ∧
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) - ν.extension ζ := by
  rcases hyp.tau_muColumnZero_sub_zeta_dichotomy_of_grid_orthogonal
      hG hodd hζS hζirr hζ1 grid hgridInner hgridExtensionOrth horth with
    h1 | ⟨htwo, h2⟩
  · exact ⟨hyp.SHC_isCoherent hG,
      (fun hχS hχirr hχ1 => hyp.SHC_extension_conj hG hχS hχirr hχ1), h1⟩
  · exact ⟨hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo,
      (fun hχS hχirr hχ1 =>
        hyp.SHC_swap_conj hG hodd hζS hζirr hζ1 htwo hχS hχirr hχ1),
      hyp.SHC_swap_grid_h114 hG hodd hζS hζirr hζ1 htwo grid h2⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), arbitrary-grid residual identification.**
The Parseval decomposition and coefficient bound are independent of sigma.
Only the norm-two residual classifier is grid-specific, so it is exposed as
`hclassify`; this is the exact input supplied by a concrete sigma-isometry. -/
theorem Hypothesis.SHC_residual_eq_grid_diff [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hclassify : ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 -
            (n : ℂ) • ζ) v) →
      Y = (δ : ℂ) • (grid i j - grid i 0)) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ((a = 0 ∨ a = 2) → Y = (δ : ℂ) • (grid i j - grid i 0)) ∧
      hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) =
        Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  obtain ⟨a, Y, hbound, _, hinner, _, hnorm2case, hYZ, hYV, hdecomp⟩ :=
    hyp.muGridAlpha_tau_residual_norm hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev
  exact ⟨a, Y, hbound, hinner,
    fun ha02 => hclassify hYZ (hnorm2case ha02) hYV, hdecomp⟩

open scoped FiniteInduce in
/-- A row difference in an orthonormal grid pairs to `-1` with the zero-column sum. -/
theorem grid_diff_inner_zeroColumnSum [Finite G] {w1 w2 : ℕ} [NeZero w2]
    (grid : Fin w1 → Fin w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (i : Fin w1) {j : Fin w2} (hj0 : j ≠ 0) :
    ClassFunction.inner (grid i j - grid i 0)
      (∑ r : Fin w1, grid r 0) = -1 := by
  classical
  rw [ClassFunction.inner_sub_left,
    OddOrder.RepresentationTheory.inner_sum_right,
    OddOrder.RepresentationTheory.inner_sum_right]
  have h1 : ∀ r : Fin w1, ClassFunction.inner (grid i j) (grid r 0) = 0 :=
    fun r => by
      rw [hgridInner i j r 0, if_neg]
      rintro ⟨_, h⟩
      exact hj0 h
  have h2 : ∀ r : Fin w1,
      ClassFunction.inner (grid i 0) (grid r 0) =
        if i = r then (1 : ℂ) else 0 := fun r => by
    rw [hgridInner i 0 r 0]
    simp
  rw [Finset.sum_congr rfl (fun r _ => h1 r),
    Finset.sum_congr rfl (fun r _ => h2 r), Finset.sum_const_zero,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- The sum of a coherent image family is orthogonal to an arbitrary grid's zero column
whenever each family member is. -/
theorem Hypothesis.R_sum_inner_grid_zeroColumnSum [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {R : Finset (ClassFunction G ℂ)}
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hext : ∀ {φ : ClassFunction ↥M ℂ}, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) →
      ClassFunction.inner (coh.extension φ) (∑ r : Fin hyp.w1, grid r 0) = 0) :
    ClassFunction.inner (∑ β ∈ R, β) (∑ r : Fin hyp.w1, grid r 0) = 0 := by
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβR => ?_
  obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
  exact hext hφS hφirr hφ1

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), arbitrary-grid conditional coefficient vanishing.**
Given the grid-parametric (11.8.2) residual classifier and h114 identity,
the two-way inner-product computation forces every even coefficient `a` to vanish. -/
theorem Hypothesis.charParam_a_eq_zero_of_grid_residualEq [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {φ : ClassFunction ↥M ℂ},
      φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) →
      ClassFunction.inner (coh.extension φ) (∑ r : Fin hyp.w1, grid r 0) = 0)
    (hclassify : ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 -
            (n : ℂ) • ζ) v) →
      Y = (δ : ℂ) • (grid i j - grid i 0))
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
      (∑ r : Fin hyp.w1, grid r 0) - coh.extension ζ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      (Even a → a = 0) := by
  obtain ⟨a, Y, hbound, hinner, hYeq, hdecomp⟩ :=
    hyp.SHC_residual_eq_grid_diff hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev grid hclassify
  refine ⟨a, hbound, hinner, ?_⟩
  intro heven
  have ha02 : a = 0 ∨ a = 2 := by
    rcases hbound with h | h | h
    · exact Or.inl h
    · obtain ⟨k, hk⟩ := heven
      omega
    · exact Or.inr h
  have hYd := hYeq ha02
  have htrans := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta
    hG hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ
  rw [h114] at htrans
  have hαgrid : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j -
        (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, grid r 0) = -(δ : ℂ) := by
    rw [hdecomp, hYd]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      grid_diff_inner_zeroColumnSum grid hgridInner i hj0,
      hgridExtensionOrth hζS hζirr hζ1,
      hyp.R_sum_inner_grid_zeroColumnSum coh hRrev grid hgridExtensionOrth]
    ring
  rw [ClassFunction.inner_sub_right, hαgrid, hinner] at htrans
  have ha0 : (a : ℂ) = 0 := by
    linear_combination -htrans
  exact_mod_cast ha0

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), arbitrary-grid regular-value pin.**
The S12 Dade image already equals the canonical aligned sigma-grid difference
on `typePV`.  Consequently it equals any other grid difference whose two
entries have the same values there.  This deliberately asks only for
regular-set value alignment, not a false global uniqueness/equality of sigma
isometries. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_of_grid_value_alignment [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2}
    (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (halign : ∀ k : Fin hyp.w2, ∀ {v : G}, v ∈ typePV M hyp.typeP →
      hyp.alignedOmegaSigmaGrid hG hodd i k v = grid i k v) :
    ∀ v ∈ typePV M hyp.typeP,
      hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v =
        ((δ : ℂ) • (grid i j - grid i 0)) v := by
  intro v hv
  rw [hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS
    hdeg hμ0 hζ1 hnf hδj hv, ClassFunction.smul_apply,
    ClassFunction.sub_apply, halign j hv, halign 0 hv,
    ← ClassFunction.sub_apply, ← ClassFunction.smul_apply]

end OddOrder.Peterfalvi.S12

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8)/(11.8.2), eta residual classifier from regular values.**
Suppose the regular set of a type-P datum is the shared S15 regular set.  If a
norm-two virtual character agrees there with a signed eta row difference, then
it equals that difference globally.  Class-function invariance upgrades the
pointwise type-P equality to the conjugacy saturation consumed by
`eta_diff_rigidity`.

This is the concrete eta implementation of the `hclassify` input in
`S12.Hypothesis.SHC_residual_eq_grid_diff`; only the source's regular-value pin
remains for a particular T-side alpha. -/
theorem eta_diff_classifier_of_typePV_value [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (data : TypePData M)
    (hV : typePV M data =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i0 : Fin base.q) {j1 j2 : Fin base.p} (hj : j1 ≠ j2)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    {source : ClassFunction G ℂ}
    (hsource : ∀ v ∈ typePV M data,
      source v = ((s : ℂ) • (base.eta i0 j1 - base.eta i0 j2)) v) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M data, Y v = source v) →
      Y = (s : ℂ) • (base.eta i0 j1 - base.eta i0 j2) := by
  intro Y hYZ hY2 hYsource
  apply eta_diff_rigidity base hYZ hY2 i0 hj hs
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ typePV M data := hV.symm ▸ hw
  rw [ClassFunction.sub_apply,
    ← Y.of_isConj hconj,
    ← (((s : ℂ) • (base.eta i0 j1 - base.eta i0 j2)).of_isConj hconj),
    hYsource w hwV, hsource w hwV, sub_self]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8), eta column-difference rigidity.**
This is the transposed dual of `eta_diff_rigidity`: a norm-two virtual
character agreeing with `s * (eta i1 j0 - eta i2 j0)` on the shared regular
set equals that column difference globally.  The abstract grid-rigidity engine
already permits arbitrary distinct grid points; only the (3.7) separability
assembly is repeated here. -/
theorem eta_column_diff_rigidity [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G)
    (hX2 : ClassFunction.inner X X = 2)
    {i1 i2 : Fin base.q} (hi : i1 ≠ i2) (j0 : Fin base.p)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hvanish : ∀ x ∈ conjClassSet
      ((base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G))),
      (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)) x = 0) :
    X = (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0) := by
  classical
  have hcardq : Nat.card (Fin base.q) = base.q :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hcardp : Nat.card (Fin base.p) = base.p :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hsep : ∀ (i i' : Fin base.q) (j j' : Fin base.p),
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i j) +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i' j') =
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i j') +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i' j) := by
    intro i i' j j'
    have h1 := inner_eta_grid_relation base hvanish i j
    have h2 := inner_eta_grid_relation base hvanish i' j'
    have h3 := inner_eta_grid_relation base hvanish i j'
    have h4 := inner_eta_grid_relation base hvanish i' j
    linear_combination h1 + h2 - h3 - h4
  have hmain := OddOrder.Peterfalvi.S05.orthonormalGrid_diff_rigidity
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    (fun pq => eta_mem_ZIrr base pq.1 pq.2)
    (fun a => by simpa using eta_orthonormal base a.1 a.1 a.2 a.2)
    (fun a b hab => by
      rw [eta_orthonormal base a.1 b.1 a.2 b.2, if_neg]
      rintro ⟨h1, h2⟩
      exact hab (Prod.ext h1 h2))
    (by rw [hcardq]; exact base.three_le_q)
    (by rw [hcardp]; exact base.three_le_p)
    (by rw [hcardq]; exact base.q_odd)
    (by rw [hcardp]; exact base.p_odd)
    (by
      rw [hcardq, hcardp]
      exact (Nat.coprime_primes base.q_prime base.p_prime).mpr
        (Ne.symm base.p_ne_q))
    hXZ hX2 (P1 := (i1, j0)) (P2 := (i2, j0))
    (by intro h; exact hi (Prod.ext_iff.mp h).1) hs hsep
  simpa using hmain

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8)/(11.8.2), transposed eta classifier from regular values.**
The type-P regular-value bridge specialized to an eta column difference, the
orientation required by the T-side transposition in (11.8). -/
theorem eta_column_diff_classifier_of_typePV_value [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (data : TypePData M)
    (hV : typePV M data =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    {i1 i2 : Fin base.q} (hi : i1 ≠ i2) (j0 : Fin base.p)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    {source : ClassFunction G ℂ}
    (hsource : ∀ v ∈ typePV M data,
      source v = ((s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)) v) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M data, Y v = source v) →
      Y = (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0) := by
  intro Y hYZ hY2 hYsource
  apply eta_column_diff_rigidity base hYZ hY2 hi j0 hs
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ typePV M data := hV.symm ▸ hw
  rw [ClassFunction.sub_apply, ← Y.of_isConj hconj,
    ← (((s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)).of_isConj hconj),
    hYsource w hwV, hsource w hwV, sub_self]

/-- The multiplicative character underlying an abstract S15 omega-grid entry.
Nonvanishing follows from multiplicativity and `omega i j 1 = 1`. -/
noncomputable def omegaMonoidHom
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) : ↥base.W →* ℂˣ where
  toFun w := Units.mk0 (base.omega i j w) (by
    intro hz
    have hmul := base.omega_mul i j w w⁻¹
    rw [mul_inv_cancel, base.omega_apply_one, hz, zero_mul] at hmul
    exact zero_ne_one hmul.symm)
  map_one' := Units.ext (base.omega_apply_one i j)
  map_mul' x y := Units.ext (base.omega_mul i j x y)

/-- The underlying omega-grid character has the original class-function value. -/
theorem omegaMonoidHom_coe
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) (w : ↥base.W) :
    ((omegaMonoidHom base i j w : ℂˣ) : ℂ) = base.omega i j w := rfl

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.3), abstract omega-grid exhaustion.**
The `q*p` multiplicative characters underlying the S15 omega-grid are
pairwise distinct by orthonormality.  Since the cyclic group `W` has order
`p*q`, its complex linear-character group has the same cardinality; hence the
grid enumerates every `W →* ℂˣ` character. -/
theorem omegaMonoidHom_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
  classical
  have hinj : Function.Injective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
    intro ⟨i, j⟩ ⟨k, l⟩ hhom
    have hcf : base.omega i j = base.omega k l := by
      ext w
      have hw := DFunLike.congr_fun hhom w
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hw
    by_contra hne
    have h1 := eta_orthonormal base i k j l
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega,
      base.tau3_isometry.inner_eq, hcf] at h1
    have h2 := base.omega_orthonormal k k l l
    have hcond : ¬ (i = k ∧ j = l) := fun ⟨hi, hj⟩ => hne (by rw [hi, hj])
    rw [if_neg hcond] at h1
    rw [if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
    exact zero_ne_one (h1.symm.trans h2)
  haveI : Fintype (↥base.W →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ↥base.W := base.W_cyclic
  letI : CommGroup ↥base.W := IsCyclic.commGroup
  haveI : NeZero (Monoid.exponent ↥base.W) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero ((Monoid.exponent ↥base.W : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat : Nat.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥base.W ℂ,
      OddOrder.Peterfalvi.S15.card_W_eq_pq base, Nat.mul_comm]
  have hcardHom : Fintype.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

open scoped Classical in
/-- Every complex linear character of the shared cyclic `W` is one omega-grid entry. -/
theorem exists_omegaMonoidHom_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (ξ : ↥base.W →* ℂˣ) :
    ∃ (i : Fin base.q) (j : Fin base.p), omegaMonoidHom base i j = ξ := by
  obtain ⟨ij, hij⟩ := (omegaMonoidHom_bijective base).surjective ξ
  exact ⟨ij.1, ij.2, hij⟩

end OddOrder.Peterfalvi.S16
