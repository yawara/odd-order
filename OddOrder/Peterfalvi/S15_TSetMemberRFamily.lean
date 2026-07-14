/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_BridgeCharacter

/-!
# Peterfalvi §9/§13 — the (5.2.d) member `R`-families for the `T`-instance §9 family

The `T`-side mirror of `S15_SSetMemberRFamily`: per-member orthonormal Dade `R`-families over
`𝒯 = sSet(setupT)`, feeding the caseB-`T` (5.7) uniform-degree coherence engine (issue 2035,
the (13.4) T-side coherence).  For an **irreducible** member the (5.2.d) datum is the
2-element signed Dade family (`dadeOrthonormalCharacterImageFamilyOfDiff` over `dadeHypT`,
inputs landed on `TSideDegrees`); for a **reducible** member `η = ν_r = ∑_j ν_{rj}` (a nonzero
ν-row sum) it is the `2p`-element signed-`η` family `R(η) = {η_{rj}} ∪ {−η_{sj}}`, built by
route B from the row-sum cross-relation `tauT_nuRow_diff_eq` (`S15_BridgeCharacter`).

Everything is parametric in the ν-grid supply `pins : NuGridSupplyData` and the
(14.9)-conclusional `hT2`/`Tdata` (the established `T`-side parameter layer, cf.
`dadeHypT0`/`tauTbetaGrid`).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The reducible `𝒯`-member `R`-family at EXPLICIT rows `r, s`** (route B core; mirror of
`sSet_reducible_memberRFamily_ofColumns`).  For a reducible member `η = ∑_j ν_{rj} ∈ 𝒯` with
conjugate `η̄ = ∑_j ν_{sj}` (`r ≠ s`, both `≠ 0`), the (5.2.d) orthonormal Dade image family
is the `2p`-element signed `η`-grid family `R(η) = {η_{rj} : j} ∪ {−η_{sj} : j}`, with
`τ_T(η − η̄) = ∑_j(η_{rj} − η_{sj})` (`tauT_nuRow_diff_eq`), orthonormal by
`eta_orthonormal` (distinct rows `r ≠ s`), and in `ℤ[Irr G]` by `eta_mem_ZIrr`. -/
noncomputable def Hypothesis.sSet_reducible_memberRFamily_ofRows [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r s : Fin hyp.q}
    (hr0 : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs0 : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s)
    (hreq : η = ∑ j : Fin hyp.p, hyp.nu r j)
    (hseq : (η : ClassFunction ↥hyp.T ℂ).conj = ∑ j : Fin hyp.p, hyp.nu s j) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2))) η := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  have hcross := tauT_nuRow_diff_eq hG hnoV hyp pins hvd hT2 Tdata hU hW1 hW2
    hr0 hs0 hrs hη hreq hseq
  set g : Fin hyp.p ⊕ Fin hyp.p → ClassFunction G ℂ :=
    Sum.elim (fun j => hyp.eta r j) (fun j => -hyp.eta s j) with hg
  have hg_inner : ∀ x y : Fin hyp.p ⊕ Fin hyp.p,
      ClassFunction.inner (g x) (g y) = if x = y then (1 : ℂ) else 0 := by
    intro x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [hg, Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp r r a b]
      by_cases hab : a = b <;> simp [hab, Sum.inl.injEq]
    · rw [ClassFunction.inner_neg_right, OddOrder.Peterfalvi.S16.eta_orthonormal hyp r s a b,
        if_neg (fun h => hrs h.1)]
      simp
    · rw [ClassFunction.inner_neg_left, OddOrder.Peterfalvi.S16.eta_orthonormal hyp s r a b,
        if_neg (fun h => hrs h.1.symm)]
      simp
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp s s a b]
      by_cases hab : a = b <;> simp [hab, Sum.inr.injEq]
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 := hg_inner x y
    rw [hxy, hg_inner y y, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  exact
    { imageSet := Finset.image g Finset.univ
      mem_ZIrr := by
        intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨x, -, rfl⟩ := hα
        rcases x with a | a <;> simp only [hg, Sum.elim_inl, Sum.elim_inr]
        · exact OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp r a
        · exact Submodule.neg_mem _ (OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp s a)
      orthonormal := by
        intro α hα β hβ
        rw [Finset.mem_image] at hα hβ
        obtain ⟨x, -, rfl⟩ := hα
        obtain ⟨y, -, rfl⟩ := hβ
        rw [hg_inner x y]
        by_cases hxy : x = y
        · rw [if_pos hxy, if_pos (by rw [hxy])]
        · rw [if_neg hxy, if_neg (fun h => hxy (hg_inj h))]
      image_eq := by
        rw [hcross, Finset.sum_image (fun x _ y _ h => hg_inj h), Fintype.sum_sum_type]
        simp only [hg, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib]
        abel }

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family for a REDUCIBLE `𝒯`-member** (mirror of
`sSet_reducible_memberRFamily`): the thin wrapper over `…_ofRows` dispatching `η, η̄` to
their ν-rows via the reverse dichotomy `sSet_reducible_eq_nuRowSum` (`.choose`), with
`r ≠ s` from non-realness (`sSet_reducible_rows_ne`). -/
noncomputable def Hypothesis.sSet_reducible_memberRFamily_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2))) η :=
  hyp.sSet_reducible_memberRFamily_ofRows hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.1
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.1
    (hyp.sSet_reducible_rows_ne hG pins hvd hη hirr)
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.2
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family over `𝒯 = sSet(setupT)`** (mirror of
`sSet_memberRFamily`; the `R` input of the caseB-`T` (5.7) coherence engine).
Clifford-case-agnostic dispatch: an irreducible member gets the 2-element signed Dade image
family (`dadeOrthonormalCharacterImageFamilyOfDiff`, inputs `oddCardT` non-realness and
`sSet_member_conjDiff_supported_T`); a reducible member gets the `2p`-element route-B family
(`sSet_reducible_memberRFamily_T`). -/
noncomputable def Hypothesis.sSet_memberRFamily_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2))) η := by
  classical
  by_cases hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η
  · refine OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) ⟨η, hirr⟩ ?_ ?_
    · exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hη
    · exact hyp.sSet_member_conjDiff_supported_T hG hvd hη
  · exact hyp.sSet_reducible_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη hirr


open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `'A0(T)`-Dade image of an `A(T)`-supported class function vanishes on the regular
set** (mirror of `dadeS0_apply_eq_zero_of_regular`): for `f.support ⊆ A(T)` and a regular
`W`-point `x`, the Dade map reads the source at the representative `w ∈ typePV(Tdata)`, which
is `0` because `A(T) ⊆ T'` while regular `W`-elements lie outside `T'`. -/
theorem Hypothesis.dadeT0_apply_eq_zero_of_regular [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {f : ClassFunction ↥hyp.T ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
        ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData
          (hyp.dadeHypT0_hconj hG hT2 Tdata)) f x = 0 := by
  classical
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
    ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hT2 Tdata))
      f).of_isConj (isConj_iff.mpr ⟨g, hg⟩)]
  have hA0supp : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (honestTypeP2ASet_subset_A0Set Tdata))
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.T Tdata := by
    refine ⟨?_, ?_⟩
    · have hWeq : (Tdata.W : Set G) = (hyp.W : Set G) := by
        rw [Tdata.W_eq, hW1, hW2, sup_comm, ← hyp.W_eq_join]
      rw [hWeq]; exact hw.1
    · rw [hW1, hW2, Set.union_comm]; exact hw.2
  have hwA0 : w ∈ honestTypeP2A0Set hyp.T Tdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    (hyp.dadeHypT0 hG hT2 Tdata)
    ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hT2 Tdata))
    hA0supp]
  let a : {a : G // a ∈ honestTypeP2A0Set hyp.T Tdata} := ⟨w, hwA0⟩
  have hwh : w ∈ (hyp.dadeHypT0 hG hT2 Tdata).hCoset a :=
    ⟨1, (hyp.dadeHypT0 hG hT2 Tdata).H a |>.one_mem, by simp [a]⟩
  rw [(hyp.dadeHypT0 hG hT2 Tdata).isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
  by_contra hne
  have hwSupp : (⟨w, (hyp.dadeHypT0 hG hT2 Tdata).mem_L hwA0⟩ : ↥hyp.T) ∈ f.support :=
    ClassFunction.mem_support.mpr hne
  have hwA : w ∈ honestTypeP2ASet hyp.T := hf hwSupp
  have hwDeriv : w ∈ derivedInG hyp.T := honestTypeP2ASet_subset_derived hwA
  exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived Tdata hwV) hwDeriv


open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
open scoped Classical in
/-- **`imageSet` of the row-parametrized reducible `R`-family** (`rfl`; mirror of
`sSet_reducible_memberRFamily_ofColumns_imageSet`). -/
theorem Hypothesis.sSet_reducible_memberRFamily_ofRows_imageSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r s : Fin hyp.q}
    (hr0 : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs0 : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s)
    (hreq : η = ∑ j : Fin hyp.p, hyp.nu r j)
    (hseq : (η : ClassFunction ↥hyp.T ℂ).conj = ∑ j : Fin hyp.p, hyp.nu s j) :
    (hyp.sSet_reducible_memberRFamily_ofRows hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη
        hr0 hs0 hrs hreq hseq).imageSet
      = Finset.image (Sum.elim (fun j : Fin hyp.p => hyp.eta r j)
          (fun j : Fin hyp.p => -hyp.eta s j)) Finset.univ :=
  rfl

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`imageSet`-reduction of the `T`-dispatcher, irreducible branch** (mirror of
`sSet_memberRFamily_imageSet_of_irr`). -/
theorem Hypothesis.sSet_memberRFamily_T_imageSet_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥hyp.T ℂ))
      (hs : ((η : ClassFunction ↥hyp.T ℂ).conj - (η : ClassFunction ↥hyp.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T),
      (hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) ⟨η, hirr⟩ hr hs).imageSet := by
  refine ⟨sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hη,
    hyp.sSet_member_conjDiff_supported_T hG hvd hη, ?_⟩
  unfold Hypothesis.sSet_memberRFamily_T
  rw [dif_pos hirr]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
open scoped Classical in
/-- **`imageSet`-reduction of the `T`-dispatcher, reducible branch** (mirror of
`sSet_memberRFamily_imageSet_of_red`). -/
theorem Hypothesis.sSet_memberRFamily_T_imageSet_of_red [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ (r s : Fin hyp.q), η = ∑ j : Fin hyp.p, hyp.nu r j ∧
      (η : ClassFunction ↥hyp.T ℂ).conj = ∑ j : Fin hyp.p, hyp.nu s j ∧
      (hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη).imageSet =
        Finset.image (Sum.elim (fun j : Fin hyp.p => hyp.eta r j)
          (fun j : Fin hyp.p => -hyp.eta s j)) Finset.univ := by
  refine ⟨(hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose,
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose,
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.2,
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.2, ?_⟩
  rw [show (hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη).imageSet
        = (hyp.sSet_reducible_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2
            hη hirr).imageSet from by
    unfold Hypothesis.sSet_memberRFamily_T; rw [dif_neg hirr]]
  exact hyp.sSet_reducible_memberRFamily_ofRows_imageSet hG hnoV pins hvd hT2 Tdata hU hW1 hW2
    hη
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.1
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.1
    (hyp.sSet_reducible_rows_ne hG pins hvd hη hirr)
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.2
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
      (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Distinct ν-rows from a vanishing cross inner product** (mirror of
`mu_colSum_ne_of_inner_zero`). -/
theorem Hypothesis.nu_rowSum_ne_of_inner_zero [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) {a b : Fin hyp.q}
    (h : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu a j)
      (∑ j : Fin hyp.p, hyp.nu b j) = 0) :
    a ≠ b := by
  classical
  haveI := hyp.finiteG
  rintro rfl
  have hself : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu a j)
      (∑ j : Fin hyp.p, hyp.nu a j) = (hyp.p : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu a j) (∑ j' : Fin hyp.p, hyp.nu a j')
        = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p,
            ClassFunction.inner (hyp.nu a j) (hyp.nu a j') := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, if j = j' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [pins.nu_orthonormal a a j j']; simp
      _ = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_; simp
      _ = (hyp.p : ℂ) := by simp
  rw [hself] at h
  exact absurd h (Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne')

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The irreducible member's Dade `R`-family is orthogonal to the whole `η`-grid**, `T`-side
(mirror of `sSet_irr_memberRFamily_eta_inner`): the two constituents of `τ_T(φ − φ̄)` are
norm-one virtual characters whose signed difference vanishes on the regular set
(`dadeT0_apply_eq_zero_of_regular` after the `A→A₀` bridge), so
`eta_orthogonal_of_norm_one_pair_vanish` (hyp-level, the shared `η`/`W` grid) applies. -/
theorem Hypothesis.sSet_irr_memberRFamily_eta_inner_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ)
    (hr : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.T ℂ))
    (hs : ((φ : ClassFunction ↥hyp.T ℂ).conj - (φ : ClassFunction ↥hyp.T ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    {α : ClassFunction G ℂ}
    (hα : α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) ⟨φ, hφirr⟩ hr hs).imageSet)
    (i : Fin hyp.q) (j : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) α = 0 := by
  classical
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
          ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2)))
        (φ : ClassFunction ↥hyp.T ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypT hG hT2)
            (hyp.dadeHypT_hconj hG hT2) ⟨φ, hφirr⟩ hr hs = cd.toOrthonormalImage := ⟨_, rfl⟩
  rw [hcd] at hα
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hα
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.mu cd.mu
    rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.nu cd.nu
    rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.mu cd.nu
    rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsign : (cd.sign : ℂ) * (cd.sign : ℂ) = 1 := by
    have := cd.sign_mul_self; exact_mod_cast congrArg (Int.cast : ℤ → ℂ) this
  have hdiffsupp' : ((φ : ClassFunction ↥hyp.T ℂ)
      - (φ : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T := by
    rw [show (φ : ClassFunction ↥hyp.T ℂ) - (φ : ClassFunction ↥hyp.T ℂ).conj =
        -((φ : ClassFunction ↥hyp.T ℂ).conj - (φ : ClassFunction ↥hyp.T ℂ)) by abel,
      ClassFunction.support_neg]
    exact hs
  have hA0supp' : ((φ : ClassFunction ↥hyp.T ℂ)
      - (φ : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T :=
    hdiffsupp'.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (honestTypeP2ASet_subset_A0Set Tdata))
  have hcdimg : (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
          ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData
            (hyp.dadeHypT0_hconj hG hT2 Tdata))
          ((φ : ClassFunction ↥hyp.T ℂ) - (φ : ClassFunction ↥hyp.T ℂ).conj) := by
    rw [hyp.tInstance_dade0_eq_induce hG hnoV hT2 Tdata hA0supp',
      ← hyp.tInstance_dade_eq_induce hG hnoV hT2 hdiffsupp',
      cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul ℂ, Int.cast_smul_eq_zsmul ℂ]
  have hvanish : ∀ y ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) y = 0 := by
    intro y hy
    rw [hcdimg]
    exact hyp.dadeT0_apply_eq_zero_of_regular hG hT2 Tdata hW1 hW2 hdiffsupp' hy
  have hvanish' : ∀ y ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((cd.sign : ℂ) • cd.nuClassFunction - (cd.sign : ℂ) • cd.muClassFunction) y = 0 := by
    intro y hy
    rw [show (cd.sign : ℂ) • cd.nuClassFunction - (cd.sign : ℂ) • cd.muClassFunction
        = -((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) by abel,
      ClassFunction.neg_apply, hvanish y hy, neg_zero]
  have hpsiZ : (cd.sign : ℂ) • cd.muClassFunction ∈ ZIrr G := by
    rw [Int.cast_smul_eq_zsmul ℂ]; exact (ZIrr G).smul_mem cd.sign hμZ
  have hconjZ : (cd.sign : ℂ) • cd.nuClassFunction ∈ ZIrr G := by
    rw [Int.cast_smul_eq_zsmul ℂ]; exact (ZIrr G).smul_mem cd.sign hνZ
  have hpsi1 : ClassFunction.inner ((cd.sign : ℂ) • cd.muClassFunction)
      ((cd.sign : ℂ) • cd.muClassFunction) = 1 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hμ1,
      mul_one, star_intCast]; exact hsign
  have hconj1 : ClassFunction.inner ((cd.sign : ℂ) • cd.nuClassFunction)
      ((cd.sign : ℂ) • cd.nuClassFunction) = 1 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hν1,
      mul_one, star_intCast]; exact hsign
  have hcross : ClassFunction.inner ((cd.sign : ℂ) • cd.muClassFunction)
      ((cd.sign : ℂ) • cd.nuClassFunction) = 0 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hμν,
      mul_zero, mul_zero]
  have hcross' : ClassFunction.inner ((cd.sign : ℂ) • cd.nuClassFunction)
      ((cd.sign : ℂ) • cd.muClassFunction) = 0 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hνμ,
      mul_zero, mul_zero]
  have hvpsi := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
  have hvconj := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hconjZ hpsiZ hconj1 hpsi1 hcross' hvanish' i j
  rcases hα with rfl | rfl
  · rw [← Int.cast_smul_eq_zsmul ℂ]; exact hvpsi
  · rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg, neg_smul, ClassFunction.inner_neg_right,
      hvconj, neg_zero]


set_option maxHeartbeats 1600000 in
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **irr × irr `R`-family orthogonality, `T`-instance form** (mirror of
`dadeOfDiff_orthogonal_typeP_S`): the (5.2.e) generic orthogonality specialized to
`dadeHypT hG hT2`, isolating the support defeq in one focused lemma. -/
theorem Hypothesis.dadeOfDiff_orthogonal_typeP_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (x χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T)
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥hyp.T ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥hyp.T ℂ).conj - (x : ClassFunction ↥hyp.T ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥hyp.T ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥hyp.T ℂ).conj - (χ : ClassFunction ↥hyp.T ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥hyp.T ℂ) (χ : ClassFunction ↥hyp.T ℂ) = 0)
    (hxχbar :
      ClassFunction.inner (x : ClassFunction ↥hyp.T ℂ) (χ : ClassFunction ↥hyp.T ℂ).conj = 0)
    (hxbarχ :
      ClassFunction.inner (x : ClassFunction ↥hyp.T ℂ).conj (χ : ClassFunction ↥hyp.T ℂ) = 0)
    (hxbarχbar : ClassFunction.inner (x : ClassFunction ↥hyp.T ℂ).conj
      (χ : ClassFunction ↥hyp.T ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypT hG hT2)
        (hyp.dadeHypT_hconj hG hT2) x hxreal hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypT hG hT2)
        (hyp.dadeHypT_hconj hG hT2) χ hχreal hχdiffsupp) :=
  OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) hxreal hxdiffsupp hχreal hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

set_option maxHeartbeats 1600000 in
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the caseB-`T` per-member `R`-families** (mirror of
`sSet_memberRFamily_orthogonal`; the `hRorth` input of the (5.7)-`T` engine): for members
`φ, ξ ∈ 𝒯` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the Dade image families are orthogonal — the `2×2`
member dichotomy over the dispatcher `imageSet` reductions, exactly as on the `S`-side (with
rows in place of columns). -/
theorem Hypothesis.sSet_memberRFamily_orthogonal_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {φ ξ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (h1 : ClassFunction.inner φ ξ = 0)
    (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hφ).Orthogonal
      (hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hξ) := by
  classical
  have hbφξ : ClassFunction.inner φ.conj ξ = 0 := by
    rw [← ClassFunction.conj_conj ξ, OddOrder.RepresentationTheory.inner_conj_conj, h2,
      star_zero]
  have hbφξb : ClassFunction.inner φ.conj ξ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_conj, h1, star_zero]
  intro α hα β hβ
  by_cases hφirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ <;>
    by_cases hξirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := hyp.sSet_memberRFamily_T_imageSet_of_irr hG hnoV pins hvd hT2
      Tdata hU hW1 hW2 hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := hyp.sSet_memberRFamily_T_imageSet_of_irr hG hnoV pins hvd hT2
      Tdata hU hW1 hW2 hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact hyp.dadeOfDiff_orthogonal_typeP_T hG hT2 ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩ hrφ hsφ hrξ hsξ
      h1 h2 hbφξ hbφξb α hα β hβ
  · -- irr × red
    obtain ⟨hrφ, hsφ, hφeq⟩ := hyp.sSet_memberRFamily_T_imageSet_of_irr hG hnoV pins hvd hT2
      Tdata hU hW1 hW2 hφ hφirr
    obtain ⟨rξ, sξ, hjξeq, hkξeq, hξeq⟩ :=
      hyp.sSet_memberRFamily_T_imageSet_of_red hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hξ hξirr
    rw [hφeq] at hα
    rw [hξeq, Finset.mem_image] at hβ
    obtain ⟨y, -, rfl⟩ := hβ
    rcases y with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.RepresentationTheory.inner_conj_symm, star_eq_zero]
      exact hyp.sSet_irr_memberRFamily_eta_inner_T hG hnoV hT2 Tdata hW1 hW2 hφirr hrφ hsφ
        hα rξ b
    · rw [ClassFunction.inner_neg_right, OddOrder.RepresentationTheory.inner_conj_symm,
        hyp.sSet_irr_memberRFamily_eta_inner_T hG hnoV hT2 Tdata hW1 hW2 hφirr hrφ hsφ
          hα sξ b,
        star_zero, neg_zero]
  · -- red × irr
    obtain ⟨rφ, sφ, hjφeq, hkφeq, hφeq⟩ :=
      hyp.sSet_memberRFamily_T_imageSet_of_red hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := hyp.sSet_memberRFamily_T_imageSet_of_irr hG hnoV pins hvd hT2
      Tdata hU hW1 hW2 hξ hξirr
    rw [hξeq] at hβ
    rw [hφeq, Finset.mem_image] at hα
    obtain ⟨x, -, rfl⟩ := hα
    rcases x with a | a <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hyp.sSet_irr_memberRFamily_eta_inner_T hG hnoV hT2 Tdata hW1 hW2 hξirr hrξ hsξ
        hβ rφ a
    · rw [ClassFunction.inner_neg_left,
        hyp.sSet_irr_memberRFamily_eta_inner_T hG hnoV hT2 Tdata hW1 hW2 hξirr hrξ hsξ
          hβ sφ a,
        neg_zero]
  · -- red × red
    obtain ⟨rφ, sφ, hjφeq, hkφeq, hφeq⟩ :=
      hyp.sSet_memberRFamily_T_imageSet_of_red hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hφ hφirr
    obtain ⟨rξ, sξ, hjξeq, hkξeq, hξeq⟩ :=
      hyp.sSet_memberRFamily_T_imageSet_of_red hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hξ hξirr
    rw [hφeq, Finset.mem_image] at hα
    rw [hξeq, Finset.mem_image] at hβ
    have hne1 : rφ ≠ rξ :=
      hyp.nu_rowSum_ne_of_inner_zero pins (by rw [← hjφeq, ← hjξeq]; exact h1)
    have hne2 : rφ ≠ sξ :=
      hyp.nu_rowSum_ne_of_inner_zero pins (by rw [← hjφeq, ← hkξeq]; exact h2)
    have hne3 : sφ ≠ rξ :=
      hyp.nu_rowSum_ne_of_inner_zero pins (by rw [← hkφeq, ← hjξeq]; exact hbφξ)
    have hne4 : sφ ≠ sξ :=
      hyp.nu_rowSum_ne_of_inner_zero pins (by rw [← hkφeq, ← hkξeq]; exact hbφξb)
    obtain ⟨x, -, rfl⟩ := hα
    obtain ⟨y, -, rfl⟩ := hβ
    rcases x with a | a <;> rcases y with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp rφ rξ a b, if_neg (fun h => hne1 h.1)]
    · rw [ClassFunction.inner_neg_right,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp rφ sξ a b,
        if_neg (fun h => hne2 h.1), neg_zero]
    · rw [ClassFunction.inner_neg_left,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp sφ rξ a b,
        if_neg (fun h => hne3 h.1), neg_zero]
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp sφ sξ a b, if_neg (fun h => hne4 h.1),
        neg_zero, neg_zero]


open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of `𝒯 = sSet(setupT)` on the honest `T`-Dade map**
(mirror of `sSet_coherent_dade_caseB`; the caseB-`T` (5.7) `uniform_degree_coherence_of_families`
assembly).  In the Galois case the whole family is uniform degree `p·v`
(`sSet_caseB_apply_one_eq_vp`), the pivot is a reducible ν-row `ν₁ = ∑_j ν_{1j}` (self-norm
`p`), every member carries its (5.2.d) `R`-datum (`sSet_memberRFamily_T`), and the family
facts (finiteness, pairwise orthogonality, conjugate-closure, no-real, Dade isometry/ZIrr/
support, cross-orthogonality) are the landed `T`-instance inputs. -/
noncomputable def Hypothesis.sSet_coherent_dade_caseB_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (caseB : CliffordCaseBData (hyp.mkSection11CharacterDataT hG hvd chief)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2)))
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)) := by
  classical
  -- Pivot: a nonzero reducible ν-row `ν₁ = ∑_j ν_{1j} ∈ 𝒯` (self-norm `p`).
  have hi0 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have hη₁ : (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
      ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0
      (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief ⟨1, hyp.q_prime.one_lt⟩ hi0)
  have hN : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
      (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) = (hyp.p : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
            (∑ j' : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j')
        = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p,
            ClassFunction.inner (hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
              (hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j') := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, if j = j' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [pins.nu_orthonormal ⟨1, hyp.q_prime.one_lt⟩ ⟨1, hyp.q_prime.one_lt⟩ j j']
          simp
      _ = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp
      _ = (hyp.p : ℂ) := by simp
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    (sSet_finite _) hη₁
    (fun η hη => hyp.sSet_memberRFamily_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hη)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) ha hb hab
      convert h using 2 <;> exact Subsingleton.elim _ _)
    (fun a ha => sSet_closedUnderConjugate _ ha)
    (fun a ha heq => sSet_hasNoRealCharacters _ (hyp.oddCardT hG) ha heq.symm)
    ⟨hyp.p, hN⟩
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) hφ.2 hψ.2)
    (fun a ha b hb => by
      have hab_Z : (a - b : ClassFunction ↥hyp.T ℂ)
          ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T :=
        Submodule.sub_mem _ (sSet_subset_ZIrr _ ha) (sSet_subset_ZIrr _ hb)
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2)
        (hyp.sSet_caseB_member_diff_supported_T hG hvd caseB ha hb) hab_Z)
    (fun a ha b hb => hyp.sSet_caseB_member_diff_supported_T hG hvd caseB ha hb)
    (fun {φ ξ} hφ hξ h1 h2 =>
      hyp.sSet_memberRFamily_orthogonal_T hG hnoV pins hvd hT2 Tdata hU hW1 hW2 hφ hξ h1 h2)
    (fun a ha => (hyp.sSet_caseB_apply_one_eq_vp hG hvd caseB ha).trans
      (hyp.sSet_caseB_apply_one_eq_vp hG hvd caseB hη₁).symm)
    (by
      rw [hyp.sSet_caseB_apply_one_eq_vp hG hvd caseB hη₁]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Nat.card_pos.ne'
        (OddOrder.Peterfalvi.S11.u_odd hG (hyp.mkSection11CharacterDataT hG hvd chief)).pos.ne'))
    (by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
      simpa using honestTypeP2ASet_one_not_mem (M := hyp.T))
    (sSet_closedUnderConjugate _ hη₁)
    (sSet_hasNoRealCharacters _ (hyp.oddCardT hG) hη₁)


open OddOrder.Peterfalvi.S11 in
/-- **The uniform-degree irreducible cut `S₁(d)` of `𝒯`** (mirror of `sSetIrrDeg`): the
degree-`d` irreducible members of the `T`-instance §9 family — the caseA-`T` base prefix
(`d = p·a`) of the (9.11) pair-adjoining route. -/
noncomputable def Hypothesis.sSetIrrDegT [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ) :
    Set (ClassFunction ↥hyp.T ℂ) :=
  { φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) |
      OddOrder.RepresentationTheory.IsIrreducibleCharacter φ ∧ (φ : ↥hyp.T → ℂ) 1 = d }

open OddOrder.Peterfalvi.S11 in
theorem Hypothesis.sSetIrrDegT_subset_sSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ) :
    hyp.sSetIrrDegT hG hvd d ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := fun _ h => h.1

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-`T` is conjugation-closed** (mirror of `sSetIrrDeg_closedUnderConjugate`). -/
theorem Hypothesis.sSetIrrDegT_closedUnderConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.sSetIrrDegT hG hvd d) := by
  intro φ hφ
  refine ⟨sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hφ.1, hφ.2.1.conj, ?_⟩
  rw [ClassFunction.conj_apply, hφ.2.2, hd]

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-`T` has no real members** (mirror of `sSetIrrDeg_hasNoRealCharacters`). -/
theorem Hypothesis.sSetIrrDegT_hasNoRealCharacters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.sSetIrrDegT hG hvd d) :=
  (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG)).mono
    (hyp.sSetIrrDegT_subset_sSet hG hvd d)

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-`T`-members are supported in `A(T) ∪ {1}`** (mirror of
`sSetIrrDeg_member_support_subset`). -/
theorem Hypothesis.sSetIrrDegT_member_support_subset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ)
    {φ : ClassFunction ↥hyp.T ℂ} (hφ : φ ∈ hyp.sSetIrrDegT hG hvd d) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T ∪ {1} := by
  obtain ⟨hφsSet, _⟩ := hφ
  obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
  rw [hφeq]
  exact hyp.sSet_member_support_subset_A_T hG hvd hξ

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-`T`-member differences are `A(T)`-supported** (mirror of
`sSetIrrDeg_member_diff_supported`): equal degrees cancel at `1`. -/
theorem Hypothesis.sSetIrrDegT_member_diff_supported [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ)
    {x : ClassFunction ↥hyp.T ℂ} (hx : x ∈ hyp.sSetIrrDegT hG hvd d)
    {y : ClassFunction ↥hyp.T ℂ} (hy : y ∈ hyp.sSetIrrDegT hG hvd d) :
    (x - y).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T := by
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have hdeg : (x : ↥hyp.T → ℂ) 1 = (y : ↥hyp.T → ℂ) 1 := by rw [hx.2.2, hy.2.2]
  rcases ClassFunction.support_sub_subset x y hz with h | h
  · rcases hyp.sSetIrrDegT_member_support_subset hG hvd d hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSetIrrDegT_member_support_subset hG hvd d hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])


open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member Dade `R`-datum for an irreducible `𝒯`-member** (mirror of
`sSet_member_differenceImage`): the (5.3.a) `CharacterDifferenceImage` over `dadeHypT`. -/
noncomputable def Hypothesis.sSet_member_differenceImage_T [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    [Fintype ↥hyp.T] [Invertible (Nat.card ↥hyp.T : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥hyp.T) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2)))
      (induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)) := by
  set φ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T :=
    ⟨induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ), hirr⟩ with hφ_def
  have hreal : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.T ℂ) :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) ⟨ξ, hξ, rfl⟩
  have hdiffsupp :
      ((φ : ClassFunction ↥hyp.T ℂ).conj - (φ : ClassFunction ↥hyp.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T :=
    hyp.sSet_member_diffsupp_T hG hvd hξ
  exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) φ hreal hdiffsupp

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-`T` is finite** (mirror of `sSetIrrDeg_finite`). -/
theorem Hypothesis.sSetIrrDegT_finite [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) (d : ℂ) :
    (hyp.sSetIrrDegT hG hvd d).Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T =>
      (χ : ClassFunction ↥hyp.T ℂ)))
  rintro φ ⟨_, hirr, _⟩
  exact ⟨⟨φ, hirr⟩, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The (5.2)-subcoherence structure for `S₁(d)`-`T`** (mirror of `sSetIrrDeg_subcoherent`):
`S07.Hypothesis` over `dadeHypT` on the uniform-degree irreducible cut. -/
noncomputable def Hypothesis.sSetIrrDegT_subcoherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    [Fintype ↥hyp.T] [Invertible (Nat.card ↥hyp.T : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.T) (G := G)
      (hyp.sSetIrrDegT hG hvd d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T) := by
  classical
  have hconjmem := hyp.sSetIrrDegT_closedUnderConjugate hG hvd d hd
  refine OddOrder.Peterfalvi.S07.irrSubcoherent
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
      ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2)))
    (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    (fun φ hφ => ?_) ?_ ?_ ?_ ?_ ?_
  · have hφsSet : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := hφ.1
    have hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ := hφ.2.1
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq] at hirr ⊢
    exact hyp.sSet_member_differenceImage_T hG hvd hT2 hξ hirr
  · exact hconjmem
  · exact hyp.sSetIrrDegT_hasNoRealCharacters hG hvd d
  · intro φ ψ hφ hψ hne
    convert sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) hφ.1 hψ.1 hne using 2 <;>
      exact Subsingleton.elim _ _
  · intro χ hχ
    exact hyp.sSetIrrDegT_member_diff_supported hG hvd d hχ (hconjmem hχ)
  · intro φ ψ hφ hψ
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) hφ.2 hψ.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) base coherence of `S₁(d)`-`T` on the honest `T`-Dade map** (mirror of
`sSetIrrDeg_coherent`): the (5.7)∘(5.3.a) uniform-degree producer on the cut, with the base
count `h2` exposed. -/
noncomputable def Hypothesis.sSetIrrDegT_coherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    [Fintype ↥hyp.T] [Invertible (Nat.card ↥hyp.T : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDegT hG hvd d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hT2)
        ((hyp.dadeHypT hG hT2).fullDadeIsometryData (hyp.dadeHypT_hconj hG hT2)))
      (hyp.sSetIrrDegT hG hvd d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)) := by
  classical
  set A := OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T with hA
  set hyp' := hyp.sSetIrrDegT_subcoherent hG hvd hT2 d hd with hhyp'
  have hSfin : (hyp.sSetIrrDegT hG hvd d).Finite := hyp.sSetIrrDegT_finite hG hvd d
  have hirr : ∀ ζ ∈ hyp.sSetIrrDegT hG hvd d, ClassFunction.inner ζ ζ = 1 :=
    fun ζ hζ => hζ.2.1.inner_self_eq_one
  have hconst : ∀ a ∈ hyp.sSetIrrDegT hG hvd d, ∀ b ∈ hyp.sSetIrrDegT hG hvd d,
      ((a : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
        = ((b : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 :=
    fun a ha b hb => by rw [ha.2.2, hb.2.2]
  have hdeg0 : ∀ a ∈ hyp.sSetIrrDegT hG hvd d,
      ((a : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 ≠ 0 :=
    fun a ha => by rw [ha.2.2]; exact hd0
  have h1A : (1 : ↥hyp.T) ∉ A := by
    rw [hA, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simpa using honestTypeP2ASet_one_not_mem (M := hyp.T)
  have hsuppdiff : ∀ x ∈ hyp.sSetIrrDegT hG hvd d, ∀ y ∈ hyp.sSetIrrDegT hG hvd d,
      ((x - y : ClassFunction ↥hyp.T ℂ)).support ⊆ A := by
    intro x hx y hy
    exact hyp.sSetIrrDegT_member_diff_supported hG hvd d hx hy
  have hZIrr : ∀ a ∈ hyp.sSetIrrDegT hG hvd d, ∀ b ∈ hyp.sSetIrrDegT hG hvd d,
      hyp'.tau (a - b) ∈ OddOrder.RepresentationTheory.ZIrr G := by
    intro a ha b hb
    have hab_supp : (a - b : ClassFunction ↥hyp.T ℂ).support ⊆ A := hsuppdiff a ha b hb
    have hab_Z : (a - b : ClassFunction ↥hyp.T ℂ)
        ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T :=
      Submodule.sub_mem _ ha.2.1.mem_ZIrr hb.2.1.mem_ZIrr
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypT hG hT2) (hyp.dadeHypT_hconj hG hT2) hab_supp hab_Z
  exact OddOrder.Peterfalvi.S07.coherent_subset_of_constant_degree hyp'
    (subset_refl _) hyp'.conjugate_closed hSfin h2 hirr hZIrr hconst hdeg0 h1A hsuppdiff

end OddOrder.Peterfalvi.S15
