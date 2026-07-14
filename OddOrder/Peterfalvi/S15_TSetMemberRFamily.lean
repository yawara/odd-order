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

end OddOrder.Peterfalvi.S15
