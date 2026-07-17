/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_Lemmas113To115

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S13_MaximalIII_IV` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S13
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member `ψ = 0` decompositions for a conjugate-closed irreducible subfamily of the
induced family** (the `Dmem` input of `adjoin_muColumnPair_of_irrFamily`): each member `x` of a
conjugate-closed irreducible `s ⊆ S` carries the (5.5) `ψ = 0` decomposition whose auxiliary
isometry is the running coherent extension (`memberExtensionDecomposition`; its `tau1` is
`hS₁.extension` definitionally, so the engine's `htau1Dmem` is `rfl`).  The inputs are discharged
from the family facts: non-reality and `⟨x, x̄⟩ = 0` from the odd order
(`inducedFamily_hasNoRealCharacters` + `inducedKernelFamily_pairwise_orthogonal`), the conjugate
difference support from `inducedKernelFamily_conjDiff_support`, and the integral extension value
from the coherence field `extension_mem_ZIrr`. -/
noncomputable def irrFamilyMemberDecomposition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (s : Finset (ClassFunction ↥M ℂ))
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) (↑s) hyp.A0)
    (hsub : (↑s : Set (ClassFunction ↥M ℂ)) ⊆ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hirr : ∀ x ∈ s, IsIrreducibleCharacter x)
    (hconjS : ∀ x ∈ s, x.conj ∈ s)
    {x : ClassFunction ↥M ℂ} (hx : x ∈ s) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) x 0 := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hxfam : x ∈ OddOrder.Peterfalvi.S12.inducedFamily M := hsub hx
  have hxIKF : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hxfam
    rwa [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot] at h
  have hne : x.conj ≠ x :=
    OddOrder.Peterfalvi.S12.inducedFamily_hasNoRealCharacters hModd hxfam
  have hreal : ¬ ClassFunction.IsReal x := fun h => hne h
  have hdiffsupp : ((x.conj - x : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.mderivSharp_subset_A0 hxIKF
  have hνZ : hS₁.extension x ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr x (Submodule.subset_span (Finset.mem_coe.mpr hx))
  have hχχbar : ClassFunction.inner x x.conj = 0 := by
    have hxc : x.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hxIKF
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hxIKF hxc
      (fun h => hne h.symm)
  exact OddOrder.Peterfalvi.S08.memberExtensionDecomposition hyp.dadeData.dade hyp.hconj hS₁
    ⟨x, hirr x hx⟩ hreal hdiffsupp (Finset.mem_coe.mpr hx)
    (Finset.mem_coe.mpr (hconjS x hx)) hνZ hχχbar

/-- **The degree-`d` irreducible cut of `𝒮(Y)` is finite** (Finset-ification input of the (9.11)
column-pair adjunction): it sits inside the finite kernel filtration `S(Y)`
(`sOf_subset_SOf` + `inducedKernelFamily_finite`). -/
theorem irrCut_finite [Finite G] {M : Subgroup G} (hyp : Hypothesis M) (Y : Subgroup G) (d : ℕ) :
    {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.Finite := by
  haveI := hyp.base.finiteG
  classical
  letI : Fintype ↥M := Fintype.ofFinite _
  refine (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
    (K := (derivedInG M).subgroupOf M) (Y.subgroupOf M)).subset ?_
  intro φ hφ
  have h := hyp.sOf_subset_SOf Y hφ.1
  rwa [hyp.SOf_eq] at h

/-- **The degree-`d` irreducible cut of `𝒮(Y)` is conjugate-closed** (the `hconjS` input of the
(9.11) column-pair adjunction): conjugation preserves `𝒮(Y)`-membership
(`sOf_closedUnderConjugate`), irreducibility, and the natural degree (`star_natCast`). -/
theorem irrCut_conjClosed [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (Y : Subgroup G) (d : ℕ) {x : ClassFunction ↥M ℂ}
    (hx : x ∈ {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}) :
    x.conj ∈ {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} := by
  haveI := hyp.base.finiteG
  obtain ⟨hmem, hirr, hdeg⟩ := hx
  refine ⟨Hypothesis.sOf_closedUnderConjugate hyp.s11Setup Y hmem, hirr.conj, ?_⟩
  rw [ClassFunction.conj_apply, hdeg, star_natCast]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §12 Dade image of an `A(M)`-supported function vanishes on the exceptional set `V`**
(the §12 analogue of `tau_apply_eq_zero_of_mem_ticVdiffV`, by a *different* route — issue 1019
update⁷³/⁷⁴): for `α` supported on `A(M) = (M')^#` and `v ∈ (ticVdiff h46).V = W ∖ (W₁ ∪ W₂) =
typePV M`, the image `α^τ` vanishes at `v`.

Unlike the Sibley case (where `V` avoids the Dade support and the image vanishes for lack of a
base point), here `V^M ⊆ A₀(M)` — `v` **is** a Dade base point.  The explicit (2.5) evaluation
(`dadeValue_eq` with the witness `a = v`, `h = 1`) gives `α^τ(v) = α(v)`, which vanishes because
`v ∉ M'` (`typePData_typePV_not_mem_derived`) while `α` is supported on `(M')^# ⊆ M'`.  This is
the anchor of the §12 cross-orthogonality `R(μ_j) ⊥ R(χ)` (the `hortho_mem` input of the (9.11)
column-pair adjunction). -/
theorem tau_apply_eq_zero_of_mem_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    {α : ClassFunction ↥M ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA M hyp.typeP) M)
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) α v = 0 := by
  haveI := hyp.finiteG
  classical
  -- `v ∈ typePV M` (the `ticVdiff` exceptional set is definitionally `W ∖ (W₁ ∪ W₂)`)
  have hvPV : v ∈ OddOrder.GroupTheory.typePV M hyp.typeP := hv
  -- `v ∈ A₀(M)` (the `V^M`-part, conjugator `1`)
  have hvA0 : v ∈ OddOrder.GroupTheory.typePA0 M hyp.typeP :=
    Or.inr ⟨v, hvPV, 1, M.one_mem, by group⟩
  -- `α` is `A₀`-supported (monotone from `A(M)`-supported)
  have hαA0 : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA0 M hyp.typeP) M :=
    hαsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- evaluate the explicit (2.5) Dade map at the base point `a = v`, `h = 1`
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hαA0,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    hyp.dadeData.dade.dadeValue_eq _ (a := ⟨v, hvA0⟩)
      (Subgroup.one_mem _) (by rw [mul_one])]
  -- `α(v) = 0`: `v ∉ M'` while `α` is `(M')^#`-supported
  by_contra hne
  have hmem := hαsupp (ClassFunction.mem_support.mpr hne)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
    OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG] at hmem
  exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hvPV hmem.1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) certain-type column vs irreducible break cross-orthogonality, §12 form**
`R(μ_j) ⊥ R(χ)` — the §12 (`A₀(M)`-Dade) analogue of
`certainTypeR_imageSet_orthogonal_dadeOfDiff` (S08_CaseBHortho, Sibley world).  The proof is a
mirror: the disjointness machine (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` on
`ticVdiff (toHypothesis46 …)`) and the two-element `R(χ)` capture are `h46`-generic; the single
Sibley-specific anchor — vanishing of `(χ − χ̄)^τ` on the exceptional `V` — is replaced by the
§12 anchor `tau_apply_eq_zero_of_mem_typePV` (base-point evaluation, `V^M ⊆ A₀`).  The conjugate
difference is `A(M)`-supported (`hdiffsuppχA`, feeding the anchor) and `A₀(M)`-supported
(`hdiffsuppχ`, defining the Dade image family `R(χ)`).  This is the `hortho_mem` core of the
(9.11) column-pair adjunction. -/
theorem certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂).mu i
        : ClassFunction ↥M ℂ) 1)
      = (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂⁻¹).mu i
        : ClassFunction ↥M ℂ) 1))
    (χ : IrreducibleCharacter ↥M)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥M ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA M hyp.typeP) M)
    (hdiffsuppχ : (((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA0 M hyp.typeP) M) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR (hyp.toHypothesis46 hG hG.odd)
        hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
        hyp.hconj χ hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  haveI := hyp.finiteG
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).three_le_card_W2
    omega
  -- core disjointness brick (mirror of the Sibley `key`)
  have key : ∀ (χ₂' : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ)
      (i : Fin (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)) {c c' : ℂ}
      {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G →
      ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V,
        (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.toHypothesis46 hG hG.odd) χ₂' i)
        = 0 := by
    intro χ₂' i c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact OddOrder.Peterfalvi.S08.inner_smul_chiFam_eq_zero_of_diff_vanishOnV
      (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (hyp.toHypothesis46 hG hG.odd))
      hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish hmin _
  -- `(χ − χ̄)^τ` vanishes on `V` (the §12 anchor, base-point evaluation)
  have hsuppsub : (((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA M hyp.typeP) M := by
    rw [show (χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj =
        -((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  have htauvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
        ((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj) v = 0 :=
    fun v hv => tau_apply_eq_zero_of_mem_typePV hG hyp hsuppsub hv
  -- capture the two-element `R(χ)` abstractly
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) (χ : ClassFunction ↥M ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
            hyp.hconj χ hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
      ((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  intro α hα β hβ
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  simp only [OddOrder.Peterfalvi.S06.certainTypeR, Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  have hvanishμν : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  have hμcast : cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction :=
    (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm
  have hνcast : (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction := by
    rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]
  rcases hβ with rfl | rfl <;> cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member `(5.4)` decomposition bundled with its (5.2.e) cross-orthogonality against a
certain-type column break, §12 form** (the `Dmem`/`hortho_mem`/`htau1Dmem` package of the (9.11)
column-pair adjunction `adjoin_muColumnPair_of_irrFamily`; the all-irreducible §12 analogue of
`caseB_member_orthoDatum_columnBreak`).

For each member `x` of a conjugate-closed irreducible family `s ⊆ S` (coherent via `hS₁`), the
`ψ = 0` decomposition `D` is `memberExtensionDecomposition` (so `D.tau1 = hS₁.extension` by
`rfl`), and its image family `R(x) = dadeOrthonormalCharacterImageFamilyOfDiff` is orthogonal to
the break's `R(μ_b) = certainTypeR χ₂b` by the §12 cross-orthogonality
`certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (conjugate-symmetry swap).  Both supports of
the member's conjugate difference are discharged from the induced-family machinery: `A₀(M)` via
`mderivSharp_subset_A0`, `A(M)` via the sharp form `typePA_eq_sharpSubgroup_derivedInG`. -/
noncomputable def irrFamilyMemberOrthoDatum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (S₁ : Set (ClassFunction ↥M ℂ))
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) S₁ hyp.A0)
    (s : Finset (ClassFunction ↥M ℂ))
    (hsS₁ : (↑s : Set (ClassFunction ↥M ℂ)) ⊆ S₁)
    (hsub : (↑s : Set (ClassFunction ↥M ℂ)) ⊆ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hirr : ∀ x ∈ s, IsIrreducibleCharacter x)
    (hconjS : ∀ x ∈ s, x.conj ∈ s)
    {χ₂b : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂b : χ₂b ≠ 1)
    (hdegb : (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂b).mu i
        : ClassFunction ↥M ℂ) 1)
      = (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂b⁻¹).mu i
        : ClassFunction ↥M ℂ) 1))
    {x : ClassFunction ↥M ℂ} (hx : x ∈ s) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) x 0 //
      (∀ α ∈ D.imageFamily.imageSet,
          ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR (hyp.toHypothesis46 hG hG.odd)
            hχ₂b hdegb).imageSet,
            ClassFunction.inner α β = 0) ∧
        D.tau1 x = hS₁.extension x } := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hxfam : x ∈ OddOrder.Peterfalvi.S12.inducedFamily M := hsub hx
  have hxIKF : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hxfam
    rwa [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot] at h
  have hne : x.conj ≠ x :=
    OddOrder.Peterfalvi.S12.inducedFamily_hasNoRealCharacters hModd hxfam
  have hreal : ¬ ClassFunction.IsReal x := fun h => hne h
  -- the conjugate difference is `A₀(M)`-supported (defining `R(x)`) and `A(M)`-supported (anchor)
  have hdiffsupp0 : ((x.conj - x : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.mderivSharp_subset_A0 hxIKF
  have hdiffsuppA : ((x.conj - x : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.typeP) M := by
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support ?_ hxIKF
    intro y hyK hy1
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
    exact ⟨Subgroup.mem_subgroupOf.mp hyK,
      fun h => hy1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h))⟩
  have hνZ : hS₁.extension x ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr x (Submodule.subset_span (hsS₁ (Finset.mem_coe.mpr hx)))
  have hχχbar : ClassFunction.inner x x.conj = 0 := by
    have hxc : x.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hxIKF
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hxIKF hxc
      (fun h => hne h.symm)
  refine ⟨OddOrder.Peterfalvi.S08.memberExtensionDecomposition hyp.dadeData.dade hyp.hconj hS₁
    ⟨x, hirr x hx⟩ hreal hdiffsupp0 (hsS₁ (Finset.mem_coe.mpr hx))
    (hsS₁ (Finset.mem_coe.mpr (hconjS x hx))) hνZ hχχbar, ?_, rfl⟩
  -- `R(x) ⊥ R(μ_b)`: the §12 (5.2.e) cross-orthogonality, conjugate-symmetry swap
  intro α hα β hβ
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp hχ₂b hdegb ⟨x, hirr x hx⟩
      hreal hdiffsuppA hdiffsupp0 β hβ α hα, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) caseB one-pair step, end-to-end**: the degree-`d` irreducible cut of `𝒮(H₀C′)`
absorbs one certain-type column pair `{μ, μ̄}`, staying coherent on `A₀(M)`.  This instantiates
`adjoin_muColumnPair_of_irrFamily` with every structural input discharged from the landed
supply chain (issue 1019 update⁷⁷):

* `hS₁` = `sOf_degreeSubfamily_isCoherent` (the anchor `χ₁` is the degree-`d` witness);
* family facts = `irrCut_finite`/`irrCut_conjClosed` + the cut definition;
* `Dmem`/`htau1Dmem`/`hortho_mem` = `irrFamilyMemberOrthoDatum`;
* `Da`/`hDatau1` = `columnBreakDa`;
* `hμ_S1`/`hμbar_S1` = `columnSum_inner_irr_member_eq_zero` (+ conjugate column);
* `hμZ` = `columnSum_mem_ZIrr`; `hdeganchor` from `hdegcol` + the anchor degree.

The remaining *genuine* inputs are the §9/caseB facts: `hDeg` (the cut has `> 2` members, the
(5.6.c) counting), `hdegcol` (the column degree matches the cut degree — caseB uniform-`qu`),
and `hdiffasuppχ` (the `A₀`-support of `μ − χ₁`, equal-degree difference). -/
noncomputable def caseB_adjoinOneColumnPair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hχ₁irr : IsIrreducibleCharacter χ₁)
    (hχ₁deg : ((χ₁ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ))
    {χ₂ : ((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.base.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdegcol : OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂ 1
      = (d : ℂ))
    (hdiffasuppχ : ((OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂
      - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0)
    (hDeg : (2 : ℝ) < (irrCut_finite hyp hyp.H0Cprime d).toFinset.card) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      ((↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ∪
        {OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂,
         (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂).conj})
      hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- the coherent irreducible cut, transported onto the Finset coercion
  have hS₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ))
      hyp.base.A0 := by
    rw [Set.Finite.coe_toFinset]
    exact sOf_degreeSubfamily_isCoherent hG hyp hyp.H0Cprime d ⟨χ₁, hχ₁mem, hχ₁irr, hχ₁deg⟩
  -- membership repackaging helpers
  have hmemiff : ∀ x : ClassFunction ↥M ℂ,
      x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset ↔
      (x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter x ∧ ((x : ↥M → ℂ) 1 = (d : ℂ))) := fun x =>
    (irrCut_finite hyp hyp.H0Cprime d).mem_toFinset
  have hsub : (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ⊆
      OddOrder.Peterfalvi.S12.inducedFamily M := by
    intro x hx
    have hcut := (hmemiff x).mp hx
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hcut.1
    rw [hyp.SOf_eq] at h
    rw [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  have hirr : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      IsIrreducibleCharacter x := fun x hx => ((hmemiff x).mp hx).2.1
  have hconjS : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      x.conj ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset := fun x hx =>
    (hmemiff _).mpr (irrCut_conjClosed hyp hyp.H0Cprime d ((hmemiff x).mp hx))
  have hχ₁s : χ₁ ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset :=
    (hmemiff χ₁).mpr ⟨hχ₁mem, hχ₁irr, hχ₁deg⟩
  have hdegmem : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      (x : ClassFunction ↥M ℂ) 1 = χ₁ 1 := fun x hx => by
    rw [((hmemiff x).mp hx).2.2, hχ₁deg]
  -- member ∈ kernel filtration (for the μ ⊥ member orthogonality)
  have hmemIKFH : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := fun x hx => by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime ((hmemiff x).mp hx).1
    rwa [hyp.SOf_eq] at h
  have hμ_S1 : ∀ x ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset
        : Set (ClassFunction ↥M ℂ)),
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum
        (hyp.base.toHypothesis46 hG hG.odd) χ₂) x = 0 := fun x hx =>
    hyp.base.columnSum_inner_irr_member_eq_zero hG hyp.type_alt hyp.params
      (hyp.params_mu_eq hG hG.odd) hχ₂ (hmemIKFH x (Finset.mem_coe.mp hx))
      (hirr x (Finset.mem_coe.mp hx))
  have hμbar_S1 : ∀ x ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset
        : Set (ClassFunction ↥M ℂ)),
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum
        (hyp.base.toHypothesis46 hG hG.odd) χ₂).conj x = 0 := fun x hx => by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    exact hyp.base.columnSum_inner_irr_member_eq_zero hG hyp.type_alt hyp.params
      (hyp.params_mu_eq hG hG.odd)
      ((@inv_ne_one (((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
        ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔
          (hyp.base.toHypothesis46 hG hG.odd).W2)) →* ℂˣ) _ χ₂).mpr hχ₂)
      (hmemIKFH x (Finset.mem_coe.mp hx))
      (hirr x (Finset.mem_coe.mp hx))
  -- anchor differences are `A₀`-supported over the cut (equal degrees, scaled-difference support)
  have hmemIKFbot : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le (hmemIKFH x hx)
  have hdegS₁diff : ∀ x ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset
        : Set (ClassFunction ↥M ℂ)),
      ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := fun x hx => by
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hmemIKFbot x (Finset.mem_coe.mp hx))
      (hmemIKFbot χ₁ hχ₁s) (d := 1)
      (by rw [Nat.cast_one, one_mul]; exact hdegmem x (Finset.mem_coe.mp hx))
    rwa [one_smul] at h
  -- the bundled per-member datum (Dmem + cross-orthogonality + tau1)
  have hdegb := (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
    (hyp.base.toHypothesis46 hG hG.odd) χ₂).symm
  let datum := fun (x : ClassFunction ↥M ℂ)
      (hx : x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset) =>
    irrFamilyMemberOrthoDatum hG hyp.base
      (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) hS₁
      (irrCut_finite hyp hyp.H0Cprime d).toFinset Set.Subset.rfl
      hsub hirr hconjS hχ₂ hdegb hx
  -- the break decomposition
  have hμZ := hyp.base.columnSum_mem_ZIrr hG χ₂
  let Da := hyp.base.columnBreakDa hG hyp.type_alt hyp.params (hyp.params_mu_eq hG hG.odd)
    hχ₂ (hmemIKFH χ₁ hχ₁s) hχ₁irr hdiffasuppχ hμZ
  -- fire the composite
  exact adjoin_muColumnPair_of_irrFamily hG hyp.base
    (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) hS₁
    (irrCut_finite hyp hyp.H0Cprime d).toFinset Set.Subset.rfl hirr hχ₁s hχ₂ hdegmem
    hdegS₁diff hμ_S1 hμbar_S1
    (fun x hx => (datum x hx).1)
    (fun x hx => (datum x hx).2.2)
    Da (by with_unfolding_all rfl)
    (fun x hx => fun α hα β hβ => by
      with_unfolding_all exact (datum x hx).2.1 α hα β hβ)
    hdiffasuppχ hμZ hDeg
    (by rw [hdegcol, hχ₁deg])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **caseB member dichotomy** (the `hcover` core of the (9.11) chain fold): under the caseB
uniform degree (`hunif`, every `𝒮(H₀C′)`-member has degree `d`), each member either lies in the
degree-`d` irreducible cut, or is a nontrivial μ-grid column sum
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` + the world-join
`muGrid_columnSum_eq_columnSum`). -/
theorem caseB_sOf_member_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    φ ∈ {ψ : ClassFunction ↥M ℂ | ψ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter ψ ∧ ((ψ : ↥M → ℂ) 1 = (d : ℂ))} ∨
      ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
        φ = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) := by
  haveI := hyp.base.finiteG
  classical
  by_cases hirr : IsIrreducibleCharacter φ
  · exact Or.inl ⟨hφ, hirr, hunif φ hφ⟩
  · right
    have hφIKF : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hφ
      rwa [hyp.SOf_eq] at h
    obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
      hφIKF hirr
    exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member orthonormal `R`-family over `𝒮(H₀C′)`** (the raw (5.2.d) datum for the
norm-general (5.7) engine `uniform_degree_coherence_of_families`).  The caseB member dichotomy
(`caseB_sOf_member_dichotomy`) splits every member into an irreducible (degree `d`) or a certain-type
column sum `μ_k`; the `R`-family is dispatched accordingly:

* **irreducible `η`** — the 2-element signed Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`
  (`hyp.base.tau (η − η̄) = ε·(μ − ν)`);
* **column `η = μ_k`** — the `2q`-element certain-type family `S06.certainTypeR` at
  `χ₂ = muColumnChar k` (`hyp.base.tau (μ_k − μ̄_k) = ∑ R(μ_k)`).

Both land *definitionally* on `hyp.base.tau = dadeIntegralCharacterMap h.dade0 h.tau` (the
`toHypothesis46` unfolding), so no `congrMap` seam.  The column case rebuilds the family at the
abstract member `η` (rather than `▸`-transporting) by reusing the `η`-independent
`imageSet`/`orthonormal`/`mem_ZIrr` fields of `certainTypeR` and re-proving `image_eq` through the
dichotomy equality `η = columnSum h χ₂` — so `(caseB_sOf_memberRFamily …).imageSet` is
*definitionally* `certainTypeR.imageSet`, the form the (5.2.e) cross-orthogonality lemmas
consume. -/
noncomputable def caseB_sOf_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- bridge to the `⊥`-kernel induced family (for support / no-real facts)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hη
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible: the signed Dade family
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0
    exact OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      hyp.base.dadeData.dade hyp.base.hconj ⟨η, hirr⟩ hreal hdiffsupp
  · -- column: rebuild `certainTypeR` at the abstract member `η` (data extracted by choice)
    have hex := (caseB_sOf_member_dichotomy hG hyp d hunif hη).resolve_left
      (fun h => hirr h.2.1)
    let k := hex.choose
    have hk0 : k ≠ 0 := hex.choose_spec.1
    have hkeq : η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := hex.choose_spec.2
    exact
      { imageSet := (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet
        mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).mem_ZIrr
        orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).orthonormal
        image_eq := by
          rw [hkeq]
          exact (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
            (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
              (hyp.base.muColumnChar hG hG.odd k)).symm).image_eq }

/-- **`caseB_sOf_memberRFamily` reduction, irreducible case**: for an irreducible member `η`, the
dispatched `R`-family *is* `dadeOrthonormalCharacterImageFamilyOfDiff` (imageSet form).  The
realness and support proofs are existential (proof-irrelevant inputs to a proof-independent
`imageSet`), so the (5.2.e) `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` lemma applies to
`(caseB_sOf_memberRFamily …).imageSet` after rewriting. -/
theorem caseB_sOf_memberRFamily_imageSet_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA0 M hyp.base.typeP) M),
      (caseB_sOf_memberRFamily hG hyp d hunif hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.base.dadeData.dade hyp.base.hconj ⟨η, hirr⟩ hr hs).imageSet := by
  haveI := hyp.base.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hη)
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0, ?_⟩
  unfold caseB_sOf_memberRFamily
  rw [dif_pos hirr]

/-- **`caseB_sOf_memberRFamily` reduction, column case**: for a reducible member `η`, the dispatched
`R`-family *is* `certainTypeR` at the certain-type column `χ₂ = muColumnChar k` (imageSet form),
for the internally-chosen column index `k` (exposed existentially together with the membership
equation `η = columnSum h χ₂`, which supplies the `≠`-side conditions of the μ×μ / μ×irr
cross-orthogonality). -/
theorem caseB_sOf_memberRFamily_imageSet_of_col [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (caseB_sOf_memberRFamily hG hyp d hunif hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  haveI := hyp.base.finiteG
  have hex := (caseB_sOf_member_dichotomy hG hyp d hunif hη).resolve_left (fun h => hcol h.2.1)
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold caseB_sOf_memberRFamily
  rw [dif_neg hcol]

set_option maxHeartbeats 1600000 in
-- the `dadeData.dade`-support defeq (`supportInSubgroup A L =?= typePA0`) is feasible but
-- expensive; discharging it once here keeps it out of the larger `hRorth` proof
/-- **irr × irr `R`-family orthogonality, typeP form**: the §12/§13 specialization of the generic
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` to `hyp.dadeData.dade` with the typePA0
supports, isolating the (feasible-but-expensive) `dadeData.dade`-support defeq in one focused lemma
(so the (5.2.e) `hRorth` case split does not re-pay it under its large local context). -/
theorem dadeOfDiff_orthogonal_dadeOfDiff_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (x χ : IrreducibleCharacter ↥M)
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥M ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥M ℂ).conj - (x : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 M hyp.typeP) M)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥M ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 M hyp.typeP) M)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥M ℂ) (χ : ClassFunction ↥M ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction ↥M ℂ) (χ : ClassFunction ↥M ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction ↥M ℂ).conj (χ : ClassFunction ↥M ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction ↥M ℂ).conj (χ : ClassFunction ↥M ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
        hyp.hconj x hxreal hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
        hyp.hconj χ hχreal hχdiffsupp) :=
  OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    hyp.dadeData.dade hyp.hconj hxreal hxdiffsupp hχreal hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against the
-- (5.2.e) lemmas through the `hyp.base.tau = dadeIntegralCharacterMap` defeq
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families over `𝒮(H₀C′)`** (the `hRorth`
input of the norm-general (5.7) engine).  For members `φ, ξ` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the
`R`-families `R(φ) ⊥ R(ξ)` — a `2×2` case split on the member dichotomy (irreducible / column):

* **irr × irr** — `dadeOfDiff_orthogonal_dadeOfDiff_typeP`; the two extra scalars
  `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` are `star`-conjugates of `⟨φ, ξ̄⟩`, `⟨φ, ξ⟩` (`inner_conj_conj`), so `0`;
* **irr × column** / **column × irr** — `certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP`
  (the irr-on-left order via an `inner_conj_symm` swap);
* **column × column** — `certainTypeR_imageSet_orthogonal_certainTypeR`, whose `χ₂ ≠ χ₂'` and
  `χ₂ ≠ χ₂'⁻¹` side conditions come from `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`: if `χ₂ = χ₂'` then `φ = ξ`
  and `⟨φ, φ⟩ = w₁ ≠ 0`; if `χ₂ = χ₂'⁻¹` then `φ = ξ̄` (`columnSum_conj_eq`) and `⟨φ, ξ̄⟩ = w₁`. -/
theorem caseB_sOf_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hξ : ξ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (caseB_sOf_memberRFamily hG hyp d hunif hφ).Orthogonal
      (caseB_sOf_memberRFamily hG hyp d hunif hξ) := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- typePA support for an irreducible member (needed by the μ×irr cross-orthogonality)
  have hIrrPA : ∀ {ζ : ClassFunction ↥M ℂ},
      ζ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.base.typeP) M) := by
    intro ζ hζ
    have hζIKF0 : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hζ)
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support ?_ hζIKF0
    intro y hyK hy1
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
    exact ⟨Subgroup.mem_subgroupOf.mp hyK,
      fun h => hy1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h))⟩
  -- self-norm `w₁ ≠ 0` of a column sum (for the μ×μ `≠`-conditions)
  have hw1ne : (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact dadeOfDiff_orthogonal_dadeOfDiff_typeP hG hyp.base ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨φ, hφirr⟩ hrφ (hIrrPA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrPA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ :=
      caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ :=
      caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46
    -- `χ₂ ≠ χ₂'`: else `φ = ξ` and `⟨φ, φ⟩ = w₁ ≠ 0` contradicts `h1`
    have hne1 : hyp.base.muColumnChar hG hG.odd kφ ≠ hyp.base.muColumnChar hG hG.odd kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    -- `χ₂ ≠ χ₂'⁻¹`: else `φ = ξ̄` and `⟨φ, ξ̄⟩ = w₁ ≠ 0` contradicts `h2`
    have hne2 : hyp.base.muColumnChar hG hG.odd kφ ≠ (hyp.base.muColumnChar hG hG.odd kξ)⁻¹ := by
      intro heq
      have hφξc : φ = ξ.conj := by
        rw [hkφeq, heq, ← OddOrder.Peterfalvi.S06.columnSum_conj_eq, hkξeq]
      rw [hφξc, hkξeq, OddOrder.Peterfalvi.S06.columnSum_conj_eq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46
      (hyp.base.muColumnChar_ne_one hG hG.odd hkφ0) (hyp.base.muColumnChar_ne_one hG hG.odd hkξ0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kφ)).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kξ)).symm
      hne1 hne2 α hα β hβ

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Uniform anchor-difference support over `𝒮(H₀C′)`** (the `hdegS₁diff` supply of every (9.11)
chain step, uniform over the whole family): under the caseB uniform degree (`hunif`), the
difference of any member against the anchor `χ₁ ∈ 𝒮(H₀C′)` is `A₀`-supported — both are
`S(⊥)`-members of equal degree, so `inducedKernelFamily_scaledDiff_support` applies at `d = 1`.
Since every chain accumulator `S₁ = pairUnion S₀ pair i` is a subfamily of `𝒮(H₀C′)`, this one
lemma feeds `hdegS₁diff` at every step. -/
theorem sOf_anchor_diff_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    {x : ClassFunction ↥M ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun y hy => by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hy
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
    hyp.base.mderivSharp_subset_A0 (hIKF x hx) (hIKF χ₁ hχ₁mem) (d := 1)
    (by rw [Nat.cast_one, one_mul, hunif x hx, hunif χ₁ hχ₁mem])
  rwa [one_smul] at h

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) caseB chain step**: a chain accumulator `S₁` (the irreducible cut plus previously
adjoined column pairs, `hS₁mu`) absorbs one *fresh* column pair (`hnotin`/`hnotin'`), staying
coherent.  The per-step inputs of `adjoin_muColumnPair_of_irrFamily` are discharged uniformly:
`hdegS₁diff` from the family-wide `sOf_anchor_diff_support` (`S₁ ⊆ 𝒮(H₀C′)`), `hμ_S1` by the
accumulator dichotomy (cut member ⟶ `columnSum_inner_irr_member_eq_zero`; old column ⟶
`columnSum_inner_columnSum_eq_zero`, the dual distinctness extracted from set-level freshness by
`columnSum_injective`), the break data from `columnBreakDa`/`irrFamilyMemberOrthoDatum`, and the
degrees from the uniform `hunif`.  This is the `hstep` core of the (9.11) caseB fold; the fold
itself only has to maintain the accumulator invariants. -/
noncomputable def caseB_chainStep [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hχ₁irr : IsIrreducibleCharacter χ₁)
    (hχ₁deg : ((χ₁ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ))
    (hDeg : (2 : ℝ) < (irrCut_finite hyp hyp.H0Cprime d).toFinset.card)
    {S₁ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : S₁ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hS₁cut : (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ⊆ S₁)
    (hS₁mu : ∀ x ∈ S₁,
      x ∉ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) →
      ∃ χ₂' : ((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
        ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.base.toHypothesis46 hG hG.odd).W2)) →* ℂˣ,
        x = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂')
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau S₁ hyp.base.A0)
    {χ₂ : ((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.base.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hμmem : OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hnotin : OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂ ∉ S₁)
    (hnotin' : (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂).conj
      ∉ S₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (S₁ ∪
        {OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂,
         (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂).conj})
      hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- membership repackaging for the cut
  have hmemiff : ∀ x : ClassFunction ↥M ℂ,
      x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset ↔
      (x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter x ∧ ((x : ↥M → ℂ) 1 = (d : ℂ))) := fun x =>
    (irrCut_finite hyp hyp.H0Cprime d).mem_toFinset
  have hirr : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      IsIrreducibleCharacter x := fun x hx => ((hmemiff x).mp hx).2.1
  have hconjS : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      x.conj ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset := fun x hx =>
    (hmemiff _).mpr (irrCut_conjClosed hyp hyp.H0Cprime d ((hmemiff x).mp hx))
  have hχ₁s : χ₁ ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset :=
    (hmemiff χ₁).mpr ⟨hχ₁mem, hχ₁irr, hχ₁deg⟩
  have hdegmem : ∀ x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset,
      (x : ClassFunction ↥M ℂ) 1 = χ₁ 1 := fun x hx => by
    rw [((hmemiff x).mp hx).2.2, hχ₁deg]
  -- kernel-filter memberships
  have hmemIKFH : ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := fun y hy => by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hy
    rwa [hyp.SOf_eq] at h
  -- anchor differences over `S₁` (uniform, family-wide)
  have hdegS₁diff : ∀ x ∈ S₁, ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
    fun x hx => sOf_anchor_diff_support hG hyp d hunif hχ₁mem (hS₁sub hx)
  -- `μ_new ⊥ S₁` (accumulator dichotomy)
  have hμ_S1 : ∀ x ∈ S₁, ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂) x = 0 := by
    intro x hx
    by_cases hcut : x ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset
        : Set (ClassFunction ↥M ℂ))
    · exact hyp.base.columnSum_inner_irr_member_eq_zero hG hyp.type_alt hyp.params
        (hyp.params_mu_eq hG hG.odd) hχ₂
        (hmemIKFH x (hS₁sub hx)) (hirr x (Finset.mem_coe.mp hcut))
    · obtain ⟨χ₂', rfl⟩ := hS₁mu x hx hcut
      exact hyp.base.columnSum_inner_columnSum_eq_zero hG
        (fun heq => hnotin (heq ▸ hx))
  have hμbar_S1 : ∀ x ∈ S₁, ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂).conj x
      = 0 := by
    intro x hx
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    by_cases hcut : x ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset
        : Set (ClassFunction ↥M ℂ))
    · exact hyp.base.columnSum_inner_irr_member_eq_zero hG hyp.type_alt hyp.params
        (hyp.params_mu_eq hG hG.odd)
        ((@inv_ne_one (((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
          ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔
            (hyp.base.toHypothesis46 hG hG.odd).W2)) →* ℂˣ) _ χ₂).mpr hχ₂)
        (hmemIKFH x (hS₁sub hx)) (hirr x (Finset.mem_coe.mp hcut))
    · obtain ⟨χ₂', rfl⟩ := hS₁mu x hx hcut
      refine hyp.base.columnSum_inner_columnSum_eq_zero hG (fun heq => hnotin' ?_)
      rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, heq]
      exact hx
  -- cut ⊆ induced family (for the member datum)
  have hsub : (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ⊆
      OddOrder.Peterfalvi.S12.inducedFamily M := by
    intro x hx
    have h := hmemIKFH x ((hmemiff x).mp (Finset.mem_coe.mp hx)).1
    rw [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  -- bundled per-member datum and the break decomposition
  have hdegb := (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
    (hyp.base.toHypothesis46 hG hG.odd) χ₂).symm
  let datum := fun (x : ClassFunction ↥M ℂ)
      (hx : x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset) =>
    irrFamilyMemberOrthoDatum hG hyp.base S₁ hcoh
      (irrCut_finite hyp hyp.H0Cprime d).toFinset hS₁cut
      hsub hirr hconjS hχ₂ hdegb hx
  have hμZ := hyp.base.columnSum_mem_ZIrr hG χ₂
  have hdiffasuppχ : ((OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂
      - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
    sOf_anchor_diff_support hG hyp d hunif hχ₁mem hμmem
  let Da := hyp.base.columnBreakDa hG hyp.type_alt hyp.params (hyp.params_mu_eq hG hG.odd)
    hχ₂ (hmemIKFH χ₁ hχ₁mem) hχ₁irr hdiffasuppχ hμZ
  -- fire the (S₁-separated) composite
  exact adjoin_muColumnPair_of_irrFamily hG hyp.base S₁ hcoh
    (irrCut_finite hyp hyp.H0Cprime d).toFinset hS₁cut hirr hχ₁s hχ₂ hdegmem
    hdegS₁diff hμ_S1 hμbar_S1
    (fun x hx => (datum x hx).1)
    (fun x hx => (datum x hx).2.2)
    Da (by with_unfolding_all rfl)
    (fun x hx => fun α hα β hβ => by
      with_unfolding_all exact (datum x hx).2.1 α hα β hβ)
    hdiffasuppχ hμZ hDeg
    (by rw [hunif _ hμmem, hχ₁deg])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (9.11) caseB column-pair enumeration**: the `j`-th adjoined pair is the certain-type
column pair `(μ_{j+1}, μ̄_{j+1})` at the nonzero column index `j + 1 < w₂` (out of range: junk
`(0, 0)`, never consumed — the chain length is `w₂ − 1`).  This enumerates *all* nontrivial
μ-columns rather than an inverse-pair transversal; conjugate columns appear twice
(`μ̄_k = μ_{k⁻¹}`), which the fold absorbs by skipping already-adjoined pairs
(`caseB_chainStep` only fires on fresh pairs) — issue 1019 update⁸⁰. -/
noncomputable def caseBPair [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] (j : ℕ) :
    ClassFunction ↥M ℂ × ClassFunction ↥M ℂ :=
  if h : j + 1 < hyp.base.w2 then
    (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
       (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩),
     (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
       (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩)).conj)
  else (0, 0)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- `caseBPair` at an in-range index `j + 1 < w₂` is the column pair `(μ_{j+1}, μ̄_{j+1})`. -/
theorem caseBPair_of_lt [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {j : ℕ} (h : j + 1 < hyp.base.w2) :
    caseBPair hG hyp j =
      (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
         (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩),
       (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
         (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩)).conj) :=
  dif_pos h

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The `j`-th adjoined pair, as the two-element set `{μ_{j+1}, μ̄_{j+1}}` (the `pairSet` form
consumed by the chain-cover engine). -/
theorem caseBPairSet_of_lt [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {j : ℕ} (h : j + 1 < hyp.base.w2) :
    OddOrder.Peterfalvi.S07.pairSet (L := ↥M) (caseBPair hG hyp) j =
      {OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
         (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩),
       (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
         (hyp.base.muColumnChar hG hG.odd ⟨j + 1, h⟩)).conj} := by
  rw [OddOrder.Peterfalvi.S07.pairSet, caseBPair_of_lt hG hyp h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), caseB mixed corner: `𝒮(H₀C′)` is coherent on `A₀(M)`.**

The final fold of the caseB (9.11) chain (issue 1019 update⁸⁰–⁸³): starting from the coherent
degree-`d` irreducible cut (`sOf_degreeSubfamily_isCoherent`), adjoin the certain-type column
pairs `{μ_k, μ̄_k}` (`k = 1, …, w₂ − 1`) one at a time (`caseB_chainStep`), skipping pairs
already absorbed (conjugate columns enumerate twice, `μ̄_k = μ_{k⁻¹}`, so a pair may reappear);
the caseB member dichotomy (`caseB_sOf_member_dichotomy`) certifies that the cut and the column
pairs cover the family, and the `coherentOfPairChainCover` engine folds the steps.  Freshness of
*both* components at an adjoining step is extracted from the failure of the skip test by
conjugation-closure of the accumulator (the cut is conjugate-closed and each pair is a conjugate
pair).

The named hypotheses are the remaining caseB §9 facts (issue 1019 update⁸²):
* `hunif` — the caseB uniform degree (every `𝒮(H₀C′)`-member has degree `d = qu`);
* the anchor `χ₁` — a degree-`d` irreducible member (seed of the cut coherence);
* `hDeg` — the (5.6.c) counting `2 < |cut|`;
* `hμmem` — every nontrivial column sum `μ_k` is an `𝒮(H₀C′)`-member ((9.5)/(9.8):
  `μ_k ∈ 𝒮(H₀C) ⊆ 𝒮(H₀C′)`, the column source kills `H₀C′`). -/
noncomputable def caseB_coherent_sOf_H0Cprime_of_mixed [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hχ₁irr : IsIrreducibleCharacter χ₁)
    (hχ₁deg : ((χ₁ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ))
    (hDeg : (2 : ℝ) < (irrCut_finite hyp hyp.H0Cprime d).toFinset.card)
    (hμmem : ∀ k : Fin hyp.base.w2, k ≠ 0 →
      OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k)
        ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- membership repackaging for the cut
  have hmemiff : ∀ x : ClassFunction ↥M ℂ,
      x ∈ (irrCut_finite hyp hyp.H0Cprime d).toFinset ↔
      (x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter x ∧ ((x : ↥M → ℂ) 1 = (d : ℂ))) := fun x =>
    (irrCut_finite hyp hyp.H0Cprime d).mem_toFinset
  -- in-range chain indices are nonzero column indices
  have hfin : ∀ {j : ℕ} (h : j + 1 < hyp.base.w2),
      (⟨j + 1, h⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro j h heq
    have := congrArg Fin.val heq
    simp at this
  -- the cover data: base and pairs land in `𝒮(H₀C′)`
  have hS₀X : (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ⊆
      OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := fun x hx =>
    ((hmemiff x).mp (Finset.mem_coe.mp hx)).1
  have hpairsX : ∀ j, j < hyp.base.w2 - 1 →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥M) (caseBPair hG hyp) j ⊆
      OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := by
    intro j hj x hx
    have hlt : j + 1 < hyp.base.w2 := by omega
    rw [caseBPairSet_of_lt hG hyp hlt] at hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hμmem _ (hfin hlt)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime
        (hμmem _ (hfin hlt))
  -- the cover: every member is in the cut or in an enumerated pair (member dichotomy)
  have hcover : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      φ ∈ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) ∨
      ∃ j, j < hyp.base.w2 - 1 ∧
        φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥M) (caseBPair hG hyp) j := by
    intro φ hφ
    rcases caseB_sOf_member_dichotomy hG hyp d hunif hφ with hcut | ⟨k, hk0, hkeq⟩
    · exact Or.inl (Finset.mem_coe.mpr ((hmemiff φ).mpr hcut))
    · have hkval : (k : ℕ) ≠ 0 := fun h0 => hk0 (Fin.ext (by simp [h0]))
      have hklt : (k : ℕ) < hyp.base.w2 := k.isLt
      have hlt : (k : ℕ) - 1 + 1 < hyp.base.w2 := by omega
      refine Or.inr ⟨(k : ℕ) - 1, by omega, ?_⟩
      rw [caseBPairSet_of_lt hG hyp hlt]
      have hkeq' : (⟨(k : ℕ) - 1 + 1, hlt⟩ : Fin hyp.base.w2) = k := by
        apply Fin.ext
        change (k : ℕ) - 1 + 1 = (k : ℕ)
        omega
      rw [hkeq', ← hkeq]
      exact Set.mem_insert _ _
  -- fold the chain
  refine OddOrder.Peterfalvi.S07.coherentOfPairChainCover (caseBPair hG hyp)
    (hyp.base.w2 - 1) hS₀X hpairsX hcover
    (by rw [Set.Finite.coe_toFinset]
        exact sOf_degreeSubfamily_isCoherent hG hyp hyp.H0Cprime d
          ⟨χ₁, hχ₁mem, hχ₁irr, hχ₁deg⟩)
    ?_
  intro i hi hcoh
  have hlt : i + 1 < hyp.base.w2 := by omega
  by_cases hskip : OddOrder.Peterfalvi.S07.pairSet (L := ↥M) (caseBPair hG hyp) i ⊆
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
        (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i
  · -- skip: the pair was already adjoined (conjugate column enumerated earlier)
    rw [OddOrder.Peterfalvi.S07.pairUnion_succ, Set.union_eq_left.mpr hskip]
    exact hcoh
  · -- adjoin a fresh pair via `caseB_chainStep`
    -- accumulator invariants
    have hS₁sub : OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
        (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i ⊆
        OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := by
      intro x hx
      rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hb | ⟨j, hji, hj⟩
      · exact hS₀X hb
      · exact hpairsX j (by omega) hj
    have hS₁cut : (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset :
        Set (ClassFunction ↥M ℂ)) ⊆
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
          (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i :=
      OddOrder.Peterfalvi.S07.pairUnion_mono _ _ (Nat.zero_le i)
    have hS₁mu : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
        (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i,
        x ∉ (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset : Set (ClassFunction ↥M ℂ)) →
        ∃ χ₂' : ((hyp.base.toHypothesis46 hG hG.odd).W2.subgroupOf
          ((hyp.base.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.base.toHypothesis46 hG hG.odd).W2))
            →* ℂˣ,
          x = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd) χ₂' := by
      intro x hx hxcut
      rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hb | ⟨j, hji, hj⟩
      · exact absurd hb hxcut
      · have hltj : j + 1 < hyp.base.w2 := by omega
        rw [caseBPairSet_of_lt hG hyp hltj] at hj
        rcases Set.mem_insert_iff.mp hj with rfl | hj
        · exact ⟨_, rfl⟩
        · rw [Set.mem_singleton_iff] at hj
          subst hj
          exact ⟨_, OddOrder.Peterfalvi.S06.columnSum_conj_eq _ _⟩
    -- the accumulator is conjugation-closed (cut conjugate-closed; pairs are conjugate pairs)
    have hconjacc : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
        (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i,
        x.conj ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
          (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i := by
      intro x hx
      rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hb | ⟨j, hji, hj⟩
      · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (Finset.mem_coe.mpr
          ((hmemiff _).mpr (irrCut_conjClosed hyp hyp.H0Cprime d
            ((hmemiff x).mp (Finset.mem_coe.mp hb))))))
      · have hltj : j + 1 < hyp.base.w2 := by omega
        rw [caseBPairSet_of_lt hG hyp hltj] at hj
        refine OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, ?_⟩)
        rw [caseBPairSet_of_lt hG hyp hltj]
        rcases Set.mem_insert_iff.mp hj with rfl | hj
        · exact Set.mem_insert_iff.mpr (Or.inr rfl)
        · rw [Set.mem_singleton_iff] at hj
          subst hj
          rw [ClassFunction.conj_conj]
          exact Set.mem_insert _ _
    -- freshness of both components from the failed skip test (`Prop`-confined: the goal is
    -- `Type`-valued, so the `∃`-witness of `Set.not_subset` may not escape this `have`)
    have hfresh : OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd ⟨i + 1, hlt⟩) ∉
          OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
            (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i ∧
        (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd ⟨i + 1, hlt⟩)).conj ∉
          OddOrder.Peterfalvi.S07.pairUnion (L := ↥M)
            (↑(irrCut_finite hyp hyp.H0Cprime d).toFinset) (caseBPair hG hyp) i := by
      obtain ⟨y, hy, hynot⟩ := Set.not_subset.mp hskip
      rw [caseBPairSet_of_lt hG hyp hlt] at hy
      constructor
      · intro hc
        rcases Set.mem_insert_iff.mp hy with rfl | hy'
        · exact hynot hc
        · rw [Set.mem_singleton_iff] at hy'
          subst hy'
          exact hynot (hconjacc _ hc)
      · intro hc
        rcases Set.mem_insert_iff.mp hy with rfl | hy'
        · have h2 := hconjacc _ hc
          rw [ClassFunction.conj_conj] at h2
          exact hynot h2
        · rw [Set.mem_singleton_iff] at hy'
          subst hy'
          exact hynot hc
    -- fire the chain step and re-shape onto the accumulator
    have hpair0 : (caseBPair hG hyp i).1 =
        OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd ⟨i + 1, hlt⟩) := by
      rw [caseBPair_of_lt hG hyp hlt]
    have hpair1 : (caseBPair hG hyp i).2 =
        (OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd ⟨i + 1, hlt⟩)).conj := by
      rw [caseBPair_of_lt hG hyp hlt]
    rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair hpair0 hpair1]
    exact caseB_chainStep hG hyp d hunif hχ₁mem hχ₁irr hχ₁deg hDeg hS₁sub hS₁cut hS₁mu hcoh
      (hyp.base.muColumnChar_ne_one hG hG.odd (hfin hlt)) (hμmem _ (hfin hlt))
      hfresh.1 hfresh.2

end OddOrder.Peterfalvi.S13
