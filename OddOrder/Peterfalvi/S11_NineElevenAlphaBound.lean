/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_NineElevenCaseA

/-!
# Peterfalvi (9.11.5)–(9.11.6): the `α`-bound layer of the (9.11) endgame

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §9, pp. 56–57,
(9.11.5)–(9.11.8) (mmd `04.11`, lines ~150–190); Coq mirror `PFsection9.v:1952-2227`.

## What this file provides

The (9.11.6) dichotomy layer of the (9.11) case-(a) endgame (issue 9083, Phase E): the norm
bound `NineElevenNormBound` is discharged up to the single named residual
`NineElevenSevenEightRefutation` — the (9.11.7)–(9.11.8) coherent-pair construction.

* **Bessel counting** (`S07.card_le_inner_self_re_of_orthonormal_inner_int_ne`): a finite
  orthonormal family of virtual characters, each non-orthogonal to `A ∈ ℤ[Irr G]` with
  integer inner products, has cardinality at most `‖A‖²` — Coq's `cnorm_dconstt` count in
  Fourier-free form (Bessel's inequality plus `|m| ≥ 1` for a nonzero integer).

* **The `hunif`-free member `R`-dispatch** (`sOf_H0Cprime_memberRFamily` and its
  `imageSet` reductions/orthogonality): the caseB dispatch `caseB_sOf_memberRFamily`
  (irreducible member → signed Dade family; reducible member → certain-type column family)
  needs no degree hypothesis — the caseB `hunif` fed only the *discarded* irreducible branch
  of the member dichotomy.  Replicated here without it, so it applies to the mixed-degree
  equality configuration.

* **`τ₃`: the `𝒮₃`-coherence** (`caseA_sThree_coherent`): book *"For `i = 1` and `i = 3`,
  let `τᵢ` be an extension of `τ` to `ℤ[𝒮ᵢ]`; that such extensions exist can be seen from
  (5.7)"* — `𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂` has uniform degree `qu` (the (9.11.1) squeeze output), so
  the norm-general (5.7) engine `uniform_degree_coherence_of_families` applies with the
  dispatched `R`-families.

* **The (9.11.6) dichotomy and the norm-bound reduction**
  (`nineElevenNormBound_of_sevenEightRefutation`): the common value
  `⟨α^τ, λ^{τ₃}⟩` (constant across `λ ∈ 𝒮₃` — `τ₃` agrees with `τ` on the `A₀`-supported
  equal-degree differences, the Dade isometry moves the pairing to `⟨α, λ − λ′⟩ = 0`) is
  either **nonzero** — then every `𝒮₄`-member's `τ₃`-image is a distinct unit constituent of
  `α^τ` and `|𝒮₄| ≤ ‖α^τ‖² = ‖α‖² = N` (the Bessel count), discharging
  `NineElevenNormBound` — or **zero**, i.e. `α^τ ⊥ 𝒮₃^{τ₃}` (book (9.11.6)), which is the
  opening position of the (9.11.7)–(9.11.8) construction, isolated as the named residual
  `NineElevenSevenEightRefutation`.

Reference note: `issues/closed/9083-lane-a-1007-decomp-moot-revised-frontier.md` (Phase E).
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S11
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]


/-! ### The `hunif`-free member `R`-dispatch over `𝒮(H₀C′)`

`caseB_sOf_memberRFamily` (S13_MaximalIII_IV) dispatches per-member (5.2.d) `R`-data —
signed Dade family for irreducibles, `certainTypeR` for the reducible certain-type columns —
but carries a whole-family uniform-degree hypothesis `hunif` that feeds only the *discarded*
irreducible branch of `caseB_sOf_member_dichotomy`.  The equality configuration of (9.11) is
mixed-degree (`qa` on `𝒮₂`, `qu` on `𝒮₃`), so the dispatch is replicated here without
`hunif` (the reducible branch uses `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`
directly). -/

section MemberRFamily

variable [Finite G]

/-- **Reducible `𝒮(H₀C′)`-members are certain-type column sums** (the `hunif`-free member
dichotomy, reducible half): a reducible member equals `μ_k = columnSum (muColumnChar k)`
for some `k ≠ 0` (`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` + the world-join
`muGrid_columnSum_eq_columnSum`). -/
theorem sOf_H0Cprime_reducible_eq_columnSum
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hirr : ¬ IsIrreducibleCharacter η) :
    ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := by
  haveI := hyp.base.finiteG
  classical
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hη
    rwa [hyp.SOf_eq] at h
  obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
    hηIKF hirr
  exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

/-- **Per-member orthonormal `R`-family over `𝒮(H₀C′)`, `hunif`-free** (mirror of
`caseB_sOf_memberRFamily` without the whole-family degree hypothesis): irreducible member →
2-element signed Dade family; reducible member → `2q`-element certain-type family
`certainTypeR` at the column of `sOf_H0Cprime_reducible_eq_columnSum`. -/
noncomputable def sOf_H0Cprime_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
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
  · -- column: rebuild `certainTypeR` at the abstract member `η`
    have hex := sOf_H0Cprime_reducible_eq_columnSum hG hyp hη hirr
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

/-- **`sOf_H0Cprime_memberRFamily` reduction, irreducible case** (mirror of
`caseB_sOf_memberRFamily_imageSet_of_irr`). -/
theorem sOf_H0Cprime_memberRFamily_imageSet_of_irr
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA0 M hyp.base.typeP) M),
      (sOf_H0Cprime_memberRFamily hG hyp hη).imageSet =
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
  unfold sOf_H0Cprime_memberRFamily
  rw [dif_pos hirr]

/-- **`sOf_H0Cprime_memberRFamily` reduction, column case** (mirror of
`caseB_sOf_memberRFamily_imageSet_of_col`). -/
theorem sOf_H0Cprime_memberRFamily_imageSet_of_col
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (sOf_H0Cprime_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  haveI := hyp.base.finiteG
  have hex := sOf_H0Cprime_reducible_eq_columnSum hG hyp hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold sOf_H0Cprime_memberRFamily
  rw [dif_neg hcol]

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against the
-- (5.2.e) lemmas through the `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in the caseB
-- original `caseB_sOf_memberRFamily_orthogonal`)
/-- **(5.2.e) cross-orthogonality of the `hunif`-free dispatched `R`-families** (mirror of
`caseB_sOf_memberRFamily_orthogonal`): for members `φ, ξ` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the
dispatched families are orthogonal — the same `2×2` case split (irr/column). -/
theorem sOf_H0Cprime_memberRFamily_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hξ : ξ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (sOf_H0Cprime_memberRFamily hG hyp hφ).Orthogonal
      (sOf_H0Cprime_memberRFamily hG hyp hξ) := by
  haveI := hyp.base.finiteG
  classical
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
    obtain ⟨hrφ, hsφ, hφeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact dadeOfDiff_orthogonal_dadeOfDiff_typeP hG hyp.base ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨φ, hφirr⟩ hrφ (hIrrPA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrPA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ := sOf_H0Cprime_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46
    have hne1 : hyp.base.muColumnChar hG hG.odd kφ ≠ hyp.base.muColumnChar hG hG.odd kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    have hne2 : hyp.base.muColumnChar hG hG.odd kφ
        ≠ (hyp.base.muColumnChar hG hG.odd kξ)⁻¹ := by
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

end MemberRFamily

/-! ### The stratum-generic member `R`-dispatch over `S(N)` (issue 1023)

The `MemberRFamily` section above dispatches per-member (5.2.d) `R`-data over the fixed
stratum `𝒮(H₀C′)`.  The (11.8.6) `hmixed` cross-orthogonality (the Coq `coherent_ortho`,
`PFsection5.v:986`) needs the same dispatch across **two different strata** —
`𝒮(H₀C) × S(HC)` — so this section replays it at the `SOf`-level: any member of any
kernel-filter family `S(N) = hyp.SOf N` (`N : Subgroup G`) carries the same orthonormal
`R`-family, and members of two strata with orthogonal character pairs have orthogonal
families.  (The `H₀C′` versions above are the `T ⊆ 𝒮(H₀C′) ⊆ S(H₀C′)` instances; folding
them onto these is a follow-up, issue 1023.) -/

section SOfMemberRFamily

variable [Finite G]

/-- **Reducible `S(N)`-members are certain-type column sums** (stratum-generic
`sOf_H0Cprime_reducible_eq_columnSum`): a reducible member of any kernel-filter family
`S(N)` equals `μ_k = columnSum (muColumnChar k)` for some `k ≠ 0`
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` is already stratum-generic). -/
theorem SOf_reducible_eq_columnSum
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hirr : ¬ IsIrreducibleCharacter η) :
    ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := by
  haveI := hyp.base.finiteG
  classical
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (N.subgroupOf M) := by
    rwa [hyp.SOf_eq] at hη
  obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
    hηIKF hirr
  exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

/-- **Per-member orthonormal `R`-family over `S(N)`** (stratum-generic
`sOf_H0Cprime_memberRFamily`): irreducible member → 2-element signed Dade family; reducible
member → `2q`-element certain-type family `certainTypeR` at the column of
`SOf_reducible_eq_columnSum`. -/
noncomputable def SOf_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hη
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
  · -- column: rebuild `certainTypeR` at the abstract member `η`
    have hex := SOf_reducible_eq_columnSum hG hyp hη hirr
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

/-- **`SOf_memberRFamily` reduction, irreducible case**. -/
theorem SOf_memberRFamily_imageSet_of_irr
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA0 M hyp.base.typeP) M),
      (SOf_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.base.dadeData.dade hyp.base.hconj ⟨η, hirr⟩ hr hs).imageSet := by
  haveI := hyp.base.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hη)
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0, ?_⟩
  unfold SOf_memberRFamily
  rw [dif_pos hirr]

/-- **`SOf_memberRFamily` reduction, column case**. -/
theorem SOf_memberRFamily_imageSet_of_col
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (SOf_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  haveI := hyp.base.finiteG
  have hex := SOf_reducible_eq_columnSum hG hyp hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold SOf_memberRFamily
  rw [dif_neg hcol]

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against the
-- (5.2.e) lemmas through the `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in the
-- `H₀C′` original `sOf_H0Cprime_memberRFamily_orthogonal`)
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families, two strata** (stratum-generic
`sOf_H0Cprime_memberRFamily_orthogonal`): for members `φ ∈ S(N₁)`, `ξ ∈ S(N₂)` with
`⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the dispatched families are orthogonal — the same `2×2` case split
(irr/column).  This is the `R`-family half of the Coq `coherent_ortho` (issue 1023). -/
theorem SOf_memberRFamily_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N₁ N₂ : Subgroup G} {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ hyp.SOf N₁) (hξ : ξ ∈ hyp.SOf N₂)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (SOf_memberRFamily hG hyp hφ).Orthogonal
      (SOf_memberRFamily hG hyp hξ) := by
  haveI := hyp.base.finiteG
  classical
  -- typePA support for an irreducible member (needed by the μ×irr cross-orthogonality)
  have hIrrPA : ∀ {ζ : ClassFunction ↥M ℂ} {Nz : Subgroup G},
      ζ ∈ hyp.SOf Nz →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.base.typeP) M) := by
    intro ζ Nz hζ
    have hζIKF0 : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hζ)
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
    obtain ⟨hrφ, hsφ, hφeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact dadeOfDiff_orthogonal_dadeOfDiff_typeP hG hyp.base ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨φ, hφirr⟩ hrφ (hIrrPA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrPA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46
    have hne1 : hyp.base.muColumnChar hG hG.odd kφ ≠ hyp.base.muColumnChar hG hG.odd kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    have hne2 : hyp.base.muColumnChar hG hG.odd kφ
        ≠ (hyp.base.muColumnChar hG hG.odd kξ)⁻¹ := by
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

end SOfMemberRFamily

/-! ### `τ₃`: coherence of `𝒮₃` (Peterfalvi (5.7) at the uniform degree `qu`) -/

section SThreeCoherent

variable [Finite G]

/-- **Equal-degree member differences are `A₀`-supported** — the `hsuppdiff` supply for the
`𝒮₃`-side (5.7) engine and the (9.11.6) constancy: two `𝒮(H₀C′)`-members of equal degree
have `A₀`-supported difference (`inducedKernelFamily_scaledDiff_support` at ratio `1`). -/
theorem sOf_equal_degree_diff_support {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hy : y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hdeg : (x : ↥M → ℂ) 1 = (y : ↥M → ℂ) 1) :
    ((x - y : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ z ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      z ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun z hz => by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hz
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
    hyp.base.mderivSharp_subset_A0 (hIKF x hx) (hIKF y hy) (d := 1)
    (by rw [Nat.cast_one, one_mul]; exact hdeg)
  rwa [one_smul] at h

set_option maxHeartbeats 1600000 in
-- the norm-general engine threads the dispatched `R`-families and the `hZdiff`/`hiso` inputs
-- through the `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in the caseB assembly)
/-- **`τ₃` exists: `𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂` is coherent on `A₀`** (Peterfalvi's *"let `τ₃` be an
extension of `τ` to `ℤ[𝒮₃]`; that such extensions exist can be seen from (5.7)"*, p. 57).
In the equality configuration every `𝒮₃`-member has degree `qu` (`hS3deg`), so the
norm-general (5.7) engine `uniform_degree_coherence_of_families` fires with the
`hunif`-free dispatched `R`-families; the pivot is any `𝒮₃`-member (`hS₃ne`), its partner
its conjugate (`𝒮₃` is conjugation-closed since `𝒮(H₀C′)` and `𝒮₂` are). -/
theorem caseA_sThree_coherent
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  -- `𝒮₃` is conjugation-closed
  have hconj : ∀ a ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      a.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := by
    intro a ha
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime ha.1, ?_⟩
    intro hc
    have h := hS₂conj hc
    rw [ClassFunction.conj_conj] at h
    exact ha.2 h
  -- no member is real
  have hnr : ∀ a ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      a ≠ a.conj := fun a ha h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF ha.1) h.symm
  -- equal-degree differences are `A₀`-supported
  have hsuppdiff : ∀ a ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ∀ b ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ((a - b : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := fun a ha b hb =>
    sOf_equal_degree_diff_support hyp ha.1 hb.1 ((hS3deg a ha).trans (hS3deg b hb).symm)
  -- natural-number self-norm of the pivot (`ℤ[Irr]` sum-of-squares)
  have hN : ∃ n : ℕ, ClassFunction.inner χ₀ χ₀ = (n : ℂ) := by
    obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hχ₀.1))
    have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨(∑ x ∈ c.support, (c x) ^ 2).toNat, ?_⟩
    rw [hcsum]
    exact_mod_cast (congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)).symm
  exact OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    (((OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)).subset
      Set.sdiff_subset)
    hχ₀
    (fun η hη => sOf_H0Cprime_memberRFamily hG hyp hη.1)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF ha.1) (hIKF hb.1) hab)
    hconj
    hnr
    hN
    (fun {φ ψ} hφ hψ =>
      hyp.base.tau_inner_eq_of_supported
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ))
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.base.dadeData.dade hyp.base.hconj (hsuppdiff a ha b hb)
        (Submodule.sub_mem _
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF ha.1))
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hb.1))))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      sOf_H0Cprime_memberRFamily_orthogonal hG hyp hφ.1 hξ.1 h1 h2)
    (fun a ha => (hS3deg a ha).trans (hS3deg χ₀ hχ₀).symm)
    (by
      rw [hS3deg χ₀ hχ₀]
      exact Nat.cast_ne_zero.mpr
        (mul_ne_zero (hyp.s11Setup.nontrivial.2.1.pos.ne')
          (OddOrder.Peterfalvi.S11.u_odd hG
            (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos.ne'))
    hyp.base.one_notMem_A0
    (hconj χ₀ hχ₀)
    (fun h => hnr χ₀ hχ₀ h.symm)

end SThreeCoherent

end OddOrder.Peterfalvi.S13
