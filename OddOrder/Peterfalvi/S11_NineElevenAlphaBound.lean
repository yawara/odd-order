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

* **Bessel counting** (`card_le_inner_self_re_of_orthonormal_inner_int_ne`): a finite
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

/-! ### The Bessel count `|T| ≤ ‖A‖²` -/

section BesselCount

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

/-- **Bessel's inequality, integer-constituent count**: if `(θ i)_{i ∈ T}` is a finite
orthonormal family and every `⟨A, θ i⟩` is a *nonzero integer*, then `|T| ≤ ‖A‖²`.
Pythagoras against `S = ∑ᵢ ⟨A, θᵢ⟩ • θᵢ`: `0 ≤ ‖A − S‖² = ‖A‖² − ∑ᵢ ‖⟨A, θᵢ⟩‖²`, and each
`‖⟨A, θᵢ⟩‖² = mᵢ² ≥ 1`.  Coq `PFsection9.v:2036-2047` (the `cnorm_dconstt` count) in
Fourier-free form. -/
theorem card_le_inner_self_re_of_orthonormal_inner_int_ne {ι : Type*}
    (A : ClassFunction Γ ℂ) (T : Finset ι)
    (θ : ι → ClassFunction Γ ℂ)
    (hON1 : ∀ i ∈ T, ClassFunction.inner (θ i) (θ i) = 1)
    (hON2 : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ClassFunction.inner (θ i) (θ j) = 0)
    (hint : ∀ i ∈ T, ∃ m : ℤ, ClassFunction.inner A (θ i) = (m : ℂ))
    (hne : ∀ i ∈ T, ClassFunction.inner A (θ i) ≠ 0) :
    (T.card : ℝ) ≤ (ClassFunction.inner A A).re := by
  classical
  set c : ι → ℂ := fun i => ClassFunction.inner A (θ i) with hc
  set S : ClassFunction Γ ℂ := ∑ i ∈ T, c i • θ i with hS
  -- sum expansions of the sesquilinear inner product
  have hsum_left : ∀ (s : Finset ι) (ψ : ClassFunction Γ ℂ),
      ClassFunction.inner (∑ i ∈ s, c i • θ i) ψ
        = ∑ i ∈ s, c i * ClassFunction.inner (θ i) ψ := by
    intro s ψ
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.inner_add_left,
          ClassFunction.inner_smul_left, ih]
  have hsum_right : ∀ (s : Finset ι) (ψ : ClassFunction Γ ℂ),
      ClassFunction.inner ψ (∑ i ∈ s, c i • θ i)
        = ∑ i ∈ s, star (c i) * ClassFunction.inner ψ (θ i) := by
    intro s ψ
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.inner_add_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  -- the three cross terms all equal `∑ᵢ cᵢ·conj cᵢ`
  have hSA : ClassFunction.inner S A = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_left T A]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ClassFunction.inner (θ i) A = star (c i) from
      OddOrder.RepresentationTheory.inner_conj_symm A (θ i)]
  have hAS : ClassFunction.inner A S = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_right T A]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci : ClassFunction.inner A (θ i) = c i := rfl
    rw [hci, mul_comm]
  have hθS : ∀ i ∈ T, ClassFunction.inner (θ i) S = star (c i) := by
    intro i hi
    rw [hS, hsum_right T (θ i)]
    rw [Finset.sum_eq_single i
      (fun j hj hji => by rw [hON2 i hi j hj (fun h => hji h.symm), mul_zero])
      (fun hnotin => absurd hi hnotin)]
    rw [hON1 i hi, mul_one]
  have hSS : ClassFunction.inner S S = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_left T S]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show ClassFunction.inner (θ i) (∑ i ∈ T, c i • θ i) = star (c i) from by
      rw [← hS]; exact hθS i hi]
  -- Pythagoras: `0 ≤ ‖A − S‖² = ‖A‖² − ∑ᵢ ‖cᵢ‖²`
  have hkey : ClassFunction.inner (A - S) (A - S)
      = ClassFunction.inner A A - ∑ i ∈ T, c i * star (c i) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hSA, hAS, hSS]
    ring
  have hnorm : (∑ i ∈ T, c i * star (c i))
      = ((∑ i ∈ T, Complex.normSq (c i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.mul_conj (c i)
  have h0 := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - S)
  rw [hkey, hnorm, Complex.sub_re, Complex.ofReal_re] at h0
  -- each `‖cᵢ‖² = mᵢ² ≥ 1`
  have hone : ∀ i ∈ T, (1 : ℝ) ≤ Complex.normSq (c i) := by
    intro i hi
    obtain ⟨m, hm⟩ := hint i hi
    have hmne : m ≠ 0 := by
      intro h0'
      apply hne i hi
      rw [hm, h0', Int.cast_zero]
    have hm1 : (1 : ℤ) ≤ m * m := by
      rcases lt_or_gt_of_ne hmne with h | h
      · nlinarith
      · nlinarith
    have hm' : c i = ((m : ℝ) : ℂ) := by
      have h : ClassFunction.inner A (θ i) = ((m : ℝ) : ℂ) := by
        rw [hm]
        push_cast
        ring
      exact h
    rw [hm', Complex.normSq_ofReal]
    exact_mod_cast hm1
  calc (T.card : ℝ) = ∑ _i ∈ T, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ T, Complex.normSq (c i) := Finset.sum_le_sum hone
    _ ≤ (ClassFunction.inner A A).re := by linarith

end BesselCount

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
    refine ⟨Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime ha.1, ?_⟩
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

/-! ### The (9.11.6) dichotomy: the norm bound, reduced to the (9.11.7)–(9.11.8) residual -/

section NormBoundReduction

variable [Finite G]

/-- **Peterfalvi (9.11.7)–(9.11.8), the orthogonal-branch refutation** (hypothesis shape,
issue 9083 Phase E residual).  Book: **(9.11.7)** for `λ₁ ∈ 𝒮₄` and `β = λ₁ − (u/a)ψ₁`,
`β^τ = Γ − (u/a)ψ₁^{τ₁} + b∑_{ψ∈𝒮₁}ψ^{τ₁}` with `Γ ∈ ℤ[𝒮₄^{τ₃}]`, `‖Γ‖² = 1`, `b ∈ {0,1}`;
**(9.11.8)** pairing with `⟨α^τ, β^τ⟩ = ⟨α, β⟩ = u/a` and `α^τ ⊥ Γ` forces `b ≡ 0 (mod u/a)`,
so `b = 0` (`u ≠ a`), and `β^τ = Γ − (u/a)τ₁ψ₁` lets the pair `{λ₁, λ̄₁}` be coherently
adjoined to `𝒮₂ = 𝒮₁` (Coq `extend_coherent_with`, `PFsection9.v:2174-2227`) —
contradicting the pair clause `hpairs`.

The `Prop` takes the full equality configuration, the `τ₃`-coherence `c₃`
(`caseA_sThree_coherent`), and the (9.11.4)/(9.11.6) `α = γ − ψ₁` context: `ψ₁ ∈ 𝒮₂`
irreducible of degree `qa`; `γ ∈ ℤ[Irr M]` of degree `qa` orthogonal to every
`𝒮(H₀C′)`-member (`H ⊆ Ker γ`); `Supp(α) ⊆ A₀`; and the (9.11.6) branch hypothesis
`α^τ ⊥ 𝒮₃^{τ₃}`.  (The Mackey norm `‖α‖²·u = (a+1)u + (q−1)a²` and `𝒮₄ ≠ ∅` are
re-derivable inside from the configuration antecedents — Phase C/D bundles.) -/
def NineElevenSevenEightRefutation {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ |
        φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau S₂ hyp.base.A0) →
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂).Nonempty →
      (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
          (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) →
      2 * caseA.a = hyp.chief.p - 1 →
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime →
      (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)) →
      {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
          (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
          IsIrreducibleCharacter χ ∧
          χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (hyp.chief.p - 1)
          * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ)) →
      (∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) →
      ∀ c₃ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂) hyp.base.A0,
      ∀ γ ψ₁ : ClassFunction ↥M ℂ,
        ψ₁ ∈ S₂ →
        IsIrreducibleCharacter ψ₁ →
        ((ψ₁ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) →
        γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M →
        ((γ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) →
        (∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
          ClassFunction.inner γ φ = 0) →
        ((γ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 →
        (∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
          ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam) = 0) →
        False

set_option maxHeartbeats 1600000 in
-- the α-context replication threads the `hyp.base.tau = dadeIntegralCharacterMap` defeq
-- (same cost profile as the Phase-D bundle `caseA_nineElevenFour_norm_inputs`)
/-- **Peterfalvi (9.11.4)–(9.11.8): the norm bound, discharged up to the (9.11.7)–(9.11.8)
residual** (issue 9083 Phase E, the (9.11.6) dichotomy).

The (9.11.4) `α = γ − ψ₁` context is rebuilt as in the Phase-D bundle (with `γ`, `ψ₁` kept
explicit); `τ₃` is `caseA_sThree_coherent`.  The value `⟨α^τ, λ^{τ₃}⟩` is **constant** over
`λ ∈ 𝒮₃`: `τ₃` agrees with `τ` on the `A₀`-supported equal-degree differences `λ − λ′`
(`extends_on_supported`), the Dade isometry gives `⟨α^τ, τ(λ−λ′)⟩ = ⟨α, λ−λ′⟩`, and
`⟨α, λ⟩ = ⟨γ, λ⟩ − ⟨ψ₁, λ⟩ = 0` (`H ⊆ Ker γ` via `nineElevenGamma_inner_induceHU`;
`ψ₁ ∈ 𝒮₂` vs `λ ∉ 𝒮₂` pairwise-orthogonal).  If the constant is **nonzero**, every
`𝒮₄`-member's `τ₃`-image is a unit constituent of `α^τ` (orthonormal by the `τ₃`-isometry,
integer pairings by `inner_mem_ZIrr_int`), so the Bessel count gives
`|𝒮₄| ≤ ‖α^τ‖² = ‖α‖² = N` — the `NineElevenNormBound` conclusion.  If **zero** — the book's
(9.11.6) `α^τ ⊥ 𝒮₃^{τ₃}` — the named residual `h78` refutes. -/
theorem nineElevenNormBound_of_sevenEightRefutation
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (h78 : NineElevenSevenEightRefutation hyp caseA)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp)
    (htype : IsTypeIII M ∨ IsTypeIV M := hyp.base.isTypeIIIorIV hG) :
    NineElevenNormBound hyp caseA := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
  -- ── `τ₃` (Peterfalvi (5.7) at the uniform degree `qu`)
  obtain ⟨c₃⟩ := caseA_sThree_coherent hG hyp hS₂conj hS₃ne hS3deg
  -- ── the (9.11.2) TI-witness and the (9.11.4) `α = γ − ψ₁` context (`γ`, `ψ₁` explicit)
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, hTI⟩ :=
    caseA_nineElevenTwo_tiWitness hG hyp caseA hS3deg hS2deg hncH0C htype
  have hUpC : OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
      = OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    have h : OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief
        = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := hCUprime
    exact h.symm
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup ≤ U₁ := by
    rw [hUpC]; exact hCU₁
  -- `ψ₁`: the (9.8.d)-positive degree-`qa` family is nonempty
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U
      ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧
      χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < hyp.chief.p := hyp.chief.p_prime.one_lt
    have h1 := Nat.pos_of_ne_zero hrelne
    have h2 : 0 < (hyp.chief.p - 1)
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) :=
      Nat.mul_pos (by omega) h1
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  -- `ψ₁ ∈ 𝒮₂` (`𝒮(H₀U′) ⊆ 𝒮(H₀C′)` and `hS₁sub`)
  have hCU : hyp.C ≤ hyp.s11Setup.U := by
    change hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
    rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
      OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
    exact Subgroup.commutator_mono hCU hCU
  have hψ₁sOfC' : ψ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
    OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hψ₁sOf
  have hψ₁S₂ : ψ₁ ∈ S₂ := hS₁sub ⟨hψ₁sOfC', hψ₁irr, hψ₁deg⟩
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hindEqζ : OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
      = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := rfl
  -- `γ = Ind_{HU₁}^M 1` and its landed (9.11.4) facts (as in the Phase-D bundle)
  set K : Subgroup ↥M := hyp.s11Setup.H.subgroupOf M ⊔ U₁.subgroupOf M with hKdef
  set γ : ClassFunction ↥M ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγsupp : γ.support ⊆ (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup : Set ↥M) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_support hyp.s11Setup hU₁U
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_mem_ZIrr hyp.s11Setup U₁
  have hγ1 : γ (1 : ↥M) = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_apply_one hyp.s11Setup hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ
        * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ)
      = ((caseA.a * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
          + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_inner_self_mul_u
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) hU₁U hUpU₁ hU₁a hTI
  -- `γ ⊥` every `𝒮(H₀C′)`-member (`H ⊆ Ker γ` at the source, `H ⊄ Ker ζ` on `𝒳`)
  have hγorth : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      ClassFunction.inner γ φ = 0 := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    have hξxi : ξ ∈ OddOrder.Peterfalvi.S11.xiSet hyp.s11Setup :=
      OddOrder.Peterfalvi.S11.xiOf_subset_xiSet hyp.s11Setup _ hξ
    have hindEqξ : OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
        = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
          (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := rfl
    rw [hindEqξ]
    exact OddOrder.Peterfalvi.S11.nineElevenGamma_inner_induceHU hyp.s11Setup hU₁U hξxi
  -- `α = γ − ψ₁`: norm split, integrality, `‖α‖² = N`, the cleared identity, support
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := hγorth ψ₁ hψ₁sOfC'
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    OddOrder.Peterfalvi.S11.cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact OddOrder.Peterfalvi.S11.induceHU_mem_ZIrr hyp.s11Setup ζ
  obtain ⟨c, -, -, hcsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]
    push_cast
    rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  have hNu : N * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
      = (caseA.a + 1) * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
        + (hyp.s11Setup.q - 1) * caseA.a ^ 2 := by
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ)
        = ((caseA.a * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
            + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)
        = (((caseA.a + 1)
              * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
            + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  have hαsupp : ((γ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    intro x hx
    have hxmem : x ∈ γ.support ∪ ψ₁.support :=
      ClassFunction.support_sub_subset γ ψ₁ hx
    have hxHU : x ∈ OddOrder.Peterfalvi.S11.huSub hyp.s11Setup := by
      rcases hxmem with h | h
      · exact hγsupp h
      · have hψsupp : ψ₁.support
            ⊆ (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup : Set ↥M) := by
          rw [hψ₁eq, hindEqζ]
          exact ClassFunction.support_induce_subset_of_normal _ _
        exact hψsupp h
    have hx1 : x ≠ 1 := by
      intro h1
      rw [ClassFunction.mem_support, h1] at hx
      apply hx
      rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self]
    have hxM' : x ∈ (derivedInG M).subgroupOf M := by
      rwa [← OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf]
    exact hyp.base.mderivSharp_subset_A0 x hxM' hx1
  -- `α^τ ∈ ℤ[Irr G]`, norm preservation
  have hταZIrr : hyp.base.tau (γ - ψ₁) ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hαsupp hαZIrr
  have hταnorm : ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (hyp.base.tau (γ - ψ₁))
      = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) :=
    hyp.base.tau_inner_eq_of_supported hαsupp hαsupp
  -- ── `α ⊥ 𝒮₃` at the source (`γ ⊥` all members; `ψ₁ ∈ 𝒮₂` vs `λ ∉ 𝒮₂` orthogonal)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hαorthS₃ : ∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ClassFunction.inner (γ - ψ₁) lam = 0 := by
    intro lam hlam
    have hψlam : ClassFunction.inner ψ₁ lam = 0 :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hψ₁sOfC') (hIKF hlam.1) (fun h => hlam.2 (h ▸ hψ₁S₂))
    rw [ClassFunction.inner_sub_left, hγorth lam hlam.1, hψlam, sub_zero]
  -- ── the (9.11.6) constancy of `⟨α^τ, λ^{τ₃}⟩` over `λ ∈ 𝒮₃`
  have hconst : ∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ∀ lam' ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam)
        = ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam') := by
    intro lam hlam lam' hlam'
    have hdiffsupp : ((lam - lam' : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
      sOf_equal_degree_diff_support hyp hlam.1 hlam'.1
        ((hS3deg lam hlam).trans (hS3deg lam' hlam').symm)
    have hzss : (lam - lam' : ClassFunction ↥M ℂ)
        ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
          (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂) hyp.base.A0 :=
      OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hlam) (Submodule.subset_span hlam'),
          hdiffsupp⟩
    have hagree : c₃.extension (lam - lam') = hyp.base.tau (lam - lam') :=
      c₃.extends_on_supported _ hzss
    have hiso : ClassFunction.inner (hyp.base.tau (γ - ψ₁))
          (hyp.base.tau (lam - lam'))
        = ClassFunction.inner (γ - ψ₁) (lam - lam') :=
      hyp.base.tau_inner_eq_of_supported hαsupp hdiffsupp
    have hz : ClassFunction.inner (γ - ψ₁) (lam - lam') = 0 := by
      rw [ClassFunction.inner_sub_right, hαorthS₃ lam hlam, hαorthS₃ lam' hlam', sub_zero]
    have hsub : ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam)
        - ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam') = 0 := by
      rw [← ClassFunction.inner_sub_right, ← map_sub, hagree, hiso, hz]
    exact sub_eq_zero.mp hsub
  -- ── the (9.11.6) dichotomy
  by_cases hc : ∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension lam) = 0
  · -- orthogonal branch — the (9.11.7)–(9.11.8) residual refutes
    exact (h78 S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg
      hcount hFbound hS2deg c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc).elim
  · -- non-orthogonal branch — the Bessel count `|𝒮₄| ≤ ‖α‖² = N`
    push Not at hc
    obtain ⟨lam₀, hlam₀, hlam₀ne⟩ := hc
    -- `𝒮₄ ⊆ 𝒮₃` along `H₀C′ ≤ H₀C`
    have hleC : hyp.H0Cprime
        ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
      change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
      refine sup_le_sup_left ?_ hyp.chief.H0
      rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
      exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
    have hS4sub : nineElevenSFour hyp S₂
        ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := fun ξ hξ =>
      ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleC hξ.1, hξ.2.2⟩
    have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
          (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
        (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
    have hS4fin : (nineElevenSFour hyp S₂).Finite :=
      hSfin.subset (fun ξ hξ => (hS4sub hξ).1)
    refine ⟨N, hNu, ?_⟩
    -- Bessel inputs at `T = 𝒮₄`, `θ = τ₃`-image
    have hON1 : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ) = 1 := by
      intro ξ hξT
      have hξ := hS4fin.mem_toFinset.mp hξT
      have hξ3 := hS4sub hξ
      rw [c₃.extension_inner_eq ξ ξ (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ3)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨ξ, hξ.2.1⟩ : IrreducibleCharacter ↥M) ⟨ξ, hξ.2.1⟩
      rwa [if_pos rfl] at h
    have hON2 : ∀ ξ ∈ hS4fin.toFinset, ∀ ξ' ∈ hS4fin.toFinset, ξ ≠ ξ' →
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ') = 0 := by
      intro ξ hξT ξ' hξ'T hne
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      have hξ'3 := hS4sub (hS4fin.mem_toFinset.mp hξ'T)
      rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ'3)]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hξ3.1) (hIKF hξ'3.1) hne
    have hint : ∀ ξ ∈ hS4fin.toFinset, ∃ m : ℤ,
        ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension ξ) = (m : ℂ) := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      exact ClassFunction.inner_mem_ZIrr_int hταZIrr
        (c₃.extension_mem_ZIrr ξ (Submodule.subset_span hξ3))
    have hnec : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₃.extension ξ) ≠ 0 := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      rw [hconst ξ hξ3 lam₀ hlam₀]
      exact hlam₀ne
    have hcount4 := card_le_inner_self_re_of_orthonormal_inner_int_ne
      (hyp.base.tau (γ - ψ₁)) hS4fin.toFinset (fun ξ => c₃.extension ξ)
      hON1 hON2 hint hnec
    have hNre : (ClassFunction.inner (hyp.base.tau (γ - ψ₁))
        (hyp.base.tau (γ - ψ₁))).re = (N : ℝ) := by
      rw [hταnorm, ← hNval, Complex.natCast_re]
    rw [hNre] at hcount4
    have hcard : ((nineElevenSFour hyp S₂).ncard : ℝ) ≤ (N : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hS4fin]
      exact hcount4
    exact_mod_cast hcard

end NormBoundReduction

/-! ### Wiring: the equality refutation, reduced to the single (9.11.7)–(9.11.8) residual -/

/-- **Peterfalvi (9.11.1)–(9.11.6), assembled**: with Phases B/C/D and the Phase-E items
landed (the `𝒮₂ = 𝒮₁` extraction, the TI-witness, the (9.11.6) dichotomy), the
equality-configuration refutation reduces to the **single** named residual
`NineElevenSevenEightRefutation` — the (9.11.7)–(9.11.8) coherent-pair construction. -/
theorem nineElevenEqualityRefutation_of_sevenEightRefutation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (h78 : NineElevenSevenEightRefutation hyp caseA)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := S_H0C_not_coherent hG hyp)
    (htype : IsTypeIII M ∨ IsTypeIV M := hyp.base.isTypeIIIorIV hG) :
    NineElevenEqualityRefutation hyp caseA :=
  nineElevenEqualityRefutation_of_sTwoExtraction_normBound hG hyp caseA
    (nineElevenSTwoExtraction hG hyp caseA)
    (nineElevenNormBound_of_sevenEightRefutation hG hyp caseA h78 hncH0C htype) hncH0C htype

end OddOrder.Peterfalvi.S13
