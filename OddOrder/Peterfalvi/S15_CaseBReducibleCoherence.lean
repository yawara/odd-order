import OddOrder.Peterfalvi.S15_BridgeCharacter

/-!
# Peterfalvi §9/§13 — the reducible caseB `R`-family for the honest `S`-instance §9 family

The Galois-case (caseB) coherence of the honest §9 family `𝒮 = sSet` needs, for every member, its
Peterfalvi (5.2.d) orthonormal Dade `R`-family.  For an *irreducible* member the (5.2.d) datum is the
two-element signed Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`.  For a **reducible**
member `η = μ_j = ∑ᵢ μ_{ij}` (a nonzero μ-column sum), the M-side (`caseB_sOf_memberRFamily`,
`S13_MaximalIII_IV`) uses the §6 `certainTypeR` — available because the M-side abstract `μ`-grid
grounds to the §6 residue grid.  The honest **`S`-instance** abstract `μ` (from `certainTypeS`) is
*not* so grounded, so this file builds the reducible `R`-family by **route B**: the honest all-rows
prime-`TI` Dade cross-relation `tauS_mu_cross` (`S15_BridgeCharacter`, itself from
`S16.eta_diff_rigidity`), summed over the μ-column.

Concretely, for a reducible `η ∈ 𝒮` the (9.11) reverse dichotomy `mu_reducible_dichotomy` gives
`η = ∑ᵢ μ_{ij}` (`j ≠ 0`); its conjugate `η̄ = ∑ᵢ μ_{ik}` (`k ≠ 0`, `j ≠ k` from non-realness); and
the honest Dade image is
`τ_S(η − η̄) = ∑ᵢ τ_S(μ_{ij} − μ_{ik}) = ∑ᵢ(η_{ij} − η_{ik})` (`tauS_mu_cross`, after
reconciling the honest `'A`-Dade `τ_S` with the `'A0`-Dade on the `A(S)`-supported column
difference).  The `2q`-element orthonormal family `R(η) = {η_{ij}} ∪ {−η_{ik}}` (orthonormal by
`eta_orthonormal`, in `ℤ[Irr G]` by `eta_mem_ZIrr`) then packages this as an
`OrthonormalCharacterImageFamily`.

This is the `S`-instance §9 route-B analogue of the M-instance `caseB_sOf_memberRFamily`.  It lives
**downstream of `S16_GridExpansion`** (unlike the M-side `certainTypeR` route, which lives upstream) —
the honest reason the caseB coherence assembly (`sSet_coherent_dade_caseB` … `coherent_H0Cprime_S`)
is relocated here from `S15_SAndT_Setup.HypothesisBasics`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Reducible `𝒮`-members are nonzero μ-column sums** (Peterfalvi (9.8)/(9.11) reverse dichotomy,
`S`-instance).  A reducible member `η ∈ 𝒮 = sSet` bridges into the general kernel-filter family
`S(⊥) = inducedKernelFamily ((derivedInG S).subgroupOf S) ⊥` — the source `ξ ∈ 𝒳` is nontrivial
(`𝒳`: `H ⊄ Ker ξ`) and `induceHU = Ind_{HU}^S` (`induceHU_eq_induce`) — where the landed field
`mu_reducible_dichotomy` dispatches it to its μ-column `∃ j ≠ 0, η = ∑ᵢ μ_{ij}`. -/
theorem Hypothesis.sSet_reducible_eq_muColumnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ ∧ η = ∑ i : Fin hyp.q, hyp.mu i j := by
  classical
  haveI := hyp.finiteG
  obtain ⟨ξ, hξ, rfl⟩ := hη
  -- `ξ ≠ trivial`: else `Ker ξ = univ ⊇ hInHu`, contradicting `ξ ∈ 𝒳`.
  have hξne : ξ ≠ trivialIrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) := by
    intro htriv
    apply hξ
    rw [htriv]
    simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  -- membership in `S(⊥)` over `huSub`, then transported to `(derivedInG S).subgroupOf S`.
  have hmemHU : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        (huSub (hyp.toTypesIIIIIIVSetupS hG)) (⊥ : Subgroup ↥hyp.S) := by
    refine ⟨ξ, hξne, ?_, (induceHU_eq_induce (hyp.toTypesIIIIIIVSetupS hG) _)⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx)
      rw [Subgroup.mem_bot] at h2; exact Subtype.ext h2
    rw [hx1]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hKeq : huSub (hyp.toTypesIIIIIIVSetupS hG) = (derivedInG hyp.S).subgroupOf hyp.S :=
    huSub_eq_derivedInG_subgroupOf _
  have hmem : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) := hKeq ▸ hmemHU
  exact hyp.mu_reducible_dichotomy hmem hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The honest Dade image of a reducible `𝒮`-member column difference** (route B, the core of the
reducible caseB `R`-family): for a reducible `η = ∑ᵢ μ_{ij} ∈ 𝒮` with conjugate `η̄ = ∑ᵢ μ_{ik}`
(`j ≠ k`, both `≠ 0`), the honest `'A(S)`-Dade image is `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})`.

The column difference `η − η̄` is `A(S)`-supported (`sSet_caseB_member_diff_supported`), so the honest
`τ_S` (`dadeHypS`) agrees there with `Ind_S^G` (`sInstance_dade_eq_induce`) and hence with the
`'A0`-Dade `τ_S⁰` (`dadeHypS0`, `sInstance_dade0_eq_induce`, since `A(S) ⊆ A₀(S)`); the per-row
prime-`TI` cross-relation `tauS_mu_cross` then evaluates `τ_S⁰(μ_{ij} − μ_{ik}) = η_{ij} − η_{ik}`,
summed by `ℤ`-linearity of the Dade map. -/
theorem Hypothesis.tauS_muColumn_diff_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {j k : Fin hyp.p} (hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k)
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hηconj : (η : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hjeq : η = ∑ i : Fin hyp.q, hyp.mu i j)
    (hkeq : (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
        (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = ∑ i : Fin hyp.q, (hyp.eta i j - hyp.eta i k) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  -- `η − η̄ = ∑ᵢ(μ_{ij} − μ_{ik})`.
  have hsub : (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = ∑ i : Fin hyp.q, (hyp.mu i j - hyp.mu i k) := by
    rw [hkeq, hjeq, ← Finset.sum_sub_distrib]
  -- `A(S)`-support of the column difference (both members of `𝒮`).
  have hAsupp : (η - (η : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_caseB_member_diff_supported hG chars caseB hη hηconj
  have hA0supp : (η - (η : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
    hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (honestTypeP2ASet_subset_A0Set hyp.Sdata))
  -- the honest `'A`-Dade agrees with the `'A0`-Dade on the `A(S)`-supported column difference.
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
        (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (η - (η : ClassFunction ↥hyp.S ℂ).conj) := by
    rw [hyp.sInstance_dade_eq_induce hG hAsupp, hyp.sInstance_dade0_eq_induce hG hA0supp]
  rw [hτeq, hsub, map_sum]
  refine Finset.sum_congr rfl fun i _ => tauS_mu_cross hG hyp i hj0 hk0 hjk

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family for a REDUCIBLE `𝒮`-member** (route B; the honest
`S`-instance analogue of the M-side column branch of `caseB_sOf_memberRFamily`).  For a reducible
`η = ∑ᵢ μ_{ij} ∈ 𝒮` (Galois caseB), the (5.2.d) orthonormal Dade image family is the `2q`-element
signed `η`-grid family `R(η) = {η_{ij} : i} ∪ {−η_{ik} : i}` (columns `j ≠ k` of `η`, `η̄`), with
`τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik}) = ∑_{α ∈ R(η)} α` (`tauS_muColumn_diff_eq`), orthonormal by
`eta_orthonormal` (distinct columns `j ≠ k`), and in `ℤ[Irr G]` by `eta_mem_ZIrr`. -/
noncomputable def Hypothesis.sSet_caseB_reducible_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) η := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  -- dispatch `η` and `η̄` to their μ-columns `j`, `k` (`.choose`, since this is a data-valued def).
  have hηconj : (η : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη
  have hconjirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (η : ClassFunction ↥hyp.S ℂ).conj := by
    intro h
    apply hirr
    rw [← ClassFunction.conj_conj η]
    exact h.conj
  have hexj := hyp.sSet_reducible_eq_muColumnSum hG hη hirr
  have hexk := hyp.sSet_reducible_eq_muColumnSum hG hηconj hconjirr
  let j := hexj.choose
  let k := hexk.choose
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := hexj.choose_spec.1
  have hjeq : η = ∑ i : Fin hyp.q, hyp.mu i j := hexj.choose_spec.2
  have hk0 : k ≠ ⟨0, hyp.p_prime.pos⟩ := hexk.choose_spec.1
  have hkeq : (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k :=
    hexk.choose_spec.2
  -- `j ≠ k` from non-realness of `η`.
  have hnonreal : ¬ ClassFunction.IsReal η :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη
  have hjk : j ≠ k := by
    intro he
    apply hnonreal
    show (η : ClassFunction ↥hyp.S ℂ).conj = η
    rw [hkeq, ← he, ← hjeq]
  -- the honest Dade image `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})`.
  have hcross := hyp.tauS_muColumn_diff_eq hG chars caseB hj0 hk0 hjk hη hηconj hjeq hkeq
  -- the `2q`-element signed `η`-grid family.
  set g : Fin hyp.q ⊕ Fin hyp.q → ClassFunction G ℂ :=
    Sum.elim (fun i => hyp.eta i j) (fun i => -hyp.eta i k) with hg
  have hg_inner : ∀ x y : Fin hyp.q ⊕ Fin hyp.q,
      ClassFunction.inner (g x) (g y) = if x = y then (1 : ℂ) else 0 := by
    intro x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [hg, Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b j j]
      by_cases hab : a = b <;> simp [hab, Sum.inl.injEq]
    · rw [ClassFunction.inner_neg_right, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b j k,
        if_neg (fun h => hjk h.2)]
      simp
    · rw [ClassFunction.inner_neg_left, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b k j,
        if_neg (fun h => hjk h.2.symm)]
      simp
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b k k]
      by_cases hab : a = b <;> simp [hab, Sum.inr.injEq]
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 := hg_inner x y
    rw [hxy, hg_inner y y, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  refine
    { imageSet := Finset.image g Finset.univ
      mem_ZIrr := ?_
      orthonormal := ?_
      image_eq := ?_ }
  · intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨x, -, rfl⟩ := hα
    rcases x with a | a <;> simp only [hg, Sum.elim_inl, Sum.elim_inr]
    · exact OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp a j
    · exact Submodule.neg_mem _ (OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp a k)
  · intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨x, -, rfl⟩ := hα
    obtain ⟨y, -, rfl⟩ := hβ
    rw [hg_inner x y]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos (by rw [hxy])]
    · rw [if_neg hxy, if_neg (fun h => hxy (hg_inj h))]
  · -- `τ_S(η − η̄) = ∑_{α ∈ R(η)} α`.
    rw [hcross, Finset.sum_image (fun x _ y _ h => hg_inj h), Fintype.sum_sum_type]
    simp only [hg, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    abel
