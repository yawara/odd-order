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

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family over `𝒮 = sSet` in the Galois case** (issue 1017, the
`R` input of the caseB (5.7) engine `uniform_degree_coherence_of_families`, the honest `S`-instance
analogue of the M-instance `caseB_sOf_memberRFamily`, `S13_MaximalIII_IV.lean:546`).  Every member
of the uniform-degree-`q·u` family `𝒮` is dispatched to its (5.2.d) `R`-datum:

* **irreducible member `η`** — the 2-element signed Dade image family
  `dadeOrthonormalCharacterImageFamilyOfDiff` (`η^τ − η̄^τ = ε·(μ − ν)`), assembled sorry-free from
  the landed inputs: non-realness (`sSet_hasNoRealCharacters` via `oddCardS`) and the conjugate
  difference support `(η̄ − η).support ⊆ A(S)` (`sSet_caseB_member_diff_supported`, both `η, η̄ ∈ 𝒮`);
* **reducible member `η = μ_j` (a nonzero μ-column sum)** — the `2q`-element signed-`η` family
  `R(η) = {η_{ij}} ∪ {−η_{ik}}`, **built sorry-free by route B** (`sSet_caseB_reducible_memberRFamily`,
  above): the (9.11) reverse dichotomy `mu_reducible_dichotomy` gives the columns `j, k` of `η, η̄`,
  and `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})` from the honest all-rows prime-`TI` cross-relation
  `tauS_mu_cross` (itself `S16.eta_diff_rigidity`, sorry-free from the abstract fields).

**Route A vs route B** (correcting the prior 748e6a27 record): route A (`certainTypeR @ hyp46S`)
is genuinely inapplicable on the S-side — the abstract `hyp.mu` (from `certainTypeS`) is *not*
grounded to `residueS.mu2`, and `certainTypeR` is over `dadeHypS0` not `dadeHypS`.  But route B
(the abstract generalization of the proven `tauS_mu_row0_cross`) **is** buildable and needs **no**
`prTIirr_id`/9014 content: the cross-relation is discharged entirely from the abstract `Hypothesis`
grid fields (`mu_apply_of_not_mem_W2`, `mu_orthonormal`, `eta_orthonormal`, `eta_diff_rigidity`).
The only architectural cost is that route B lives **downstream of `S16_GridExpansion`**, hence this
whole caseB coherence chain was relocated here from `S15_SAndT_Setup.HypothesisBasics`. -/
noncomputable def Hypothesis.sSet_caseB_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) η := by
  classical
  by_cases hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η
  · -- irreducible member: the 2-element signed Dade image family (assembled sorry-free)
    refine OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) ⟨η, hirr⟩ ?_ ?_
    · exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη
    · exact hyp.sSet_caseB_member_diff_supported hG chars caseB
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη) hη
  · -- reducible member (`η = μ_j`): the `2q`-element signed-η `R`-family, built above by route B
    -- (`sSet_caseB_reducible_memberRFamily`), verified sorry-free (`tauS_mu_cross` +
    -- `mu_reducible_dichotomy`).  Route A (`certainTypeR`) is genuinely inapplicable on the S-side
    -- (`hyp.mu` from `certainTypeS`, ungrounded), but route B is buildable from the abstract fields —
    -- refuting the prior (748e6a27) "9014-blocked" record.
    exact hyp.sSet_caseB_reducible_memberRFamily hG chars caseB hη hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the caseB per-member `R`-families** (issue 1017, the `hRorth`
input of `uniform_degree_coherence_of_families`, the honest `S`-instance analogue of the M-instance
`caseB_sOf_memberRFamily_orthogonal`).  For members `φ, ξ ∈ 𝒮` with `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`
(distinct non-conjugate members), the Dade image families `R(φ)`, `R(ξ)` are orthogonal.

**RESIDUAL (issue 1017): the `2×2` cross-orthogonality assembly** — the reducible `R`-family
itself now LANDS (`sSet_caseB_reducible_memberRFamily`, above, sorry-free), so this is no longer
gated on any missing `R`-datum.  What remains is the member-wise constituent-disjointness `2×2`
case split, which needs (i) `imageSet`-reduction lemmas exposing `(sSet_caseB_memberRFamily …).imageSet`
in each branch (irr → `dadeOrthonormalCharacterImageFamilyOfDiff.imageSet`; red → the signed-`η`
family `{η_{ij}} ∪ {−η_{ik}}`), mirroring the M-side `caseB_sOf_memberRFamily_imageSet_of_{irr,col}`,
and (ii) the eta-family cross-orthogonality lemmas: **irr×irr** from the landed (5.2.e)
`dadeOrthonormalCharacterImageFamilyOfDiff` orthogonality; **red×red** from `eta_orthonormal`
(distinct columns `{j,k} ∩ {j',k'} = ∅` forced by `⟨φ,ξ⟩ = ⟨φ,ξ̄⟩ = 0`); **irr×red** from
`eta_orthogonal_of_norm_one_pair_vanish` (`S16_GridExpansion`).  Sorried-cite pending that
infrastructure (the analogue of the M-side `certainTypeR_imageSet_orthogonal_*` lemmas, which
do not transfer since the S-side family is the eta-grid family, not `certainTypeR`). -/
theorem Hypothesis.sSet_caseB_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {φ ξ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (h1 : ClassFunction.inner φ ξ = 0)
    (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (hyp.sSet_caseB_memberRFamily hG chars caseB hφ).Orthogonal
      (hyp.sSet_caseB_memberRFamily hG chars caseB hξ) := by
  -- RESIDUAL (issue 1017): the reducible `R`-family now LANDS; remaining is the `2×2` member-wise
  -- cross-orthogonality assembly (imageSet-reduction + eta-family orthogonality) — see docstring.
  sorry

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of `𝒮 = sSet` on the honest Dade map** (issue 1017, caseB — the
`uniform_degree_coherence_of_families` assembly, the honest `S`-instance mirror of the M-instance
`caseB_coherent_sOf_H0Cprime`, `S13_CoreStructure.lean:1544`).  In the Galois case the whole family
`𝒮` is uniform degree `q·u` (`sSet_caseB_apply_one_eq_qu`), so the (5.7) *norm-general* coherence
producer fires directly (no reducible-column *fold* needed): the pivot is a reducible μ-column
`μ₁ = ∑ᵢ μ_{i1}` (of self-norm `q`, from `mu_orthonormal`), and every member carries its (5.2.d)
`R`-datum via `sSet_caseB_memberRFamily`.  All the family inputs — finiteness (`sSet_finite`),
pairwise orthogonality (`sSet_pairwiseOrthogonal`), conjugate-closure (`sSet_closedUnderConjugate`),
no-real (`sSet_hasNoRealCharacters`), the Dade isometry / ZIrr-image / support facts
(`dadeIntegralCharacterMap_*_of_supported`, `sSet_caseB_member_diff_supported`), and the uniform
degree — are landed sorry-free; the sole residual is the reducible branch of
`sSet_caseB_memberRFamily` (+ `_orthogonal`), the `S`-instance §6 certain-type port. -/
noncomputable def Hypothesis.sSet_coherent_dade_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  -- Pivot: a nonzero reducible μ-column `μ₁ = ∑ᵢ μ_{i1} ∈ 𝒮` (self-norm `q`).
  have hj0 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have hη₁ : (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief ⟨1, hyp.p_prime.one_lt⟩ hj0)
  have hN : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩) = (hyp.q : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ i : Fin hyp.q, ClassFunction.inner (hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
            (∑ i' : Fin hyp.q, hyp.mu i' ⟨1, hyp.p_prime.one_lt⟩)
        = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q,
            ClassFunction.inner (hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
              (hyp.mu i' ⟨1, hyp.p_prime.one_lt⟩) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, if i = i' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          rw [hyp.mu_orthonormal i i' ⟨1, hyp.p_prime.one_lt⟩ ⟨1, hyp.p_prime.one_lt⟩]
          simp
      _ = ∑ _i : Fin hyp.q, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
      _ = (hyp.q : ℂ) := by simp
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    (sSet_finite _) hη₁
    (fun η hη => hyp.sSet_caseB_memberRFamily hG chars caseB hη)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) ha hb hab
      convert h using 2 <;> exact Subsingleton.elim _ _)
    (fun a ha => sSet_closedUnderConjugate _ ha)
    (fun a ha heq => sSet_hasNoRealCharacters _ (hyp.oddCardS hG) ha heq.symm)
    ⟨hyp.q, hN⟩
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hφ.2 hψ.2)
    (fun a ha b hb => by
      have hab_Z : (a - b : ClassFunction ↥hyp.S ℂ) ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
        Submodule.sub_mem _ (sSet_subset_ZIrr _ ha) (sSet_subset_ZIrr _ hb)
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG)
        (hyp.sSet_caseB_member_diff_supported hG chars caseB ha hb) hab_Z)
    (fun a ha b hb => hyp.sSet_caseB_member_diff_supported hG chars caseB ha hb)
    (fun {φ ξ} hφ hξ h1 h2 =>
      hyp.sSet_caseB_memberRFamily_orthogonal hG chars caseB hφ hξ h1 h2)
    (fun a ha => (hyp.sSet_caseB_apply_one_eq_qu hG chars caseB ha).trans
      (hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hη₁).symm)
    (by
      rw [hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hη₁]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Nat.card_pos.ne'
        (OddOrder.Peterfalvi.S11.u_odd hG chars).pos.ne'))
    (by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
      simpa using honestTypeP2ASet_one_not_mem (M := hyp.S))
    (sSet_closedUnderConjugate _ hη₁)
    (sSet_hasNoRealCharacters _ (hyp.oddCardS hG) hη₁)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of the full family `𝒮 = sSet` on `Ind_S^G`** (issue 1017, caseB
of Peterfalvi (9.11) `Ptype_core_coherence`).  In the Galois case (`CliffordCaseBData`) **every**
member of `𝒮 = sSet` has degree `q·u` (`caseB_degree_qu`/`caseB_character_counts`), but `𝒮` is still
**mixed**: it contains exactly `p−1` reducible members (the μ_j residues, each `Ind` of a linear
character of `HC`, `reducible_count_sOf_H0`) alongside the degree-`q·u` irreducibles.

Honest route (mirroring the *landed* M-instance `caseB_coherent_sOf_H0Cprime`,
`S13_CoreStructure.lean:1544`, which likewise routes through the norm-general (5.7) engine rather
than the mixed *fold*): since the whole family is **uniform** degree `q·u`
(`sSet_caseB_apply_one_eq_qu`), coherence on the honest Dade map `τ` follows directly from
`uniform_degree_coherence_of_families` (`sSet_coherent_dade_caseB`, this file) with a reducible μ-column
pivot; then `congrMap` re-grounds `τ` onto `Ind_S^G` on the `A(S)`-supported span
(`sInstance_dade_eq_induce`).  All the (5.7)-engine wiring, the uniform-degree fact, the pivot norm,
the Dade isometry/ZIrr/support inputs, and the *irreducible* per-member `R`-datum are landed
sorry-free here; the sole residual is the **reducible** branch of `sSet_caseB_memberRFamily`
(+ `_orthogonal`) — the `S`-instance §6 certain-type image-family port. -/
theorem Hypothesis.sSet_coherent_indS_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) :=
  -- Coherence on the honest Dade map `τ` (`sSet_coherent_dade_caseB`, the (5.7) `uniform_degree`
  -- assembly) re-grounded onto `Ind_S^G` by `congrMap`: `τ` and `indS` agree on every
  -- `A(S)`-supported class function (`sInstance_dade_eq_induce`, the (13.2.e) `normedTI` isometry
  -- half), and `IsCoherent` depends on its map only through the `A(S)`-supported span — exactly the
  -- `indS`-re-grounding `sSetIrrDeg_coherent_indS` performs for the uniform sub-family.
  (hyp.sSet_coherent_dade_caseB hG chars caseB).map fun c =>
    c.congrMap fun φ hφ => by
      rw [hyp.indS_apply]
      exact hyp.sInstance_dade_eq_induce hG hφ.2

open OddOrder.Peterfalvi.S11 in
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Honest §9 character data on `S`** (issue 2035 step 3; support corrected to `A(S)`, issue 1017):
the `mkSection11CharacterDataS` mirror with the *genuine* coherence inputs — `tau := Ind_S^G` (`indS`,
Peterfalvi (13.2.e)) and `H0CprimeSupport := A(S)` (`supportInSubgroup (honestTypeP2ASet S) S`, the
honest Dade support `⋃_{x∈S_σ#} C_{S′}(x)#`).

**Support choice (issue 1017 verify-first).**  For the type-`P₂` maximal `S` the coherence support
`(H₀ ⊔ C′)^#` degenerates to the empty set — `H₀ = ⊥` (chief kernel trivial) and `C′ = [C,C] = ⊥`
(`Cprime_eq_bot`, `C ≤ U` abelian), so `(C′)^# = cprimeSharpS = ∅` (`cprimeSharpS_eq_empty`).  With
support `∅`, `zSupportedSpan 𝒮 ∅ = {0}`, which makes `IsCoherent`'s `nonzero` field (a nonzero
supported witness) **unsatisfiable** — the target `IsCoherent Ind_S^G 𝒮 ∅` is uninhabited, which is
exactly why the old `sibleyTarget_H0C` route was unsound.  The honest support is the (13.2.e) Dade
support `A(S)`, on which the family differences genuinely live (`sSet_member_diffsupp`) and
`extends_on_supported` carries real content (`τ₁ = Ind_S^G` on `A(S)`-supported combinations); the
degenerate `(C′)^# ⊆ A(S)` (`cprimeSharpS_subset_supportA`) restriction would only re-vacuate it.

Fed to `coherent_H0Cprime_S` (re-grounded off the unsound `sibleyTarget_H0C` onto the honest
`sSet_coherent_indS_A`) to extract the coherent extension `τ₁` (the (13.2.d)⇐(9.11) route to the
(13.3) `τ₁`-fields).  `u` and `u_eq_card_quotient` are unchanged (rfl-pinned to the `U`-action
image, as in the placeholder). -/
noncomputable def Hypothesis.mkSection11CharacterDataS_honest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      ((hyp.toTypesIIIIIIVSetupS hG).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S
  tau := hyp.indS
  quotientSemidirectFrobenius := True

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) coherence of the full honest §9 family `𝒮 = sSet` on `Ind_S^G`, unconditional** (issue
1017 — the honest S-instance Peterfalvi (9.11) `Ptype_core_coherence`, replacing the unsound
`sibleyTarget_H0C`).  Case-splits the Clifford dichotomy (9.7) (`clifford_dichotomy` on the honest
character data) and dispatches to the Galois branch (`sSet_coherent_indS_caseB`) or the non-Galois
branch (`sSet_coherent_indS_caseA`).  The map is the genuine induction `τ = Ind_S^G` (`indS`,
(13.2.e)) and the support is the honest Dade support `A(S)` (nonempty — unlike the degenerate
`(C′)^# = ∅`, which makes `IsCoherent`'s `nonzero` field unsatisfiable). -/
theorem Hypothesis.sSet_coherent_indS_A [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS_honest hG chief) with hA | hB
  · exact hyp.sSet_coherent_indS_caseA hG (hyp.mkSection11CharacterDataS_honest hG chief) hA.some
  · exact hyp.sSet_coherent_indS_caseB hG (hyp.mkSection11CharacterDataS_honest hG chief) hB.some

open scoped FiniteInduce in
/-- **(9.11)-coherence of the honest `S`-instance §9 data** (issue 2035 step 4; re-grounded off the
unsound `sibleyTarget_H0C`, issue 1017).  The `.some` of the honest unconditional
`sSet_coherent_indS_A`, yielding `IsCoherent Ind_S^G 𝒮 A(S)` — the Peterfalvi (13.2.d)⇐(9.11)
coherence for `𝒮(H₀C′) = 𝒮` (in the type-`P₂` `S`-instance, `H₀C′ = ⊥`) with the genuine Dade map
`τ = Ind_S^G` and the honest Dade support `A(S)`.

**This no longer routes through `coherent_H0C_commutator`/`sibleyTarget_H0C`** (the unsound (6.8)
shortcut whose target `IsCoherent Ind_S^G 𝒮 (C′)^# = IsCoherent Ind_S^G 𝒮 ∅` is uninhabited).  The
remaining gap is the honest (9.11) pair-adjoining assembly inside `sSet_coherent_indS_{caseA,caseB}`
(base coherences landed, the mixed-family lift sorried-cite), not a soundness defect. -/
noncomputable def Hypothesis.coherent_H0Cprime_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IsCoherent (hyp.mkSection11CharacterDataS_honest hG chief).tau
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport :=
  (hyp.sSet_coherent_indS_A hG chief).some

open scoped FiniteInduce in
/-- **The coherent extension `τ₁` for the honest `S`-instance** (issue 2035 step 4): the
`.extension` of the (9.11)-coherence `coherent_H0Cprime_S`.  This is the (13.2.d) `τ₁ :
IntegralCharacterMap ↥S G` that the (13.3) degree analysis threads (the `μ_j^{τ₁}` machinery).
Now grounded on the honest `sSet_coherent_indS_A` (base coherences landed, mixed-family lift
sorried-cite), no longer on the unsound `sibleyTarget_H0C`. -/
noncomputable def Hypothesis.tau1S_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.coherent_H0Cprime_S hG chief).extension

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
private theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5) preamble / (1.5.a) — the family membership `Ind_{PC}^S θ ∈ ℤ[𝒮]`**
(issue 2035 step 5a).

For an irreducible character `θ` of `H = PC` **whose kernel does not contain `P`**, the induced
character `Ind_{PC}^S θ` lies in `ℤ[𝒮]` (`zSpan` of the honest §9 family `𝒮 = sSet`).  In
Coq's `PFsection13` this is `sS1S : {subset calS1 <= 'Z[calS]}` (with `calS1 = seqIndD H S P 1`,
`calS = seqIndD PU S P 1`), used implicitly throughout (13.5)–(13.8).

**Honest proof, grounded on the S06 §4 residue theory** (issue 9014 session 8).  The family
`𝒮 = sSet = {Ind_{S'}^S χ | χ ∈ Irr(S'), P ⊄ ker χ}` is *exactly* the set of inductions
from the derived subgroup `S' = huSub` of `P`-nonlinear irreducibles (`P = data.H`), so **membership
is by witness** — no dichotomy on the induced character is needed.  Writing the single-stage
`Ind_{PC}^S θ` as the two-stage `Ind_{S'}^S (Ind_{PC'}^{S'} θ')` (`induce_induce_subgroupOf`, with
`PC' = (PC).subgroupOf S'` and `θ'` the transport of `θ`) and expanding the inner induction into
`S'`-constituents `Ind_{PC'}^{S'} θ' = ∑_{s ∈ Irr(S')} ⟨θ', Res s⟩ • s`
(`induce_eq_sum_inner_restrict_smul`), each constituent `s` with nonzero (necessarily `ℕ`)
coefficient has `P ⊄ ker s` (`constituent_P_not_subset_characterKernel`), so `Ind_{S'}^S s`
lies in `sSet` by witness `s`; the coefficient-weighted `ℤ`-sum lands in `zSpan sSet`.  This
grounds the family
membership on the proven S06 setup (`typePData_toS06Hypothesis` for `S` supplies the certain-type
Hypothesis, though only its `S'`-family shape is needed here); no prime-TI residue dichotomy is used. -/
theorem Hypothesis.induce_H_mem_zSpan_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Target family is `sSet data` with `data = toTypesIIIIIIVSetupS hG`.
  rw [OddOrder.Peterfalvi.S11.Section11CharacterData.S_eq]
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  -- Work with the §9 induction carrier `HU = huSub data`, equal to `S' = derivedInG S` in `↥S`.
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `PC = H.subgroupOf S ≤ S' = HU`.
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  -- Two-stage induction: `Ind_{PC}^S θ = Ind_{HU}^S (Ind_{PC'}^{HU} θ')`.
  rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ]
  -- Expand the inner induction into `HU`-constituents and push `Ind_{HU}^S` inside.
  rw [OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
    ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ', Res s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
  have hc : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
      (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
        (s : ClassFunction ↥HU ℂ)) = (k : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    -- `P (in HU) ⊄ ker s`: kernel step from `P ⊄ ker θ'` (from `hθP`) and constituent `θ'`.
    have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
        Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      -- The image of `((P.subgroupOf S).subgroupOf HU).subgroupOf (PC.subgroupOf HU)` under `e`
      -- is `(P.subgroupOf S).subgroupOf (PC.subgroupOf S)`, which `hθP` does not kill.
      have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
            ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]; exact hθP
    refine Submodule.subset_span ?_
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    -- `s ∈ xiSet data`: `hInHu data ⊄ ker s`, with `hInHu = (P.subgroupOf S).subgroupOf HU`.
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    -- The generic kernel step: `θ'` is a constituent of `Res s` (coefficient `k > 0`), and
    -- `P (in HU) ⊄ ker θ'` (`hθ'P`), so `P (in HU) ⊄ ker s`.
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hc]; exact_mod_cast hk0.ne'
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr` field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
