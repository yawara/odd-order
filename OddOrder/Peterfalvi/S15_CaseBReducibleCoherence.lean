import OddOrder.Peterfalvi.S15_SSetMemberRFamily

/-!
# Peterfalvi §9/§13 — caseB coherence and the (5.6) pair bound of the honest `S`-instance family

The Galois-case coherence of the honest §9 family `𝒮 = sSet` and the (9.11.1) pair bound, from
the per-member (5.2.d) `R`-families built in `S15_SSetMemberRFamily`:

* **caseB (Galois)**: `𝒮` is uniform degree `q·u` (`sSet_caseB_apply_one_eq_qu`), so the (5.7)
  norm-general coherence producer fires directly — `sSet_coherent_dade_caseB` /
  `sSet_coherent_indS_caseB`.
* **(5.6) pair bound (caseA, Peterfalvi (9.11.1))**: the `𝒮 ↪ S(⊥)` embedding
  `sSet_subset_inducedKernelFamily`, the ψ-decomposition bricks `sSet_memberPsiDecomp` /
  `sSet_breakPsiDecomp`, the scaled-difference support `sSet_scaledDiff_support`, and the pair
  bound `nineElevenPairBoundS` (`sumnS F ≤ 2q²a·d` at any pair-refuted member, via the raw (5.6)
  engine `S08.coherentDegreeSqNormBound_of_not_coherentW_k`).

The (9.11) caseA equality campaign, the case-combined coherence assembly, and the (13.2.d) `τ₁`
engines live downstream in `S15_CaseACoherence` (which imports this file).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of `𝒮 = sSet` on the honest Dade map** (issue 1017, caseB — the
`uniform_degree_coherence_of_families` assembly, the honest `S`-instance mirror of the M-instance
`caseB_coherent_sOf_H0Cprime`, `S13_CoreStructure.lean:1544`).  In the Galois case the whole family
`𝒮` is uniform degree `q·u` (`sSet_caseB_apply_one_eq_qu`), so the (5.7) *norm-general* coherence
producer fires directly (no reducible-column *fold* needed): the pivot is a reducible μ-column
`μ₁ = ∑ᵢ μ_{i1}` (of self-norm `q`, from `mu_orthonormal`), and every member carries its (5.2.d)
`R`-datum via `sSet_memberRFamily`.  All the family inputs — finiteness (`sSet_finite`),
pairwise orthogonality (`sSet_pairwiseOrthogonal`), conjugate-closure (`sSet_closedUnderConjugate`),
no-real (`sSet_hasNoRealCharacters`), the Dade isometry / ZIrr-image / support facts
(`dadeIntegralCharacterMap_*_of_supported`, `sSet_caseB_member_diff_supported`), and the uniform
degree — are landed sorry-free; the sole residual is the reducible branch of
`sSet_memberRFamily` (+ `_orthogonal`), the `S`-instance §6 certain-type port. -/
noncomputable def Hypothesis.sSet_coherent_dade_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
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
    (fun η hη => hyp.sSet_memberRFamily hG hnoV hη)
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
      hyp.sSet_memberRFamily_orthogonal hG hnoV hφ hξ h1 h2)
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
sorry-free here; the sole residual is the **reducible** branch of `sSet_memberRFamily`
(+ `_orthogonal`) — the `S`-instance §6 certain-type image-family port. -/
theorem Hypothesis.sSet_coherent_indS_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
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
  (hyp.sSet_coherent_dade_caseB hG hnoV chars caseB).map fun c =>
    c.congrMap fun φ hφ => by
      rw [hyp.indS_apply]
      exact hyp.sInstance_dade_eq_induce hG hnoV hφ.2

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
/-- **`𝒮 = sSet` embeds into the general kernel-filter family `S(⊥)`** (issue 1017 step (c), the
`S`-instance analogue of the M-side `hyp.sOf_subset_SOf` bridge).  Every member `η = Ind_{HU}^S ξ`
(`ξ ∈ 𝒳`, hence `ξ` nontrivial — else `Ker ξ = ⊤ ⊇ hInHu`) lies in
`S(⊥) = inducedKernelFamily ((derivedInG S).subgroupOf S) ⊥` (the `⊥`-kernel demand is vacuous), the
membership the general §8 family layer (`inducedKernelFamily_*`: Gram positivity, ZIrr-integrality,
scaled-difference supports, break-character fields) consumes.  This is the first part of
`sSet_reducible_eq_muColumnSum`, extracted for the (5.6) engine wiring. -/
theorem Hypothesis.sSet_subset_inducedKernelFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    sSet (hyp.toTypesIIIIIIVSetupS hG) ⊆
      OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) := by
  haveI := hyp.finiteG
  rintro η ⟨ξ, hξ, rfl⟩
  have hξne : ξ ≠ trivialIrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) := by
    intro htriv
    apply hξ
    rw [htriv]
    simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
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
  exact hKeq ▸ hmemHU

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member (5.4) decomposition `D(φ)` for a member `φ ∈ 𝒮₂`, case-agnostic** (issue 1017
step (c)).  The `ψ = 0` `CharacterPsiDecomposition` over the honest Dade map `τ` whose orthonormal
image family is the case-agnostic `R`-family `sSet_memberRFamily` (irreducible *or* reducible μ-column)
and whose auxiliary isometry is the coherent extension `ν = hS₂coh.extension` — every `ofProjection`
input (non-realness cross-orthogonality `⟨φ, φ̄⟩ = 0`, conjugate-difference support `(φ̄ − φ) ⊆ A(S)`,
`ν`-integrality `νφ ∈ ℤ[Irr G]`, the sponsoring-lattice `ℤ[φ, φ̄]` inner-preservation and
`ν(φ − φ̄) = τ(φ − φ̄)`) discharged from the family layer via `sSet_subset_inducedKernelFamily`.  The
`S`-instance analogue of `memberExtensionDecomposition`, with the case-agnostic family in place of the
irreducible-only `dadeOrthonormalCharacterImageFamilyOfDiff`. -/
noncomputable def Hypothesis.sSet_memberPsiDecomp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {S₂ : Set (ClassFunction ↥hyp.S ℂ)}
    (hS₂coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      S₂ (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S))
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hφS₂ : φ ∈ S₂) (hφcS₂ : (φ : ClassFunction ↥hyp.S ℂ).conj ∈ S₂) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥hyp.S) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) φ 0 //
      D.imageFamily = hyp.sSet_memberRFamily hG hnoV hφ ∧ D.tau1 φ = hS₂coh.extension φ } := by
  classical
  haveI := hyp.finiteG
  have hfam : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) :=
    hyp.sSet_subset_inducedKernelFamily hG hφ
  have hφmem : φ ∈ Submodule.span ℤ S₂ := Submodule.subset_span hφS₂
  have hφcmem : (φ : ClassFunction ↥hyp.S ℂ).conj ∈ Submodule.span ℤ S₂ :=
    Submodule.subset_span hφcS₂
  have hdiffsupp : ((φ : ClassFunction ↥hyp.S ℂ).conj - φ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_member_conjDiff_supported hG hφ
  have hχχbar : ClassFunction.inner φ (φ : ClassFunction ↥hyp.S ℂ).conj = 0 := by
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hfam
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hfam) (fun h => ?_)
    exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hφ h.symm
  have hνZ : hS₂coh.extension φ ∈ ZIrr G := hS₂coh.extension_mem_ZIrr φ hφmem
  have hle : Submodule.span ℤ ({φ - (φ : ClassFunction ↥hyp.S ℂ).conj, φ - 0}
      : Set (ClassFunction ↥hyp.S ℂ)) ≤ Submodule.span ℤ S₂ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hφmem hφcmem
    · rw [sub_zero]; exact hφmem
  have hdiffsupported : (φ - (φ : ClassFunction ↥hyp.S ℂ).conj) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ hφmem hφcmem, by
        rw [show (φ - (φ : ClassFunction ↥hyp.S ℂ).conj)
            = -((φ : ClassFunction ↥hyp.S ℂ).conj - φ) from by abel,
          ClassFunction.support_neg]
        exact hdiffsupp⟩
  exact ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.sSet_memberRFamily hG hnoV hφ) hS₂coh.extension
    (fun ψ' ζ' hψ' hζ' => hS₂coh.extension_inner_eq ψ' ζ' (hle hψ') (hle hζ'))
    (hS₂coh.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp) (by simp) hχχbar, rfl, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The break decomposition `Da` for a pair-refuted member `χ`, case-agnostic** (issue 1017
step (c)).  The `ψ = a·χ₁` `CharacterPsiDecomposition` over the honest Dade map `τ` (with `τ` itself as
the auxiliary isometry, so `Da.tau1 = τ`) whose image family is the case-agnostic `R`-family
`sSet_memberRFamily hG hnoV hχ`; the difference set `{χ − χ̄, χ − a·χ₁}` is `A(S)`-supported
(`sSet_member_conjDiff_supported` + `hdiffasupp`), so the Dade isometry preserves the sponsoring-lattice
inner products (`dadeIntegralCharacterMap_inner_eq_on_supported_span`).  The `S`-instance analogue of
`decompositionDaFromDadeOfDiff`, case-agnostic in `χ`. -/
noncomputable def Hypothesis.sSet_breakPsiDecomp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {χ : ClassFunction ↥hyp.S ℂ} (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {χ₁ : ClassFunction ↥hyp.S ℂ} {a : ℕ}
    (hdiffasupp : (χ - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)
    (htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
        (χ - a • χ₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner χ (a • χ₁ : ClassFunction ↥hyp.S ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥hyp.S ℂ).conj
      (a • χ₁ : ClassFunction ↥hyp.S ℂ) = 0)
    (hχχbar : ClassFunction.inner χ (χ : ClassFunction ↥hyp.S ℂ).conj = 0) :
    { Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥hyp.S) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) χ (a • χ₁) //
      Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) ∧
      Da.imageFamily = hyp.sSet_memberRFamily hG hnoV hχ } := by
  classical
  haveI := hyp.finiteG
  have hdiffsupp : ((χ : ClassFunction ↥hyp.S ℂ).conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_member_conjDiff_supported hG hχ
  have hSdiff : ∀ s ∈ ({χ - (χ : ClassFunction ↥hyp.S ℂ).conj, χ - a • χ₁}
      : Set (ClassFunction ↥hyp.S ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ - (χ : ClassFunction ↥hyp.S ℂ).conj)
          = -((χ : ClassFunction ↥hyp.S ℂ).conj - χ) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  exact ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.sSet_memberRFamily hG hnoV hχ)
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
    (fun ψ' ζ' hψ' hζ' =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hSdiff hψ' hζ')
    rfl htau1_mema hχaχ1 hχbaraχ1 hχχbar, rfl, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Scaled-difference support for `𝒮`-members** (issue 1017 step (c), the honest-`A(S)` analogue of
the general `inducedKernelFamily_scaledDiff_support`).  For members `φ, ψ ∈ 𝒮` with a matching scaled
degree `φ(1) = c·ψ(1)` (`c : ℕ`), the difference `φ − c·ψ` vanishes at `1`, so — since every `𝒮`-member
is supported in `A(S) ∪ {1}` (`sSet_member_support_subset`, the honest (4.7) support) — its support
lands in `A(S)`.  Used in place of the general induced-family support lemma, whose `hKsupp` premise
`(S′)^# ⊆ A(S)` is *false* for the honest, strictly-smaller type-`P₂` support `A(S)`. -/
theorem Hypothesis.sSet_scaledDiff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ ψ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hψ : ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {c : ℕ}
    (hdeg : (φ : ↥hyp.S → ℂ) 1 = (c : ℂ) * (ψ : ↥hyp.S → ℂ) 1) :
    (φ - c • ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  haveI := hyp.finiteG
  have hnsmul : ∀ y : ↥hyp.S, (c • ψ : ClassFunction ↥hyp.S ℂ) y = (c : ℂ) * ψ y := fun y => by
    rw [← Nat.cast_smul_eq_nsmul ℂ c ψ, ClassFunction.smul_apply]
  have hzero : (φ - c • ψ) (1 : ↥hyp.S) = 0 := by
    rw [ClassFunction.sub_apply, hnsmul, hdeg, sub_self]
  have hcψsupp : (c • ψ : ClassFunction ↥hyp.S ℂ).support ⊆ ψ.support := by
    intro w hw
    rw [ClassFunction.mem_support] at hw ⊢
    intro hwψ
    apply hw
    rw [hnsmul, hwψ, mul_zero]
  intro z hz
  have hz0 : (φ - c • ψ) z ≠ 0 := hz
  rcases ClassFunction.support_sub_subset φ (c • ψ) hz with h | h
  · rcases hyp.sSet_member_support_subset hG hφ h with h' | h'
    · exact h'
    · rw [Set.mem_singleton_iff] at h'; subst h'; exact absurd hzero hz0
  · rcases hyp.sSet_member_support_subset hG hψ (hcψsupp h) with h' | h'
    · exact h'
    · rw [Set.mem_singleton_iff] at h'; subst h'; exact absurd hzero hz0

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
set_option maxHeartbeats 1600000 in
/-- **Peterfalvi (9.11.1), the `S`-instance (5.6) pair-bound residual** (issue 1017 step (c); the
`S`-mirror of `S11.NineElevenPairBound`, whose M-side provider `S11.nineElevenPairBound` requires
`htype : IsTypeIII M ∨ IsTypeIV M` — false for the type-II `S` — so it must be rebuilt in the
`indS`/`A(S)` world rather than cited).  For a pair-refuted `χ ∈ 𝒮 ∖ 𝒮₂` (its conjugate pair
`{χ, χ̄}` not coherently adjoinable to the coherent maximal `𝒮₂`), the member `χ = Ind_{HU}^S ζ` has
degree `χ(1) = q·d` with source degree `d ≤ u`, and every finite `F ⊆ 𝒮₂` obeys the (5.6)
norm-weighted degree-square bound `sumnS F ≤ 2·(q·a)·(q·d) = 2q²a·d` (Theorem (5.6) at the degree-`qa`
anchor read contrapositively through `S08.coherentDegreeSqNormBound_of_not_coherentW_k`).

**Precisely-named residual (issue 1017 step (c), `TRUE` signature, no hoisted content).**  The
genuinely-`S`-specific inputs still to build: the caseA per-member Dade `R`-family — now
Clifford-case-agnostic, `sSet_memberRFamily` (issue 1017 update #45), citable here after the step (b)
relocation — feeding the (5.6) engine, and the (9.8.a) source-degree divisibility `a ∣ ζ(1)`
(`S11.caseA_sOf_source_degree_ratio` via `sSet_eq_sOf_H0Cprime`). -/
theorem Hypothesis.nineElevenPairBoundS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (χ : ClassFunction ↥hyp.S ℂ)
    (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂)
    (hnopair : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S))) :
    ∃ d : ℕ, ((χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * d : ℕ) : ℂ)) ∧
      d ≤ chars.u ∧
      ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
  classical
  haveI := hyp.finiteG
  obtain ⟨hχS, hχnotS₂⟩ := hχ
  obtain ⟨cohS₂_indS⟩ := hS₂coh
  -- (1) Dade-side coherence via `congrMap`: `indS = Ind_S^G = τ` on `A(S)`-supported class functions.
  have hindS_dade : ∀ f : ClassFunction ↥hyp.S ℂ,
      f ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) →
      hyp.indS f = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) f := fun f hf => by
    rw [hyp.indS_apply, ← hyp.sInstance_dade_eq_induce hG hnoV
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2]
  have cohS₂ := cohS₂_indS.congrMap hindS_dade
  -- (2) not-coherent (Dade side) from `hnopair` (indS side), the contrapositive of `congrMap`.
  have hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (S₂ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
    rintro ⟨c⟩
    refine hnopair ⟨c.congrMap (fun f hf => ?_)⟩
    rw [hyp.sInstance_dade_eq_induce hG hnoV
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2, hyp.indS_apply]
  -- (3) break dictionary: `χ = Ind_{HU}^S ξ`, `χ(1) = q·d`, `d ≤ u`, source ratio `q·a·e`.
  have hχsOf : χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ chars.Cprime) := by rw [← hyp.sSet_eq_sOf_H0Cprime hG chars]; exact hχS
  obtain ⟨ξ, hξ, rfl⟩ := OddOrder.Peterfalvi.S11.mem_sOf.mp hχsOf
  obtain ⟨d, -, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  have hχdeg : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * d : ℕ) : ℂ) := by
    rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdζ]; push_cast; ring
  have hduC := OddOrder.Peterfalvi.S11.xiOf_H0Cprime_source_apply_one_le_u chars hξ
  rw [hdζ] at hduC
  have hdu : d ≤ chars.u := by
    have h := (Complex.le_def.mp hduC).1
    rw [Complex.natCast_re, Complex.natCast_re] at h
    exact_mod_cast h
  obtain ⟨e, he⟩ := OddOrder.Peterfalvi.S13.caseA_sOf_source_degree_ratio caseA
    (OddOrder.Peterfalvi.S11.mem_sOf.mpr ⟨ξ, hξ, rfl⟩)
  have hde : d = caseA.a * e := by
    have h1 : (hyp.toTypesIIIIIIVSetupS hG).q * d
        = (hyp.toTypesIIIIIIVSetupS hG).q * caseA.a * e := by exact_mod_cast hχdeg.symm.trans he
    have h2 : (hyp.toTypesIIIIIIVSetupS hG).q * d
        = (hyp.toTypesIIIIIIVSetupS hG).q * (caseA.a * e) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos h2
  -- (4) anchor: a degree-`qa` irreducible of `𝒮`, transported into `𝒮₂` via `hS₁S₂`.
  obtain ⟨χ₁, hχ₁sOfU', hχ₁irr, hχ₁deg⟩ :=
    OddOrder.Peterfalvi.S11.caseA_exists_irreducible_qa hG chars caseA
  have hχ₁sSet : χ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
    have h1 : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) := by
      rw [OddOrder.Peterfalvi.S11.Section11CharacterData.SOf_eq] at hχ₁sOfU'; exact hχ₁sOfU'
    rwa [hyp.sOf_H0_uprime_eq_sSet hG chief] at h1
  have hχ₁S₂ : χ₁ ∈ S₂ := hS₁S₂ ⟨hχ₁sSet, hχ₁irr, hχ₁deg⟩
  -- (5) `S₂` is finite; enumerate it and locate the anchor index.
  have hS₂fin : S₂.Finite := (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset hS₂S
  obtain ⟨k, χmem, hinj, hrange⟩ := OddOrder.Peterfalvi.S08.exists_finEnum_general hS₂fin
  have hmemS1set : ∀ j, χmem j ∈ S₂ := fun j => hrange ▸ Set.mem_range_self j
  have hχ₁mem : χ₁ ∈ Set.range χmem := hrange ▸ hχ₁S₂
  obtain ⟨i₁, hi₁eq⟩ := hχ₁mem
  subst hi₁eq
  have hmemsSet : ∀ j, χmem j ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := fun j => hS₂S (hmemS1set j)
  have hmemsOf : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ chars.Cprime) := fun j => by
    rw [← hyp.sSet_eq_sOf_H0Cprime hG chars]; exact hmemsSet j
  choose deg hdeg using fun j : Fin k =>
    OddOrder.Peterfalvi.S13.caseA_sOf_source_degree_ratio caseA (hmemsOf j)
  have hdeg_anchor : ∀ j, (χmem j : ↥hyp.S → ℂ) 1
      = (deg j : ℂ) * (χmem i₁ : ↥hyp.S → ℂ) 1 := by
    intro j; rw [hdeg j, hχ₁deg]; push_cast; ring
  have ha1 : deg i₁ = 1 := by
    have h : (hyp.toTypesIIIIIIVSetupS hG).q * caseA.a * 1
        = (hyp.toTypesIIIIIIVSetupS hG).q * caseA.a * deg i₁ := by
      rw [mul_one]; exact Nat.cast_inj.mp (hχ₁deg.symm.trans (hdeg i₁))
    exact (Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos caseA.a_pos) h).symm
  have hψdeg : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        : ↥hyp.S → ℂ) 1 = (e : ℂ) * (χmem i₁ : ↥hyp.S → ℂ) 1 := by
    rw [hχdeg, hχ₁deg, hde]; push_cast; ring
  -- (6) family-layer facts via the `S(⊥)` embedding: Gram data, break-character orthogonalities.
  have hχfam : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) :=
    hyp.sSet_subset_inducedKernelFamily hG hχS
  have hmemfam : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) :=
    fun j => hyp.sSet_subset_inducedKernelFamily hG (hmemsSet j)
  have hmcpos : ∀ j, 0 < (ClassFunction.inner (χmem j) (χmem j)).re := fun j =>
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam j)).2
  have hmemortho : ∀ i j, ClassFunction.inner (χmem i) (χmem j)
      = @ite ℂ (i = j) (Classical.propDecidable (i = j))
          (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]
      exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam i)).1
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hmemfam i) (hmemfam j) (fun h => hij (hinj h))
  have hanchorNorm : (ClassFunction.inner (χmem i₁) (χmem i₁)).re = 1 := by
    have hval : ClassFunction.inner (χmem i₁) (χmem i₁) = 1 := by
      have h := irreducibleCharacter_inner_eq_ite
        (⟨χmem i₁, hχ₁irr⟩ : IrreducibleCharacter ↥hyp.S) ⟨χmem i₁, hχ₁irr⟩
      rwa [if_pos rfl] at h
    rw [hval, Complex.one_re]
  have hχcnotS₂ : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
        ∉ S₂ := by
    intro hc; apply hχnotS₂
    have h := hS₂conj hc; rwa [ClassFunction.conj_conj] at h
  have hdiffsuppχ : ((OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      - OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_member_conjDiff_supported hG hχS
  have hχψb : ClassFunction.inner (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχfam
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hχfam)
      (fun h => sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hχS h.symm)
  have hχbψ : ClassFunction.inner (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hχfam) hχfam
      (fun h => sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hχS h)
  have hχχne : ClassFunction.inner (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      ≠ 0 := by
    rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hχfam).1]
    exact_mod_cast (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hχfam).2.ne'
  have hχbχbne : ClassFunction.inner (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      ≠ 0 := by
    have hcf := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate
      (⊥ : Subgroup ↥hyp.S) hχfam
    rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hcf).1]
    exact_mod_cast (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hcf).2.ne'
  have hψ_S1 : ∀ x ∈ S₂, ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) x
      = 0 := fun x hx =>
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hχS (hS₂S hx)
      (fun h => hχnotS₂ (h ▸ hx))
  have hψbar_S1 : ∀ x ∈ S₂, ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj x
      = 0 := fun x hx =>
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG)
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hχS) (hS₂S hx)
      (fun h => hχcnotS₂ (h ▸ hx))
  -- (7) scaled-difference supports (honest `A(S)`), `ZIrr`-integrality, generation clauses.
  have hmemdegdiffsupp : ∀ i : Fin k, i ∈ (Finset.univ : Finset (Fin k)) →
      ((χmem i - deg i • χmem i₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) := fun i _ =>
    hyp.sSet_scaledDiff_support hG (hmemsSet i) (hmemsSet i₁) (hdeg_anchor i)
  have hdiffasuppχ : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      - e • χmem i₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_scaledDiff_support hG hχS (hmemsSet i₁) hψdeg
  have htau1ψ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        - e • χmem i₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported (hyp.dadeHypS hG)
      (hyp.dadeHypS_hconj hG) hdiffasuppχ
      (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hχfam)
        (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hmemfam i₁)) e))
  have hcover : ∀ x ∈ S₂, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
      hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : ((OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
        : ↥hyp.S → ℂ) 1
      = (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        : ↥hyp.S → ℂ) 1 := by
    rw [ClassFunction.conj_apply, hχdeg]; exact star_natCast _
  have hχ₁ne : (χmem i₁ : ↥hyp.S → ℂ) 1 ≠ 0 := by
    rw [hχ₁deg]
    exact Nat.cast_ne_zero.mpr
      (Nat.mul_pos (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos caseA.a_pos).ne'
  have h1A : (1 : ↥hyp.S)
      ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simpa using honestTypeP2ASet_one_not_mem (M := hyp.S)
  have hgen :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (χ := OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      (chibar := (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj)
      (chi1 := χmem i₁) (a := e)
      hSgen hψdeg hbar1 hχ₁ne h1A
  -- (8) the decomposition supply from the case-agnostic `R`-family (break `Da`, per-member `D`).
  have hχaeχ1 : ClassFunction.inner (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
      (e • χmem i₁ : ClassFunction ↥hyp.S ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ e (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hψ_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  have hχbaraeχ1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
      (e • χmem i₁ : ClassFunction ↥hyp.S ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ e (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hψbar_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  obtain ⟨Da, hDatau1, hDaimg⟩ :=
    hyp.sSet_breakPsiDecomp hG hnoV hχS hdiffasuppχ htau1ψ hχaeχ1 hχbaraeχ1 hχψb
  have memberDatum := fun j : Fin k =>
    hyp.sSet_memberPsiDecomp hG hnoV cohS₂ (hmemsSet j) (hmemS1set j) (hS₂conj (hmemS1set j))
  have hortho_mem : ∀ i (_ : i ∈ (Finset.univ : Finset (Fin k))),
      ((memberDatum i).1).imageFamily.Orthogonal Da.imageFamily := by
    intro i _
    rw [(memberDatum i).2.1, hDaimg]
    exact hyp.sSet_memberRFamily_orthogonal hG hnoV (hmemsSet i) hχS
      (sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hmemsSet i) hχS
        (fun h => hχnotS₂ (h ▸ hmemS1set i)))
      (sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hmemsSet i)
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hχS)
        (fun h => hχcnotS₂ (h ▸ hmemS1set i)))
  -- (9) fire the norm-weighted (5.6) engine (contrapositive of `xAdjoinStepW_k`).
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSqNormBound_of_not_coherentW_k
    (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) cohS₂
    (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))
    hdiffsuppχ hχχne hχbχbne hχψb hχbψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    hmemdegdiffsupp (fun j _ => hmemS1set j)
    (fun j => (ClassFunction.inner (χmem j) (χmem j)).re) (fun j _ => hmcpos j)
    (fun i _ j _ => hmemortho i j) hanchorNorm
    (fun i _ => (memberDatum i).1)
    Da hDatau1 hortho_mem (fun i _ => (memberDatum i).2.2)
    hdiffasuppχ htau1ψ ha1 hSgen hgen hnc
  -- (10) rescale `sumnS F ≤ sumnS 𝒮₂ = (qa)²·∑ deg²/‖·‖² ≤ (qa)²·2e = 2q²a·d`.
  refine ⟨d, hχdeg, hdu, ?_⟩
  intro F hF
  have hFsub : F ⊆ hS₂fin.toFinset := fun ψ hψ => hS₂fin.mem_toFinset.mpr (hF hψ)
  have henum : OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset
      = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := by
    rw [OddOrder.Peterfalvi.S07.sumnS,
      show hS₂fin.toFinset = (Set.range χmem).toFinset by
        ext ψ; rw [Set.Finite.mem_toFinset, Set.mem_toFinset, hrange],
      OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hinj]
  have hsnorm : ∀ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j)
      = ((deg j : ℝ) * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ)) ^ 2
        / (ClassFunction.inner (χmem j) (χmem j)).re := by
    intro j
    unfold OddOrder.Peterfalvi.S07.Snorm
    congr 1
    rw [hdeg j, Complex.natCast_re]; push_cast; ring
  calc OddOrder.Peterfalvi.S07.sumnS F
      ≤ OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset :=
        OddOrder.Peterfalvi.S07.sumnS_le_of_subset hFsub
    _ = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := henum
    _ = ∑ j : Fin k, ((deg j : ℝ) * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ)) ^ 2
          / (ClassFunction.inner (χmem j) (χmem j)).re :=
        Finset.sum_congr rfl (fun j _ => hsnorm j)
    _ = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2
          * ∑ j : Fin k, (deg j : ℝ) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2 * (2 * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
        rw [hde]; push_cast; ring

end OddOrder.Peterfalvi.S15
