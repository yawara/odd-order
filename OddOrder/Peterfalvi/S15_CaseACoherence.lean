/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_NineElevenSevenEight
import OddOrder.Peterfalvi.S15_SAndT_Setup.MuColumnPin
import OddOrder.Peterfalvi.S15_SAndT_Setup.DegreesFirstSplit

/-!
# Peterfalvi (9.11.5)–(9.11.8) — the `S`-instance caseA coherence endgame and assembly

The endgame of the honest `S`-instance (9.11) campaign, on the step lemmas of
`S15_NineElevenSteps`:

* **(9.11.6)**: the norm bound `nineElevenNormBoundS` (`|𝒮₄| ≤ ‖α^τ‖²`), closed by the
  dichotomy — orthogonal branch to the (9.11.7)–(9.11.8) residual, non-orthogonal branch by
  Bessel over the `τ₃`-images.
* **(9.11.2)–(9.11.5)**: the equality-configuration refutation `nineElevenEqualityRefutationS`,
  assembled from the generic (9.11) apparatus (no `htype`/`hncH0C` gate survives the
  definitional `sSet = 𝒮(H₀C′)` dictionary).
* **squeeze + case split**: `sSet_caseA_nineElevenRefutation` → `sSet_coherent_indS_caseA` →
  `sSet_coherent_indS_A`.
* **assembly**: the honest §9 character data `mkSection11CharacterDataS_honest`
  (`tau := Ind_S^G`, support `A(S)`), the packaged coherence `coherent_H0Cprime_S`, the coherent
  extension `tau1S_ofHonest`, and its (13.2.d) engines (`induce_H_mem_zSpan_S`,
  `tau1S_ofHonest_inner_induce`, `tau1S_ofHonest_induce_mem_ZIrr`) for the (13.3)
  `CharacterDegreeData` `τ₁`-fields.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8), the norm bound — `S`-instance residual** (issue 1017; the
`S`-mirror of the M-side `S13.NineElevenNormBound` discharge
(`nineElevenNormBound_of_sevenEightRefutation` + `nineElevenSevenEightRefutation`, issue 9083
Phases D/E, both landed M-side)).  **(9.11.4)**: `α = Ind_{HU₁}^S 1 − ψ₁` is an `A(S)`-supported
virtual character with the cleared Mackey norm `N·u = (a+1)·u + (q−1)·a²` (mirror of
`caseA_nineElevenFour_norm_inputs`: the (9.11.2) TI-witness from
`S11.nineElevenTwoTIWitness_of_degree_dichotomy` at the `S`-instance degree dichotomy, the
double-coset count `S11.nineElevenGamma_inner_self_mul_u`, and `‖α‖² = ‖γ‖² + 1` via
`S11.cfnorm_sub_irreducible_orthogonal`).  **(9.11.5)–(9.11.8)**: `|𝒮₄| ≤ N = ‖α^τ‖²` — in the
orthogonal branch of the (9.11.6) dichotomy the projection budget
(`S13.exists_bridge_target_of_budget`) plus the union-pair extension
(`S13.isCoherent_union_pair_of_bridge`, suppliable via the case-agnostic `sSet_memberRFamily`)
would coherently adjoin a conjugate pair from `𝒮₄`, contradicting `hnopair`; in the
non-orthogonal branch distinct `𝒮₄`-members consume orthogonal integral slices of `α^τ` (Bessel,
`card_le_inner_self_re_of_orthonormal_inner_int_ne`).  Here `𝒮₄` is the irreducible part of the
`𝒮(H₀C)` stratum outside `𝒮₂` (the `S`-instance `nineElevenSFour`), whose `ncard` is exactly the
`S4` of the (9.11.3) class equation. -/
theorem Hypothesis.nineElevenNormBoundS [Finite G]
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
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 ∧
      {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard ≤ N := by
  classical
  haveI := hyp.finiteG
  -- ── `indS` → honest-Dade conversions for the coherence clauses (as in `nineElevenPairBoundS`)
  obtain ⟨cohS₂_indS⟩ := hS₂coh
  have hindS_dade : ∀ f : ClassFunction ↥hyp.S ℂ,
      f ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) →
      hyp.indS f = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) f := fun f hf => by
    rw [hyp.indS_apply, ← hyp.sInstance_dade_eq_induce hG hnoV
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2]
  have hS₂cohD : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) :=
    ⟨cohS₂_indS.congrMap hindS_dade⟩
  have hnopairD : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
        (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
    intro χ hχ
    rintro ⟨c⟩
    refine hnopair χ hχ ⟨c.congrMap (fun f hf => ?_)⟩
    rw [hyp.sInstance_dade_eq_induce hG hnoV
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2, hyp.indS_apply]
  -- ── `τ₃` = the (9.11.6) `𝒮₃`-coherence on the honest Dade
  obtain ⟨c₃⟩ := hyp.sSet_sThree_coherent_dade hG hnoV chars hS₂conj hS₃ne hS3deg
  -- ── the `𝒮(H₀C)`-stratum dictionary and degree dichotomy (as in the equality assembler)
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
    rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── the (9.11.4) `α = γ − ψ₁` context at the explicit TI-witness (as in the Phase-D bundle)
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hTI := cuSubOf_zero_tiWitness caseA hdich
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupS hG).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupS hG).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
      ≤ cuSubOf caseA ⟨0, hq0⟩ := by
    have hUpC : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
        = OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief := hCUprime.symm
    rw [hUpC]; exact hCU₁
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
      (hyp.toTypesIIIIIIVSetupS hG).U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have hrpos := Nat.pos_of_ne_zero hrelne
    have : 0 < (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
        (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U) :=
      Nat.mul_pos (by omega) hrpos
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  have hψ₁sSet : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    hyp.sOf_H0Uprime_subset_sSet hG chars hψ₁sOf
  have hψ₁S₂ : ψ₁ ∈ S₂ := hS₁S₂ ⟨hψ₁sSet, hψ₁irr, hψ₁deg⟩
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  -- `γ = Ind_{HU₁}^S 1` and its (9.11.4) facts
  set K : Subgroup ↥hyp.S := (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
    ⊔ (cuSubOf caseA ⟨0, hq0⟩).subgroupOf hyp.S with hKdef
  set γ : ClassFunction ↥hyp.S ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
    nineElevenGamma_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) (cuSubOf caseA ⟨0, hq0⟩)
  have hγ1 : γ (1 : ↥hyp.S) = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupS hG) hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u
          + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  -- `γ ⊥` every `𝒮`-member (`H ⊆ Ker γ` at the source, `H ⊄ Ker ξ` on `𝒳`)
  have hγorth : ∀ φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG),
      ClassFunction.inner γ φ = 0 := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    have hindEqξ : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupS hG))
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) := rfl
    rw [hindEqξ]
    exact nineElevenGamma_inner_induceHU (hyp.toTypesIIIIIIVSetupS hG) hU₁U hξ
  -- `α = γ − ψ₁`: norm split, integrality, `‖α‖² = N`, the cleared identity, support
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := hγorth ψ₁ hψ₁sSet
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) ζ
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
  have hNu : N * chars.u = (caseA.a + 1) * chars.u
      + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 := by
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  have hαsupp : ((γ - ψ₁ : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.nineElevenAlphaSupportS hG chars caseA ⟨0, hq0⟩ hψ₁sSet hψ₁deg
  -- `α^τ ∈ ℤ[Irr G]`, norm preservation
  have hταZIrr : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁)
      ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hαsupp hαZIrr
  have hταnorm : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
      = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hαsupp hαsupp
  -- ── `α ⊥ 𝒮₃` at the source
  have hαorthS₃ : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ClassFunction.inner (γ - ψ₁) lam = 0 := by
    intro lam hlam
    have hψlam : ClassFunction.inner ψ₁ lam = 0 :=
      sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hψ₁sSet hlam.1
        (fun h => hlam.2 (h ▸ hψ₁S₂))
    rw [ClassFunction.inner_sub_left, hγorth lam hlam.1, hψlam, sub_zero]
  -- ── the (9.11.6) constancy of `⟨α^τ, λ^{τ₃}⟩` over `λ ∈ 𝒮₃`
  have hconst : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ∀ lam' ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
        (c₃.extension lam)
      = ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
            ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
          (c₃.extension lam') := by
    intro lam hlam lam' hlam'
    have hdiffsupp : ((lam - lam' : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
      have h := hyp.sSet_scaledDiff_support hG hlam.1 hlam'.1 (c := 1)
        (by rw [hS3deg lam hlam, hS3deg lam' hlam', Nat.cast_one, one_mul])
      rwa [one_smul] at h
    have hzss : (lam - lam' : ClassFunction ↥hyp.S ℂ)
        ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
          (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) :=
      OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hlam) (Submodule.subset_span hlam'),
          hdiffsupp⟩
    have hagree : c₃.extension (lam - lam')
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (lam - lam') :=
      c₃.extends_on_supported _ hzss
    have hiso : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (lam - lam'))
        = ClassFunction.inner (γ - ψ₁) (lam - lam') :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hαsupp hdiffsupp
    have hz : ClassFunction.inner (γ - ψ₁) (lam - lam') = 0 := by
      rw [ClassFunction.inner_sub_right, hαorthS₃ lam hlam, hαorthS₃ lam' hlam', sub_zero]
    have hsub : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
        (c₃.extension lam)
        - ClassFunction.inner
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
              ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
            (c₃.extension lam') = 0 := by
      rw [← ClassFunction.inner_sub_right, ← map_sub, hagree, hiso, hz]
    exact sub_eq_zero.mp hsub
  -- ── the (9.11.6) dichotomy
  by_cases hc : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
        (c₃.extension lam) = 0
  · -- orthogonal branch — the (9.11.7)–(9.11.8) residual refutes
    exact (hyp.nineElevenSevenEightRefutationS hG hnoV chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂cohD
      hS₃ne hnopairD h2a hCUprime hS3deg hcount hFboundU hS2deg c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg
      hγZIrr hγ1 hγorth hαsupp hc).elim
  · -- non-orthogonal branch — the Bessel count `|𝒮₄| ≤ ‖α^τ‖² = N`
    push Not at hc
    obtain ⟨lam₀, hlam₀, hlam₀ne⟩ := hc
    have hS4sub : {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}
        ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := fun ξ hξ => ⟨hsubC hξ.1, hξ.2.2⟩
    have hS4fin : ({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂} : Set (ClassFunction ↥hyp.S ℂ)).Finite :=
      (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset (fun ξ hξ => (hS4sub hξ).1)
    refine ⟨N, hNu, ?_⟩
    have hON1 : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ) = 1 := by
      intro ξ hξT
      have hξ := hS4fin.mem_toFinset.mp hξT
      have hξ3 := hS4sub hξ
      rw [c₃.extension_inner_eq ξ ξ (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ3)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨ξ, hξ.2.1⟩ : IrreducibleCharacter ↥hyp.S) ⟨ξ, hξ.2.1⟩
      rwa [if_pos rfl] at h
    have hON2 : ∀ ξ ∈ hS4fin.toFinset, ∀ ξ' ∈ hS4fin.toFinset, ξ ≠ ξ' →
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ') = 0 := by
      intro ξ hξT ξ' hξ'T hne
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      have hξ'3 := hS4sub (hS4fin.mem_toFinset.mp hξ'T)
      rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ'3)]
      exact sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hξ3.1 hξ'3.1 hne
    have hint : ∀ ξ ∈ hS4fin.toFinset, ∃ m : ℤ,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
            ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
          (c₃.extension ξ) = (m : ℂ) := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      exact ClassFunction.inner_mem_ZIrr_int hταZIrr
        (c₃.extension_mem_ZIrr ξ (Submodule.subset_span hξ3))
    have hnec : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
            ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
          (c₃.extension ξ) ≠ 0 := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      rw [hconst ξ hξ3 lam₀ hlam₀]
      exact hlam₀ne
    have hcount4 := OddOrder.Peterfalvi.S13.card_le_inner_self_re_of_orthonormal_inner_int_ne
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
      hS4fin.toFinset (fun ξ => c₃.extension ξ) hON1 hON2 hint hnec
    have hNre : (ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) (γ - ψ₁))).re
        = (N : ℝ) := by
      rw [hταnorm, ← hNval, Complex.natCast_re]
    rw [hNre] at hcount4
    have hcard : (({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard : ℝ)) ≤ (N : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hS4fin]
      exact hcount4
    exact_mod_cast hcard

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.8), the `S`-instance equality-configuration refutation**
(issue 1017 step (c); the `S`-mirror of the M-side assembler
`S13.nineElevenEqualityRefutation_of_sTwoExtraction_normBound`).  The (9.11.1) squeeze in
`sSet_caseA_nineElevenRefutation` forces the *equality configuration* at any pair-refuted maximal
`𝒮₂` — `2a = p−1`, `C = U′`, every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member of degree `q·u`, the count equality
`|𝒮₁(q·a)|·a² = (p−1)·[U:U′]`, and the saturated subfamily bound `sumnS F ≤ 2q²a·u`.  This
theorem refutes that configuration.

**Assembly (no `htype`/`hncH0C` gate).**  The generic (9.11) apparatus fires directly at
`data := toTypesIIIIIIVSetupS hG`: the `𝒮(H₀C)`-stratum degree dichotomy — from `hS3deg` and the
(9.11.1) `𝒮₂ = 𝒮₁` extraction `nineElevenSTwoExtractionS` through the `sSet = 𝒮(H₀C′)`
dictionary `sSet_eq_sOf_H0Cprime` — feeds the (9.11.2) inertia identity
`S11.nineElevenTwo_two_summand_inertia` and the (9.11.3) class equation
`S11.nineElevenThree_orbit_split`; the (9.11.4)–(9.11.8) norm bound `nineElevenNormBoundS`
supplies `hnorm`/`hle`; the tau-free arithmetic core `S11.nineElevenCaseA_equality_refutation`
closes.  The M-side `htype`/`hncH0C` inputs existed only to identify the `Hypothesis M`
packaging's `H₀C′` with the generic `cprimeSub` stratum (`C_eq_cSub_of_noncoherent`); the
`S`-instance dictionary is definitional, so they vanish.  Remaining named residuals:
`nineElevenSTwoExtractionS` and `nineElevenNormBoundS`. -/
theorem Hypothesis.nineElevenEqualityRefutationS [Finite G]
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
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    False := by
  classical
  -- ── (9.11.1) `𝒮₂ = 𝒮₁`: the saturated-bound extraction (residual)
  have hS₂cut := hyp.nineElevenSTwoExtractionS hG chars caseA S₂ hS₁S₂ hS₂S h2a hCUprime
    hcount hFboundU
  have hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    fun χ hχ => (hS₂cut hχ).2.2
  -- ── dictionary: the `𝒮(H₀C)` stratum sits inside `𝒮 = 𝒮(H₀C′)` (`C′ ≤ C`)
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
    rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  -- ── the `𝒮(H₀C)`-stratum degree dichotomy (`qu` outside `𝒮₂`, `qa` inside)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── (9.11.2): the two-summand inertia identity `C = K₁ ⊓ K₂`, `[U:Kᵢ] = a`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA hdich
  -- ── (9.11.3): the class equation at `n = |𝒮₄|·q + (p−1)`
  have hS₁'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet hG chars hχ.1, hχ.2.1, hχ.2.2⟩
  have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG) := hCUprime
  have hclass := OddOrder.Peterfalvi.S11.nineElevenThree_orbit_split hG caseA hS₁'sub
    (fun χ hχ hn => hS3deg χ ⟨hsubC hχ, hn⟩) hS2deg hCU hcount
  -- ── (9.11.4)–(9.11.8): the norm bound `|𝒮₄| ≤ N` (residual)
  obtain ⟨N, hnorm, hleN⟩ := hyp.nineElevenNormBoundS hG hnoV chars caseA S₂ hS₁S₂ hS₂S hS₂conj
    hS₂coh hS₃ne hnopair h2a hCUprime hS3deg hcount hFboundU hS2deg
  -- ── numerics: `q ≥ 3` odd prime, `u ≥ 1`, `p = 2a+1`
  have hqp : ((hyp.toTypesIIIIIIVSetupS hG).q).Prime :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1
  have hqodd : Odd (hyp.toTypesIIIIIIVSetupS hG).q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)
  have hq3 : 3 ≤ (hyp.toTypesIIIIIIVSetupS hG).q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu : 1 ≤ chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  -- ── the tau-free arithmetic core closes
  exact OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu hpeq
    hK₁ hK₂ hCinf hclass rfl hnorm hleN

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1)–(9.11.8), the `S`-instance equality-configuration refutation** (issue
1017,
the sole residual of `sSet_coherent_indS_caseA`, mirroring the M-instance
`nineElevenSevenEightRefutation` / `nineElevenEqualityRefutation_of_sevenEightRefutation`).

Given a maximal proper coherent conjugation-closed `𝒮₂` with the degree-`q·a` base cut
`S₁(q·a) ⊆ 𝒮₂ ⊊ 𝒮 = sSet`, `𝒮₃ = 𝒮 ∖ 𝒮₂ ≠ ∅` and *no* conjugate pair `{χ, χ̄}` (`χ ∈ 𝒮₃`)
coherently adjoinable, derive `False`.

**Reuse map (verified STEP-1 for the assembly, issue 1017 hub note).**  Via
`sSet_eq_sOf_H0Cprime` the full family `𝒮` *is* the `H₀C′` stratum
`sOf data (chief.H₀ ⊔ chars.Cprime)`,
so the entire generic (9.11) apparatus — all phrased over `sOf data (chief.H₀ ⊔ …)`,
`{data}{chief}{chars}(caseA)`-parametrized, hence directly instantiable at `data :=
toTypesIIIIIIVSetupS hG` — applies:
* the (9.11.2)–(9.11.5) arithmetic contradiction `S11.nineElevenCaseA_equality_refutation`;
* the (9.11.1) squeeze `S11.nineElevenOne_configuration` + `S11.sumnS_irreducible_constant_degree`;
* the world-facts *from the degree dichotomy*: `S11.nineElevenTwoTIWitness_of_degree_dichotomy`
  (TI-witness), `S11.nineElevenTwo_two_summand_inertia` (inertia `C = K₁ ⊓ K₂`),
  `S11.nineElevenGamma_inner_self_mul_u` (Mackey norm), `S11.nineElevenThree_orbit_split` (class
  eq);
* the abstract projection budget `S13.exists_bridge_target_of_budget` and the (5.6.3) union-pair
  extension `S13.isCoherent_union_pair_of_bridge` for the (9.11.7)–(9.11.8) coherent-pair
  adjunction.
The genuinely `S`-specific pieces still to build are the caseA per-member Dade `R`-family (the
analogue of the M-side `sOf_H0Cprime_memberRFamily`, feeding `𝒮₃`-coherence and the coherent-image
cross-orthogonality) and the (5.6) pair-bound producer for the `indS`/`A(S)` world; the (9.11.7)–
(9.11.8) orthogonal branch is itself a residual on the M-side (issue 9083 Phase E). -/
theorem Hypothesis.sSet_caseA_nineElevenRefutation [Finite G]
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
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S))) :
    False := by
  classical
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- numeric positivity inputs of the (9.11.1) squeeze
  have hq : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hu : 0 < chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  -- strata collapse (issue 1017 step (a)): the generic (9.11) `U′`-anchor stratum is the full
  -- family
  have hcollapse : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG))
      = sSet (hyp.toTypesIIIIIIVSetupS hG) := hyp.sOf_H0_uprime_eq_sSet hG chief
  -- the degree-`qa` anchor cut over the `U′`-stratum sits inside `𝒮₂` (it is `S₁(qa) ⊆ 𝒮₂`)
  have hS1'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ :=
    fun χ hχ => hS₁S₂ ⟨hcollapse ▸ hχ.1, hχ.2.1, hχ.2.2⟩
  have hS1'fin : ({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}).Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset (fun χ hχ => hcollapse ▸ hχ.1)
  -- (9.11.5) left endpoint: `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one uniform degree-`qa` irreducibles)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hs1' : (({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard : ℝ))
        * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2
      ≤ OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset :=
    le_of_eq (by rw [Set.ncard_eq_toFinset_card _ hS1'fin, hsum1'])
  -- per-`χ` (9.11.1) squeeze: the (5.6) pair-bound + squeeze force the equality configuration
  have hconfig : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ∃ d : ℕ, ((χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * d : ℕ) : ℂ)) ∧
        (2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ d = chars.u ∧
          {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
              (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
              IsIrreducibleCharacter χ ∧
                χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
            * (caseA.a * caseA.a)
            = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
              (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U)) ∧
        (∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
          OddOrder.Peterfalvi.S07.sumnS F
            ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)) := by
    intro χ hχ
    obtain ⟨d, hχdeg, hdu, hFbound⟩ :=
      hyp.nineElevenPairBoundS hG hnoV chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh χ hχ (hnopair χ hχ)
    have hpair : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) :=
      hFbound hS1'fin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
    exact ⟨d, hχdeg,
      OddOrder.Peterfalvi.S11.nineElevenOne_configuration hG caseA hq hu hp1 hdu hs1' hpair,
      hFbound⟩
  -- extract the global equality-configuration facts from a `𝒮₃`-witness
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  obtain ⟨d₀, -, ⟨h2a, hCUprime, hd₀u, hcount⟩, hFbound₀⟩ := hconfig χ₀ hχ₀
  -- every `𝒮₃`-member has the uniform degree `qu` (the squeeze run per member)
  have hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨d, hχdeg, ⟨-, -, hdu, -⟩, -⟩ := hconfig χ hχ
    rwa [hdu] at hχdeg
  -- the saturated subfamily bound `sumnS F ≤ 2q²au`
  have hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    intro F hF
    have h := hFbound₀ F hF
    rwa [hd₀u] at h
  -- hand the equality configuration to the (9.11.2)–(9.11.8) refutation residual
  exact hyp.nineElevenEqualityRefutationS hG hnoV chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh
    ⟨χ₀, hχ₀⟩ hnopair h2a hCUprime hS3deg hcount hFboundU

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois-branch coherence of the full family `𝒮 = sSet` on `Ind_S^G`** (issue 1017,
caseA of Peterfalvi (9.11) `Ptype_core_coherence`, Coq `PFsection9.v:1484`).  In the non-Galois case
(`CliffordCaseAData`) the honest §9 family `𝒮 = sSet` is **genuinely mixed-degree**: the
degree-`q·a`
irreducibles fill `𝒮(H₀U′)` (at least `((p−1)/a)·(|U|/(a|U′|))` of them, `caseA_character_counts` /
`caseA_exists_irreducible_qa`) alongside the degree-`q·u` members of `𝒮(H₀C)` (the `p−1` reducible
μ_j residues plus an irreducible).  Because the degrees genuinely differ (`q·a ≠ q·u`), this is
**not** the uniform-degree Galois route (caseB `sSet_coherent_indS_caseB`,
`uniform_degree_coherence_of_families`): it is Peterfalvi's (9.11) **maximal-coherent-subfamily
refutation**, mirroring the M-instance non-Galois assembly (`S11_NineElevenAlphaBound.lean`), not
the
uniform fold `caseB_coherent_sOf_H0Cprime_of_mixed`.

Honest route via `coherent_of_maximal_coherent_pair_refuted` (`S07_Subcoherent.lean:702`):
* **base** = the degree-`q·a` irreducible cut `S₁(q·a)` is the coherent conjugation-closed prefix
  (`sSetIrrDeg_qa_coherent_indS_caseA`, **landed sorry-free** modulo the accepted `dadeHypS` Dade
  foundation; conjugation-closure `sSetIrrDeg_closedUnderConjugate`, `q·a` positive real);
* **reduction** = the ambient family `𝒮` is finite (`sSet_finite`) and conjugation-closed
  (`sSet_closedUnderConjugate`), so a maximal proper coherent conj-closed intermediate `S₁ ⊆ 𝒮₂ ⊊ 𝒮`
  either equals `𝒮` (done) or is the (9.11) refutation target.

The reduction is landed sorry-free; the **sole residual** is the refuter, i.e. Peterfalvi's
(9.11.1)–(9.11.8) equality-configuration refutation for the honest Dade world (`indS`, `A(S)`).  The
`S`-instance-specific prerequisites for closing it (each still to be built in `b`-territory):
* the **caseA per-member Dade `R`-family** — the `CliffordCaseAData` analogue of the landed
  `sSet_caseB_memberRFamily` (`S15_CaseBReducibleCoherence.lean`), feeding the `Dmem`/`Da` of the
  (5.6) adjoining engine `xAdjoinStepW_k`;
* the **(9.11.1)–(9.11.6) squeeze assembly** for `indS`/`A(S)` — the analogue of the M-instance
  `nineElevenEqualityRefutation_of_sevenEightRefutation` (`S11_NineElevenAlphaBound.lean:1124`),
  whose
  bricks `lb0_le_lb1_of_degreeRatio_le` / `two_mul_le_of_dvd_of_odd` / `relIndex_le_relIndex_of_le`
  /
  `sumnS_of_norm_one_constant_degree` / `sumnS_le_of_subset` are already landed in
  `S07_Subcoherent`;
* the **(9.11.7)–(9.11.8) orthogonal-branch refutation** — the `S`-instance analogue of the
M-instance
  `NineElevenSevenEightRefutation` (`S11_NineElevenAlphaBound.lean:786`), which is *itself* still a
  named residual on the M-side (issue 9083 Phase E), i.e. the deepest genuinely-unlanded piece of
  the
  whole non-Galois (9.11) — not an `S`-instance-only gap. -/
theorem Hypothesis.sSet_coherent_indS_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  -- Peterfalvi (9.11) non-Galois: the maximal-coherent-subfamily refutation.  The degree-`q·a`
  -- irreducible cut `S₁(q·a)` is the coherent conjugation-closed base prefix
  -- (`sSetIrrDeg_qa_coherent_indS_caseA`, landed); `coherent_of_maximal_coherent_pair_refuted`
  -- reduces coherence of the full mixed family `𝒮 = sSet` to refuting a maximal proper coherent
  -- conjugation-closed `𝒮₂ ⊇ S₁(q·a)` with `𝒮₃ = 𝒮 \ 𝒮₂ ≠ ∅` and no adjoinable conjugate pair.
  refine OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (sSet_finite _)
    (sSet_closedUnderConjugate _)
    (hyp.sSetIrrDeg_subset_sSet hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hyp.sSetIrrDeg_closedUnderConjugate hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)
      (star_natCast _))
    (hyp.sSetIrrDeg_qa_coherent_indS_caseA hG hnoV chars caseA)
    ?_
  -- The (9.11.1)–(9.11.8) refuter (sole residual): given a maximal proper coherent
  -- conjugation-closed
  -- `𝒮₂ ⊇ S₁(q·a)` with `𝒮₃ = 𝒮 \ 𝒮₂ ≠ ∅` and *no* conjugate pair `{χ, χ̄}` (`χ ∈ 𝒮₃`) coherently
  -- adjoinable, derive `False`. Book argument: the (9.11.1) degree squeeze
  -- `lb0 = 2·q·a·χ(1) < sumnS 𝒮₂`
  -- would fire the (5.6) adjoining engine `xAdjoinStepW_k` on some `χ ∈ 𝒮₃` (contradicting
  -- `hnopair`),
  -- so every squeeze inequality `lb0 ≤ lb1 ≤ lb2 ≤ lb3 ≤ sumnS S₁′ ≤ sumnS 𝒮₂` is an equality — a
  -- configuration refuted by (9.11.7)–(9.11.8).  See the theorem docstring for the three remaining
  -- `b`-territory prerequisites (caseA `R`-family; (9.11.1)–(9.11.6) squeeze assembly for
  -- `indS`/`A(S)`;
  -- the (9.11.7)–(9.11.8) refutation, still a residual even on the M-side, issue 9083).
  intro S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair
  exact hyp.sSet_caseA_nineElevenRefutation hG hnoV chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne
    hnopair
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
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS_honest hG chief) with hA | hB
  · exact hyp.sSet_coherent_indS_caseA hG hnoV (hyp.mkSection11CharacterDataS_honest hG chief)
      hA.some
  · exact hyp.sSet_coherent_indS_caseB hG hnoV (hyp.mkSection11CharacterDataS_honest hG chief)
      hB.some

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The (9.11) coherence of `𝒮 = sSet`, pinned by the (13.3.c) `μ`-column formula** (issue 2035
更新 #17; Coq `FTtypeP_coherence`, `PFsection13.v:347`, with `typeP_TIred_coherent`'s global-sign
disjunction `PFsection13.v:338`): there is a coherent extension of `𝒮` on `Ind_S^G` whose values
on the reducible `μ`-column sums are the aligned `η`-column sums — either uniformly (`δ = 1`), or
(the `p = 3` sign-flip exception) with a global negative sign and the two nonzero columns swapped.

By-cases on an irreducible member of `𝒮`:

* **has-irr**: *any* inhabitant (`sSet_coherent_indS_A`) is pinned by the γ-trick dichotomy
  `coherentIndS_muColumn_pin_of_irr`.  A clean pivot propagates by column-independence; a flipped
  pivot forces `p = 3` (for `p ≥ 5` a third column `j₂ ∉ {0, 1, k}` makes the column-difference
  identity contradict the flip) and the columns swap.
* **all-reducible**: the constructed glue `exists_pinned_coherent_sSet_of_all_reducible` supplies
  a clean-pinned inhabitant (here arbitrary inhabitants may genuinely violate the formula — the
  `p = 3` mixed splits — so the pin must come from the construction). -/
theorem Hypothesis.sSet_coherent_indS_A_pinned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    ∃ c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S),
      (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
        c.extension (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j) ∨
      (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
        j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
        c.extension (∑ i : Fin hyp.q, hyp.mu i j) = -∑ i : Fin hyp.q, hyp.eta i j') := by
  classical
  haveI := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have hqne : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  by_cases hirr : ∃ ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG), IsIrreducibleCharacter ξ
  · -- has-irr: any inhabitant is pinned by the γ-trick dichotomy
    obtain ⟨ξ, hξ, hξirr⟩ := hirr
    obtain ⟨c⟩ := hyp.sSet_coherent_indS_A hG hnoV chief
    refine ⟨c, ?_⟩
    rcases hyp.coherentIndS_muColumn_pin_of_irr hG hnoV chief c hξ hξirr hp1 with
      hclean | ⟨k, hk0, hk1, hkconj, hflip⟩
    · exact Or.inl fun j hj =>
        hyp.coherentIndS_muColumn_eq_etaColumn_of_pivot hG hnoV chief c hclean hj
    · -- flipped pivot: `p = 3` is forced, and the two nonzero columns swap
      right
      have hμcols := hyp.muColumn_inner
      have hηcols := hyp.etaColumn_inner
      -- a flipped pivot with a third nonzero column `j₂ ∉ {0, 1, k}` is contradictory
      have hno3rd : ∀ j₂ : Fin hyp.p, j₂ ≠ ⟨0, hyp.p_prime.pos⟩ →
          j₂ ≠ ⟨1, hyp.p_prime.one_lt⟩ → j₂ ≠ k → False := by
        intro j₂ hj₂0 hj₂1 hj₂k
        have hdiff := hyp.coherentIndS_muColumn_diff hG hnoV chief c hp1 hj₂0
          (fun h => hj₂1 h.symm)
        -- inner the difference identity with the pivot `η`-column
        have hinner := congrArg (fun f => ClassFunction.inner f
          (∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩)) hdiff
        simp only [ClassFunction.inner_sub_left] at hinner
        rw [hflip, ClassFunction.inner_neg_left,
          hηcols k ⟨1, hyp.p_prime.one_lt⟩, if_neg hk1, neg_zero,
          hηcols ⟨1, hyp.p_prime.one_lt⟩ ⟨1, hyp.p_prime.one_lt⟩, if_pos rfl,
          hηcols j₂ ⟨1, hyp.p_prime.one_lt⟩, if_neg hj₂1] at hinner
        -- so `⟨c(μ_{j₂}), η-col₁⟩ = −q`; but the dichotomy at `j₂` gives `0`
        rcases hyp.coherentIndS_muColumn_pin_of_irr hG hnoV chief c hξ hξirr hj₂0 with
          hc2 | ⟨k₂, hk₂0, hk₂j₂, hk₂conj, hc2⟩
        · rw [hc2, hηcols j₂ ⟨1, hyp.p_prime.one_lt⟩, if_neg hj₂1] at hinner
          rw [sub_zero] at hinner
          exact hqne (by linear_combination -hinner)
        · have hk₂1 : k₂ ≠ ⟨1, hyp.p_prime.one_lt⟩ := by
            rintro rfl
            -- `k₂ = 1` would give `conj(μ_{j₂}) = μ_1`, i.e. `μ_{j₂} = conj(μ_1) = μ_k`
            have h1 : (∑ i : Fin hyp.q, hyp.mu i j₂ : ClassFunction ↥hyp.S ℂ)
                = (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩ :
                    ClassFunction ↥hyp.S ℂ).conj := by
              rw [← hk₂conj, ClassFunction.conj_conj]
            rw [hkconj] at h1
            have h2 := hμcols j₂ k
            rw [if_neg hj₂k, h1, hμcols k k, if_pos rfl] at h2
            exact hqne h2
          rw [hc2, ClassFunction.inner_neg_left,
            hηcols k₂ ⟨1, hyp.p_prime.one_lt⟩, if_neg hk₂1, neg_zero, sub_zero] at hinner
          exact hqne (by linear_combination -hinner)
      -- `p = 3`: otherwise `p ≥ 5` and a third column exists
      have hp3 : hyp.p = 3 := by
        by_contra hp3ne
        have h3p := hyp.three_le_p
        have hp4 : hyp.p ≠ 4 := fun h => by
          have := hyp.p_prime; rw [h] at this; norm_num at this
        have hp5 : 5 ≤ hyp.p := by omega
        have h2lt : 2 < hyp.p := by omega
        have h3lt : 3 < hyp.p := by omega
        by_cases hk2 : k = ⟨2, h2lt⟩
        · refine hno3rd ⟨3, h3lt⟩ ?_ ?_ ?_
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · rw [hk2]; intro h; exact absurd (congrArg Fin.val h) (by norm_num)
        · refine hno3rd ⟨2, h2lt⟩ ?_ ?_ ?_
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact hk2 h.symm
      refine ⟨hp3, ?_⟩
      -- with `p = 3` the nonzero columns are `1` and `k = 2`
      have hkval : (k : Fin hyp.p).val = 2 := by
        have hklt := k.isLt
        have hk0' : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
        have hk1' : k.val ≠ 1 := fun h => hk1 (Fin.ext h)
        omega
      intro j j' hj hj' hjj'
      have hjlt := j.isLt; have hj'lt := j'.isLt
      have hj0' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hj'0 : j'.val ≠ 0 := fun h => hj' (Fin.ext h)
      have hjj'' : j.val ≠ j'.val := fun h => hjj' (Fin.ext h)
      rcases show j.val = 1 ∧ j'.val = 2 ∨ j.val = 2 ∧ j'.val = 1 by omega with
        ⟨hjv, hj'v⟩ | ⟨hjv, hj'v⟩
      · -- `j` is the pivot, `j' = k`: the flip itself
        have hjp : j = ⟨1, hyp.p_prime.one_lt⟩ := Fin.ext hjv
        have hj'k : j' = k := Fin.ext (hj'v.trans hkval.symm)
        rw [hjp, hj'k]
        exact hflip
      · -- `j = k`, `j'` the pivot: transport the flip through the column difference
        have hjk : j = k := Fin.ext (hjv.trans hkval.symm)
        have hj'p : j' = ⟨1, hyp.p_prime.one_lt⟩ := Fin.ext hj'v
        rw [hjk, hj'p]
        have hdiff := hyp.coherentIndS_muColumn_diff hG hnoV chief c hp1 hk0 hk1.symm
        have : c.extension (∑ i : Fin hyp.q, hyp.mu i k)
            = c.extension (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
              - ((∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩)
                - ∑ i : Fin hyp.q, hyp.eta i k) := by
          rw [← hdiff]; abel
        rw [this, hflip]
        abel
  · -- all-reducible: the constructed glue supplies the clean pin
    push Not at hirr
    obtain ⟨c, hpivot⟩ := hyp.exists_pinned_coherent_sSet_of_all_reducible hG hnoV chief hirr
    exact ⟨c, Or.inl fun j hj =>
      hyp.coherentIndS_muColumn_eq_etaColumn_of_pivot hG hnoV chief c hpivot hj⟩

open scoped FiniteInduce in
/-- **(9.11)-coherence of the honest `S`-instance §9 data** (issue 2035 step 4; re-grounded off the
unsound `sibleyTarget_H0C`, issue 1017).  The `.choose` of the **pinned** unconditional
`sSet_coherent_indS_A_pinned`, yielding `IsCoherent Ind_S^G 𝒮 A(S)` — the Peterfalvi
(13.2.d)⇐(9.11) coherence for `𝒮(H₀C′) = 𝒮` (in the type-`P₂` `S`-instance, `H₀C′ = ⊥`) with the
genuine Dade map `τ = Ind_S^G` and the honest Dade support `A(S)` — carrying the (13.3.c)
`μ`-column formula (`tau1S_ofHonest_muColumn_formula`) **bundled at construction** (the pin is not
invariant across inhabitants, so it cannot be recovered from a bare `.some`; issue 2035 更新
#8/#17).

**This no longer routes through `coherent_H0C_commutator`/`sibleyTarget_H0C`** (the unsound (6.8)
shortcut whose target `IsCoherent Ind_S^G 𝒮 (C′)^# = IsCoherent Ind_S^G 𝒮 ∅` is uninhabited).  The
remaining gap is the honest (9.11) pair-adjoining assembly inside `sSet_coherent_indS_{caseA,caseB}`
(base coherences landed, the mixed-family lift sorried-cite), not a soundness defect. -/
noncomputable def Hypothesis.coherent_H0Cprime_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IsCoherent (hyp.mkSection11CharacterDataS_honest hG chief).tau
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport :=
  (hyp.sSet_coherent_indS_A_pinned hG hnoV chief).choose

open scoped FiniteInduce in
/-- **The coherent extension `τ₁` for the honest `S`-instance** (issue 2035 step 4): the
`.extension` of the (9.11)-coherence `coherent_H0Cprime_S`.  This is the (13.2.d) `τ₁ :
IntegralCharacterMap ↥S G` that the (13.3) degree analysis threads (the `μ_j^{τ₁}` machinery).
Now grounded on the honest `sSet_coherent_indS_A` (base coherences landed, mixed-family lift
sorried-cite), no longer on the unsound `sibleyTarget_H0C`. -/
noncomputable def Hypothesis.tau1S_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.coherent_H0Cprime_S hG hnoV chief).extension

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column formula for `τ₁ = tau1S_ofHonest`** (issue 2035; Coq
`FTtypeP_coherence`, `PFsection13.v:347`): the (9.11)-coherent extension sends every reducible
`μ`-column sum `μ_j = ∑_i μ_{ij}` (`j ≠ 0`) to the aligned `η`-column sum `∑_i η_{ij}` — either
uniformly, or (the `p = 3` sign-flip exception) with a global negative sign and the two nonzero
columns swapped.  The `.choose_spec` of the pinned carrier `sSet_coherent_indS_A_pinned`; this is
the exact shape of the `CharacterDegreeData.mu_tau1_formula` field (`Machinery135`). -/
theorem Hypothesis.tau1S_ofHonest_muColumn_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = -∑ i : Fin hyp.q, hyp.eta i j') :=
  (hyp.sSet_coherent_indS_A_pinned hG hnoV chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a)+(13.3.c), the distinguished `μ`-column for `τ₁ = tau1S_ofHonest`**
(issue 2035): a column `j ≠ 0` whose sum is induced from a linear character of `H = PC`
((13.3.a), `mu_j_isIndPC`) and whose `τ₁`-image is `±∑_i η_{i1}` — the (13.3.c) formula routed to
the `η`-column `1` (`j = 1, δ = 1` in the clean branch; the `p = 3` sign-flip exception takes
`j = 2, δ = -1`).  This is the honest supply of the `CharacterDegreeData.mu_col_tau1_eta_col_one`
field. -/
theorem Hypothesis.tau1S_ofHonest_mu_col_eta_col_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      j ≠ ⟨0, hyp.p_prime.pos⟩ ∧
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
  classical
  haveI := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨hp3, hflip⟩
  · -- clean branch: `j = 1`, `δ = 1`
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨1, hyp.p_prime.one_lt⟩ hp1
    exact ⟨⟨1, hyp.p_prime.one_lt⟩, 1, θ, hp1, Or.inl rfl, hθirr, hθ1, hθeq,
      by rw [hclean ⟨1, hyp.p_prime.one_lt⟩ hp1]; push_cast; rw [one_smul]⟩
  · -- `p = 3` sign-flip branch: `j = 2`, `δ = -1`
    have h2lt : 2 < hyp.p := by omega
    have hj2 : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    have hne : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨1, hyp.p_prime.one_lt⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨2, h2lt⟩ hj2
    refine ⟨⟨2, h2lt⟩, -1, θ, hj2, Or.inr rfl, hθirr, hθ1, hθeq, ?_⟩
    rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.p_prime.one_lt⟩ hj2 hp1 hne]
    push_cast
    rw [neg_one_smul]

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG hnoV chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG hnoV chief).extends_on_supported φ hφ
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
theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
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
Hypothesis, though only its `S'`-family shape is needed here); no prime-TI residue dichotomy is
used. -/
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
    change hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
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
    change ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      change (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
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
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
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
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG hnoV chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr`
field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG hnoV chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

open scoped FiniteInduce in
/-- **(13.2.e)+(7.2), the τ₁-extension semantics on `H`-induced differences** (issue 2035, the
honest supply for the `CharacterDegreeData.tau1S_apply_induce_sub` field): for irreducible
characters `θ, θ'` of `H = PC` with `P ⊄ Ker` (the guard the (13.5) proof carries — Peterfalvi
converts `(ζ_i − ζ_0)^{τ}` to `Ind_S^G` *only* for the `𝒮₁`-members `i ≤ n`, the `P`-kernel side
staying as the unknown `α`), `τ₁` agrees with `Ind_S^G` on the difference `Ind θ − Ind θ'`.

Assembly: both inductions lie in `ℤ[𝒮]` (`induce_H_mem_zSpan_S`, the (1.5.a) membership); `H` is
abelian ((13.2.a)) so both are degree `uq` and the difference vanishes at `1`; hence the
difference is `A(S)`-supported (`zSpan_sSet_degree_zero_support`) and `extends_on_supported`
evaluates `τ₁` as `Ind_S^G` there. -/
theorem Hypothesis.tau1S_ofHonest_apply_induce_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
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
    hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  haveI := hyp.finiteG
  -- `ℤ[𝒮]` membership of both inductions ((1.5.a))
  have hmem := hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP
  have hmem' := hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P
  have hsub : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      ∈ OddOrder.Peterfalvi.S07.zSpan
          (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupS hG)) :=
    Submodule.sub_mem _ hmem hmem'
  -- `H = PC` abelian ((13.2.a)): both inducing characters are linear, the difference has degree 0
  haveI hHcomm : IsMulCommutative ↥(hyp.H.subgroupOf hyp.S) := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hθ1 : θ 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  have hθ'1 : θ' 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ'
  have hdeg : (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') (1 : ↥hyp.S) = 0 := by
    rw [ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, hθ'1, sub_self]
  -- `A(S)`-support of the degree-0 difference, then the (13.2.d) extension evaluates as `Ind`
  exact hyp.tau1S_ofHonest_extends_on_supported hG hnoV chief _
    ⟨hsub, hyp.zSpan_sSet_degree_zero_support hG hsub hdeg⟩

end OddOrder.Peterfalvi.S15
