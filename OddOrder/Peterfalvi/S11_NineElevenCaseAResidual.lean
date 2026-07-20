/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_PivotCoherence
import OddOrder.Peterfalvi.S11_NineElevenSubcoherentBridge
import OddOrder.Peterfalvi.S11_NineElevenBridgeBase
import OddOrder.Peterfalvi.S11_NineElevenRFamily
import OddOrder.Peterfalvi.S10_SubcoherentTypeP
import OddOrder.Peterfalvi.S11_MaximalII_III_IV.ThetaCountAssembly
import OddOrder.Peterfalvi.S11_NineElevenCoherence
import OddOrder.Peterfalvi.S11_NineElevenTwoSummand
import OddOrder.Peterfalvi.S11_NineElevenTIWitness
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

/-!
# The case (9.7.a) residual chain — §9 level

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8 (8.15.3) and §9 (9.5), pp. 47-51 (issue 1045).

Peterfalvi gets the base coherence used by (9.11) from **(8.15.3)**: the family `𝒮` of §9 is a
conjugation-closed set of induced characters to which Hypothesis (5.2) applies, and (5.7)
(`S07.coherent_subset_of_constant_degree`) then makes any constant-degree subfamily coherent.
The repo instead routed that through the §10 μ-grid engine
(`S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`), which is what tied the (9.11) chain to
the §10/§11 packaging and hence to types III/IV.

This file supplies the missing link — that §9's family is a subfamily of the (8.15.3) one:

* §9 (9.5) family: `𝒮(Y) = {Ind_{HU}^M χ | χ ∈ Irr(HU), H ⊄ Ker χ, Y ⊆ Ker χ}` (`S11.sOf`);
* (8.15.3) family: `{Ind_{M'}^M θ | θ ∈ Irr M', M_σ ⊄ Ker θ}` (`S10.inducedNonKernelFamily`).

They induce from the *same* subgroup, since `HU = M'` (`huSub_eq_derivedInG_subgroupOf`,
Peterfalvi (9.2)); and §9's filter is the *stronger* one, since `M_F ≤ M_σ`
(`BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`) makes `M_F ⊄ Ker χ` imply `M_σ ⊄ Ker χ`.

⚠ In types III/IV, `M_s = M'`, so (8.15.3)'s filter degenerates to `θ ≠ 1` and §9's family is
strictly narrower; the containment still runs the direction we need.

⚠ **Why a separate leaf**: `S10_SubcoherentTypeP` (where `inducedNonKernelFamily` lives) and
`S11_MaximalII_III_IV.*` (where `sOf` lives) are *sibling* modules — neither imports the other.
Putting the bridge in the §8 file would make an §8 module import §9, reintroducing exactly the
layering inversion that issues 1045/1046 removed.
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.7) at the uniform degree `qu`: `𝒮₃` is coherent, at §9 level** — the §9 form of
`S13.caseA_sThree_coherent`, supplying the `τ₃` of the (9.11.6) dichotomy.

`𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂` has uniform degree `qu` (`hS3deg`), is conjugation-closed (`𝒮(H₀C′)` is, and
`𝒮₂` is), has no real members (odd order), and its equal-degree differences are `A₀`-supported —
so the norm-general (5.7) engine applies with the §9 `R`-family dispatch in place of the §10 one.

Structurally identical to `sOf_caseB_coherent`; only the family and the degree differ. -/
theorem caseA_sThree_coherent [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj46 : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj46)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  have hconjS : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      a.conj ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := by
    intro a ha
    refine ⟨sOf_closedUnderConjugate data _ ha.1, ?_⟩
    intro hc
    exact ha.2 (by simpa using hS₂conj hc)
  have hnr : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂, a ≠ a.conj := fun a ha h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _ (hIKF ha.1) h.symm
  have hsuppdiff : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ b ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ((a - b : ClassFunction ↥M ℂ)).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    intro a ha b hb
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF ha.1) (hIKF hb.1) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS3deg a ha, hS3deg b hb])
    rwa [one_smul] at h
  have hN : ∃ n : ℕ, ClassFunction.inner χ₀ χ₀ = (n : ℂ) := by
    obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hχ₀.1))
    have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨(∑ x ∈ c.support, (c x) ^ 2).toNat, ?_⟩
    rw [hcsum]
    exact_mod_cast (congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)).symm
  exact OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    ((sOf_finite data (chief.H0 ⊔ cprimeSub data chief)).subset Set.sdiff_subset)
    hχ₀
    (fun η hη => sOf_memberRFamily hG hM data h46 hKeq hconj46 htau hKsupp hη.1)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF ha.1) (hIKF hb.1) hab)
    hconjS hnr hN
    (fun {φ ψ} hφ hψ => by
      rw [htau]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
        hconj46 (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ))
    (fun a ha b hb => by
      rw [htau]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        h46.dade0 hconj46 (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF ha.1))
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hb.1))))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      sOf_memberRFamily_orthogonal hG hM data h46 hKeq hconj46 htau hKsupp hVsub hφ.1 hξ.1 h1 h2)
    (fun a ha => (hS3deg a ha).trans (hS3deg χ₀ hχ₀).symm)
    (by
      rw [hS3deg χ₀ hχ₀]
      exact Nat.cast_ne_zero.mpr
        (mul_ne_zero data.nontrivial.2.1.pos.ne' (u_odd hG chars).pos.ne'))
    (fun h => (OddOrder.Peterfalvi.S04.mem_sharp.mp
      (h46.dade0.subset_sharp (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h))).2 rfl)
    (hconjS χ₀ hχ₀)
    (fun h => hnr χ₀ hχ₀ h.symm)

set_option maxHeartbeats 1600000 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8): the norm bound, at §9 level** — the §9 form of
`S13.nineElevenNormBound_of_sevenEightRefutation`, discharged up to the (9.11.7)–(9.11.8)
residual.

The (9.11.4) context `α = γ − ψ₁` is rebuilt with `γ = Ind_{HU₁}^M 1` from the TI-witness, and
`τ₃` is `caseA_sThree_coherent`.  `⟨α^τ, λ^{τ₃}⟩` is **constant** over `λ ∈ 𝒮₃`: `τ₃` agrees with
`τ` on the `A₀`-supported equal-degree differences, the Dade isometry moves the pairing to the
source, and `⟨α, λ⟩ = 0` there.  Nonzero constant ⇒ each `𝒮₄`-member's `τ₃`-image is a unit
constituent of `α^τ`, so Bessel gives `|𝒮₄| ≤ ‖α‖² = N`.  Zero constant is the book's (9.11.6)
branch, refuted by `h78`.

All the `nineElevenGamma_*` inputs were already §9-level; the only §13 pieces were the TI-witness
and `τ₃`, both descended above.  **No type hypothesis remains** — §13's `hncH0C`/`htype` served
the `H₀C′ ≤ H₀C` step for `𝒮₄ ⊆ 𝒮₃`, definitional here. -/
theorem caseA_normBound_of_sevenEightRefutation [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj46 : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj46)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    (h78 : CaseASevenEightRefutation caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :
    CaseANormBound caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
  set A0 : Set ↥M := OddOrder.Peterfalvi.S04.supportInSubgroup
    (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M with hA0def
  obtain ⟨c₃⟩ := caseA_sThree_coherent hG hM chars h46 hKeq hconj46 htau hKsupp hVsub
    hS₂conj hS₃ne hS3deg
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, hTI⟩ := caseA_nineElevenTwo_tiWitness caseA hS3deg hS2deg
  have hUpU₁ : uprimeSub data ≤ U₁ := by
    have h : cSub data chief = uprimeSub data := hCUprime
    rw [← h]; exact hCU₁
  have hrelne : (uprimeSub data).relIndex data.U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have h1 := Nat.pos_of_ne_zero hrelne
    have h2 : 0 < (chief.p - 1) * ((uprimeSub data).relIndex data.U) := Nat.mul_pos (by omega) h1
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  have hψ₁sOfC' : ψ₁ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := sOf_antitone data hle hψ₁sOf
  have hψ₁S₂ : ψ₁ ∈ S₂ := hS₁sub ⟨hψ₁sOfC', hψ₁irr, hψ₁deg⟩
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hindEqζ : induceHU data (ζ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := rfl
  set K : Subgroup ↥M := data.H.subgroupOf M ⊔ U₁.subgroupOf M with hKdef
  set γ : ClassFunction ↥M ℂ := ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγsupp : γ.support ⊆ (huSub data : Set ↥M) := nineElevenGamma_support data hU₁U
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := nineElevenGamma_mem_ZIrr data U₁
  have hγ1 : γ (1 : ↥M) = ((data.q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one data hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  have hγorth : ∀ φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief),
      ClassFunction.inner γ φ = 0 := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    have hξxi : ξ ∈ xiSet data := xiOf_subset_xiSet data _ hξ
    have hindEqξ : induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ξ : ClassFunction ↥(huSub data) ℂ) := rfl
    rw [hindEqξ]
    exact nineElevenGamma_inner_induceHU data hU₁U hξxi
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := hγorth ψ₁ hψ₁sOfC'
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr data ζ
  obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]; push_cast; rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  have hNu : N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 := by
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  have hαsupp : ((γ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    intro x hx
    have hxmem : x ∈ γ.support ∪ ψ₁.support := ClassFunction.support_sub_subset γ ψ₁ hx
    have hxHU : x ∈ huSub data := by
      rcases hxmem with h | h
      · exact hγsupp h
      · have hψsupp : ψ₁.support ⊆ (huSub data : Set ↥M) := by
          rw [hψ₁eq, hindEqζ]
          exact ClassFunction.support_induce_subset_of_normal _ _
        exact hψsupp h
    have hx1 : x ≠ 1 := by
      intro h1
      rw [ClassFunction.mem_support, h1] at hx
      apply hx
      rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self]
    have hxM' : x ∈ (derivedInG M).subgroupOf M := by
      rwa [← huSub_eq_derivedInG_subgroupOf]
    exact hKsupp x hxM' hx1
  have hταZIrr : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁)
      ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      h46.dade0 hconj46 hαsupp hαZIrr
  have htauiso : ∀ {φ ψ : ClassFunction ↥M ℂ}, φ.support ⊆ A0 → ψ.support ⊆ A0 →
      ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau φ)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau ψ)
        = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
      hconj46 hφ hψ
  have hταnorm := htauiso hαsupp hαsupp
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  have hαorthS₃ : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner (γ - ψ₁) lam = 0 := by
    intro lam hlam
    have hψlam : ClassFunction.inner ψ₁ lam = 0 :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hψ₁sOfC') (hIKF hlam.1) (fun h => hlam.2 (h ▸ hψ₁S₂))
    rw [ClassFunction.inner_sub_left, hγorth lam hlam.1, hψlam, sub_zero]
  have hdiffsupp3 : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ lam' ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ((lam - lam' : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    intro lam hlam lam' hlam'
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF hlam.1) (hIKF hlam'.1) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS3deg lam hlam, hS3deg lam' hlam'])
    rwa [one_smul] at h
  have hconst : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ lam' ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam)
        = ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam') := by
    intro lam hlam lam' hlam'
    have hdiffsupp := hdiffsupp3 lam hlam lam' hlam'
    have hzss : (lam - lam' : ClassFunction ↥M ℂ)
        ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
          (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂) A0 :=
      OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hlam) (Submodule.subset_span hlam'),
          hdiffsupp⟩
    have hagree := c₃.extends_on_supported _ hzss
    have hiso := htauiso hαsupp hdiffsupp
    have hz : ClassFunction.inner (γ - ψ₁) (lam - lam') = 0 := by
      rw [ClassFunction.inner_sub_right, hαorthS₃ lam hlam, hαorthS₃ lam' hlam', sub_zero]
    have hsub : ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam)
        - ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam') = 0 := by
      rw [← ClassFunction.inner_sub_right, ← map_sub, hagree, hiso, hz]
    exact sub_eq_zero.mp hsub
  by_cases hc : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
        (c₃.extension lam) = 0
  · exact (h78 S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg
      hcount hFbound hS2deg c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc).elim
  · push Not at hc
    obtain ⟨lam₀, hlam₀, hlam₀ne⟩ := hc
    have hleC : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
      sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
    have hS4sub : caseASFour data chief S₂
        ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := fun ξ hξ =>
      ⟨sOf_antitone data hleC hξ.1, hξ.2.2⟩
    have hS4fin : (caseASFour data chief S₂).Finite :=
      (sOf_finite data (chief.H0 ⊔ cprimeSub data chief)).subset (fun ξ hξ => (hS4sub hξ).1)
    refine ⟨N, hNu, ?_⟩
    have hON1 : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ) = 1 := by
      intro ξ hξT
      have hξ := hS4fin.mem_toFinset.mp hξT
      have hξ3 := hS4sub hξ
      rw [c₃.extension_inner_eq ξ ξ (Submodule.subset_span hξ3) (Submodule.subset_span hξ3)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨ξ, hξ.2.1⟩ : IrreducibleCharacter ↥M) ⟨ξ, hξ.2.1⟩
      rwa [if_pos rfl] at h
    have hON2 : ∀ ξ ∈ hS4fin.toFinset, ∀ ξ' ∈ hS4fin.toFinset, ξ ≠ ξ' →
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ') = 0 := by
      intro ξ hξT ξ' hξ'T hne
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      have hξ'3 := hS4sub (hS4fin.mem_toFinset.mp hξ'T)
      rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ3) (Submodule.subset_span hξ'3)]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hξ3.1) (hIKF hξ'3.1) hne
    have hint : ∀ ξ ∈ hS4fin.toFinset, ∃ m : ℤ,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension ξ) = (m : ℂ) := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      exact ClassFunction.inner_mem_ZIrr_int hταZIrr
        (c₃.extension_mem_ZIrr ξ (Submodule.subset_span hξ3))
    have hnec : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension ξ) ≠ 0 := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      rw [hconst ξ hξ3 lam₀ hlam₀]
      exact hlam₀ne
    have hcount4 := OddOrder.Peterfalvi.S07.card_le_inner_self_re_of_orthonormal_inner_int_ne
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
      hS4fin.toFinset (fun ξ => c₃.extension ξ) hON1 hON2 hint hnec
    have hNre : (ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))).re
        = (N : ℝ) := by
      rw [hταnorm, ← hNval, Complex.natCast_re]
    rw [hNre] at hcount4
    have hcard : ((caseASFour data chief S₂).ncard : ℝ) ≤ (N : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hS4fin]
      exact hcount4
    exact_mod_cast hcard


end OddOrder.Peterfalvi.S11
