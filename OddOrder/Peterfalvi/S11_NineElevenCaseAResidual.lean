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


end OddOrder.Peterfalvi.S11
