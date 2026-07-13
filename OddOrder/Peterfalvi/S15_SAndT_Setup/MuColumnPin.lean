import OddOrder.Peterfalvi.S15_SAndT_Setup.Machinery135
import OddOrder.Peterfalvi.S15_CaseACoherence

/-!
# Peterfalvi (13.3.c) — the `μ`-column pin for the coherent extension

The main part of Peterfalvi (13.3.c): the (9.11)-coherent extension `τ₁ = tau1S_ofHonest` sends the
reducible prime-`TI` column sum `μ_j = ∑_i μ_{ij}` to the aligned `η`-column sum `∑_i η_{ij}` (the
`δ_j = 1` normalization of `delta_eq_one_S`).  This is the S15-world analogue of Coq's
`FTtypeP_coherence` (`PFsection13.v:347`) and of the S11/S12-world lemma
`coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (`S13_Orthogonality`).

**Positive-definiteness pin** (issue 2035): the norm inputs `muColumn_inner_self` /
`etaColumn_inner_self` (`⟨μ_j, μ_j⟩ = ⟨∑η, ∑η⟩ = q`), the coherence isometry
(`extension_inner_eq`, `μ_j ∈ ℤ[𝒮]` by `mu_colSum_mem_sOf_H0` + `sOf_subset_sSet`), and the cross
inner product `⟨τ₁μ_j, ∑η⟩ = q` (`muColumn_tau1_inner_etaColumn`, the γ-trick, still sorried)
combine through the abstract pin `inner_pin_eq` to force `τ₁μ_j = ∑η`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c) main, the cross inner product** (issue 2035 更新 #8): `⟨τ₁ μ_j, ∑_i η_{ij}⟩
= q` (`δ_j = 1`, `delta_eq_one_S`).  ⚠ **This is NOT closeable as a standalone lemma about the
current `tau1S_ofHonest`.**  `tau1S_ofHonest = (sSet_coherent_indS_A …).some.extension` is the
`extension` of an *arbitrary* inhabitant of the data-carrying `IsCoherent Ind_S^G 𝒮 A(S)`, and that
`Nonempty` carries **no μ-column pin**: in the all-reducible (`clifford` caseB) branch the
sign-flipped map `μ_j ↦ −∑_i η_{i,finNeg j}` is an equally valid inhabitant (isometric, agreeing with
`Ind` on the `A(S)`-supported conjugate differences), for which `⟨·, ∑η_{ij}⟩ = 0 ≠ q`.  The pin is
**not invariant across coherence inhabitants**, so it must be **bundled into `sSet_coherent_indS_A`
/ `coherent_H0Cprime_S` at construction** (Coq's `typeP_TIred_coherent`, `PFsection13.v:338`) — the
real frontier (issue 2035 更新 #8: `clifford`-branchwise, caseA γ-forcing via
`sSet_coherent_extension_eq_sum_memberRFamily` + `sSet_memberRFamily_imageSet_of_red` +
`sSet_irr_memberRFamily_eta_inner`, caseB the `+`-pinned `sSet_coherent_dade_caseB`).  Once
bundled, this `sorry` is discharged by the coherence's pin component. -/
theorem Hypothesis.muColumn_tau1_inner_etaColumn [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j))
      (∑ i : Fin hyp.q, hyp.eta i j) = (hyp.q : ℂ) :=
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column pin**: the coherent extension `τ₁` sends the reducible
`μ`-column sum `μ_j = ∑_i μ_{ij}` (`j ≠ 0`) to the aligned `η`-column sum `∑_i η_{ij}` (the
`δ_j = 1` normalization).  Positive-definiteness pin: `‖τ₁μ_j‖² = ‖μ_j‖² = q = ‖∑η‖²` (isometry +
orthonormal grids `muColumn_inner_self`/`etaColumn_inner_self`) and `⟨τ₁μ_j, ∑η⟩ = q`
(`muColumn_tau1_inner_etaColumn`, the γ-trick), so `inner_pin_eq` forces `τ₁μ_j = ∑η`.

This materializes the (13.3.c)-main branch of the `CharacterDegreeData.mu_tau1_formula` /
`mu_col_tau1_eta_col_one` fields (issue 2035). -/
theorem Hypothesis.tau1S_ofHonest_muColumn_eq_etaColumn [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
      = ∑ i : Fin hyp.q, hyp.eta i j := by
  have hmem : (∑ i : Fin hyp.q, hyp.mu i j) ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S :=
    Submodule.subset_span
      (OddOrder.Peterfalvi.S11.sOf_subset_sSet _ _ (hyp.mu_colSum_mem_sOf_H0 hG chief j hj))
  have hxx : ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j))
      (hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)) = (hyp.q : ℂ) := by
    simp only [Hypothesis.tau1S_ofHonest]
    rw [(hyp.coherent_H0Cprime_S hG hnoV chief).extension_inner_eq _ _ hmem hmem,
      hyp.muColumn_inner_self]
  exact inner_pin_eq hxx (hyp.etaColumn_inner_self j)
    (hyp.muColumn_tau1_inner_etaColumn hG hnoV chief j hj) (by simp)

end OddOrder.Peterfalvi.S15
