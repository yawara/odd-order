import OddOrder.Peterfalvi.S15_SAndT_Setup.Machinery135
import OddOrder.Peterfalvi.S15_CaseACoherence

/-!
# Peterfalvi (13.3.c) — the `μ`-column pin for the coherent extension

The main part of Peterfalvi (13.3.c): the (9.11)-coherent extension `τ₁ = tau1S_ofHonest` sends the
reducible prime-`TI` column sum `μ_j = ∑_i μ_{ij}` to the aligned `η`-column sum `∑_i η_{ij}` (the
`δ_j = 1` normalization of `delta_eq_one_S`).  This is the S15-world analogue of Coq's
`FTtypeP_coherence` (`PFsection13.v:347`) and of the S11/S12-world lemma
`coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (`S13_Orthogonality`).

**Column-independence reduction to a single pivot** (issue 2035 更新 #11): the general-`j` pin
`tau1S_ofHonest_muColumn_eq_etaColumn` reduces — *sorry-free* — to the single **pivot column**
`j = 1` via the column-difference identity `tau1S_ofHonest_muColumn_diff`
(`τ₁(μ_j) − τ₁(μ_k) = ∑η_{ij} − ∑η_{ik}`).  The latter is genuine (13.3.c) content, itself
sorry-free: `τ₁` agrees with `Ind_S^G = dadeHypS` on the `A(S)`-supported column difference
(`extends_on_supported` + `sInstance_dade_eq_induce`), and the per-row prime-`TI` cross-relation
`tauS_mu_cross` (`S15_BridgeCharacter`, sorry-free) evaluates each row, summed over `i`
(`dadeHypS_muColumn_diff`, the arbitrary-column generalization of `tauS_muColumn_diff_eq`).

**The pivot pin** `tau1S_ofHonest_muColumn_pivot` (`τ₁(∑ᵢ μ_{i1}) = ∑ᵢ η_{i1}`) is the single
residual `sorry`.  ⚠ It is **not** closeable for the current `tau1S_ofHonest = (…).some.extension`:
in the all-reducible (`clifford` caseB) branch the sign-flipped map is an equally valid coherence
inhabitant (update #8's flip witness), so the pin must be **bundled into `sSet_coherent_indS_A` at
construction** (Coq's `typeP_TIred_coherent`, `PFsection13.v:338`) — caseB via the pinned glue
`coherentImageMap` (mirror of the M-side `exists_pinned_coherent_sOf_H0C_of_all_reducible`), caseA
via the γ-forcing of an irreducible member (mirror of
`coherent_sOf_H0C_extension_muColumnSum_pin_of_irr`).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **μ-column degree** (Peterfalvi (13.3.a), case-agnostic): `(∑ᵢ μ_{ij})(1) = q·u` for `j ≠ 0`.
Each per-entry `μ_{ij}(1) = u` (`mu_apply_one_eq_u`), independent of the Clifford case — the
mixed-degree members of `𝒮` in caseA are the *irreducible* `q·a`-degree ones, never the reducible
`μ`-columns. -/
theorem Hypothesis.muColumn_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1
      = (hyp.q : ℂ) * (hyp.u : ℂ) := by
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun i _ => hyp.mu_apply_one_eq_u hG i j hj),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **μ-column differences are `A(S)`-supported** (case-agnostic).  Both columns have degree `q·u`
(`muColumn_apply_one`), so `μ_j − μ_k` vanishes at `1`; each column lies in `𝒮`
(`mu_colSum_mem_sOf_H0` + `sOf_subset_sSet`) whose members are supported on `A(S) ∪ {1}`
(`sSet_member_support_subset`), so the difference avoids `{1}` and lands in `A(S)`.  The
arbitrary-column, Clifford-case-agnostic analogue of `sSet_caseB_member_diff_supported`. -/
theorem Hypothesis.muColumn_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  intro z hz
  have hz0 : ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) z ≠ 0 := hz
  have hxmem : (∑ i : Fin hyp.q, hyp.mu i j) ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  have hymem : (∑ i : Fin hyp.q, hyp.mu i k) ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief k hk)
  have hdeg : ((∑ i : Fin hyp.q, hyp.mu i j : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1
      = ((∑ i : Fin hyp.q, hyp.mu i k : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 := by
    rw [hyp.muColumn_apply_one hG j hj, hyp.muColumn_apply_one hG k hk]
  rcases ClassFunction.support_sub_subset _ _ hz with h | h
  · rcases hyp.sSet_member_support_subset hG hxmem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset hG hymem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open scoped FiniteInduce in
/-- **General-column `dadeHypS` cross-relation**: for distinct nonzero columns `j ≠ k`,
`τ_S(∑ᵢ μ_{ij} − ∑ᵢ μ_{ik}) = ∑ᵢ(η_{ij} − η_{ik})`.  The arbitrary-column generalization of
`tauS_muColumn_diff_eq` (which fixes `k` = conjugate of `j`): the honest `A(S)`-Dade agrees with the
`A₀`-Dade on the `A(S)`-supported column difference (`sInstance_dade_eq_induce` /
`sInstance_dade0_eq_induce`), and the per-row prime-`TI` `tauS_mu_cross` evaluates each summand. -/
theorem Hypothesis.dadeHypS_muColumn_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
        ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = ∑ i : Fin hyp.q, (hyp.eta i j - hyp.eta i k) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  have hAsupp := hyp.muColumn_diff_supported hG chief hj hk
  have hA0supp := hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
    (honestTypeP2ASet_subset_A0Set hyp.Sdata))
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
        ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) := by
    rw [hyp.sInstance_dade_eq_induce hG hnoV hAsupp, hyp.sInstance_dade0_eq_induce hG hnoV hA0supp]
  rw [hτeq, show ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = ∑ i : Fin hyp.q, (hyp.mu i j - hyp.mu i k) from by rw [Finset.sum_sub_distrib], map_sum]
  refine Finset.sum_congr rfl fun i _ => tauS_mu_cross hG hnoV hyp i hj hk hjk

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **τ₁ column-difference identity** (issue 2035 更新 #11, the (13.3.c) column-independence): the
(9.11)-coherent extension `τ₁ = tau1S_ofHonest` sends the reducible column difference to the aligned
`η`-column difference, `τ₁(∑ᵢ μ_{ij}) − τ₁(∑ᵢ μ_{ik}) = (∑ᵢ η_{ij}) − (∑ᵢ η_{ik})`, for distinct
nonzero `j ≠ k`.  `τ₁` agrees with `Ind_S^G = dadeHypS` on the `A(S)`-supported column difference
(`extends_on_supported`), evaluated by `dadeHypS_muColumn_diff`.  This reduces the `μ`-column pin to
a single pivot column — sorry-free. -/
theorem Hypothesis.tau1S_ofHonest_muColumn_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k) :
    hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        - hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i k)
      = (∑ i : Fin hyp.q, hyp.eta i j) - (∑ i : Fin hyp.q, hyp.eta i k) := by
  classical
  have hmemSpan : ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) :=
    ⟨Submodule.sub_mem _
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)))
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief k hk))),
      hyp.muColumn_diff_supported hG chief hj hk⟩
  rw [← map_sub, hyp.tau1S_ofHonest_extends_on_supported hG hnoV chief _ hmemSpan,
    ← hyp.sInstance_dade_eq_induce hG hnoV (hyp.muColumn_diff_supported hG chief hj hk),
    hyp.dadeHypS_muColumn_diff hG hnoV chief hj hk hjk, Finset.sum_sub_distrib]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column pin at the pivot column `j = 1`**: `τ₁(∑ᵢ μ_{i1}) =
∑ᵢ η_{i1}`.  ⚠ **Still `sorry`** — this is the single column pin the (9.11)-coherence carrier must
bundle at construction.  The flip witness of update #8 (`μ_j ↦ −∑ᵢ η_{i,finNeg j}` is an equally
valid inhabitant of `IsCoherent Ind_S^G 𝒮 A(S)` in the all-reducible caseB) shows it is **not**
invariant across `.some` inhabitants, hence not closeable for the current `tau1S_ofHonest`.  Its
discharge is the caseB pinned glue (`coherentImageMap`) / caseA γ-forcing carrier redesign of
`sSet_coherent_indS_A` (issue 2035 更新 #10–#11). -/
theorem Hypothesis.tau1S_ofHonest_muColumn_pivot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ :=
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column pin**: the coherent extension `τ₁` sends the reducible
`μ`-column sum `μ_j = ∑_i μ_{ij}` (`j ≠ 0`) to the aligned `η`-column sum `∑_i η_{ij}` (the
`δ_j = 1` normalization).  Reduced — sorry-free — to the single pivot column
(`tau1S_ofHonest_muColumn_pivot`) via the column-independence `tau1S_ofHonest_muColumn_diff`:
`τ₁ μ_j = (τ₁ μ_j − τ₁ μ_1) + τ₁ μ_1 = (∑η_{ij} − ∑η_{i1}) + ∑η_{i1} = ∑η_{ij}`.

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
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  by_cases hjp : j = ⟨1, hyp.p_prime.one_lt⟩
  · subst hjp; exact hyp.tau1S_ofHonest_muColumn_pivot hG hnoV chief
  · have hdiff := hyp.tau1S_ofHonest_muColumn_diff hG hnoV chief hj hp1 hjp
    have hpivot := hyp.tau1S_ofHonest_muColumn_pivot hG hnoV chief
    have hsplit : hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = (hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
            - hyp.tau1S_ofHonest hG hnoV chief
                (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩))
          + hyp.tau1S_ofHonest hG hnoV chief
              (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩) := by abel
    rw [hsplit, hdiff, hpivot]; abel

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c) main, the cross inner product**: `⟨τ₁ μ_j, ∑_i η_{ij}⟩ = q` (`δ_j = 1`,
`delta_eq_one_S`), now a corollary of the `μ`-column pin `tau1S_ofHonest_muColumn_eq_etaColumn`
together with the orthonormal grid norm `etaColumn_inner_self` (`⟨∑η, ∑η⟩ = q`). -/
theorem Hypothesis.muColumn_tau1_inner_etaColumn [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j))
      (∑ i : Fin hyp.q, hyp.eta i j) = (hyp.q : ℂ) := by
  rw [hyp.tau1S_ofHonest_muColumn_eq_etaColumn hG hnoV chief j hj, hyp.etaColumn_inner_self j]

end OddOrder.Peterfalvi.S15
