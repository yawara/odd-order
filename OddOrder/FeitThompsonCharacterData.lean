import OddOrder.FeitThompsonNuGrid
import OddOrder.Peterfalvi.S13_TypeDetermination
import OddOrder.FeitThompsonPairProducer
import OddOrder.Peterfalvi.S15_HonestTypeP2A0

/-!
# Feit–Thompson Section 16 character data

Peterfalvi §§3–13 (pp. 5–68): the genuine Dade σ-integral on `W`,
the aligned `omega`/`mu` character grid, and the API consumed by the
canonical `Section16CharacterData` producer.
-/
namespace OddOrder
open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.RepresentationTheory
open scoped Pointwise

universe u

section
open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData
variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

/-! ### `tau3`: the real Dade σ-integral on `W = tp.W` (cd piece 5)

The integral character map `τ₃ : ClassFunction ↥tp.W →ₗ[ℤ] ClassFunction G` is the Peterfalvi (3.2)
σ-isometry of the **G-internal TI-cyclic structure** on `W = S ∩ T = mp.K ⊔ mp.Kstar`, supported on
the
regular set `Ẑ = W \ (W₁ ∪ W₂)` (`= S14.zTilde mp.K mp.Kstar`). It must be the genuine Dade map (not
a
formal one): `η := τ₃ ∘ ω` is consumed downstream as a real virtual character (notes 更新¹⁷). The
TI-set
fact is read off the proven `BG §14 typeP_duality` (Theorem 14.7), and the Dade isometry from the
general §4 producer `S04.Hypothesis.fullDadeIsometryData` (all local `H(a) = ⊥`, so `HConjInvariant`
is
automatic).  Named `tau3W` to avoid the `Section16CharacterData.tau3` field projection. -/

/-- The **G-internal TI-cyclic structure (3.1)** on `W = S ∩ T = mp.K ⊔ mp.Kstar`, supported on
the regular set `Ẑ = W ∖ (W₁ ∪ W₂)` (`= S14.zTilde mp.K mp.Kstar`); the TI-set fact is the proven
BG §14 `typeP_duality` (Theorem 14.7).  Extracted from `tau3W`'s local `let` as a top-level
definition so the (3.2) σ-isometry property package (`tau3W_isometry` etc., the issue-3002 grid
property supply) can be read off the `S05` lemmas. -/
noncomputable def tiCyclicW : OddOrder.Peterfalvi.S05.TICyclicHypothesis G :=
  { W := tp.W
    W1 := tp.W1
    W2 := tp.W2
    W1_le_W := by rw [tp.W_eq_join]; exact le_sup_left
    W2_le_W := by rw [tp.W_eq_join]; exact le_sup_right
    W1_nontrivial := by
      rw [tp.W1_eq_K hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
        (Subgroup.card_eq_one.mpr h)
    W2_nontrivial := by
      rw [tp.W2_eq_Kstar hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
        (Subgroup.card_eq_one.mpr h)
    W_sup := tp.W_eq_join.symm
    W_disjoint := disjoint_iff.mpr tp.W1_inf_W2_eq_bot
    W_card_coprime := by
      rw [← tp.q_eq_card_W1, ← tp.p_eq_card_W2]
      exact (Nat.coprime_primes tp.q_prime tp.p_prime).mpr (ne_of_lt tp.q_lt_p)
    W_card_odd := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card tp.W)
    W_cyclic := tp.W_cyclic
    V := (tp.W : Set G) \ ((tp.W1 : Set G) ∪ (tp.W2 : Set G))
    V_subset_sharp := by
      rintro x hx
      rw [Set.mem_sdiff] at hx
      obtain ⟨_, hxni⟩ := hx
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hxni
      change x ∈ Set.univ \ ({1} : Set G)
      refine ⟨Set.mem_univ x, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact fun h => hxni.1 (h ▸ one_mem tp.W1)
    V_subset_W := Set.sdiff_subset
    W_normalizes_V := by
      intro w v hv
      have hvW : v ∈ tp.W := hv.1
      haveI := tp.W_cyclic
      letI : CommGroup ↥tp.W := IsCyclic.commGroup
      have hcg : (w : G) * v = v * (w : G) := by
        have h := mul_comm w (⟨v, hvW⟩ : ↥tp.W)
        have := congrArg (Subgroup.subtype tp.W) h
        simpa using this
      have heq : (w : G) * v * (w : G)⁻¹ = v := by rw [hcg]; group
      rw [heq]; exact hv
    V_ti := by
      -- The `Ẑ = zTilde` TI-set fact for the canonical pair (BG Theorem 14.7).
      have hZti : OddOrder.GroupTheory.IsTISubset (BG.Ch4.S14.zTilde mp.K mp.Kstar)
          (mp.K ⊔ mp.Kstar) := by
        obtain ⟨Mst, hMstP⟩ :=
          (BG.Ch4.S14.typeP_duality hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
            mp.Kstar_eq).2.2.exists
        exact hMstP.2.2.2.2.2.1
      rw [tp.W_eq_kappa_join hG, tp.W1_eq_K hG, tp.W2_eq_Kstar hG]
      exact hZti }

/-- The full §4 Dade application for `tiCyclicW` (all local subgroups `H(a) = ⊥`, so
`HConjInvariant` is automatic). -/
noncomputable def tiCyclicWDadeApp :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (tiCyclicW hG mp tp) :=
  OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication.mk
    ((tiCyclicW hG mp tp).toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)))

/-- **The (3.2) Dade σ-integral on `W = tp.W`** (see the section header above): the σ-isometry of
`tiCyclicW`, re-viewed as an integral character map. -/
noncomputable def tau3W : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G :=
  (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp)

/-! #### The (3.2) property package of `tau3W` (issue-3002 grid property supply)

Read off the `S05` σ-isometry lemmas through the extracted `tiCyclicW`/`tiCyclicWDadeApp`;
these discharge the `tau3_*` fields of `Section16CharacterData` (and hence of
`Section16Inputs` / `S15.Hypothesis`). -/

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2), isometry part**: `tau3W` preserves the class-function inner product. -/
theorem tau3W_isometry :
    OddOrder.Peterfalvi.S07.IsIntegralIsometry (tau3W hG mp tp) :=
  (tiCyclicW hG mp tp).sigmaIntegral_isIntegralIsometry rfl (tiCyclicWDadeApp hG mp tp)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2)**: `tau3W` sends the trivial character to the trivial character. -/
theorem tau3W_trivial :
    tau3W hG mp tp (trivialClassFunction ↥tp.W) = trivialClassFunction G :=
  (tiCyclicW hG mp tp).sigmaIntegral_trivial rfl (tiCyclicWDadeApp hG mp tp)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2)**: `tau3W` sends virtual characters to virtual characters. -/
theorem tau3W_mem_ZIrr {z : ClassFunction ↥tp.W ℂ} (hz : z ∈ ZIrr ↥tp.W) :
    tau3W hG mp tp z ∈ ZIrr G :=
  (tiCyclicW hG mp tp).sigmaIntegral_mem_ZIrr rfl (tiCyclicWDadeApp hG mp tp) hz

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `tau3W` is the
identity. -/
theorem tau3W_apply_of_regular (α : ClassFunction ↥tp.W ℂ) (w : G) (hwW : w ∈ tp.W)
    (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    tau3W hG mp tp α w = α ⟨w, hwW⟩ :=
  (tiCyclicW hG mp tp).sigmaIntegral_apply_of_mem_V rfl (tiCyclicWDadeApp hG mp tp) α
    (show w ∈ (tiCyclicW hG mp tp).V from ⟨hwW, hnot⟩)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (4.3.b), full-grid orthonormality of the S-side `μ`-grid** (issues 9076/9014):
`⟨μ_{ij}, μ_{kl}⟩ = [(i,j) = (k,l)]`.  Within a column by the (1.4) family injectivity; across
columns by the certain-type cross-column distinctness `columnFamily_mu_ne`. -/
theorem muS_orthonormal (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (muS hG mp tp i j) (muS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  simp only [muS]
  rw [irreducibleCharacter_inner_eq_ite]
  by_cases hjl : j = l
  · subst hjl
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun hc => hik ((eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).injective) hc))),
        if_neg (by simp [hik])]
  · rw [if_neg ((mp.certainTypeS hG).columnFamily_mu_ne
        (fun hc => hjl ((chi2enum hG mp tp).injective hc)) _ _),
      if_neg (by simp [hjl])]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The type-`P₂` `Hypothesis46` on the `muS` producer instance** (issue 2038, the shortcut
that avoids the two-instance grid identification): a §6 `Hypothesis46 (A(S)) S` whose
`toHypothesis` is the κ-Hall instance `mp.certainTypeS` — the *same* instance whose
`columnFamily` is the `muS` grid — so the §6 certain-type engines
(`certainType_diff_supp_subset_A0`, `certainType_diff_dade_apply_eq_of_mem_V`) apply to `muS`
directly.  The `tic` reconciliations are the `W₁/W₂/K`-equalities of the two §6 instances
(`sdataS06_*`/`certainTypeS_*_eq`); the Dade data is the honest `'A0(S)`-Dade of
`dadeSupportHypothesisData_honestTypeP2A0Set`; the kernel-family subgroup is `M_σ(S)` with the
`A(S)`-covering of `mem_honestTypeP2ASet` (mirroring `S15.Hypothesis.hyp46S`). -/
noncomputable def hyp46Smp :
    OddOrder.Peterfalvi.S06.Hypothesis46
      (OddOrder.Peterfalvi.S15.honestTypeP2ASet mp.S) mp.S :=
  { toHypothesis := mp.certainTypeS hG
    dade := ((OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
          mp.S_maximal mp.S_typeP2.1 tp.Sdata).some.dade).restrict Set.subset_union_left
        (fun l _ ha => OddOrder.Peterfalvi.S15.honestTypeP2ASet_conj_mem l.2 ha)
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis tp.Sdata hG.odd
    tic_W1 := by
      change tp.Sdata.W1 = _
      rw [certainTypeS_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.K_le_S,
        tp.Sdata_W1_eq, tp.W1_eq_K hG]
    tic_W2 := by
      change tp.Sdata.W2 = _
      rw [certainTypeS_W2_eq, Subgroup.map_subgroupOf_eq_of_le (kstar_le_S hG mp),
        tp.Sdata_W2_eq, tp.W2_eq_Kstar hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.S).subgroupOf mp.S
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeS_W2_eq, ← tp.W2_eq_Kstar hG, ← tp.Sdata_W2_eq]
      refine Subgroup.subgroupOf_mono mp.S ?_
      have hW2H : tp.Sdata.W2 ≤ tp.Sdata.H := le_trans tp.Sdata.W2_le inf_le_left
      rw [tp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.S_maximal)
    subH_le_K := by
      rw [certainTypeS_K_eq]
      exact Subgroup.subgroupOf_mono mp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.S_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeS_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S15.mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.S) rfl
        have := congrArg (mp.S.subtype) hcomm
        simpa using this
    dade0 := (OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
        mp.S_maximal mp.S_typeP2.1 tp.Sdata).some.dade
    tau := ((OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
          mp.S_maximal mp.S_typeP2.1 tp.Sdata).some.dade).fullDadeIsometryData
      (OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
        mp.S_maximal mp.S_typeP2.1 tp.Sdata).some.hconj }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The Dade-free (4.6) core on the `muS` producer instance** (issue 9081): the structural
fields of `hyp46Smp` — the κ-Hall grid instance, `tic` reconciliations, `M_σ(S)` kernel family,
`A(S)`-covering, and the `L`-conjugation invariance of `A(S)`
(`honestTypeP2ASet_conj_mem`, honest) — **without** the Dade data.  The (4.7)/(4.8)-(1) support
engines (`certainType_diff_supp_subset_A0`) run on this core, so their producer applications
(`muS_diff_support`) do not require the full `A₀(S)`-Dade package bundled by `hyp46Smp`.
Both packages are axiom-clean; the split records the support theorem's true prerequisite boundary. -/
noncomputable def hyp46SmpCore :
    OddOrder.Peterfalvi.S06.Hypothesis46Core
      (OddOrder.Peterfalvi.S15.honestTypeP2ASet mp.S) mp.S :=
  { toHypothesis := mp.certainTypeS hG
    L_normalizes_A := fun l _ ha => OddOrder.Peterfalvi.S15.honestTypeP2ASet_conj_mem l.2 ha
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis tp.Sdata hG.odd
    -- The structural proofs are verbatim copies of the `hyp46Smp` fields so this core remains
    -- definitionally independent of the full `A₀(S)`-Dade package.
    tic_W1 := by
      change tp.Sdata.W1 = _
      rw [certainTypeS_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.K_le_S,
        tp.Sdata_W1_eq, tp.W1_eq_K hG]
    tic_W2 := by
      change tp.Sdata.W2 = _
      rw [certainTypeS_W2_eq, Subgroup.map_subgroupOf_eq_of_le (kstar_le_S hG mp),
        tp.Sdata_W2_eq, tp.W2_eq_Kstar hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.S).subgroupOf mp.S
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeS_W2_eq, ← tp.W2_eq_Kstar hG, ← tp.Sdata_W2_eq]
      refine Subgroup.subgroupOf_mono mp.S ?_
      have hW2H : tp.Sdata.W2 ≤ tp.Sdata.H := le_trans tp.Sdata.W2_le inf_le_left
      rw [tp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.S_maximal)
    subH_le_K := by
      rw [certainTypeS_K_eq]
      exact Subgroup.subgroupOf_mono mp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.S_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeS_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S15.mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.S) rfl
        have := congrArg (mp.S.subtype) hcomm
        simpa using this }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (4.8) conclusion (1) on the `muS` grid** (Coq `prDade_sub_TIirr_on`; the
`(13.18)` support engine in producer vocabulary): for nontrivial equal-degree columns
`j, k ≠ 0`, the `μ`-column difference `μ_{ij} − μ_{ik}` is supported in
`A₀(S) = A(S) ∪ V^S`.  The §6 support engine `certainType_diff_supp_subset_A0` applied at the
Dade-free `hyp46SmpCore` (issue 9081), whose `toHypothesis` is the `muS` instance
`mp.certainTypeS` — no grid identification needed, and no `A₀(S)`-Dade pin in the closure. -/
theorem muS_diff_support (i : Fin tp.q) {j k : Fin tp.p}
    (hj0 : j ≠ ⟨0, tp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, tp.p_prime.pos⟩)
    (hdeg : muS hG mp tp i j 1 = muS hG mp tp i k 1) :
    (muS hG mp tp i j - muS hG mp tp i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S15.honestTypeP2A0Set mp.S tp.Sdata) mp.S := by
  classical
  haveI : NeZero (Nat.card ↥(hyp46SmpCore hG mp tp).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(mp.certainTypeS hG).W1))
  have hχj : chi2enum hG mp tp j ≠ 1 := by
    intro hc
    exact hj0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  have hχk : chi2enum hG mp tp k ≠ 1 := by
    intro hc
    exact hk0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0 (hyp46SmpCore hG mp tp)
    hχj hχk (eqQ hG mp tp i) hdeg hz

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The `omegaS` are linear characters: `ω_{ij}(1) = 1`. -/
theorem omegaS_apply_one (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j 1 = 1 := by
  rw [omegaS, ClassFunction.compHom_apply, map_one]
  exact (mp.certainTypeS hG).chiColumn_apply_one _ _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Each `omegaS i j` is a virtual character of `↥tp.W` (the pullback along `gridEquivE` of an
irreducible character). -/
theorem omegaS_mem_ZIrr (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j ∈ ZIrr ↥tp.W := by
  rw [omegaS]
  exact ClassFunction.compHom_mem_ZIrr _
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i)).mem_ZIrr

/-! #### The (3.3) value semantics of `omegaS` (issue-2033 factorization supply)

Each `omegaS i j` is a *linear* character — its values are the monoid-hom values of
`omegaProdChar (w1CharEquiv (eqQ i)) (chi2enum j)` transported along `gridEquivE` — the
column-`0`/row-`0` normalizations are trivial on `W₂`/`W₁`, and the `W₁`- and `W₂`-values
are `q`-th and `p`-th roots of unity.  These five facts are the Peterfalvi (3.3) grid semantics
that the (1.10)-congruence atoms of the §13 norm cascade consume, threaded through the
matching fields of `Peterfalvi.S15.Hypothesis` (issue 2033, the 3002-pattern successor). -/

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), linearity** (issue 2033): each `ω_{ij}` is multiplicative — a linear
character of `W`.  Discharges the `omega_mul` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_mul (i : Fin tp.q) (j : Fin tp.p) (w w' : ↥tp.W) :
    omegaS hG mp tp i j (w * w') = omegaS hG mp tp i j w * omegaS hG mp tp i j w' := by
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    map_mul, Units.val_mul]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), column-`0` normalization** (issue 2033): the column-`0` grid characters
`ω_{i0}` are trivial on `W₂` (`chi2enum 0 = 1` is the trivial `W₂`-dual).  Discharges the
`omega_col_zero_apply_of_mem_W2` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_col_zero_apply_of_mem_W2 (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, chi2enum_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), row-`0` normalization** (issue 2033): the row-`0` grid characters
`ω_{0j}` are trivial on `W₁` (`w1CharEquiv 0 = 1` is the trivial `W₁`-dual).  Discharges the
`omega_row_zero_apply_of_mem_W1` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_row_zero_apply_of_mem_W1 (j : Fin tp.p) (w : ↥tp.W) (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, eqQ_zero hG mp tp,
    (mp.certainTypeS hG).w1CharEquiv_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), `W₁`-value order** (issue 2033): on `W₁` the grid values are `q`-th
roots of unity — the `W₂`-factor is trivial there and the `W₁`-factor character has order
dividing `|W₁| = q`.  Discharges the `omega_pow_q_of_mem_W1` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_q_of_mem_W1 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w ^ tp.q = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  have mem := gridEquivE_mem_W1 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W1_le_W).toEquiv]
    exact cardCertainTypeS_W1 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.q = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), `W₂`-value order** (issue 2033): on `W₂` the grid values are `p`-th
roots of unity — the `W₁`-factor is trivial there and the `W₂`-factor character has order
dividing `|W₂| = p`.  Discharges the `omega_pow_p_of_mem_W2` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_p_of_mem_W2 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w ^ tp.p = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  have mem := gridEquivE_mem_W2 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W).toEquiv]
    exact cardCertainTypeS_W2 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.p = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

/-! #### The (3.2.d) completeness of the `η`-grid (issue-2034 supply)

The `omegaS`-family is `pq` *distinct* linear characters of the `pq`-element cyclic `↥tp.W`,
hence exhausts them; through `sigma_omega` the `η`-grid `tau3W (omegaS i j)` therefore
enumerates the whole `(3.5)` family `χ_{ab}`, and the S05 completeness
(`eq_zero_of_mem_V_of_inner_chiFam_eq_zero`) transfers: any class function of `G` orthogonal
to the whole `η`-grid vanishes on the regular set `Ŵ`. -/

/-- The underlying linear character of `omegaS i j`, as a monoid hom of `↥tp.W`. -/
noncomputable def omegaSChar (i : Fin tp.q) (j : Fin tp.p) : ↥tp.W →* ℂˣ :=
  ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
    ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)).comp
    (gridEquivE hG mp tp).toMonoidHom

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- `omegaS i j` is the `tiCyclicW`-grid character of its underlying hom. -/
theorem omegaS_eq_omega_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j
      = ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction := by
  ext w
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The row-axis underlying character is the corresponding power of the first
nonprincipal row character. -/
theorem omegaSChar_row_eq_pow (i : Fin tp.q) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩ ^ (i : ℕ) := by
  let χ := (mp.certainTypeS hG).w1CharEquiv
    (eqQ hG mp tp ⟨1, tp.q_prime.one_lt⟩)
  have hpow : (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i) = χ ^ (i : ℕ) := by
    simp [χ, OddOrder.Peterfalvi.S06.Hypothesis.w1CharEquiv,
      OddOrder.Peterfalvi.S06.cyclicPowEnum_apply, eqQ]
  unfold omegaSChar
  rw [chi2enum_zero, hpow, (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right]
  apply MonoidHom.ext
  intro w
  simp only [MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ (i : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst).comp
        (gridEquivE hG mp tp).toMonoidHom)
      (i : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The column-axis underlying character is the corresponding power of the first
nonprincipal column character. -/
theorem omegaSChar_column_eq_pow (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩ ^ (j : ℕ) := by
  let χ := chi2enum hG mp tp ⟨1, tp.p_prime.one_lt⟩
  have hpow : chi2enum hG mp tp j = χ ^ (j : ℕ) := by
    simp [χ, chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  have hzero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
    apply Fin.ext
    simp [eqQ]
  have hχ₀ : (mp.certainTypeS hG).w1CharEquiv
      (eqQ hG mp tp ⟨0, tp.q_prime.pos⟩) =
        (1 : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
          (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) := by
    rw [hzero]
    exact (mp.certainTypeS hG).w1CharEquiv_zero
  unfold omegaSChar
  rw [hpow, hχ₀,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_left,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_left]
  apply MonoidHom.ext
  intro w
  simp only [MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ (j : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd).comp
        (gridEquivE hG mp tp).toMonoidHom) (j : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The concrete Dade-grid member is the S05 sigma image of its underlying
linear character. -/
theorem tau3W_omegaS_eq_sigma_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    tau3W hG mp tp (omegaS hG mp tp i j) =
      (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
        ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j) :
          ClassFunction ↥(tiCyclicW hG mp tp).W ℂ) := by
  rw [omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]

omit [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)] [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The cyclic factor `W = W₁ ⊔ W₂` has order `|W| = q·p` (`W₁ ∩ W₂ = ⊥`, `W₁` normalizes `W₂`
since they commute). -/
theorem cardTPW : Nat.card ↥tp.W = tp.q * tp.p := by
  have hconj : ∀ x ∈ tp.W1, ∀ a ∈ tp.W2, x * a * x⁻¹ ∈ tp.W2 := by
    intro x hx a ha
    have hc : Commute x a := tp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : tp.W1 ≤ Subgroup.normalizer (tp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (tp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [tp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm
      tp.W1_inf_W2_eq_bot,
    ← tp.q_eq_card_W1, ← tp.p_eq_card_W2]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The underlying-character grid is injective: orthonormal grid characters cannot have
the same underlying linear character. -/
theorem omegaSChar_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h
  by_contra hne
  have hCF : omegaS hG mp tp i j = omegaS hG mp tp k l := by
    rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
    exact congrArg _ (congrArg _ h)
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hCF] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Exhaustion by counting**: every linear character of `↥tp.W` underlies some `omegaS i j` —
the `(i,j) ↦ omegaSChar i j` map is injective (the `omegaS` are orthonormal, hence distinct)
between types of the same cardinality `pq`. -/
theorem exists_omegaS_eq_omega (ξ : ↥tp.W →* ℂˣ) :
    ∃ (i : Fin tp.q) (j : Fin tp.p),
      omegaS hG mp tp i j = ((tiCyclicW hG mp tp).omega ξ).toClassFunction := by
  classical
  haveI : Fintype (↥tp.W →* ℂˣ) := Fintype.ofFinite _
  have hinj := omegaSChar_injective hG mp tp
  -- cardinalities agree: `|Fin q × Fin p| = pq = |W| = |Ŵ|`
  have hcardW : Nat.card ↥tp.W = tp.q * tp.p := cardTPW mp tp
  have hcardHom : Fintype.card (↥tp.W →* ℂˣ) = tp.q * tp.p := by
    haveI := tp.W_cyclic
    letI : CommGroup ↥tp.W := IsCyclic.commGroup
    haveI : NeZero ((Monoid.exponent ↥tp.W : ℂ)) := ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
    rw [← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥tp.W ℂ]
    exact hcardW
  have hsurj : Function.Surjective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
    have hbij := (Fintype.bijective_iff_injective_and_card
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2)).mpr
      ⟨hinj, by simp [hcardHom]⟩
    exact hbij.surjective
  obtain ⟨⟨i, j⟩, hij⟩ := hsurj ξ
  refine ⟨i, j, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  exact congrArg _ (congrArg _ hij)

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.9.c) for the S-side `η`-grid** (issue-3002 supply): the grid value
`η_{ij}(g) = (τ₃ω)_{ij}(g)` is a rational integer on elements `g` of order prime to `pq`.

The value is `σ(ω(ξ_{ij}))(g)` for the underlying linear character `ξ_{ij} = omegaSChar i j`
(`omegaS_eq_omega_omegaSChar` + `sigmaIntegral_apply`).  Since `ξ_{ij}` is a character of the
cyclic `W` (`|W| = pq`, `cardTPW`), its order divides `pq`, so `Coprime(orderOf g, pq)` gives
`Coprime(orderOf g, orderOf ξ_{ij})`, and the S05 (3.9.c) Galois-integrality
`exists_intCast_sigma_omega_apply` applies. -/
theorem tau3W_omegaS_intCast_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    ∃ n : ℤ, tau3W hG mp tp (omegaS hG mp tp i j) g = (n : ℂ) := by
  classical
  haveI : Fintype ↥tp.W := Fintype.ofFinite _
  -- `orderOf (omegaSChar i j) ∣ pq`: the hom `ξ` satisfies `ξ ^ |W| = 1` and `|W| = pq`.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hcop : (orderOf g).Coprime (orderOf (omegaSChar hG mp tp i j)) :=
    hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) hcop
  refine ⟨n, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  exact hn

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The principal grid character `omegaS ⟨0⟩ ⟨0⟩` is the trivial character of `↥tp.W`:
its underlying hom is `omegaProdChar (w1CharEquiv 0) (chi2enum 0) = omegaProdChar 1 1 = 1`
(`w1CharEquiv_zero`, `chi2enum_zero`), and `omega 1 = trivialClassFunction`. -/
theorem omegaS_principal_eq_trivial :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩
      = trivialClassFunction ↥tp.W := by
  have hchar : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    have h0 : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
      apply Fin.ext; simp [eqQ]
    rw [omegaSChar, h0, (mp.certainTypeS hG).w1CharEquiv_zero, chi2enum_zero]
    apply MonoidHom.ext
    intro w
    change ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar 1 1
      ((gridEquivE hG mp tp).toMonoidHom w) : ℂˣ) = 1
    rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one, MonoidHom.one_apply]
  rw [omegaS_eq_omega_omegaSChar, hchar]
  apply ClassFunction.ext
  intro w
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply]
  change ((1 : ↥tp.W →* ℂˣ) w : ℂ) = _
  rw [MonoidHom.one_apply, Units.val_one, trivialClassFunction_apply]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.9) principal value on generic elements** (issue-3002 supply): the principal
grid value `(τ₃ω)_{00}(g) = 1` for every `g` (the coprimality hypothesis is unused:
`omegaS₀₀` is the trivial character and `τ₃(1_W) = 1_G`). -/
theorem tau3W_omegaS_principal_of_coprime {g : G}
    (_hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩) g = 1 := by
  rw [omegaS_principal_eq_trivial, tau3W_trivial, trivialClassFunction_apply]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **The `eqQ` reindex commutes with index negation**: `eqQ` is a `finCongr` (value-preserving
cast along `|W₁| = q`), so the `S15.finNeg` negation on `Fin tp.q` transports to the explicit
`(w₁ − ·) % w₁` negation on `Fin |W₁|` — the index form of `w1CharEquiv_finNeg`. -/
theorem eqQ_finNeg (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
            % Nat.card ↥(mp.certainTypeS hG).W1,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
  apply Fin.ext
  simp only [eqQ, finCongr_apply, Fin.val_cast, OddOrder.Peterfalvi.S15.finNeg]
  rw [cardCertainTypeS_W1 hG mp tp]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Index negation is character inversion for the S-side grid characters** (Peterfalvi (3.5):
the grid is indexed by character powers, so `ω_{−i,−j} = ω_{ij}⁻¹`).  Assembled from the two
power-enumeration halves (`w1CharEquiv_finNeg` via the `eqQ` cast, `chi2enum_finNeg`) and the
coordinatewise inversion `omegaProdChar_inv`. -/
theorem omegaSChar_finNeg (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (omegaSChar hG mp tp i j)⁻¹ := by
  rw [omegaSChar, omegaSChar, eqQ_finNeg hG mp tp i,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i),
    chi2enum_finNeg hG mp tp j]
  -- `(ω(χ₁⁻¹, χ₂⁻¹)).comp e = (ω(χ₁, χ₂).comp e)⁻¹`: pointwise, `ℂˣ` values invert
  -- coordinatewise (`omegaProdChar` is the product of the two coordinate pullbacks).
  ext w
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
  -- the row factor's `⁻¹` sits at the (defeq) `W₁ ⊔ W₂`-form hom type, where the `simp`
  -- lemmas do not fire syntactically; close it by definitional unfolding of the pointwise inv.
  congr 1
  exact Units.val_inv_eq_inv_val _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The `eqQ` reindex intertwines row negation (`S15.finNeg`) with the character-inversion
row permutation `rowInv`: both send `i` to the index of the inverse `W₁`-character. -/
theorem eqQ_finNeg_eq_rowInv (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = OddOrder.Peterfalvi.S06.rowInv (mp.certainTypeS hG) (eqQ hG mp tp i) := by
  apply (mp.certainTypeS hG).w1CharEquiv.injective
  rw [eqQ_finNeg hG mp tp i, (mp.certainTypeS hG).w1CharEquiv_finNeg,
    OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **CF-level conjugation pairs the `ω`-grid at the negated index** (Peterfalvi (3.9.a),
character half): `ω̄_{ij} = ω_{−i,−j}` — complex conjugation inverts the linear grid character
(`galoisMap_conj_omega`), and index negation is character inversion (`omegaSChar_finNeg`). -/
theorem omegaS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (omegaS hG mp tp i j).conj
      = omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(tiCyclicW hG mp tp).W =>
      (χ : ClassFunction ↥(tiCyclicW hG mp tp).W ℂ))
    (OddOrder.Peterfalvi.S06.galoisMap_conj_omega (tiCyclicW hG mp tp)
      (omegaSChar hG mp tp i j))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, omegaSChar_finNeg,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **CF-level conjugation pairs the `μ`-grid at the negated index** (Peterfalvi (4.9)(a)):
`μ̄_{ij} = μ_{−i,−j}` — the §6 conjugation bridge `certainType_mu_conj_eq` with the two
power-enumeration index bridges (`chi2enum_finNeg`, `eqQ_finNeg_eq_rowInv`). -/
theorem muS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (muS hG mp tp i j).conj
      = muS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥mp.S =>
      (χ : ClassFunction ↥mp.S ℂ))
    (OddOrder.Peterfalvi.S06.certainType_mu_conj_eq (mp.certainTypeS hG)
      (chi2enum hG mp tp j) (eqQ hG mp tp i))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [muS, muS, chi2enum_finNeg hG mp tp j, eqQ_finNeg_eq_rowInv hG mp tp i,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **CF-level conjugation pairs the `η = τ₃∘ω` grid at the negated index** (Peterfalvi (3.9.a),
full CF form — strengthening the generic-element `tau3W_omegaS_pair_of_coprime` below):
`(τ₃ω_{ij})̄ = τ₃ω_{−i,−j}`.  `σ` intertwines the coefficientwise Galois action
(`sigma_mapRingEquiv_comm`), and conjugation inverts the grid character
(`galoisMap_conj_omega` + `omegaSChar_finNeg`). -/
theorem tau3W_omegaS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (tau3W hG mp tp (omegaS hG mp tp i j)).conj
      = tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) := by
  have hcomm := OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_mapRingEquiv_comm
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) Complex.conjAe.toRingEquiv
    ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j))
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(tiCyclicW hG mp tp).W =>
      (χ : ClassFunction ↥(tiCyclicW hG mp tp).W ℂ))
    (OddOrder.Peterfalvi.S06.galoisMap_conj_omega (tiCyclicW hG mp tp)
      (omegaSChar hG mp tp i j))
  rw [hg2] at hcomm
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, omegaSChar_finNeg,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hcomm

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.9.a) conjugate-pair symmetry on generic elements** (issue-3002 supply):
for `g` of order prime to `pq`, the `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)`
(`S15.finNeg`), `(τ₃ω)_{−i,−j}(g) = (τ₃ω)_{ij}(g)`.

Peterfalvi's (3.9.a) content: the negated-index grid character is the *inverse* linear character
(`omegaSChar_finNeg` — honest because the enumerations are **power enumerations**, Peterfalvi's
own (3.5) grid indexing), whose `ω` is the complex conjugate (`galoisMap_conj_omega`); `σ`
intertwines coefficientwise Galois action ((3.9.a), `sigma_mapRingEquiv_comm`), so
`η_{−i,−j}(g) = conj (η_{ij}(g))`; and the value `η_{ij}(g)` is a rational **integer** by (3.9.c)
(`exists_intCast_sigma_omega_apply`, `Coprime(ord g, pq)`), hence conjugation-fixed. -/
theorem tau3W_omegaS_pair_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
      = tau3W hG mp tp (omegaS hG mp tp i j) g := by
  classical
  haveI : Fintype ↥tp.W := Fintype.ofFinite _
  -- (3.9.c): the σ-value at the base index is a rational integer.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) (hg.coprime_dvd_right hdvd)
  -- the negated-index grid character is the Galois conjugate of the base one
  have homega : (tiCyclicW hG mp tp).omega (omegaSChar hG mp tp
        (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j))
      = IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv
          ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)) := by
    rw [OddOrder.Peterfalvi.S06.galoisMap_conj_omega]
    exact congrArg _ (omegaSChar_finNeg hG mp tp i j)
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
    = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply, homega,
    ← (tiCyclicW hG mp tp).sigma_mapRingEquiv_comm rfl (tiCyclicWDadeApp hG mp tp),
    OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply]
  have hv : (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction g = (n : ℂ) := hn
  rw [hv]
  exact map_intCast _ n

/-- **Peterfalvi (3.2.d), `η`-grid form** (issue-2034 supply): a class function of `G`
orthogonal to the whole grid `tau3W (omegaS i j)` vanishes on the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)`.  Transfer of the S05 completeness
`eq_zero_of_mem_V_of_inner_chiFam_eq_zero` along the exhaustion `exists_omegaS_eq_omega`
and the `σ`-grid identification `sigma_omega`. -/
theorem tau3W_omegaS_complete_vanish (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin tp.q) (j : Fin tp.p),
      ClassFunction.inner (tau3W hG mp tp (omegaS hG mp tp i j)) χ = 0)
    {w : G} (hwW : w ∈ tp.W) (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    χ w = 0 := by
  classical
  refine OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_zero_of_mem_V_of_inner_chiFam_eq_zero
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) (χ := χ) ?_ (show w ∈ _ from ⟨hwW, hnot⟩)
  intro a b
  obtain ⟨i, j, hij⟩ := exists_omegaS_eq_omega hG mp tp
    ((tiCyclicW hG mp tp).omegaProdChar a b)
  have hchi : (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (a, b)
      = tau3W hG mp tp (omegaS hG mp tp i j) := by
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar a b)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar a b] at h1
    rw [← h1, ← hij]
    change _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  rw [OddOrder.RepresentationTheory.inner_conj_symm _ χ, hchi, horth i j, star_zero]

/-! #### The (3.4)/(3.5) four-corner relation on the `η`-grid (issue-2036 supply)

`tau3W (omegaS i j)` is the `(3.5)`-family member at the hom-pair of `omegaSChar i j`; the
`(3.5)` defining relation `τ(α_{ab}) = 1 − χ_{a1} − χ_{1b} + χ_{ab}` plus the vanishing of
`τ(α)` off the `V`-saturation gives the four-corner identity
`1 − η_{i0}(x) − η_{0j}(x) + η_{ij}(x) = 0` there. -/

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Column-independence of the `omegaS`-values on `W₁` (the row character alone survives). -/
theorem omegaS_apply_of_mem_W1_col_eq (i : Fin tp.q) (j j' : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w = omegaS hG mp tp i j' w := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Row-independence of the `omegaS`-values on `W₂` (the column character alone survives). -/
theorem omegaS_apply_of_mem_W2_row_eq (i i' : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w = omegaS hG mp tp i' j w := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Values of `omegaSChar` are the `omegaS`-values. -/
theorem omegaSChar_val (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W) :
    ((omegaSChar hG mp tp i j w : ℂˣ) : ℂ) = omegaS hG mp tp i j w := by
  rw [omegaS_eq_omega_omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Row alignment**: `omegaSChar i 0` is the product character of the first component of
`omegaSChar i j`'s pair with the trivial second component. -/
theorem omegaSChar_row_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩
      = (tiCyclicW hG mp tp).omegaProdChar
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 1 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · -- on `W₁`: both equal `omegaSChar i j` there
    intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W1_col_eq hG mp tp i ⟨0, tp.p_prime.pos⟩ j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    change _ * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
      = _ * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, map_one]
  · -- on `W₂`: both are `1`
    intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_col_zero_apply_of_mem_W2 hG mp tp i w hw, Units.val_one])
    rw [h1]
    change (1 : ℂˣ) = ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w)
      * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hfst, map_one, MonoidHom.one_apply, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Column alignment**: `omegaSChar 0 j` is the product character of the trivial first
component with the second component of `omegaSChar i j`'s pair. -/
theorem omegaSChar_col_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j
      = (tiCyclicW hG mp tp).omegaProdChar 1
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_row_zero_apply_of_mem_W1 hG mp tp j w hw, Units.val_one])
    rw [h1]
    change (1 : ℂˣ) = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        ((tiCyclicW hG mp tp).wFst w)
      * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
          (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, MonoidHom.one_apply, one_mul]
  · intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W2_row_eq hG mp tp ⟨0, tp.q_prime.pos⟩ i j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    change ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w) * _
      = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wFst w) * _
    rw [hfst, map_one, map_one]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue-2036 supply): off the
conjugacy saturation of the regular set `V = W ∖ (W₁ ∪ W₂)`,
`1 − η_{i0}(x) − η_{0j}(x) + η_{ij}(x) = 0` for nonzero row and column indices — the `(3.5)`
relation `τ(α_{AB}) = 1_G − χ_{A1} − χ_{1B} + χ_{AB}` evaluated where the `V`-supported
`τ(α)` vanishes, with the `χ`-corners identified with the `η`-grid along the
`omegaSChar`-pair alignments. -/
theorem tau3W_omegaS_fourcorner_vanish (i : Fin tp.q) (j : Fin tp.p)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) (hj : j ≠ ⟨0, tp.p_prime.pos⟩) {x : G}
    (hx : x ∉ Group.conjugatesOfSet ((tiCyclicW hG mp tp).V)) :
    (1 : ℂ) - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x = 0 := by
  classical
  set A := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 with hAdef
  set B := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 with hBdef
  have hpair : (tiCyclicW hG mp tp).omegaProdChar A B = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  -- distinctness of the grid forces nontrivial components
  have hdistinct : ∀ (k : Fin tp.q) (l : Fin tp.p), (k, l) ≠ (i, j) →
      omegaSChar hG mp tp k l ≠ omegaSChar hG mp tp i j := by
    intro k l hne heq
    have hCF : omegaS hG mp tp k l = omegaS hG mp tp i j := by
      rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, heq]
    have h1 := omegaS_inner hG mp tp k i l j
    rw [hCF] at h1
    have h2 := omegaS_inner hG mp tp i i j j
    rw [h1] at h2
    have hcond : ¬ (k = i ∧ l = j) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
    rw [if_neg hcond, if_pos ⟨rfl, rfl⟩] at h2
    exact zero_ne_one h2
  have hA1 : A ≠ 1 := by
    intro h1
    refine hdistinct ⟨0, tp.q_prime.pos⟩ j (fun hp => hi (congrArg Prod.fst hp).symm) ?_
    rw [omegaSChar_col_align hG mp tp i j, ← hBdef, ← h1, hAdef]
    exact hpair
  have hB1 : B ≠ 1 := by
    intro h1
    refine hdistinct i ⟨0, tp.p_prime.pos⟩ (fun hp => hj (congrArg Prod.snd hp).symm) ?_
    rw [omegaSChar_row_align hG mp tp i j, ← hAdef, ← h1, hBdef]
    exact hpair
  -- the (3.5) relation, evaluated at `x`
  have hrel := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).2.2.2
    A B hA1 hB1
  have hvanish : (tiCyclicWDadeApp hG mp tp).tau.toDadeMap
      ((tiCyclicW hG mp tp).alpha rfl A B) x = 0 :=
    OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
      (tiCyclicWDadeApp hG mp tp).tau.toDadeIsometryData.isDadeMap (fun _ => rfl) _ hx
  -- identify the χ-corners with the η-grid
  have hcorner : ∀ (k : Fin tp.q) (l : Fin tp.p)
      (pr : ((tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        × ((tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)),
      omegaSChar hG mp tp k l = (tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2 →
      (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) pr
        = tau3W hG mp tp (omegaS hG mp tp k l) := by
    intro k l pr hchar
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar pr.1 pr.2] at h1
    rw [← h1, ← hchar, omegaS_eq_omega_omegaSChar]
    change _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  have hc11 := hcorner i j (A, B) hpair.symm
  have hcA1 := hcorner i ⟨0, tp.p_prime.pos⟩ (A, 1) (omegaSChar_row_align hG mp tp i j)
  have hc1B := hcorner ⟨0, tp.q_prime.pos⟩ j (1, B) (omegaSChar_col_align hG mp tp i j)
  have htriv := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).1
  -- evaluate at `x` and rearrange
  have hev := congrArg (fun f : ClassFunction G ℂ => f x) hrel
  rw [hvanish] at hev
  have hev' : (0 : ℂ) = 1 - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x := by
    rw [← hcA1, ← hc1B, ← hc11]
    calc (0 : ℂ) = (trivialClassFunction G
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, 1)
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (1, B)
          + (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, B)) x := hev
      _ = _ := by
        simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
          trivialClassFunction_apply]
  exact hev'.symm

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The first nonprincipal row-axis character has the full prime order `q`. -/
theorem orderOf_omegaSChar_row_base :
    orderOf
      (omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) = tp.q := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hpow : ξ ^ tp.q = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_q_of_mem_W1 hG mp tp _ _ w hw
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_col_zero_apply_of_mem_W2 hG mp tp _ w hw, one_pow]
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    rw [omegaSChar_row_eq_pow]
    exact @pow_zero (↥tp.W →* ℂˣ) _ _
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩
        ⟨0, tp.p_prime.pos⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨1, tp.q_prime.one_lt⟩ : Fin tp.q),
        (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.1 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.q_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- The first nonprincipal column-axis character has the full prime order `p`. -/
theorem orderOf_omegaSChar_column_base :
    orderOf
      (omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩) = tp.p := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hpow : ξ ^ tp.p = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_row_zero_apply_of_mem_W1 hG mp tp _ w hw, one_pow]
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_p_of_mem_W2 hG mp tp _ _ w hw
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    rw [omegaSChar_column_eq_pow]
    exact @pow_zero (↥tp.W →* ℂˣ) _ _
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩
        ⟨1, tp.p_prime.one_lt⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
        (⟨1, tp.p_prime.one_lt⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.2 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.p := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.p_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

/-- Full Galois orbit of the nonprincipal row-axis `η`-characters. -/
theorem tau3W_omegaS_row_galois_orbit (i : Fin tp.q)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩)) =
        tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hi0 : (i : ℕ) ≠ 0 := by
    intro h
    apply hi
    apply Fin.ext
    simpa using h
  have hicop : (i : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.q by
      simpa [ξ] using orderOf_omegaSChar_row_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.q_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) i.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hicop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_row_eq_pow hG mp tp i]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

/-- Full Galois orbit of the nonprincipal column-axis `η`-characters. -/
theorem tau3W_omegaS_column_galois_orbit (j : Fin tp.p)
    (hj : j ≠ ⟨0, tp.p_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩)) =
        tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    simpa using h
  have hjcop : (j : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.p by
      simpa [ξ] using orderOf_omegaSChar_column_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.p_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) j.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hjcop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_column_eq_pow hG mp tp j]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

/-- **Peterfalvi (3.9.b), vanishing transport along the row** (issue-2036 supply):
if the `η₁₀`-value vanishes at `x`, so do all nonprincipal row-axis values.  This is the
pointwise zero consequence of `tau3W_omegaS_row_galois_orbit`. -/
theorem tau3W_omegaS_row_vanish_of_one_zero {x : G}
    (h0 : tau3W hG mp tp
      (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) x = 0)
    (i : Fin tp.q) (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x = 0 := by
  obtain ⟨u, hu⟩ := tau3W_omegaS_row_galois_orbit hG mp tp i hi
  have hv := congrArg (fun f : ClassFunction G ℂ => f x) hu
  simp only [OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply, h0, map_zero] at hv
  exact hv.symm

end Section16CharacterData

end
end OddOrder
