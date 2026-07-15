/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CharacterDegreeEngines
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.OrderRelayerCore
import OddOrder.Peterfalvi.S15_SAndT_Setup.SwappedNuGridSupply

/-!
# Peterfalvi §13 (pp. 75–86) — the (13.3.b)/(13.4) dichotomy supplies

The `LambdaWitness`/`ThetaWitness` dichotomy layer over the τ₁-supply engines
(`S15_CharacterDegreeEngines.lean`, prefix-split): the (9.8.c) witnessed irreducible, the
λ/θ-witness producers on both Clifford branches, the no-λ/no-θ `T`-side (13.4) facts, the
assembled θ-package `tSide_theta_package_of_not_caseB_core`, the λ-route
`lambda_forces_T_caseB_core`, and the b-side export `T_caseB_facts_unconditional` (the
(14.9) type-II endpoint supply, issue 9094).
-/
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **`T` is type-`P₂` — the (13.2.b)-at-`T` classification gate** (precisely-named
layer-inverted cite, issue 2035 #41 / 0116-class): the honest producer is `S16.T_isTypeP2`
(`S16_NonExistenceG/TTypeII.lean`, via the type classification and the (11.9) non-Galois
exclusion chain), which sits **downstream** of this file in the import DAG (the S16 leaves
import this supply layer).  Same inversion class as the issue 0116 inventory; discharged when
the hub relocates the producer or resolves the inversion. -/
theorem Hypothesis.T_isTypeP2_gate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T := by
  sorry

open scoped FiniteInduce in
/-- **Differences of degree-one `K`-inductions are supported in `(QD)^#`** (the general-`θ'`
form of `indK_sub_nuRow_support`; the θ-package conjunct-2 companion for the conjugate pair
`Ind_K θ − Ind_K θ̄`): both terms vanish off the normal `K = QD` and share the degree
`[T:K]·1`. -/
theorem Hypothesis.indK_sub_indK_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ θ' : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1) :
    (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ').support ⊆
      {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1} := by
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hKn := hyp.K_subgroupOf_T_normal hG
  intro z hz
  have hzne : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') z ≠ 0 := hz
  refine ⟨?_, ?_⟩
  · by_contra hzK
    apply hzne
    have hzKsub : z ∉ hyp.K.subgroupOf hyp.T := fun h => hzK (Subgroup.mem_subgroupOf.mp h)
    rw [ClassFunction.sub_apply,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ hzKsub,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ' hzKsub, sub_zero]
  · intro hz1
    apply hzne
    rw [hz1, ClassFunction.sub_apply, ClassFunction.induce_apply_one, hθ1,
      ClassFunction.induce_apply_one, hθ'1, sub_self]

open scoped FiniteInduce in
/-- **The (13.2.e) `S`/`T` cross-orthogonality** (the (13.4) disjoint-support input, in
producer form): for an `H^#`-supported `α` on `S` and a `(QD)^#`-supported `β` on `T`, the
inductions to `G` are orthogonal — `(H^#)^G ∩ ((QD)^#)^G = ∅` since every `H^#`-point has
`P ≤ C_G(x)` while `(QD)^#`-centralizers lie in the `T`-conjugates, and no `P`-conjugate lies
in `T`. -/
theorem Hypothesis.inner_induce_H_QD_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {α : ClassFunction ↥hyp.S ℂ}
    (hα : α.support ⊆ {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    {β : ClassFunction ↥hyp.T ℂ}
    (hβ : β.support ⊆ {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) :
    ClassFunction.inner (ClassFunction.induce hyp.S α) (ClassFunction.induce hyp.T β) = 0 := by
  haveI := hyp.finiteG
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  exact inner_induce_induce_eq_zero_of_disjoint hα hβ hdisj

open scoped FiniteInduce in
/-- **Differences of degree-one `H`-inductions are supported in `H^#`** (the `S`-side mirror
of `indK_sub_indK_support`; the (13.4) `α`-support for the conjugate pair `λ − λ̄`). -/
theorem Hypothesis.indH_sub_indH_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1) :
    (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ').support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hHn : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  intro y hy
  have hyne : (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') y ≠ 0 := hy
  refine ⟨?_, ?_⟩
  · by_contra hyH
    apply hyne
    have hyHsub : y ∉ hyp.H.subgroupOf hyp.S := fun h => hyH (Subgroup.mem_subgroupOf.mp h)
    rw [ClassFunction.sub_apply,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ hyHsub,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ θ' hyHsub, sub_zero]
  · intro hy1
    apply hyne
    rw [hy1, ClassFunction.sub_apply, ClassFunction.induce_apply_one, hθ1,
      ClassFunction.induce_apply_one, hθ'1, sub_self]

open scoped FiniteInduce in
/-- **The `𝒮₁`-λ-witness predicate** (Pf (13.3.b)): `𝒮` contains a `uq`-degree `PC`-induced
irreducible — a linear `θ ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ` whose induction is
irreducible.  Its existence is the conditional branch of the (13.3.b) dichotomy
(`lambdaClusterData_of_irr_witness` packages it into `LambdaClusterData`); its failure is the
Galois/`C = ⊥` case. -/
def LambdaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)

open OddOrder.Peterfalvi.S11 in
/-- **(9.8.c) with the regular seed exposed**: the degree-`qu` irreducible member of `𝒮(H₀C)` from
Peterfalvi (9.8.c) is `Ind_{HU}^M(Ind_{HC}(hcPsi θ))` for a *regular* seed `θ` (nontrivial on every
Clifford summand `caseA.Hpart i`, hence `θ ≠ 1`).  Identical parity argument to
`caseA_exists_irreducible_sOf_H0C` (`exists_regular_not_reducible_of_odd` on `Xθ \ Xmu`,
`|Xμ| = p-1`, `u·|Xθ| = (p-1)^q`, `u` odd, `p-1` even), but returns the *witnessing* `θ` (needed to
recover the `Ind_{HC}(linear)` shape and route it through `isIndHC_of_source_eq_induce_hcPsi` to a
`LambdaWitness`; the bare existence hides `θ`). -/
theorem caseA_exists_irreducible_witnessed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 ∧
      (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IsIrreducibleCharacter (induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ).toClassFunction)) := by
  classical
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H := ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  have hp1_even : Even (chief.p - 1) := by
    obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
    exact ⟨k, by omega⟩
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  have hcard : (↑Xmu : Set (ClassFunction ↥(huSub data) ℂ)).ncard = chief.p - 1 := by
    rw [Set.ncard_coe_finset]; exact caseA_Xmu_card_eq caseA hG
  have hcount : chars.u * (↑Xθ : Set (ClassFunction ↥(huSub data) ℂ)).ncard
      = (chief.p - 1) ^ data.q := by
    rw [Set.ncard_coe_finset]; exact oXtheta_count caseA
  obtain ⟨ζ, hζ, hζn⟩ := exists_regular_not_reducible_of_odd Xθ.finite_toSet
    (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hcard hcount
    (Nat.sub_pos_of_lt chief.p_prime.one_lt) hp1_even (u_odd hG chars) data.nontrivial.2.1.two_le
  rw [Finset.mem_coe, hXθ, Finset.mem_image] at hζ
  obtain ⟨θ, hθ, rfl⟩ := hζ
  have hreg := (Finset.mem_filter.mp hθ).2
  have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
  refine ⟨θ, hnt, hreg, ?_⟩
  by_contra h
  refine hζn ?_
  simp only [Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image]
  exact ⟨⟨θ, hθ, rfl⟩, h⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b) caseB forward — the Singer/Galois branch witness**: an irreducible member `χ` of
the `S`-instance family `𝒮(H₀ ⊔ C')` in Clifford case (b) is a `LambdaWitness` (a `uq`-degree
`PC`-linear induced irreducible).  Mirrors the caseA branch of `S_caseB_facts_no_lambda` (which
produces the witness unconditionally from the (9.8.c) regular seed); here the source is the given
`χ = Ind_{HU} ζ`, and the reverse (13.3.a)-for-irr characterization is the pair (`C'`-kernel)
`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`: `ζ ∈ 𝒳(H₀C')` irreducible equals
`Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character (`λ` trivial on `C'`).  Flattening
(`isIndHC_of_source_eq_induce_hcPsiPair`) and the `HC.map subtype = (PC).subgroupOf S` transport
(`hcRealized_map_subtype_eq`, `toTypesIIIIIIVSetupS_cSub_eq_C`) give the linear
`θ' ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ'` whose induction (`= χ`) is irreducible.

Stated with `chief`/`caseB`/`χ`-membership as explicit arguments (no `set` inside): the caseB
branch of `S_caseB_facts_no_lambda` is then a one-line call. -/
theorem lambdaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData (hyp.mkSection11CharacterDataS hG chief))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    LambdaWitness hyp := by
  classical
  haveI := hyp.finiteG
  -- Extract the source `ζ ∈ 𝒳(H₀C')` of the given irreducible `χ = Ind_{HU} ζ`.  Done *before*
  -- any `let`, and re-cast to `data`-form so every downstream term is uniform (a `set` here would
  -- revert/rename `ζ`; the extraction stays clean because `hχmem` names the explicit terms).
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupS hG
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  -- (1) the reverse (13.3.a)-for-irr characterization: `ζ = Ind_{HC}(hcPsiPair θ̄ λ)`, `θ̄ ≠ 1`.
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  -- (2) flatten `induceHU(Ind_{HC}(hcPsiPair)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
  -- (3) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)`, which (converse (1.6.a)) pushes to
    -- `P ⊆ Ker ζ`, contradicting `ζ ∈ 𝒳` (`P = H ⊄ Ker ζ`).  Mirrors `mu_j_isIndPC_not_ker`.
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
      Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hPH θ' hker
    have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b) caseA — the unconditional branch witness**: in Clifford case (a) a `LambdaWitness`
exists unconditionally (independent of the given `χ`).  The (9.8.c) degree-`qu` irreducible member
`Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` for a *regular* seed `θ̄` (`caseA_exists_irreducible_witnessed`) is
`Ind_{PC}^S(linear irr)`: flattening (`isIndHC_of_source_eq_induce_hcPsi`) and the
`HC.map subtype = (PC).subgroupOf S` transport give the linear `θ' ∈ Irr(H.subgroupOf S)` with
`P ⊄ Ker θ'` whose induction is irreducible.

Stated with `chief`/`caseA` explicit (no `set` inside), so the caseA branch of
`S_caseB_facts_no_lambda` is a one-line call and hbridge stays `set`-free (a `set` there would
split `chief` and desync the branch calls). -/
theorem lambdaWitness_of_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData (hyp.mkSection11CharacterDataS hG chief)) :
    LambdaWitness hyp := by
  classical
  haveI := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupS hG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  -- (1) the regular seed `θbar` with irreducible `induceHU(Ind_{HC}(hcPsi θbar))`.
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  -- (2) the `S'`-source `ζ' = Ind_{HC}(hcPsi θbar) ∈ 𝒳(H₀C)` (`P ⊄ Ker ζ'`).
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  -- (3) flatten `induceHU(Ind_{HC}(hcPsi)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  -- (4) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ')` pushes to `P ⊆ Ker ζ'`,
    -- contradicting `ζ' ∈ 𝒳` (`P = H ⊄ Ker ζ'`).  Mirrors `mu_j_isIndPC_not_ker`.
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
      Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hPH θ' hker
    have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-λ (Galois) branch of the `S`-side (13.3.b) facts** (issue 9094 RULING §2, faithful
sorried bridging): if `𝒮` contains no `uq`-degree `PC`-induced irreducible (`¬ LambdaWitness`),
then by Pf (13.3.b) `M = S` is in case (9.7.b) with `C = ⊥` and `u = (p^q−1)/(p−1)` — the Galois
case.

Assembled from the §9-generic `caseB_of_no_irreducible_sOf_H0Cprime` (sorry-free) through the
S15↔S11 `Section11CharacterData` SOf-identification: an irreducible member of the `S`-instance
family `𝒮(H₀ ⊔ C')` is (13.3.a-style) a `uq`-degree `PC`-linear induced irreducible, i.e. a
`LambdaWitness`, and the `chars.C`/`chars.u` conclusion transports to `hyp.C`/`hyp.u`
(`toTypesIIIIIIVSetupS_cSub_eq_C`).  That identification is the deep (13.3.b) forward bridge
(S15↔S11, multi-session); until it lands this is the honest, precisely-named gate. -/
theorem S_caseB_facts_no_lambda [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnolam : ¬ LambdaWitness hyp) :
    hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  haveI := hyp.finiteG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  -- **(13.3.b) forward, the one isolated genuine gate**: an irreducible member of the `S`-instance
  -- family `𝒮(H₀ ⊔ C')` is a `uq`-degree `PC`-linear induced irreducible — a `LambdaWitness`.
  -- (The reducible members are `Ind_{HC}` linear by `caseB_reducible_sOf_H0_isIndHC`; the
  -- irreducible ones — the `λ`-candidates — need the (13.3.a)-for-irr characterization, the
  -- multi-session S15↔S11 assembly.)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → LambdaWitness hyp := by
    intro χ _hχmem _hχirr
    -- `set`-free case split: a `set data`/`set chars` here would split the (externally obtained)
    -- `chief` into a folded copy plus a stray `chief✝`, desyncing `_hχmem` from `caseB`.  Both
    -- branches are `set`-free standalone witnesses (`lambdaWitness_of_caseA` / `_of_caseB_member`),
    -- each doing its own `let data` internally, so hbridge passes one pristine `chief`.
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · -- **caseA**: a `LambdaWitness` exists unconditionally (ignore `χ`) — the (9.8.c) degree-`qu`
      -- irreducible `Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` is `Ind_{PC}^S(linear irr)`.
      obtain ⟨caseA⟩ := hA
      exact lambdaWitness_of_caseA hG hyp chief caseA
    · -- **caseB** (Singer/Galois, `U` irreducible on `H̄`): the given irreducible `χ = Ind_{HU} ζ`
      -- (`ζ ∈ 𝒳(H₀C')`) is `Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character
      -- (`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`); `lambdaWitness_of_caseB_member` flattens and
      -- transports it to the `Ind_{PC}(linear irr)` = `LambdaWitness` shape.
      obtain ⟨caseB⟩ := hB
      exact lambdaWitness_of_caseB_member hG hyp chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnolam (hbridge χ hmem hirr)
  obtain ⟨-, hCbot, hufull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataS hG chief) hno
  refine ⟨?_, ?_⟩
  · -- `chars.C = cSub = hyp.C` (`toTypesIIIIIIVSetupS_cSub_eq_C`)
    rw [← hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    exact hCbot
  · -- transport `chars.u = (chief.p^data.q − 1)/(chief.p − 1)` to `hyp.u = (p^q − 1)/(p − 1)`
    rw [← hyp.mkSection11CharacterDataS_u_eq hG chief, hufull, hyp.chiefFactorS_p_eq hG chief,
      hyp.toTypesIIIIIIVSetupS_q_eq hG]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.b) dichotomy, the `S`-side keystone producer** (issue 9094 RULING 案 A/§2):
either `𝒮` contains the honest λ-cluster (`Nonempty (LambdaClusterData hyp)`), or `M = S` is in
the Galois case (`C = ⊥`, `u = (p^q−1)/(p−1)`).  This is the producer every λ-independent
consumer of the legacy `character_degree_analysis` threads: the λ-branch supplies the
`LambdaClusterData` (against the unconditional `CharacterDegreeCore`), the no-λ branch supplies
the (13.10)-arithmetic inputs `C = ⊥ ∧ u = full`.

The case-split is `LambdaWitness hyp` (`Classical.em`): the λ-branch is
`lambdaClusterData_of_irr_witness`, the no-λ branch is `S_caseB_facts_no_lambda`. -/
theorem lambdaCluster_or_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LambdaClusterData hyp) ∨
      (hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    exact Or.inl (hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind)
  · exact Or.inr (S_caseB_facts_no_lambda hG hyp hlam)

/-! ## The (13.3.b)-at-`T` θ-witness dichotomy

The `T`-side mirror of the `LambdaWitness` machinery (`S15_CharacterDegreeSupply`): a
`ThetaWitness` is a `vp`-degree `QD`-linear induced irreducible of `T` — Peterfalvi's
"`𝒯` contains an irreducible character of degree `vp` induced from a linear character of
`QD`" ((13.3.b)/(13.4)).  Its failure forces the Galois case `D = ⊥`,
`v = (q^p−1)/(q−1)` (`T_caseB_facts_no_theta`); contrapositively, `¬(13.4-caseB)` produces
the witness (`thetaWitness_of_not_caseB`) — the θ of the (13.4) proof. -/

open scoped FiniteInduce in
/-- **The `T`-side (13.3.b) witness shape**: a linear character of `K = QD` not containing
`Q` in its kernel whose induction to `T` is irreducible (a `vp`-degree `QD`-linear induced
irreducible).  Mirror of `LambdaWitness`. -/
def ThetaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseB forward — the Singer/Galois branch witness**: an irreducible
member `χ` of the `T`-instance family `𝒮_T(H₀ ⊔ C')` in Clifford case (b) is a
`ThetaWitness`.  Mirror of `lambdaWitness_of_caseB_member`. -/
theorem Hypothesis.thetaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {χ : ClassFunction ↥hyp.T ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ThetaWitness hyp := by
  classical
  haveI := hyp.finiteG
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
  have hsupeq : (data.H : Subgroup G) ⊔ cSub data chief = hyp.K := by
    rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.K.subgroupOf hyp.T := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `Q ⊄ Ker θ'`: else `Q ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)` pushes to `Q ⊆ Ker ζ`,
    -- contradicting `ζ ∈ 𝒳` (`Q = H ⊄ Ker ζ`).
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal := by
      have hQle : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
    have hQK : hyp.Q.subgroupOf hyp.T ≤ hyp.K.subgroupOf hyp.T :=
      Subgroup.subgroupOf_mono hyp.T (show hyp.Q ≤ hyp.K from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hQK θ' hker
    have hInd_eq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseA — the unconditional branch witness**: in Clifford case (a) a
`ThetaWitness` exists unconditionally.  Mirror of `lambdaWitness_of_caseA`. -/
theorem Hypothesis.thetaWitness_of_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataT hG hvd chief)) :
    ThetaWitness hyp := by
  classical
  haveI := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  have hsupeq : (data.H : Subgroup G) ⊔ cSub data chief = hyp.K := by
    rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.K.subgroupOf hyp.T := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal := by
      have hQle : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
    have hQK : hyp.Q.subgroupOf hyp.T ≤ hyp.K.subgroupOf hyp.T :=
      Subgroup.subgroupOf_mono hyp.T (show hyp.Q ≤ hyp.K from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hQK θ' hker
    have hInd_eq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-θ (Galois) branch of the `T`-side (13.3.b) facts**: if `𝒯` contains no
`vp`-degree `QD`-induced irreducible (`¬ ThetaWitness`), then `M = T` is in case (9.7.b)
with `D = ⊥` and `v = (q^p−1)/(q−1)`.  Mirror of `S_caseB_facts_no_lambda` (whose
`hbridge`/`hno` shape it reproduces verbatim on the `T`-instance). -/
theorem Hypothesis.T_caseB_facts_no_theta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnotheta : ¬ ThetaWitness hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  haveI := hyp.finiteG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → ThetaWitness hyp := by
    intro χ _hχmem _hχirr
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataT hG hvd chief) with hA | hB
    · obtain ⟨caseA⟩ := hA
      exact hyp.thetaWitness_of_caseA hG hvd chief caseA
    · obtain ⟨caseB⟩ := hB
      exact hyp.thetaWitness_of_caseB_member hG hvd chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnotheta (hbridge χ hmem hirr)
  obtain ⟨-, hDbot, hvfull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataT hG hvd chief) hno
  refine ⟨?_, ?_⟩
  · rw [← hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    exact hDbot
  · rw [← hyp.mkSection11CharacterDataT_v_eq hG hvd chief, hvfull,
      hyp.chiefFactorT_p_eq hG hvd chief, hyp.toTypesIIIIIIVSetupT_q_eq hG hvd]

/-- **The (13.4) θ-supply**: if `T` is *not* in the (9.7.b) Galois case (the `_hne` of
`tSide_theta_package_of_not_caseB_core`), then `𝒯` contains a `vp`-degree `QD`-linear
induced irreducible.  Contrapositive of `T_caseB_facts_no_theta` + the unconditional
`card_Q_eq_qp` (the third conjunct is always true, so `_hne` reduces to
`¬(D = ⊥ ∧ v = full)`). -/
theorem Hypothesis.thetaWitness_of_not_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) : ThetaWitness hyp := by
  by_contra hno
  obtain ⟨hD, hv⟩ := hyp.T_caseB_facts_no_theta hG hno
  exact hne ⟨hD, hv, hyp.card_Q_eq_qp hG⟩


open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package, Core/λ-cluster form** ((13.4) character gate — the
core/lam restatement of `tSide_theta_package_of_not_caseB`, issue 9094 案 A).

**Residual (precisely named, mirrors the legacy sorried gate)**: the T-side (13.3.b)/(13.3.c)
package — `𝒯` contains an irreducible `θ` induced from a linear character of `K = QD`, the
`ν`-row τ₁-formula, and the pairwise orthogonality of `η`, `λ^{τ₁}`, `θ^{τ₁}`.  Gated on the
ν-side grid supply (`nuGridSupply`) and the `T`-side coherence — the swap-instance of the
S-side (13.3) engines (issue 9013 追記⁶). -/
theorem tSide_theta_package_of_not_caseB_core [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r r' : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (core.tau1S lam.lambda) θG = 0 := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- ── supply: the Hypothesis-level producers
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional _hG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one _hG
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T := hyp.T_isTypeP _hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T _hG hyp
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG
    (hyp.toTypesIIIIIIVSetupT _hG hvd)
  -- ── the (13.3.b)-at-`T` θ-witness
  obtain ⟨θ, hθirr, hθ1, hθQ, hind⟩ := hyp.thetaWitness_of_not_caseB _hG _hne
  have hq1 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  -- ── the (13.3.c)-at-`T` pin at the anchor row `1`
  obtain ⟨r', δ', hr'0, hδ', hpin⟩ :=
    hyp.tau1T_ofHonest_nuRow_eta_row _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief hq1
  refine ⟨ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ, ⟨1, hyp.q_prime.one_lt⟩, r', δ',
    hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ),
    hδ', ?_, ?_, ?_, ?_⟩
  · -- conjunct 2: the (13.4) support estimate
    exact hyp.indK_sub_nuRow_support _hG pins θ hθ1 ⟨1, hyp.q_prime.one_lt⟩ hq1
  · -- conjunct 3: `Ind_T(θ_T − ν₁) = θ_G − δ'·∑_j η_{r'j}` ((13.2.e) agreement + the pin)
    have hzspan : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
        ∈ OddOrder.Peterfalvi.S07.zSpan
            (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT _hG hvd)) :=
      Submodule.sub_mem _ (hyp.induce_K_mem_zSpan_T _hG hvd θ hθirr hθQ)
        (Submodule.subset_span (OddOrder.Peterfalvi.S11.sOf_subset_sSet _ chief.H0
          (hyp.nu_rowSum_mem_sOf_H0_T _hG pins hvd chief ⟨1, hyp.q_prime.one_lt⟩ hq1)))
    have hdeg0 : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) (1 : ↥hyp.T) = 0 := by
      obtain ⟨θr, hθrirr, hθr1, hθreq⟩ :=
        hyp.nu_i_isIndQD _hG pins ⟨1, hyp.q_prime.one_lt⟩ hq1
      rw [ClassFunction.sub_apply, hθreq,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθr1, sub_self]
    have hext := hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1
      hW2 chief _ ⟨hzspan, hyp.zSpan_sSet_degree_zero_support_T _hG hvd hzspan hdeg0⟩
    rw [← hext, map_sub, hpin]
  · -- conjunct 4: `θ_G ⊥ η`-grid ((4.1)+(5.3.b)-at-`T`)
    intro i j
    exact hyp.tau1T_ofHonest_induce_inner_eta _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      i j θ hθirr hθQ hind
  · -- conjunct 5: `⟨λ^{τ₁S}, θ^{τ₁T}⟩ = 0` (the (13.4) pairwise orthogonality)
    obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
      lam.lambda_induced_from_PC_linear
    have hthetaLP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel thetaL) := by
      intro hsub
      exact hx₀ker (hsub (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact hx₀P))
    -- ── `S`-side conjugate data
    have hthetaLc1 : thetaL.conj 1 = 1 := by
      rw [ClassFunction.conj_apply, hthetaL1, star_one]
    have hthetaLPc : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel thetaL.conj) := by
      rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
      exact hthetaLP
    have hlamconj : lam.lambda.conj
        = ClassFunction.induce (hyp.H.subgroupOf hyp.S) thetaL.conj := by
      rw [hlamEq, OddOrder.RepresentationTheory.ClassFunction.induce_conj]
    -- ── `λ` is non-real (odd `|S|`, degree `u·q ≠ 1`)
    have hu_ne : hyp.u ≠ 0 := by
      intro h0
      have hcard : 0 < Nat.card ↥hyp.U := Nat.card_pos
      rw [hyp.card_U_eq_uc, h0, zero_mul] at hcard
      exact absurd hcard (lt_irrefl 0)
    have hlamdeg : lam.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := by
      rw [hlamEq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hthetaL1,
        mul_one, hyp.H_index_eq_uq _hG]
    have hlamNR : ¬ ClassFunction.IsReal lam.lambda := by
      have hne : (⟨lam.lambda, lam.lambda_irreducible⟩ : IrreducibleCharacter ↥hyp.S)
          ≠ trivialIrreducibleCharacter ↥hyp.S := by
        intro h
        have h1 := congrArg (fun ξ : IrreducibleCharacter ↥hyp.S =>
          (ξ : ClassFunction ↥hyp.S ℂ) (1 : ↥hyp.S)) h
        simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter] at h1
        rw [hlamdeg] at h1
        have h2 : (hyp.u * hyp.q : ℕ) = 1 := by
          have h3 : ((hyp.u * hyp.q : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
            rw [h1]; norm_num
          exact_mod_cast h3
        have h3q := hyp.three_le_q
        have hqd : hyp.q ∣ 1 := ⟨hyp.u, by rw [← h2]; ring⟩
        have := Nat.le_of_dvd one_pos hqd
        omega
      exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
        (hyp.oddCardS _hG) hne
    have hAB0 : ClassFunction.inner lam.lambda lam.lambda.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner lam.lambda_irreducible
        lam.lambda_irreducible.conj, if_neg (fun h => hlamNR h.symm)]
    -- ── `S`-side dirr inputs via the Core fields
    have hAZ : core.tau1S lam.lambda ∈ ZIrr G := by
      rw [hlamEq]
      exact core.tau1S_induce_mem_ZIrr thetaL hthetaLirr hthetaLP
    have hBZ : core.tau1S lam.lambda.conj ∈ ZIrr G := by
      rw [hlamconj]
      exact core.tau1S_induce_mem_ZIrr thetaL.conj hthetaLirr.conj hthetaLPc
    have hA1 : ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 := by
      conv_lhs => rw [hlamEq]
      rw [core.tau1S_inner_induce thetaL thetaL hthetaLirr hthetaLirr hthetaLP hthetaLP,
        ← hlamEq]
      exact lam.lambda_irreducible.inner_self_eq_one
    have hB1 : ClassFunction.inner (core.tau1S lam.lambda.conj)
        (core.tau1S lam.lambda.conj) = 1 := by
      conv_lhs => rw [hlamconj]
      rw [core.tau1S_inner_induce thetaL.conj thetaL.conj hthetaLirr.conj hthetaLirr.conj
        hthetaLPc hthetaLPc, ← hlamconj]
      exact lam.lambda_irreducible.conj.inner_self_eq_one
    have hABi : ClassFunction.inner (core.tau1S lam.lambda)
        (core.tau1S lam.lambda.conj) = 0 := by
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_inner_induce thetaL thetaL.conj hthetaLirr hthetaLirr.conj hthetaLP
        hthetaLPc, ← hlamEq, ← hlamconj]
      exact hAB0
    have hABdiff : core.tau1S lam.lambda - core.tau1S lam.lambda.conj
        = ClassFunction.induce hyp.S (lam.lambda - lam.lambda.conj) := by
      rw [← map_sub]
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_apply_induce_sub thetaL thetaL.conj hthetaLirr hthetaLirr.conj
        hthetaLP hthetaLPc, ← hlamEq, ← hlamconj]
    have hBAdiff : core.tau1S lam.lambda.conj - core.tau1S lam.lambda
        = ClassFunction.induce hyp.S (lam.lambda.conj - lam.lambda) := by
      rw [← map_sub]
      conv_lhs => rw [hlamconj, hlamEq]
      rw [core.tau1S_apply_induce_sub thetaL.conj thetaL hthetaLirr.conj hthetaLirr
        hthetaLPc hthetaLP, ← hlamEq, ← hlamconj]
    have hABconj : (core.tau1S lam.lambda).conj - (core.tau1S lam.lambda.conj).conj
        = core.tau1S lam.lambda.conj - core.tau1S lam.lambda := by
      rw [← ClassFunction.conj_sub, hABdiff, hBAdiff,
        OddOrder.RepresentationTheory.ClassFunction.induce_conj]
      congr 1
      rw [ClassFunction.conj_sub, ClassFunction.conj_conj]
    -- ── `T`-side conjugate data
    have hθc1 : θ.conj 1 = 1 := by
      rw [ClassFunction.conj_apply, hθ1, star_one]
    have hθQc : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ.conj) := by
      rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
      exact hθQ
    have hindconjeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj
        = (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ).conj :=
      (OddOrder.RepresentationTheory.ClassFunction.induce_conj _ _).symm
    have hindc : OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) := by
      rw [hindconjeq]
      exact hind.conj
    -- ── `θ_T` is non-real (odd `|T|`, degree `v·p ≠ 1`)
    have hv_ne : hyp.v ≠ 0 := by
      intro h0
      have hcard : 0 < Nat.card ↥hyp.V := Nat.card_pos
      rw [hyp.card_V_eq_vd, h0, zero_mul] at hcard
      exact absurd hcard (lt_irrefl 0)
    have hθTdeg : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ (1 : ↥hyp.T)
        = ((hyp.v * hyp.p : ℕ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one,
        hyp.K_index_eq_vp _hG]
    have hθTNR : ¬ ClassFunction.IsReal
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      have hne : (⟨ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ, hind⟩ :
          IrreducibleCharacter ↥hyp.T) ≠ trivialIrreducibleCharacter ↥hyp.T := by
        intro h
        have h1 := congrArg (fun ξ : IrreducibleCharacter ↥hyp.T =>
          (ξ : ClassFunction ↥hyp.T ℂ) (1 : ↥hyp.T)) h
        simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter] at h1
        rw [hθTdeg] at h1
        have h2 : (hyp.v * hyp.p : ℕ) = 1 := by
          have h3 : ((hyp.v * hyp.p : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
            rw [h1]; norm_num
          exact_mod_cast h3
        have h3p := hyp.three_le_p
        have hpd : hyp.p ∣ 1 := ⟨hyp.v, by rw [← h2]; ring⟩
        have := Nat.le_of_dvd one_pos hpd
        omega
      exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
        (hyp.oddCardT _hG) hne
    have hCD0 : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) = 0 := by
      rw [hindconjeq, OddOrder.RepresentationTheory.irr_cf_inner hind hind.conj,
        if_neg (fun h => hθTNR h.symm)]
    -- ── `T`-side dirr inputs via the pinned coherence carrier
    have hmemθ := hyp.induce_K_mem_zSpan_T _hG hvd θ hθirr hθQ
    have hmemθc := hyp.induce_K_mem_zSpan_T _hG hvd θ.conj hθirr.conj hθQc
    have hCZ : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) ∈ ZIrr G :=
      (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief).extension_mem_ZIrr _ hmemθ
    have hDZ : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) ∈ ZIrr G :=
      (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief).extension_mem_ZIrr _ hmemθc
    have hC1 : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) = 1 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθ hmemθ]
      exact hind.inner_self_eq_one
    have hD1 : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 1 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθc hmemθc]
      exact hindc.inner_self_eq_one
    have hCDi : ClassFunction.inner
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 0 := by
      rw [show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) from rfl,
        show (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj))
          = (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
            chief).extension (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) from rfl,
        (hyp.coherentIndT_pinned _hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief).extension_inner_eq _ _ hmemθ hmemθc]
      exact hCD0
    -- ── the `T`-side difference is the honest induction ((13.2.e))
    have hCDzspan : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        ∈ OddOrder.Peterfalvi.S07.zSpan
            (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT _hG hvd)) :=
      Submodule.sub_mem _ hmemθ hmemθc
    have hCDdeg0 : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) (1 : ↥hyp.T) = 0 := by
      rw [ClassFunction.sub_apply,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθc1, sub_self]
    have hCDdiff : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
              - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj) := by
      rw [← map_sub]
      exact hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief _ ⟨hCDzspan, hyp.zSpan_sSet_degree_zero_support_T _hG hvd hCDzspan hCDdeg0⟩
    have hDCdiff : hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
        - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj
              - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      rw [← map_sub]
      refine hyp.tau1T_ofHonest_extends_on_supported _hG hnoV pins hvd hTP Tdata hU hW1 hW2
        chief _ ⟨Submodule.sub_mem _ hmemθc hmemθ,
          hyp.zSpan_sSet_degree_zero_support_T _hG hvd (Submodule.sub_mem _ hmemθc hmemθ) ?_⟩
      rw [ClassFunction.sub_apply,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθc1,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, sub_self]
    have hCDconj : (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)).conj
        - (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)).conj
        = hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)
          - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ) := by
      rw [← ClassFunction.conj_sub, hCDdiff, hDCdiff,
        OddOrder.RepresentationTheory.ClassFunction.induce_conj]
      congr 1
      rw [ClassFunction.conj_sub, hindconjeq, ClassFunction.conj_conj]
    -- ── the (13.2.e) disjoint-support cross input
    have hαsupp : (lam.lambda - lam.lambda.conj).support ⊆
        {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
      rw [hlamconj, hlamEq]
      exact hyp.indH_sub_indH_support _hG thetaL thetaL.conj hthetaL1 hthetaLc1
    have hβsupp : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1} :=
      hyp.indK_sub_indK_support _hG θ θ.conj hθ1 hθc1
    have h0 : ClassFunction.inner
        (core.tau1S lam.lambda - core.tau1S lam.lambda.conj)
        (hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
          - hyp.tau1T_ofHonest _hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ.conj)) = 0 := by
      rw [hABdiff, hCDdiff]
      exact hyp.inner_induce_H_QD_eq_zero _hG hαsupp hβsupp
    -- ── the dirr brick closes conjunct 5
    exact inner_eq_zero_of_conj_diff_orthogonal hAZ hBZ hCZ hDZ hA1 hB1 hC1 hD1 hABi hCDi
      hABconj hCDconj h0

open scoped FiniteInduce in
/-- **Peterfalvi (13.4), Core/λ-cluster form** (the core/lam restatement of
`lambda_forces_T_caseB`, issue 9094 案 A): if `𝒮` contains the λ-cluster (a degree-`uq`
character induced from a linear character of `PC`), then case (9.7.b) holds for `T`, with
`D = 1`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`.  The witnesses of the Core `mu_col` field and
the λ-cluster thread the guarded `tau1S_apply_induce_sub`/`tau1S_induce_inner_eta`. -/
theorem lambda_forces_T_caseB_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  haveI := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, r', δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB_core hG core lam pins hne
  -- S-side (13.3) data with the `𝒮₁`-witnesses.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hthetaLP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel thetaL) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  obtain ⟨j₀, δ, θlin, -, hδ, hθlinirr, hθlin1, hθlinP, hμeq, hμtau⟩ :=
    core.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hαsupp : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = core.tau1S lam.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← core.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr hthetaLP hθlinP,
      map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (core.tau1S lam.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := core.tau1S_induce_inner_eta i j thetaL hthetaLirr hthetaLP
      (hlamEq ▸ lam.lambda_irreducible)
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (core.tau1S lam.lambda) θG r' ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0


open scoped FiniteInduce in
/-- **Peterfalvi (13.12), swapped Core form**: `d = 1` without the legacy unconditional
character-degree carrier.  The swap's `ν`-grid is supplied honestly by the original `μ`-grid;
the λ-branch uses Core (13.10), while the no-λ branch already has the swap's `C = ⊥`. -/
theorem Hypothesis.d_eq_one_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.d = 1 := by
  have hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T := hyp.T_isTypeP2_gate hG
  have hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  let hyp' : Hypothesis (G := G) := hyp.swap hT2 hV Tdata hU hW1 hW2 pins
  have pins' : NuGridSupplyData hyp' :=
    hyp.nuGridSupply_swap hT2 hV Tdata hU hW1 hW2 pins
  obtain ⟨core'⟩ := hyp'.characterDegreeCore_nonempty hG
  have hc1 : hyp'.c = 1 := by
    rcases lambdaCluster_or_caseB hG hyp' with hlam | ⟨hCbot, _hu⟩
    · obtain ⟨lam'⟩ := hlam
      obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
      have hQcomm : IsMulCommutative ↥hyp'.Q :=
        IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
      exact core'.c_eq_one_of_caseB_facts hG lam' hD hv hQcomm
    · exact hyp'.c_eq_card_C.trans (Subgroup.card_eq_one.mpr hCbot)
  exact hc1

/-- **Peterfalvi (13.12), swapped Core subgroup form**: `D = ⊥`. -/
theorem Hypothesis.T_side_D_eq_bot_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ := by
  have hd := hyp.d_eq_one_of_swapped_lambda_dichotomy hG pins
  rw [hyp.d_eq_card_D] at hd
  exact Subgroup.card_eq_one.mp hd

open scoped FiniteInduce in
/-- **Peterfalvi (13.13)/(13.15) at the swap**: under `q < p`, the `T`-side Singer
parameter has the full order, using only the Core analytic relayer. -/
theorem Hypothesis.T_caseB_v_eq_full_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) (pins : NuGridSupplyData hyp) :
    hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  have hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T := hyp.T_isTypeP2_gate hG
  have hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  let hyp' : Hypothesis (G := G) := hyp.swap hT2 hV Tdata hU hW1 hW2 pins
  have pins' : NuGridSupplyData hyp' :=
    hyp.nuGridSupply_swap hT2 hV Tdata hU hW1 hW2 pins
  obtain ⟨core'⟩ := hyp'.characterDegreeCore_nonempty hG
  obtain ⟨chief', -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp'.toTypesIIIIIIVSetupS hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp'.mkSection11CharacterDataS hG chief') with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := lambdaWitness_of_caseA hG hyp' chief' caseA
    obtain ⟨lam'⟩ := hyp'.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
    obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
    have hQcomm : IsMulCommutative ↥hyp'.Q :=
      IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
    obtain ⟨hq3, -⟩ :=
      core'.caseA_parameters_of_caseB_facts hG lam' hD hv hQcomm caseA
    have hp3 : hyp.p = 3 := hq3
    have h3q : 3 ≤ hyp.q := hyp.three_le_q
    omega
  · obtain ⟨caseB⟩ := hB
    have hnotmod : ¬ hyp'.p ≡ 1 [MOD hyp'.q] := by
      show ¬ hyp.q ≡ 1 [MOD hyp.p]
      intro hmod
      have hq_mod : hyp.q % hyp.p = hyp.q := Nat.mod_eq_of_lt hqp
      have h1_mod : 1 % hyp.p = 1 :=
        Nat.mod_eq_of_lt (lt_of_lt_of_le (by norm_num) hyp.three_le_p)
      have h3q : 3 ≤ hyp.q := hyp.three_le_q
      have := hmod
      unfold Nat.ModEq at this
      omega
    rcases lambdaCluster_or_caseB hG hyp' with hlam | ⟨_hCbot, hufull⟩
    · obtain ⟨lam'⟩ := hlam
      obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
      have hQcomm : IsMulCommutative ↥hyp'.Q :=
        IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
      exact (core'.caseB_order_u_of_caseB_facts hG lam' hD hv hQcomm caseB).2 hnotmod
    · exact hufull

/-- **The `T`-side (13.4)/(14.4) facts under `q < p`, Core-only form**. -/
theorem T_caseB_facts_of_q_lt_p_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p :=
  ⟨hyp.T_side_D_eq_bot_of_swapped_lambda_dichotomy hG pins,
    hyp.T_caseB_v_eq_full_of_swapped_lambda_dichotomy hG hqp pins,
    hyp.card_Q_eq_qp hG⟩

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)/(14.4), `T`-side case (9.7.b), unconditional via the (13.3.b) dichotomy**
(issue 9094 RULING 案 A + §4): `D = ⊥`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`, obtained **without**
the overstated unconditional λ-cluster of the legacy `character_degree_analysis`.

Case-splits on `LambdaWitness hyp` (Pf (13.3.b) dichotomy): the λ-branch builds the honest
`LambdaClusterData` (`lambdaClusterData_of_irr_witness`) and runs `lambda_forces_T_caseB_core`
against the unconditional `CharacterDegreeCore`; the no-λ branch is the (Galois) T-mirror
`T_caseB_facts_no_lambda`.  This is the b-side export the (14.9) type-II endpoint
(`S16 … T_side_caseB_facts`) cites in place of the uninhabitable monolithic producer. -/
theorem T_caseB_facts_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p)
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
    exact lambda_forces_T_caseB_core hG core lam pins
  · exact T_caseB_facts_of_q_lt_p_core hG hyp hqp pins

end OddOrder.Peterfalvi.S15
