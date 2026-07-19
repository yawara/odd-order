import OddOrder.Peterfalvi.S16_NonExistenceG.TGapDelta
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.OrderRelayer

/-!
# Peterfalvi (14.9): assembly of the S/T gap identity

This file isolates the linear-algebraic end of the identity
`⟨Γ, τ₁ζ⟩ = 1 + ⟨Δ, Γ⟩`, where
`Γ = τ_S β_S - 1_G + η₀₁` and `Δ = τ_T β_T - 1_G + τ₁ζ`.
Once the two genuine cross-side inputs
`⟨τ_T β_T, τ_S β_S⟩ = 0` and `⟨τ_T β_T, η₀₁⟩ = 0` are known,
the claimed equality follows formally.  The only subtlety is that the
class-function inner product is Hermitian; integrality makes it symmetric
on virtual characters.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]
open scoped BigOperators

/-- Two Peterfalvi (2.2) hypotheses on the same support and subgroup are equal once their
`H`-fields agree.  The `H`-field is the only data field; all other fields are propositions. -/
theorem dadeHypothesis_eq_of_H_eq [Fintype G] {A : Set G} {L : Subgroup G}
    {h₁ h₂ : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (hH : ∀ a, h₁.H a = h₂.H a) : h₁ = h₂ := by
  obtain ⟨s₁, l₁, n₁, H₁, c₁, ce₁, cd₁, hn₁, cc₁⟩ := h₁
  obtain ⟨s₂, l₂, n₂, H₂, c₂, ce₂, cd₂, hn₂, cc₂⟩ := h₂
  have hHeq : H₁ = H₂ := funext hH
  subst hHeq
  rfl

open scoped Classical in
/-- **Peterfalvi (2.11)/(13.2.e), T-side Dade restriction reconciliation.**

For a type-`P₁` datum on `T`, the Dade map on `A₁(T)=T_σ#` used by the (14.9)
coherent family is the restriction of the full type-`P₁` Dade map on
`A₀(T)=A(T)∪V^T`.  Thus both integral-character lifts agree on every
`A₁(T)`-supported class function.

This is the reusable map-identification step needed before the remaining
`FTtypeP_facts(e)` normed-TI assertion can identify the full map with induction. -/
theorem tSideDadeMap_eq_full_typeP1DadeMap_of_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ =
      let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData full.hconj) φ := by
  classical
  let side := (tSideDadeSupport_nonempty hG hyp).some
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hA1norm : ∀ (l : ↥hyp.base.T) ⦃a : G⦄,
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T →
        (l : G) * a * (l : G)⁻¹ ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    side.dade.L_normalizes_A
  let restricted := full.dade.restrict hA1A0 hA1norm
  have hH : ∀ a, restricted.H a = side.dade.H a := by
    intro a
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H,
      full.H_eq_ftSupportKernel, side.H_eq_ftSupportKernel]
    exact (OddOrder.Peterfalvi.S10.ftSupportKernel_restrict hA1A0 a.2).symm
  have hdade : restricted = side.dade := dadeHypothesis_eq_of_H_eq hH
  have hfullSupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  change tSideDadeMap hyp hG φ =
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
      (full.dade.fullDadeIsometryData full.hconj) φ
  rw [tSideDadeMap,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support side.dade
      (side.dade.fullDadeIsometryData side.hconj) hφsupp,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
      (full.dade.fullDadeIsometryData full.hconj) hfullSupp]
  rw [← hdade]
  exact full.dade.dadeMap_restrict_apply hA1A0 hA1norm
    ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩

open scoped Classical in
/-- **Peterfalvi (13.2.e), type-`P₁` `A₀(M)` has no escaping point.**

This is the Type-`P₁` instance of Coq `FTtypeP_facts(e)` (`PFsection13.v:224–242`).
An escaping `A₀(M)` point is `M_σ#` by (8.13.b).  BG Theorem D(4) attaches a unique
maximal neighbour `N`, of type `F` or `P₂`.  In the type-`F` branch, Peterfalvi (12.7)
Frobenius-kernel regularity forces the point into `N_σ`, contradicting D(4).  In the
type-`P₂` branch, D(4) makes `M` type `F`, contradicting that `M` is type `P₁`.

This is the genuine group-theoretic producer behind the T-side full-`A₀` normed-TI
input; it does not use the downstream conclusion that `T` is type II. -/
theorem escaping_typePA0_eq_empty_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G)
    (data : OddOrder.GroupTheory.TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.GroupTheory.escapingCentralizerSet M
      (OddOrder.GroupTheory.typePA0 M data) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro a haesc
  have haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.Peterfalvi.S10.escaping_typePA0_mem_sigmaSharp_of_isTypeP1
      hG hM data hP1 haesc
  obtain ⟨R, -, N, ⟨hNmem, -, hMFN, hxAN, hNtype, -, hP2imp⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG hM haσ haesc.2
  rcases hNtype with hNF | hNP2
  · have hNmax : N ∈ OddOrder.GroupTheory.maximalSubgroups G := hNmem.1
    have hNI : OddOrder.GroupTheory.IsTypeI N :=
      (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hNmax).mpr hNF
    obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hNmax hNI
    have hker : fdata.typeI.typeF.H = OddOrder.BG.Ch3.S10.Msigma N := by
      rw [fdata.typeI.typeF.H_eq]
      exact hMFN
    obtain ⟨haN, hne⟩ : a ∈ OddOrder.BG.Ch4.S16.hatMsigma N := hxAN.1.1
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp z.2
    have hzN : (z : G) ∈ N := OddOrder.BG.Ch3.S10.Msigma_le N hzMσ
    have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have haker : (⟨a, haN⟩ : ↥N) ∈ fdata.typeI.typeF.H.subgroupOf N := by
      refine fdata.frobenius.centralizer_kernel_le ⟨(z : G), hzN⟩
        (Subgroup.mem_subgroupOf.mpr (by rw [hker]; exact hzMσ))
        (fun h => hzG1 (congrArg Subtype.val h)) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm
    exact hxAN.2 (SetLike.mem_coe.mpr
      (by rw [← hker]; exact Subgroup.mem_subgroupOf.mp haker))
  · obtain ⟨hFM, -⟩ := hP2imp hNP2
    exact OddOrder.BG.Ch4.S14.not_isTypeP_and_isTypeF ⟨hP1.1, hFM⟩

open scoped Classical in
/-- **Peterfalvi (13.2.e), full type-`P₁` `A₀(M)` is a TI-subset.**

The escape exclusion above makes every faithful Dade stabilizer trivial; Peterfalvi
(2.3), already encoded by `Hypothesis.isTISubset_of_forall_H_eq_bot`, then supplies the
full TI statement.  This is Coq's `normedTI 'A0(M) G M` conclusion with no downstream
type-II assumption. -/
theorem typePA0_isTISubset_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G)
    (data : OddOrder.GroupTheory.TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.GroupTheory.IsTISubset (OddOrder.GroupTheory.typePA0 M data) M := by
  letI := Fintype.ofFinite G
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hM data hP1).some
  apply full.dade.isTISubset_of_forall_H_eq_bot
  intro a
  rw [full.H_eq_ftSupportKernel]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping (by
    intro haesc
    have hempty := escaping_typePA0_eq_empty_of_isTypeP1 hG hnoV hM data hP1
    rw [hempty] at haesc
    exact Set.notMem_empty a.1 haesc)

open scoped Classical in
/-- **Peterfalvi (13.2.e), reduction of full `A₀(T)` normed-TI to `A(T)`.**

The exceptional `V^T` part is already non-escaping, so centralizer containment on
`A(T)=typePA(T)` implies every full `A₀(T)` point is non-escaping. Hence the faithful
Dade stabilizer `H(a)=ftSupportKernel ... a` is bottom. -/
theorem fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hA : ∀ x ∈ OddOrder.GroupTheory.typePA hyp.base.T dataT,
      Subgroup.centralizer ({x} : Set G) ≤ hyp.base.T) :
    ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥ := by
  classical
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hA0 : ∀ x ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT,
      Subgroup.centralizer ({x} : Set G) ≤ hyp.base.T := by
    intro x hx
    change x ∈ OddOrder.GroupTheory.typePA hyp.base.T dataT ∪
      OddOrder.GroupTheory.conjClassSetIn hyp.base.T
        (OddOrder.GroupTheory.typePV hyp.base.T dataT) at hx
    rcases hx with hxA | hxV
    · exact hA x hxA
    · exact OddOrder.Peterfalvi.S15.conjClassSetIn_typePV_centralizer_le_M dataT hxV
  intro a
  change full.dade.H a = ⊥
  rw [full.H_eq_ftSupportKernel]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => hesc.2 (hA0 a.1 a.2))

open scoped Classical in
/-- **Peterfalvi (13.2.e), full `A₀(T)` normed-TI gives trivial Dade stabilizers.**

This is the direct bridge from the Coq conclusion `normedTI 'A0(T) G T` to the selected
full type-`P₁` Dade datum.  TI controls each point centralizer, while the exceptional
`V^T` reduction is handled by `fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le`. -/
theorem fullTypeP1Dade_H_eq_bot_of_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T) :
    ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥ :=
  fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le hG hyp dataT hP1 fun _ hx =>
    hTI.centralizer_le (Set.mem_union_left _ hx)

open scoped Classical in
/-- **Peterfalvi (13.2.e), exact T-side Dade=induction bridge.**

Once the full type-`P₁` `A₀(T)` Dade datum has trivial point stabilizers—the
Lean form of Coq's `normedTI 'A0(T) G T` conclusion—the (2.5) uniqueness theorem
identifies its Dade map with `Ind_T^G`.  Composing with
`tSideDadeMap_eq_full_typeP1DadeMap_of_support` gives the (14.9) map
`τ_T φ = Ind_T^G φ` for every `A₁(T)`-supported `φ`.

The only non-formal input is `hH`; no normed-TI content is hidden in this theorem. -/
theorem tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hH : ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ := by
  classical
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hfullSupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  rw [tSideDadeMap_eq_full_typeP1DadeMap_of_support hG hyp dataT hP1 hφsupp,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
      (full.dade.fullDadeIsometryData full.hconj) hfullSupp]
  have hind := OddOrder.Peterfalvi.S14.isDadeMap_induce_of_forall_H_eq_bot full.dade
    (by simpa only [full] using hH)
  have heq := OddOrder.Peterfalvi.S04.IsDadeMap.unique
    (full.dade.isDadeMap_dadeMap (k := ℂ)) hind
  exact congrFun heq ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hfullSupp⟩

open scoped Classical in
/-- **Peterfalvi (13.2.e), T-side Dade=induction from `A(T)` centralizers.**

This is the consumer form of
`fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le`: the already-settled exceptional
`V^T` part leaves only centralizer containment on the ordinary type-`P` set. -/
theorem tSideDadeMap_eq_induce_of_typePA_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hA : ∀ x ∈ OddOrder.GroupTheory.typePA hyp.base.T dataT,
      Subgroup.centralizer ({x} : Set G) ≤ hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ := by
  exact tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot hG hyp dataT hP1
    (fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le hG hyp dataT hP1 hA) hφsupp

open scoped Classical in
/-- **Peterfalvi (13.2.e), T-side Dade=induction from full `A₀(T)` normed-TI.**

This is the form consumed by (14.9): once the genuine `A₀(T)` TI theorem is available,
the reconciled T-side Dade map is induction on every `A₁(T)`-supported class function. -/
theorem tSideDadeMap_eq_induce_of_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ :=
  tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot hG hyp dataT hP1
    (fullTypeP1Dade_H_eq_bot_of_isTISubset hG hyp dataT hP1 hTI) hφsupp

open scoped Classical in
/-- **Peterfalvi (13.2.e), exact T-side Dade=induction theorem.**

The Type-`P₁` escape analysis now supplies full `A₀(T)` normed-TI internally, so no
TI hypothesis or downstream type-II conclusion remains in the consumer interface. -/
theorem tSideDadeMap_eq_induce_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ :=
  tSideDadeMap_eq_induce_of_isTISubset hG hyp dataT hP1
    (typePA0_isTISubset_of_isTypeP1 hG hnoV hyp.base.T_maximal dataT hP1) hφsupp

/-- Conjugate closures are disjoint when a prime divides every order on the left
and no order on the right.

This is the abstract order-separation core used in Peterfalvi (14.9). -/
theorem disjoint_conjugatesIntoSet_of_prime_order_separator
    {M N : Subgroup G} {A : Set ↥M} {B : Set ↥N} {p : ℕ}
    (hA : ∀ y ∈ A, p ∣ orderOf (y : G))
    (hB : ∀ z ∈ B, ¬ p ∣ orderOf (z : G)) :
    Disjoint (ClassFunction.conjugatesIntoSet M A)
      (ClassFunction.conjugatesIntoSet N B) := by
  rw [Set.disjoint_left]
  rintro g ⟨a, ha, hya⟩ ⟨b, hb, hzb⟩
  have horda : orderOf (a⁻¹ * g * a) = orderOf g := by
    simpa [MulAut.conj_apply] using
      (orderOf_injective (MulAut.conj a⁻¹).toMonoidHom
        (MulAut.conj a⁻¹).injective g)
  have hordb : orderOf (b⁻¹ * g * b) = orderOf g := by
    simpa [MulAut.conj_apply] using
      (orderOf_injective (MulAut.conj b⁻¹).toMonoidHom
        (MulAut.conj b⁻¹).injective g)
  have hp : p ∣ orderOf g := by
    rw [← horda]
    exact hA ⟨a⁻¹ * g * a, ha⟩ hya
  exact hB ⟨b⁻¹ * g * b, hb⟩ hzb (by rwa [hordb])

/-- **Peterfalvi (14.9), the S/T order separator.**

For a type-`P` maximal `T`, `[T:T']=p` and `|T'|` are coprime.  Consequently every
element conjugate into `(T')#` has order prime to `p`, so its conjugate closure is
disjoint from the closure of any S-side set whose elements all have order divisible by `p`.

This is the group-theoretic core of Coq's `QV'betaS` support separation.  The remaining
character input is precisely the (13.18.a) assertion that every point in the support of
`β_S` has order divisible by `p`. -/
theorem disjoint_conjugatesIntoSet_S_Tderived_of_p_dvd [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    {A : Set ↥hyp.base.S}
    (hpA : ∀ y ∈ A, hyp.base.p ∣ orderOf (y : G)) :
    Disjoint (ClassFunction.conjugatesIntoSet hyp.base.S A)
      (ClassFunction.conjugatesIntoSet hyp.base.T
        {z : ↥hyp.base.T |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
            (OddOrder.GroupTheory.derivedInG hyp.base.T)}) := by
  apply disjoint_conjugatesIntoSet_of_prime_order_separator hpA
  intro z hz
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI
      hG hyp.base.T_maximal hyp.base.T_nonI
  have hcop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.base.T)) hyp.base.p := by
    have h := OddOrder.Peterfalvi.S15.coprime_card_derivedInG_index_of_isTypeP
      hG hyp.base.T_maximal hP
    rwa [T_derived_index_eq_p hyp] at h
  have hord : orderOf (z : G) ∣
      Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.base.T) := by
    have hz' : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.base.T := hz.1
    have h1 := orderOf_dvd_natCard
      (⟨(z : G), hz'⟩ : ↥(OddOrder.GroupTheory.derivedInG hyp.base.T))
    rwa [← Subgroup.orderOf_coe] at h1
  exact hyp.base.p_prime.coprime_iff_not_dvd.mp
    ((hcop.coprime_dvd_left hord).symm)

open scoped Classical in
/-- **Peterfalvi (13.18.a), every point of `P# ∪ V_S` has p-divisible order.**

On `P#` this is the p-group order criterion using `|P|=p^q`.  A regular
`V_S = (W ∖ (W₁ ∪ W₂))^S` point has a σ-prime divisor; since
`S_σ=P` and `|P|=p^q`, that prime is exactly `p`. -/
theorem p_dvd_orderOf_of_mem_sharpP_union_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    {y : G}
    (hy : y ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
      OddOrder.GroupTheory.conjClassSetIn hyp.base.S
        (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)) :
    hyp.base.p ∣ orderOf y := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases hy with hyP | hyV
  · have hPgroup : IsPGroup hyp.base.p ↥hyp.base.P :=
      IsPGroup.of_card (hyp.base.card_P_eq hG hyp.base.Sdata_W2_eq)
    have hdiv := hPgroup.dvd_orderOf (g := ⟨y, hyP.1⟩) (by
      intro h
      exact hyP.2 (congrArg Subtype.val h))
    rwa [← Subgroup.orderOf_coe] at hdiv
  · obtain ⟨v, hv, m, hmS, hmv⟩ := hyV
    obtain ⟨r, hrord, _hrσ, hrW2⟩ :=
      OddOrder.Peterfalvi.S15.exists_sigma_prime_dvd_orderOf_typePV
        hG hyp.base.S_maximal hyp.base.Sdata hv
    rw [hyp.base.Sdata_W2_eq, ← hyp.base.p_eq_card_W2] at hrW2
    have hrp : r = hyp.base.p :=
      (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hrord).1
        hyp.base.p_prime).mp hrW2
    have hpv : hyp.base.p ∣ orderOf v :=
      hrp ▸ Nat.dvd_of_mem_primeFactors hrord
    have hord : orderOf y = orderOf v := by
      rw [← hmv]
      simpa [MulAut.conj_apply] using
        (orderOf_injective (MulAut.conj m).toMonoidHom
          (MulAut.conj m).injective v)
    rwa [hord]

/-- **Peterfalvi (13.18.a)/(14.9), exact S/T source-support separation.**

The conjugate closure of the genuine S-side support carrier `P# ∪ V_S` is disjoint
from the conjugate closure of `(T')#`.  This closes the group/order part of the
`QV'betaS` argument; only the character statement
`supp(β_S) ⊆ P# ∪ V_S` remains to feed it. -/
theorem disjoint_conjugatesIntoSet_sharpP_union_typePV_Tderived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Disjoint
      (ClassFunction.conjugatesIntoSet hyp.base.S
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
      (ClassFunction.conjugatesIntoSet hyp.base.T
        {z : ↥hyp.base.T |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
            (OddOrder.GroupTheory.derivedInG hyp.base.T)}) :=
  disjoint_conjugatesIntoSet_S_Tderived_of_p_dvd hG hyp fun _ hy =>
    p_dvd_orderOf_of_mem_sharpP_union_typePV hG hyp hy

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), cross-Dade orthogonality from the exact support inputs.**

This is the final consumer of the two genuine character-theoretic residuals in the
`τ_T`/`τ_S` cross term.  Full `A₀(T)` normed-TI identifies the T-side Dade map with
induction, while `supp(β_S) ⊆ P# ∪ V_S` places the S-side Dade map in its already-proved
`A₀(S)` induction range.  The exact order separator above then makes the induced
characters orthogonal.

No support or TI content is hidden here: `hTI` and `hbeta` are the two exact inputs of
this reusable boundary theorem.  The Type-`P₁` TI producer is now proved above; the
specialized theorem below discharges `hTI` and retains only the (13.18.a) β support. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_exact_supports [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T)
    (hbeta : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hsig : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      OddOrder.GroupTheory.sharpSubgroup
        (OddOrder.GroupTheory.derivedInG hyp.base.T) := by
    rw [← OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
  have hφderiv : φ.support ⊆
      {z : ↥hyp.base.T |
        (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
          (OddOrder.GroupTheory.derivedInG hyp.base.T)} := by
    intro z hz
    have hz' := hφsupp hz
    change (z : G) ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T at hz'
    rwa [hsig] at hz'
  have hbetaA0 : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 hyp.base.S hyp.base.Sdata)
        hyp.base.S := by
    intro y hy
    exact OddOrder.Peterfalvi.S15.sharpP_union_V_subset_A0 hG hyp.base (hbeta hy)
  have hTmap : tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ :=
    tSideDadeMap_eq_induce_of_isTISubset hG hyp dataT hP1 hTI hφsupp
  have hSmap : OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base =
      ClassFunction.induce hyp.base.S
        (OddOrder.Peterfalvi.S15.betaGrid hyp.base
          ⟨1, by have := hyp.base.three_le_p; omega⟩) := by
    rw [OddOrder.Peterfalvi.S15.tauSbetaGrid]
    exact hyp.base.sInstance_dade0_eq_induce hG hnoV hbetaA0
  rw [hTmap, hSmap]
  exact OddOrder.Peterfalvi.S15.inner_induce_induce_eq_zero_of_disjoint
    hφderiv hbeta
      (disjoint_conjugatesIntoSet_sharpP_union_typePV_Tderived hG hyp).symm

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), cross-Dade orthogonality from the exact β support.**

The Type-`P₁` full-`A₀(T)` TI theorem is now proved internally, so the only remaining
character-theoretic input for the S/T Dade cross term is Peterfalvi (13.18.a)'s exact
`β_S` support statement. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_beta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hbeta : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
  tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_exact_supports hG hnoV hyp dataT hP1
    (typePA0_isTISubset_of_isTypeP1 hG hnoV hyp.base.T_maximal dataT hP1)
    hbeta hφsupp

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), unconditional cross-Dade orthogonality.**

The S-side exact support is supplied by the fully proved `(13.18.a)` theorem
`S15.betaGrid_support_of_c_eq_one`, with (13.12) supplied by the upstream Core endpoint
`Hypothesis.c_eq_one_of_lambda_dichotomy`; all group structure, normed-TI, Dade=Ind, and
support-separation steps are therefore discharged. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hc1 : hyp.base.c = 1)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
  tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_beta_support hG hnoV hyp dataT hP1
    (OddOrder.Peterfalvi.S15.betaGrid_support_of_c_eq_one hG hyp.base
      hc1
      ⟨1, by have := hyp.base.three_le_p; omega⟩ (by norm_num))
    hφsupp

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Compatibility entry point supplied by the upstream Core (13.12) endpoint. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
  tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_c_eq_one hG hnoV hyp
    (hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply) dataT hP1 hφsupp

/-- The inner product of two virtual characters is symmetric: its value is
an integer, hence fixed by complex conjugation. -/
theorem inner_eq_swap_of_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {φ ψ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hψ : ψ ∈ ZIrr G) :
    ClassFunction.inner φ ψ = ClassFunction.inner ψ φ := by
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφ hψ
  calc
    ClassFunction.inner φ ψ = (m : ℂ) := hm
    _ = star (m : ℂ) := by rw [star_intCast]
    _ = star (ClassFunction.inner φ ψ) := by rw [hm]
    _ = ClassFunction.inner ψ φ :=
      (OddOrder.RepresentationTheory.inner_conj_symm φ ψ).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)/(14.9), projection-to-row reduction.**

Let `b` be the T-side Dade image of `β_{T,0}`.  The output of the
`FTtype34_structure` projection calculation is that every `η_{0j}`
has the same inner product with `b` as with the zero-column sum
`∑ᵢ η_{i0}`.  Orthonormality of the η-grid then gives
`⟨b,η_{0j}⟩ = [j=0]`.

This theorem is the fully formal linear-algebraic passage from the deep
(11.9) projection statement to Coq's `o_eta0_betaT0`; the remaining
character-theoretic input is now exactly `hproj`. -/
theorem tSide_beta_inner_eta_of_zeroColumn_projection [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ)
    (hproj : ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q,
            base.eta i ⟨0, base.p_prime.pos⟩))
    (j : Fin base.p) :
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
      if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hsum : ClassFunction.inner
      (base.eta ⟨0, base.q_prime.pos⟩ j)
      (∑ i : Fin base.q, base.eta i ⟨0, base.p_prime.pos⟩) =
        if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    by_cases hj : j = ⟨0, base.p_prime.pos⟩
    · subst j
      rw [Finset.sum_eq_single_of_mem (⟨0, base.q_prime.pos⟩ : Fin base.q)
        (Finset.mem_univ _) (fun i _ hi => by
          rw [eta_orthonormal, if_neg]
          rintro ⟨h, -⟩
          exact hi h.symm)]
      rw [eta_orthonormal, if_pos ⟨rfl, rfl⟩]
      simp
    · simp only [if_neg hj]
      apply Finset.sum_eq_zero
      intro i _
      rw [eta_orthonormal, if_neg]
      exact fun h => hj h.2
  calc
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
        star (ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b) :=
      OddOrder.RepresentationTheory.inner_conj_symm _ _
    _ = star (if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) := by rw [hproj j, hsum]
    _ = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by split <;> simp

/-- **Peterfalvi (14.9), S/T gap assembly.**

Expand `Γ = σβ - 1 + η` and `Δ = τβ - 1 + a`.  Cross-Dade
orthogonality and the T-side β–η row give `⟨τβ, Γ⟩ = -1`;
principal orthogonality of `Γ` kills the trivial term.  Integrality of
the remaining virtual-character pairings removes the Hermitian
conjugations and yields `⟨Γ,a⟩ = 1 + ⟨Δ,Γ⟩`. -/
theorem gap_cross_inner_identity [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {Γ Δ τβ σβ η a one : ClassFunction G ℂ}
    (hΓZ : Γ ∈ ZIrr G) (haZ : a ∈ ZIrr G) (honeZ : one ∈ ZIrr G)
    (hΓ : Γ = σβ - one + η)
    (hΔ : Δ = τβ - one + a)
    (hτβ_one : ClassFunction.inner τβ one = 1)
    (hτβ_σβ : ClassFunction.inner τβ σβ = 0)
    (hτβ_eta : ClassFunction.inner τβ η = 0)
    (hΓ_one : ClassFunction.inner Γ one = 0) :
    ClassFunction.inner Γ a = 1 + ClassFunction.inner Δ Γ := by
  have hτβΓ : ClassFunction.inner τβ Γ = -1 := by
    rw [hΓ, ClassFunction.inner_add_right, ClassFunction.inner_sub_right,
      hτβ_σβ, hτβ_one, hτβ_eta]
    norm_num
  have honeΓ : ClassFunction.inner one Γ = 0 := by
    rw [inner_eq_swap_of_mem_ZIrr honeZ hΓZ, hΓ_one]
  have haΓ : ClassFunction.inner a Γ = ClassFunction.inner Γ a :=
    inner_eq_swap_of_mem_ZIrr haZ hΓZ
  rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    hτβΓ, honeΓ, haΓ]
  ring

end OddOrder.Peterfalvi.S16
