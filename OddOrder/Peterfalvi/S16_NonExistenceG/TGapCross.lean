import OddOrder.Peterfalvi.S16_NonExistenceG.TGapDelta
import OddOrder.Peterfalvi.S16_GridExpansion

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
