/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapProjection

/-!
# Peterfalvi (11.9)(a): T-side eta-grid coefficient relations

The T-side Dade image of a class function supported on `A(T) = (T')#` vanishes on the
regular part of the shared cyclic subgroup `W`.  Peterfalvi (3.7) then gives the
four-corner relation for its integral eta-grid projection coefficients.  This is the
support-theoretic part of Coq `FTtype34_structure`'s `bridgeS1` calculation.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), regular-set vanishing of the T-side bridge.**
If `φ` is supported on `A(T) = T_σ#`, the restricted T-side Dade map agrees with the
full type-`P₁` map.  On the regular type-`P` set `V(T)`, the full map evaluates to `φ`,
which is zero because `V(T)` is disjoint from `T'`.  Class invariance extends the
vanishing to the conjugacy saturation used by the shared eta-grid. -/
theorem tSideDadeMap_vanish_on_etaRegular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ∀ x ∈ conjClassSet
      ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      tSideDadeMap hyp hG φ x = 0 := by
  classical
  let dataT := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
  have hdata := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose_spec
  have hW1 : dataT.W1 = hyp.base.W2 := hdata.2.1
  have hW2 : dataT.W2 = hyp.base.W1 := hdata.2.2
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
    have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification
      hG hyp.base.T_maximal
    exact (hcls.2.2.1.mp (Or.inl hIII)).1
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
  have hfullSupp : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  have hmaps : tSideDadeMap hyp hG φ =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData full.hconj) φ := by
    simpa only [full] using
      tSideDadeMap_eq_full_typeP1DadeMap_of_support hG hyp dataT hP1 hφsupp
  have hW : dataT.W = hyp.base.W := by
    rw [dataT.W_eq, hW1, hW2, hyp.base.W_eq_join, sup_comm]
  have hV : OddOrder.GroupTheory.typePV hyp.base.T dataT =
      (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) := by
    simp only [OddOrder.GroupTheory.typePV, hW, hW1, hW2, Set.union_comm]
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  rw [hmaps]
  rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
    (full.dade.fullDadeIsometryData full.hconj) φ).of_isConj
      (isConj_iff.mpr ⟨g, hg⟩)]
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.base.T dataT := hV.symm ▸ hw
  have hwA0 : w ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT :=
    Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
    (full.dade.fullDadeIsometryData full.hconj) hfullSupp]
  let a : {a : G // a ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT} := ⟨w, hwA0⟩
  have hwh : w ∈ full.dade.hCoset a := ⟨1, full.dade.H a |>.one_mem, by simp [a]⟩
  rw [full.dade.isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
  by_contra hne
  have hwSupp : (⟨w, full.dade.mem_L hwA0⟩ : ↥hyp.base.T) ∈ φ.support :=
    ClassFunction.mem_support.mpr hne
  have hwSigma : w ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T := hφsupp hwSupp
  have hwDeriv : w ∈ derivedInG hyp.base.T := by
    rw [OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma
      hG hyp.base.T_maximal hP1]
    exact hwSigma.1
  exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived dataT hwV) hwDeriv

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The T-side bridge coefficients satisfy Peterfalvi's (3.7) four-corner relation. -/
theorem tSideDadeMap_etaGrid_relation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ClassFunction.inner (tSideDadeMap hyp hG φ) (hyp.base.eta i j) +
        ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) =
      ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) +
        ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  exact inner_eta_grid_relation hyp.base
    (tSideDadeMap_vanish_on_etaRegular hG hyp hIII hφsupp) i j

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the principal T-side eta coefficient.**
Dade reciprocity preserves the trivial multiplicity, and `η₀₀ = 1_G`. -/
theorem tSideDadeMap_inner_eta_principal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) =
      ClassFunction.inner φ (trivialClassFunction ↥hyp.base.T) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  rw [eta_principal_eq_trivial hyp.base,
    tSideDadeMap_inner_trivial hyp hG hφsupp]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral T-side projection with principal and four-corner data.** -/
theorem exists_tSide_etaGrid_intProjection_with_relation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hφone : ClassFunction.inner φ
      (trivialClassFunction ↥hyp.base.T) = 1)
    (hτZ : tSideDadeMap hyp hG φ ∈ ZIrr G)
    (hτnorm : ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG φ) =
      (((hyp.base.p : ℤ) + 1) : ℂ)) :
    ∃ m : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, ClassFunction.inner (tSideDadeMap hyp hG φ) (hyp.base.eta i j) =
        (m i j : ℂ)) ∧
      ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG φ) =
        ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner
            (tSideDadeMap hyp hG φ - etaGridProjection hyp.base m)
            (tSideDadeMap hyp hG φ - etaGridProjection hyp.base m) ∧
      (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) ≤
        (hyp.base.p : ℤ) + 1 ∧
      m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 ∧
      (∀ i j, m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j) := by
  obtain ⟨m, hcoeff, hpyth, hbound⟩ :=
    exists_etaGrid_intProjection_of_inner_self_eq hyp.base hτZ hτnorm
  have hprincipalC := tSideDadeMap_inner_eta_principal hG hyp hφsupp
  rw [hφone,
    hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩] at hprincipalC
  have hprincipal :
      m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    exact_mod_cast hprincipalC
  have hrelation : ∀ i j,
      m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j := by
    intro i j
    have h := tSideDadeMap_etaGrid_relation hG hyp hIII hφsupp i j
    rw [hcoeff i j,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff i ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ j] at h
    exact_mod_cast h
  exact ⟨m, hcoeff, hpyth, hbound, hprincipal, hrelation⟩

/-- **Peterfalvi (11.9)(a), the axis-coefficient arithmetic.**
Suppose the nonprincipal row and column coefficients are constant, the four-corner
coefficient is their sum minus the principal coefficient `1`, and the projection norm
is at most `p`, where `3 ≤ q < p`.  Then exactly the two axis projections remain:
the zero-column coefficients `(1,0,0)` or the zero-row coefficients `(0,1,0)`.

This is the integer inequality core of Coq `FTtype34_structure`.  The character-theoretic
(11.8) non-orthogonality subsequently excludes the zero-row alternative. -/
theorem axis_coefficients_eq_column_or_row
    {q p a10 a01 a11 : ℤ}
    (hq : 3 ≤ q) (hp : 3 ≤ p) (hqp : q < p)
    (hrelation : a11 = a10 + a01 - 1)
    (hbound :
      1 + (q - 1) * a10 ^ 2 + (p - 1) * a01 ^ 2 +
        (q - 1) * (p - 1) * a11 ^ 2 ≤ p) :
    (a10 = 1 ∧ a01 = 0 ∧ a11 = 0) ∨
      (a10 = 0 ∧ a01 = 1 ∧ a11 = 0) := by
  have hq0 : 0 ≤ q - 1 := by omega
  have hp0 : 0 ≤ p - 1 := by omega
  have h10nonneg : 0 ≤ (q - 1) * a10 ^ 2 :=
    mul_nonneg hq0 (sq_nonneg a10)
  have h01nonneg : 0 ≤ (p - 1) * a01 ^ 2 :=
    mul_nonneg hp0 (sq_nonneg a01)
  have hprod0 : 0 ≤ (q - 1) * (p - 1) := mul_nonneg hq0 hp0
  have h11nonneg : 0 ≤ (q - 1) * (p - 1) * a11 ^ 2 :=
    mul_nonneg hprod0 (sq_nonneg a11)
  have ha11 : a11 = 0 := by
    by_contra hne
    have hsquare : 1 ≤ a11 ^ 2 := by
      nlinarith [Int.one_le_abs hne, sq_abs a11]
    have hlower := mul_le_mul_of_nonneg_left hsquare hprod0
    have hgap : 0 ≤ (q - 3) * (p - 1) :=
      mul_nonneg (by omega) hp0
    nlinarith
  have hsum : a10 + a01 = 1 := by omega
  by_cases h01 : a01 = 0
  · left
    refine ⟨by omega, h01, ha11⟩
  · have h01square : 1 ≤ a01 ^ 2 := by
      nlinarith [Int.one_le_abs h01, sq_abs a01]
    have h01lower := mul_le_mul_of_nonneg_left h01square hp0
    have ha10 : a10 = 0 := by
      by_contra h10
      have h10square : 1 ≤ a10 ^ 2 := by
        nlinarith [Int.one_le_abs h10, sq_abs a10]
      have h10lower := mul_le_mul_of_nonneg_left h10square hq0
      nlinarith
    right
    refine ⟨ha10, by omega, ha11⟩

/-- **Peterfalvi (11.9)(a), full-grid norm compression.**  If the eta-projection coefficients
are constant on each nonprincipal axis and satisfy the four-corner relation, their full squared
norm is exactly the three-coefficient expression used by `axis_coefficients_eq_column_or_row`.

This is the finite-grid bookkeeping between the already-proven sharp projection bound
`sum m_ij^2 <= p` and the arithmetic dichotomy.  It partitions each axis into its principal point
and complement; the four-corner relation makes every interior coefficient equal to `m_11`. -/
theorem etaGrid_axis_sum_eq_sum_sq
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j) :
    1 + ((base.q : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
        ((base.p : ℤ) - 1) *
          m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
        ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 =
      ∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 := by
  classical
  let i0 : Fin base.q := ⟨0, base.q_prime.pos⟩
  let j0 : Fin base.p := ⟨0, base.p_prime.pos⟩
  let i1 : Fin base.q := ⟨1, base.q_prime.one_lt⟩
  let j1 : Fin base.p := ⟨1, base.p_prime.one_lt⟩
  have hinter : ∀ i, i ≠ i0 → ∀ j, j ≠ j0 → m i j = m i1 j1 := by
    intro i hi j hj
    have hij := hrelation i j
    have h11 := hrelation i1 j1
    have h00 : m i0 j0 = 1 := by simpa [i0, j0] using hprincipal
    have hi0 : m i j0 = m i1 j0 := by
      simpa [i0, i1, j0] using hrow i (by simpa [i0] using hi)
    have h0j : m i0 j = m i0 j1 := by
      simpa [i0, j0, j1] using hcol j (by simpa [j0] using hj)
    change m i j + m i0 j0 = m i j0 + m i0 j at hij
    change m i1 j1 + m i0 j0 = m i1 j0 + m i0 j1 at h11
    rw [h00, hi0, h0j] at hij
    rw [h00] at h11
    omega
  have sum_eq_base_add_const : ∀ {n : ℕ} (x0 : Fin n) (f : Fin n → ℤ) (a b : ℤ),
      f x0 = a → (∀ x, x ≠ x0 → f x = b) →
        (∑ x : Fin n, f x) = a + ((n : ℤ) - 1) * b := by
    intro n x0 f a b hx0 hrest
    have hn : 1 ≤ n := by
      have hx0lt := x0.isLt
      omega
    calc
      (∑ x : Fin n, f x) =
          (∑ x ∈ Finset.univ.erase x0, f x) + f x0 :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ x0)).symm
      _ = (∑ x ∈ Finset.univ.erase x0, b) + a := by
        rw [hx0]
        congr 1
        exact Finset.sum_congr rfl fun x hx => hrest x (Finset.ne_of_mem_erase hx)
      _ = a + ((n : ℤ) - 1) * b := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ x0),
          Finset.card_univ, Fintype.card_fin]
        push_cast [Nat.cast_sub hn]
        ring
  have hrow0 : (∑ j : Fin base.p, (m i0 j) ^ 2) =
      1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 := by
    apply sum_eq_base_add_const j0 _ 1 ((m i0 j1) ^ 2)
    · simp only [i0, j0, hprincipal, one_pow]
    · intro j hj
      rw [hcol j (by simpa [j0] using hj)]
  have hrowOther : ∀ i, i ≠ i0 →
      (∑ j : Fin base.p, (m i j) ^ 2) =
        (m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2 := by
    intro i hi
    apply sum_eq_base_add_const j0 _ ((m i1 j0) ^ 2) ((m i1 j1) ^ 2)
    · rw [hrow i (by simpa [i0] using hi)]
    · intro j hj
      rw [hinter i hi j hj]
  have hgrid := sum_eq_base_add_const i0
    (fun i => ∑ j : Fin base.p, (m i j) ^ 2)
    (1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2)
    ((m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2)
    hrow0 hrowOther
  change
    1 + ((base.q : ℤ) - 1) * (m i1 j0) ^ 2 +
          ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 +
          ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) * (m i1 j1) ^ 2 =
        ∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2
  calc
    _ = 1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 +
          ((base.q : ℤ) - 1) *
            ((m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2) := by ring
    _ = _ := hgrid.symm

/-- The sharp full-grid coefficient bound supplies the axis bound expected by the arithmetic
dichotomy. -/
theorem etaGrid_axis_bound_of_sum_sq_le
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (hfull : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ base.p) :
    1 + ((base.q : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
        ((base.p : ℤ) - 1) *
          m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
        ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 ≤ base.p := by
  rw [etaGrid_axis_sum_eq_sum_sq base m hprincipal hrow hcol hrelation]
  exact hfull

/-- Lift the three-coefficient arithmetic classification to the full eta-grid.
The axis-constancy hypotheses are the exact output expected from Peterfalvi (3.9)(b)
and Dade--Galois commutation. -/
theorem etaGrid_coefficients_eq_column_or_row
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hqp : base.q < base.p)
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (haxisBound :
      1 + ((base.q : ℤ) - 1) *
            m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
          ((base.p : ℤ) - 1) *
            m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
          ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
            m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 ≤
        (base.p : ℤ)) :
    (∀ i j, m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) ∨
      (∀ i j, m i j = if i = ⟨0, base.q_prime.pos⟩ then 1 else 0) := by
  let i0 : Fin base.q := ⟨0, base.q_prime.pos⟩
  let j0 : Fin base.p := ⟨0, base.p_prime.pos⟩
  let i1 : Fin base.q := ⟨1, base.q_prime.one_lt⟩
  let j1 : Fin base.p := ⟨1, base.p_prime.one_lt⟩
  have hqZ : (3 : ℤ) ≤ base.q := by exact_mod_cast base.three_le_q
  have hpZ : (3 : ℤ) ≤ base.p := by exact_mod_cast base.three_le_p
  have hqpZ : (base.q : ℤ) < base.p := by exact_mod_cast hqp
  have haxis := axis_coefficients_eq_column_or_row hqZ hpZ hqpZ
    (show m i1 j1 = m i1 j0 + m i0 j1 - 1 by
      have h := hrelation i1 j1
      have hp0 : m i0 j0 = 1 := by simpa [i0, j0] using hprincipal
      change m i1 j1 + m i0 j0 = m i1 j0 + m i0 j1 at h
      rw [hp0] at h
      omega)
    (by simpa [i0, j0, i1, j1] using haxisBound)
  rcases haxis with hcolumn | hrowAxis
  · left
    intro i j
    by_cases hj : j = j0
    · rw [if_pos (by simpa [j0] using hj)]
      by_cases hi : i = i0
      · rw [hi, hj]
        simpa [i0, j0] using hprincipal
      · rw [hj]
        simpa [i0, j0, i1] using
          (hrow i (by simpa [i0] using hi)).trans hcolumn.1
    · rw [if_neg (by simpa [j0] using hj)]
      by_cases hi : i = i0
      · rw [hi]
        simpa [i0, j0, j1] using (hcol j (by simpa [j0] using hj)).trans hcolumn.2.1
      · have h := hrelation i j
        rw [hprincipal, hrow i (by simpa [i0] using hi),
          hcol j (by simpa [j0] using hj), hcolumn.1, hcolumn.2.1] at h
        omega
  · right
    intro i j
    by_cases hi : i = i0
    · rw [if_pos (by simpa [i0] using hi)]
      by_cases hj : j = j0
      · rw [hi, hj]
        simpa [i0, j0] using hprincipal
      · rw [hi]
        simpa [i0, j0, j1] using
          (hcol j (by simpa [j0] using hj)).trans hrowAxis.2.1
    · rw [if_neg (by simpa [i0] using hi)]
      by_cases hj : j = j0
      · rw [hj]
        simpa [i0, j0, i1] using (hrow i (by simpa [i0] using hi)).trans hrowAxis.1
      · have h := hrelation i j
        rw [hprincipal, hrow i (by simpa [i0] using hi),
          hcol j (by simpa [j0] using hj), hrowAxis.1, hrowAxis.2.1] at h
        omega

/-- **Peterfalvi (11.9)(a), eta-grid projection rigidity.**  The sharp bound on the full
integer projection grid, together with the Galois-axis constancy and the four-corner relation,
forces the grid to be a coordinate row or column.  Unlike
`etaGrid_coefficients_eq_column_or_row`, this is stated with the full squared norm produced by
the projection argument. -/
theorem etaGrid_coefficients_eq_column_or_row_of_sum_sq_le
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hqp : base.q < base.p)
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (hfull : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ base.p) :
    (∀ i j, m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) ∨
      (∀ i j, m i j = if i = ⟨0, base.q_prime.pos⟩ then 1 else 0) := by
  apply etaGrid_coefficients_eq_column_or_row base hqp m hprincipal hrow hcol hrelation
  exact etaGrid_axis_bound_of_sum_sq_le base m hprincipal hrow hcol hrelation hfull

end OddOrder.Peterfalvi.S16
