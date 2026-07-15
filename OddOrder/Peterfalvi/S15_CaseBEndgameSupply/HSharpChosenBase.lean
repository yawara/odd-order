/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CharacterDegreeEnginesSSide

/-!
# Peterfalvi §13 (pp. 75–86) — chosen-base `H^#` endgame supply

This file begins the `CharacterDegreeData`-free reconstruction of the (13.5)/(13.6)
`H^#` correction packages.  Its input is the honest pair `CharacterDegreeCore` and
`LambdaClusterData`.

The distinguished nonkernel base is selected from the reducible `μ`-column supplied by the
core.  Its induction cannot equal `λ`, since that would make the column irreducible.  This
gives a chosen (7.6) family whose base is distinct from `λ`, so `λ` occurs at a positive
index and the guarded coefficient theorem `lambda_tau1_cCoeff_base` applies.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.3)–(13.5): chosen-base `H^#` correction data (pp. 78–82) -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), chosen `𝒶₁` base for (13.5)**: the distinguished reducible
`μ`-column in `CharacterDegreeCore` supplies a `P`-nonkernel irreducible character `φ₀` of
`H = PC`.  Its induction is different from the irreducible `λ`; otherwise the column sum
would be irreducible. -/
theorem CharacterDegreeCore.exists_hSharpBase_ne_lambda [Finite G]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp)
    (lam : LambdaClusterData hyp) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S),
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) ∧
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda := by
  haveI := hyp.finiteG
  obtain ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hμτ⟩ :=
    core.mu_col_tau1_eta_col_one
  refine ⟨⟨θ, hθirr⟩, hθP, ?_⟩
  intro heq
  apply hyp.mu_colSum_not_irreducible j
  rw [hμeq, heq]
  exact lam.lambda_irreducible

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.d)/(13.3), Core form**: `λ^{τ₁}` is a norm-one virtual
character.  The `P`-nonkernel witness stored in `LambdaClusterData` is exactly the guard needed
by the honest `CharacterDegreeCore` coherence fields. -/
theorem lambda_tau1_norm_one_core [Finite G] {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    core.tau1S lam.lambda ∈ ZIrr G ∧
      ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 ∧
      ClassFunction.inner lam.lambda lam.lambda = 1 := by
  haveI := hyp.finiteG
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hnorm : ClassFunction.inner lam.lambda lam.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨lam.lambda, lam.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨lam.lambda, lam.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact core.tau1S_induce_mem_ZIrr θ hθirr hθP
  · rw [hlamEq, core.tau1S_inner_induce θ θ hθirr hθirr hθP hθP, ← hlamEq]
    exact hnorm

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base membership half**: `λ = Ind_H^S θ` occurs
in the (7.6) family based at `φ₀`.  It occurs at a positive index because the chosen base
induction is assumed distinct from `λ`; its `P`-nonkernel witness descends through induction. -/
theorem LambdaClusterData.exists_hSharpFamilyIndex_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
  classical
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  obtain ⟨i₁, hi₁⟩ :=
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta_family_cover ⟨θ, hθirr⟩
  have heq : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
    rw [hi₁, hlamEq]
    congr!
  have hker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) := by
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr hx₀P
    have hmem : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) := by
      have h1 := hsub hx₀S
      rw [heq, hlamEq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) hθirr x₀.2 hmem
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥(hyp.H.subgroupOf hyp.S)) = x₀ from rfl]
      at hbridge
  refine ⟨i₁, ?_, hker, heq⟩
  rw [Fin.pos_iff_ne_zero]
  intro hzero
  apply hφ₀ne
  rw [← heq, hzero, H_sharp_hypothesis76_base_zeta_zero]

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base distinguished index**: combines family
membership with the guarded (7.7.a) coefficient computation.  This is the honest
`CharacterDegreeCore`/`LambdaClusterData` replacement for the legacy `exists_lambda_index`. -/
theorem CharacterDegreeCore.exists_lambda_index_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i = 0) := by
  obtain ⟨i₁, hpos, hker, heq⟩ := lam.exists_hSharpFamilyIndex_base hG φ₀ hφ₀ne
  obtain ⟨hc1, hmid⟩ := lambda_tau1_cCoeff_base hG core lam φ₀ hφ₀P hφ₀ne i₁ heq
  exact ⟨i₁, hpos, hker, heq, hc1, fun i _ hine hiP => hmid i hine hiP⟩

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5.a), chosen-base decomposition**: on `H^#`, a test character is the
explicit (7.7.a) `ρ`-sum for the family based at `φ₀`. -/
theorem H_sharp_chiRho_eq_explicit_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ) (a : hyp.S)
    (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      ∑ i ∈ Finset.Ioi (0 : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1)),
        (star ((H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i) /
            (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i) *
          (H_sharp_hypothesis76_base hG hyp φ₀).zeta i a :=
  (chiRho_eq_self_of_H_eq_bot (H_sharp_hypothesis71 hG hyp) (fun _ => rfl) χ a ha).symm.trans
    (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula
      (H_sharp_hypothesis76_base hG hyp φ₀) χ ha)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.a), chosen-base point formula**: after extracting a distinguished
`P`-nonkernel index and dropping the remaining nonkernel coefficients, the residual sum is
the `P`-kernel correction tail. -/
theorem H_sharp_point_formula_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ)
    (i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1)) (hi₁ : 0 < i₁)
    (hi₁ker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)))
    (hmiddle : ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      0 < i → i ≠ i₁ →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i = 0)
    (a : hyp.S) (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      (star ((H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i₁) /
          (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁) *
        (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ a
      + ∑ i ∈
          (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel
                ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)),
          (star ((H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i) /
            (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i) *
              (H_sharp_hypothesis76_base hG hyp φ₀).zeta i a := by
  classical
  rw [H_sharp_chiRho_eq_explicit_base hG hyp φ₀ χ a ha,
    ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi₁)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i₁)
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i₁).filter (fun i =>
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i))),
      (star ((H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i) /
        (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i) *
          (H_sharp_hypothesis76_base hG hyp φ₀).zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2,
      star_zero, zero_div, zero_mul]
  have hi₁notin : i₁ ∉
      (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))).filter
        (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) := by
    rw [Finset.mem_filter]
    exact fun h => hi₁ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi₁notin]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- The chosen-base (13.5.a) correction `α`: the `P`-kernel tail of the (7.7.a)
decomposition. -/
noncomputable def H_sharp_alphaFun_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ) : ↥hyp.S → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))).filter
        (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)),
      (star ((H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i) /
        (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i) *
          (H_sharp_hypothesis76_base hG hyp φ₀).zeta i a

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The chosen-base correction is constant on `P`, since every family member in its tail has
`P` in its kernel. -/
theorem H_sharp_alphaFun_base_const_on_P [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ hyp.P.subgroupOf hyp.S,
      H_sharp_alphaFun_base hG hyp φ₀ χ x = H_sharp_alphaFun_base hG hyp φ₀ χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  have hx1 : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i x
      = (H_sharp_hypothesis76_base hG hyp φ₀).zeta i 1 := hker hx
  rw [hx1]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The chosen-base correction vanishes outside `H`, since every family member is induced
from `H`. -/
theorem H_sharp_alphaFun_base_eq_zero_of_not_mem [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → H_sharp_alphaFun_base hG hyp φ₀ χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i x = 0 := by
    refine (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i x ?_
    intro hmem
    exact hx (Subgroup.mem_subgroupOf.mpr (by
      rwa [show (H_sharp_hypothesis76_base hG hyp φ₀).H = hyp.H from rfl] at hmem))
  rw [hzero, mul_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.c), chosen-base form**: the `P`-constant correction tail satisfies
`(|P| - 1) ‖α(1)‖² ≤ ∑_{x∈H^#} ‖α(x)‖²`. -/
theorem H_sharp_alphaFun_base_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖H_sharp_alphaFun_base hG hyp φ₀ χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖H_sharp_alphaFun_base hG hyp φ₀ χ x‖ ^ 2 := by
  classical
  set α := H_sharp_alphaFun_base hG hyp φ₀ χ with hαdef
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup (hyp.P.subgroupOf hyp.S) α
    (H_sharp_alphaFun_base_const_on_P hG hyp φ₀ χ)
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hcard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hsupp : ∑ x : ↥hyp.S, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.H.subgroupOf hyp.S)]
    have hzero : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
        ‖α x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, H_sharp_alphaFun_base_eq_zero_of_not_mem hG hyp φ₀ χ x
        (Finset.mem_filter.mp hx).2]
      simp
    rw [hzero, add_zero]
  have hone : (1 : ↥hyp.S) ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hyp.H.subgroupOf hyp.S).one_mem⟩
  have hsharp :
      ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2
        = (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2)
          - ‖α 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hone]
    ring
  rw [hsharp, ← hsupp]
  calc
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖α 1‖ ^ 2
        = ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ) - 1) * ‖α 1‖ ^ 2 := by
          rw [hcard]
          congr 1
          have h1 : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
            Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
          rw [Nat.cast_sub h1]
          norm_num
    _ ≤ (∑ x : ↥hyp.S, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := hcore

end

end OddOrder.Peterfalvi.S15
