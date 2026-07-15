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
/-- **Peterfalvi (13.3.a), a chosen `𝒮₁` base**: the distinguished reducible
`μ`-column in `CharacterDegreeCore` contains a linear irreducible character of
`H = PC` whose kernel does not contain `P`.  This base is enough for the
`η₁₀` correction; no conditional `λ` datum is needed. -/
theorem CharacterDegreeCore.exists_hSharpBase [Finite G]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S),
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) := by
  haveI := hyp.finiteG
  obtain ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hμτ⟩ :=
    core.mu_col_tau1_eta_col_one
  exact ⟨⟨θ, hθirr⟩, hθP⟩

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

end

end OddOrder.Peterfalvi.S15
