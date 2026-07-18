/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerResidual
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLDistinguished
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiRoot
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiDistinguished
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSUDistinguished

/-!
# Peterfalvi Part II, Ch. I §3: the centralizer trichotomy

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Proposition 1(c), pp. 105–106.

This file assembles the classification-independent centralizer residual facts
and the three concrete branches supplied by Suzuki's Theorem A.  For a
nontrivial `X ≤ V`, put `C = C_G(X)`, `C_Q = C_Q(X)`, and
`F = O^{2′}(C)`.  The common conclusion identifies `F` with the normal
closure of `C_Q`, identifies the action kernel inside that normal closure
with its center, and proves `C_{Q₁}(X) = 1`.

The branch data then give the exact alternatives in the source:

* `PSL(2,ℓ)`, with elementary-abelian `C_Q`, `|C_Q| = ℓ`, and `|st| = 3`;
* `Sz(ℓ)`, with type-A Suzuki root `C_Q`, `|C_Q| = ℓ²`, and `|st| = 5`;
* `PSU(3,ℓ)`, with Suzuki `2`-group root `C_Q`, `|C_Q| = ℓ³`, and
  `|st| = 3`.

In accordance with Proposition 1(c), the unitary branch does not assert a
type-B structure: that stronger conclusion belongs to a later result with
an additional hypothesis.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

section /- §3 Proposition 1(c) (pp. 105–106) -/

/-- The classification-independent part of **Peterfalvi Part II, Ch. I §3,
Proposition 1(c)** for `C = C_G(X)` and `C_Q = C_Q(X)`. -/
structure CentralizerCommonData (hyp : Hypothesis G Omega)
    (X : Subgroup G) where
  cQ_isPGroup :
    IsPGroup 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
  q1_inf_centralizer_eq_bot :
    hyp.Q1 ⊓ Subgroup.centralizer (X : Set G) = ⊥
  residual_eq_normalClosure :
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    let C_Q : Subgroup C := hyp.Q.subgroupOf C
    Subgroup.primeComplementResidual 2 C =
      Subgroup.normalClosure (C_Q : Set C)
  normalCore_subgroupOf_normalClosure_eq_center :
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    let C_H : Subgroup C := hyp.H.subgroupOf C
    let C_Q : Subgroup C := hyp.Q.subgroupOf C
    let F : Subgroup C := Subgroup.normalClosure (C_Q : Set C)
    C_H.normalCore.subgroupOf F = Subgroup.center F

/-- The exact `PSL(2,ℓ)` payload in Proposition 1(c). -/
structure CentralizerPSLData (hyp : Hypothesis G Omega) (X : Subgroup G)
    [MulAction (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)]
    (result : TheoremAConclusion (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega))
    (data : PSL2InductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) where
  residualQuotientEquiv :
    letI : Field data.F := data.fieldF
    letI : Finite data.F := data.finiteF
    letI : CharP data.F 2 := data.charTwoF
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    ((Subgroup.primeComplementResidual 2 C) ⧸
        Subgroup.center (Subgroup.primeComplementResidual 2 C)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F
  cQEquivRoot :
    letI : Field data.F := data.fieldF
    letI : Finite data.F := data.finiteF
    letI : CharP data.F 2 := data.charTwoF
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.rootSubgroup
        (F := data.F)
  distinguishedProduct_order :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3
  cQ_isElementaryAbelian :
    OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
  natCard_cQ0_eq_field :
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card data.F
  natCard_cQ_eq_field :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card data.F

/-- The exact `Sz(ℓ)` payload in Proposition 1(c), including constructive
type-A coordinates whose parameter is the parameter of the induction
target. -/
structure CentralizerSuzukiData (hyp : Hypothesis G Omega) (X : Subgroup G)
    [MulAction (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)]
    (result : TheoremAConclusion (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega))
    (data : SuzukiInductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) where
  residualQuotientEquiv :
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    ((Subgroup.primeComplementResidual 2 C) ⧸
        Subgroup.center (Subgroup.primeComplementResidual 2 C)) ≃*
      OddOrder.GroupTheory.SpecificGroups.Suzuki.standardPermGroup data.m
  cQEquivRoot :
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      OddOrder.GroupTheory.SpecificGroups.Suzuki.RootGroup data.m
  standardTypeAData :
    OddOrder.GroupTheory.SpecificGroups.Suzuki.StandardTypeAData
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
  standardTypeA_parameter : standardTypeAData.parameter = data.m
  distinguishedProduct_order :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 5
  cQ_isSuzuki2Group :
    OddOrder.Peterfalvi.Appendices.Suzuki2Groups.IsSuzuki2Group
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
  natCard_cQ0_eq_field :
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (OddOrder.GroupTheory.SpecificGroups.Suzuki.Field data.m)
  natCard_cQ_eq_field_sq :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (OddOrder.GroupTheory.SpecificGroups.Suzuki.Field data.m) ^ 2
  natCard_cQ_eq_cQ0_sq :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 2

/-- The exact `PSU(3,ℓ)` payload in Proposition 1(c).  Deliberately there is
no type-B field: Proposition 1(c) only proves that this root is a Suzuki
`2`-group. -/
structure CentralizerPSUData (hyp : Hypothesis G Omega) (X : Subgroup G)
    [MulAction (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)]
    (result : TheoremAConclusion (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega))
    (data : PSU3InductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) where
  residualQuotientEquiv :
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    ((Subgroup.primeComplementResidual 2 C) ⧸
        Subgroup.center (Subgroup.primeComplementResidual 2 C)) ≃*
      OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.standardPermGroup
        data.n
  cQEquivRoot :
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroup data.n
  distinguishedProduct_order :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3
  cQ_isSuzuki2Group :
    OddOrder.Peterfalvi.Appendices.Suzuki2Groups.IsSuzuki2Group
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
  natCard_cQ0_eq_baseField :
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card
        (OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.BaseField data.n)
  natCard_cQ_eq_baseField_cube :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card
        (OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.BaseField data.n) ^ 3
  natCard_cQ_eq_cQ0_cube :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 3

/-- Branch data tied by equality to the actual target carried by the
`TheoremAConclusion` returned by induction. -/
inductive CentralizerBranchData (hyp : Hypothesis G Omega) (X : Subgroup G)
    [MulAction (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)]
    (result : TheoremAConclusion (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)) where
  | psl2 (data : PSL2InductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L)
      (target_eq : result.target = TheoremATarget.psl2 data)
      (details : CentralizerPSLData hyp X result data)
  | suzuki (data : SuzukiInductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L)
      (target_eq : result.target = TheoremATarget.suzuki data)
      (details : CentralizerSuzukiData hyp X result data)
  | psu3 (data : PSU3InductionTarget
      (Omega := ↥(MulAction.fixedPoints X Omega)) result.L)
      (target_eq : result.target = TheoremATarget.psu3 data)
      (details : CentralizerPSUData hyp X result data)

/-- The assembled data of **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**:
the actual conclusion returned by induction, the common centralizer residual
facts, and the exact matching concrete branch. -/
structure CentralizerTrichotomyData (hyp : Hypothesis G Omega)
    (X : Subgroup G)
    [MulAction (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Omega)] where
  result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Omega)
  common : CentralizerCommonData hyp X
  branch : CentralizerBranchData hyp X result

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c).**
Apply Suzuki's Theorem A inductively to the faithful centralizer quotient
and assemble its three alternatives with all source-level conclusions for
the original group `C_G(X)`.

The quotient model is retained as the existing `TheoremAConclusion`; the
branch equality ensures that every concrete payload is the branch actually
returned by induction. -/
theorem centralizer_trichotomy_of_induction (hyp : Hypothesis G Omega)
    {X : Subgroup G} (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (inductionHypothesis : TheoremAInductionBelow G Omega) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nonempty (CentralizerTrichotomyData hyp X) := by
  letI := hyp.centralizerQuotientMulAction hXV
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let C_Q : Subgroup C := hyp.Q.subgroupOf C
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hsmall : Nat.card (hyp.centralizerActionQuotient X) < Nat.card G :=
    hyp.card_centralizerActionQuotient_lt hXV hX
  obtain ⟨result⟩ := inductionHypothesis hsmall qhyp
  have hresultCore := result.Q_and_residual qhyp
  have hQbar : IsPGroup 2 qhyp.Q := hresultCore.1
  have hCQ : IsPGroup 2 C_Q :=
    hyp.centralizer_cQ_isPGroup_of_quotient hXV hQbar
  have hCQinf : IsPGroup 2 ↥(hyp.Q ⊓ C) := by
    have hsub : IsPGroup 2 ↥((hyp.Q ⊓ C).subgroupOf C) := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hCQ
    exact hsub.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : hyp.Q ⊓ C ≤ C))
  have hQ1 : hyp.Q1 ⊓ C = ⊥ :=
    hyp.Q1_inf_centralizer_eq_bot_of_isPGroup X hCQinf
  obtain ⟨P, hP⟩ := hyp.exists_sylow_two_eq_cQ_of_isPGroup hXV hCQ
  have hResidual : Subgroup.primeComplementResidual 2 C =
      Subgroup.normalClosure (C_Q : Set C) := by
    rw [Subgroup.primeComplementResidual_eq_normalClosure P, hP]
  let common : CentralizerCommonData hyp X :=
    { cQ_isPGroup := hCQ
      q1_inf_centralizer_eq_bot := hQ1
      residual_eq_normalClosure := hResidual
      normalCore_subgroupOf_normalClosure_eq_center :=
        hyp.normalCore_subgroupOf_normalClosure_cQ_eq_center hXV }
  have hresultResidual : result.L =
      Subgroup.primeComplementResidual 2
        (hyp.centralizerActionQuotient X) := hresultCore.2.2.1
  cases htarget : result.target with
  | psl2 data =>
      letI : Field data.F := data.fieldF
      letI : Finite data.F := data.finiteF
      letI : CharP data.F 2 := data.charTwoF
      have eTarget :
          Subgroup.primeComplementResidual 2
              (hyp.centralizerActionQuotient X) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F := by
        rw [← hresultResidual]
        exact data.groupEquiv
      let details : CentralizerPSLData hyp X result data :=
        { residualQuotientEquiv :=
            (hyp.centralizerResidualQuotientEquiv hXV hCQ).trans eTarget
          cQEquivRoot :=
            hyp.centralizerCQMulEquivPSLRoot hXV hA3 result data
          distinguishedProduct_order :=
            hyp.orderOf_distinguishedInvolution_mul_t_of_centralizer_psl2Target
              hXV hA3 result data
          cQ_isElementaryAbelian :=
            hyp.centralizerCQ_isElementaryAbelian_of_psl2Target
              hXV hA3 result data
          natCard_cQ0_eq_field :=
            hyp.natCard_centralizerQ0_eq_field_of_psl2Target
              hXV hA3 result data
          natCard_cQ_eq_field :=
            hyp.natCard_centralizerCQ_eq_field_of_psl2Target
              hXV hA3 result data }
      exact ⟨
        { result := result
          common := common
          branch := .psl2 data htarget details }⟩
  | suzuki data =>
      have eTarget :
          Subgroup.primeComplementResidual 2
              (hyp.centralizerActionQuotient X) ≃*
            OddOrder.GroupTheory.SpecificGroups.Suzuki.standardPermGroup
              data.m := by
        rw [← hresultResidual]
        exact data.groupEquiv
      let details : CentralizerSuzukiData hyp X result data :=
        { residualQuotientEquiv :=
            (hyp.centralizerResidualQuotientEquiv hXV hCQ).trans eTarget
          cQEquivRoot :=
            hyp.centralizerCQMulEquivSuzukiRoot hXV hA3 result data
          standardTypeAData :=
            hyp.centralizerCQStandardTypeAData_of_suzukiTarget
              hXV hA3 result data
          standardTypeA_parameter := rfl
          distinguishedProduct_order :=
            hyp.orderOf_distinguishedInvolution_mul_t_of_centralizer_suzukiTarget
              hXV hA3 result data
          cQ_isSuzuki2Group :=
            hyp.centralizerCQ_isSuzuki2Group_of_suzukiTarget
              hXV hA3 result data
          natCard_cQ0_eq_field :=
            hyp.natCard_centralizerQ0_eq_field_of_suzukiTarget
              hXV hA3 result data
          natCard_cQ_eq_field_sq :=
            hyp.natCard_centralizerCQ_eq_field_sq_of_suzukiTarget
              hXV hA3 result data
          natCard_cQ_eq_cQ0_sq :=
            hyp.natCard_centralizerCQ_eq_centralizerQ0_sq_of_suzukiTarget
              hXV hA3 result data }
      exact ⟨
        { result := result
          common := common
          branch := .suzuki data htarget details }⟩
  | psu3 data =>
      have eTarget :
          Subgroup.primeComplementResidual 2
              (hyp.centralizerActionQuotient X) ≃*
            OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.standardPermGroup
              data.n := by
        rw [← hresultResidual]
        exact data.groupEquiv
      let details : CentralizerPSUData hyp X result data :=
        { residualQuotientEquiv :=
            (hyp.centralizerResidualQuotientEquiv hXV hCQ).trans eTarget
          cQEquivRoot :=
            hyp.centralizerCQMulEquivPSURoot hXV hA3 result data
          distinguishedProduct_order :=
            hyp.orderOf_distinguishedInvolution_mul_t_of_centralizer_psu3Target
              hXV hA3 result data
          cQ_isSuzuki2Group :=
            hyp.centralizerCQ_isSuzuki2Group_of_psu3Target
              hXV hA3 result data
          natCard_cQ0_eq_baseField :=
            hyp.natCard_centralizerQ0_eq_baseField_of_psu3Target
              hXV hA3 result data
          natCard_cQ_eq_baseField_cube :=
            hyp.natCard_centralizerCQ_eq_baseField_cube_of_psu3Target
              hXV hA3 result data
          natCard_cQ_eq_cQ0_cube :=
            hyp.natCard_centralizerCQ_eq_centralizerQ0_cube_of_psu3Target
              hXV hA3 result data }
      exact ⟨
        { result := result
          common := common
          branch := .psu3 data htarget details }⟩

end

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
