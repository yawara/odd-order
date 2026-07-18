/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupSuzukiType
import OddOrder.GroupTheory.SpecificGroups.Suzuki.RootSubgroupSuzukiType
import OddOrder.GroupTheory.SylowTransport
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge

/-!
# Peterfalvi Part II, Ch. I section 3: the PSU centralizer root group

In the `PSU(3,q)` branch of Suzuki's Theorem A, Lemma 1 makes `Q` an
ambient Sylow `2`-subgroup and places it in the normal subgroup `L`.
Transport through the concrete equivalence `L equiv PSU(3,q)` and Sylow
conjugacy identifies it with the standard Hermitian root group.

For the faithful centralizer quotient this gives an explicit equivalence

`C_Q(X) equiv ProjectiveUnitary.RootGroup n`.

The equivalence transports the honest Appendix III Definition 1 Suzuki
`2`-group witness.  Its restriction to square-one elements identifies
`C_Q0(X)` with the central coordinate line.  Therefore, with
`ell = |C_Q0(X)|`, the actual centralizer root has order `ell ^ 3`, exactly
as in Proposition 1(c).

This file does not assert that the unitary root has type B: Proposition 1(c)
only calls it a Suzuki `2`-group, and Peterfalvi's later type-B conclusion
requires an additional hypothesis.  The order-three assertion for the
distinguished product is likewise separate: an arbitrary Sylow equivalence
does not retain the ambient element `t` or its identification with the
standard Weyl element.

T. Peterfalvi, *Character Theory for the Odd Order Theorem*, Part II,
Chapter I section 3, Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

section /- The unitary root in a concrete Theorem A target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
The root group `Q` in a concrete unitary induction target is
multiplicatively equivalent to the Hermitian coordinate root group. -/
noncomputable def qMulEquivPSURoot (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSU3InductionTarget (Omega := Omega) L) :
    hyp.Q ≃* RootGroup data.n := by
  have hn0 : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
  have hcore := hyp.Q_and_residual_of_psu3_target L hLnormal hLodd
    data.one_lt_n data.groupEquiv data.actionEquiv
      data.actionEquiv_bijective
  obtain ⟨hQp, hQL, _, _⟩ := hcore
  let P : Sylow 2 G := Classical.choose (hyp.exists_sylow_two_eq_Q hQp)
  have hP : (P : Subgroup G) = hyp.Q :=
    Classical.choose_spec (hyp.exists_sylow_two_eq_Q hQp)
  have hPL : (P : Subgroup G) ≤ L := hP ▸ hQL
  let PL : Sylow 2 L := P.subtype hPL
  let eQPL : hyp.Q ≃* PL :=
    (MulEquiv.subgroupCongr hP).symm.trans
      (Subgroup.subgroupOfEquivOfLe hPL).symm
  exact eQPL.trans <|
    (Sylow.transportMulEquiv data.groupEquiv PL
      (standardRootSylow data.n hn0)).trans <|
        (MulEquiv.subgroupCongr (coe_standardRootSylow data.n hn0)).trans
          (rootEquivStandardRoot data.n).symm

/-- In a concrete unitary target, `Q` is an honest Suzuki `2`-group. -/
theorem q_isSuzuki2Group_of_psu3Target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSU3InductionTarget (Omega := Omega) L) :
    IsSuzuki2Group hyp.Q :=
  OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv
    (RootGroup.isSuzuki2Group data.n data.one_lt_n)
      (hyp.qMulEquivPSURoot L hLnormal hLodd data).symm

/-- In a concrete unitary target, `Q` has order the cube of the defining
base-field order. -/
theorem natCard_Q_eq_baseField_cube_of_psu3Target
    (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSU3InductionTarget (Omega := Omega) L) :
    Nat.card hyp.Q = Nat.card (BaseField data.n) ^ 3 := by
  have hn0 : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
  calc
    Nat.card hyp.Q = Nat.card (RootGroup data.n) :=
      Nat.card_congr (hyp.qMulEquivPSURoot L hLnormal hLodd data).toEquiv
    _ = Nat.card (BaseField data.n) ^ 3 :=
      RootGroup.natCard_eq_baseField_cube data.n hn0

end

section /- Faithful centralizer quotient, PSU branch -/

variable (hyp : Hypothesis G Omega) {X : Subgroup G}

/-- The quotient root group in the unitary branch of the centralizer
induction is explicitly equivalent to the Hermitian coordinate root. -/
noncomputable def centralizerQuotientQMulEquivPSURoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    qhyp.Q ≃* RootGroup data.n := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.qMulEquivPSURoot result.L result.normal result.oddIndex data

/-- The quotient root group is an honest Suzuki `2`-group in the unitary
branch. -/
theorem centralizerQuotientQ_isSuzuki2Group_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    IsSuzuki2Group qhyp.Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.q_isSuzuki2Group_of_psu3Target result.L result.normal
    result.oddIndex data

/-- The quotient root group has order the cube of the defining base-field
order in the unitary branch. -/
theorem natCard_centralizerQuotientQ_eq_baseField_cube_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    Nat.card qhyp.Q = Nat.card (BaseField data.n) ^ 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.natCard_Q_eq_baseField_cube_of_psu3Target result.L result.normal
    result.oddIndex data

/-- In the unitary branch, the actual centralizer root group `C_Q(X)` is
equivalent to the Hermitian coordinate root group. -/
noncomputable def centralizerCQMulEquivPSURoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      RootGroup data.n := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerQQuotientEquiv hXV).trans
    (hyp.centralizerQuotientQMulEquivPSURoot hXV hA3 result data)

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
The actual group `C_Q(X)` is an honest Suzuki `2`-group. -/
theorem centralizerCQ_isSuzuki2Group_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    IsSuzuki2Group
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv
    (RootGroup.isSuzuki2Group data.n data.one_lt_n)
      (hyp.centralizerCQMulEquivPSURoot hXV hA3 result data).symm

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
The actual group `C_Q(X)` has order the cube of the defining base field. -/
theorem natCard_centralizerCQ_eq_baseField_cube_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (BaseField data.n) ^ 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  have hn0 : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
  calc
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card (RootGroup data.n) :=
      Nat.card_congr
        (hyp.centralizerCQMulEquivPSURoot hXV hA3 result data).toEquiv
    _ = Nat.card (BaseField data.n) ^ 3 :=
      RootGroup.natCard_eq_baseField_cube data.n hn0

/-- The equivalence with the standard unitary root restricts to an
equivalence between `C_Q0(X)` and its central coordinate line.  Both are
characterized intrinsically as the elements whose square is one, so this
restriction does not depend on the chosen Sylow conjugator. -/
noncomputable def centralizerCQ0EquivPSUCenterLine
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ≃
      ↥(RootGroup.centerLine data.n) := by
  letI := hyp.centralizerQuotientMulAction hXV
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let CQ : Subgroup C := hyp.Q.subgroupOf C
  let e : CQ ≃* RootGroup data.n :=
    hyp.centralizerCQMulEquivPSURoot hXV hA3 result data
  let toCQ : ↥(hyp.Q0.subgroupOf C) → CQ := fun x =>
    ⟨x, hyp.Q0_le_Q x.2⟩
  have hto_mem : ∀ x : ↥(hyp.Q0.subgroupOf C),
      e (toCQ x) ∈ RootGroup.centerLine data.n := by
    intro x
    rw [RootGroup.mem_centerLine_iff_sq_eq_one]
    have hx2 : (toCQ x) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact x.2.1
    simpa only [map_pow, map_one] using congrArg e hx2
  let fromRoot : ↥(RootGroup.centerLine data.n) →
      ↥(hyp.Q0.subgroupOf C) := fun y =>
    ⟨(e.symm y : CQ), by
      have hy2 : (y : RootGroup data.n) ^ 2 = 1 :=
        (RootGroup.mem_centerLine_iff_sq_eq_one
          (y : RootGroup data.n)).1 y.2
      have hq2 : (e.symm (y : RootGroup data.n)) ^ 2 = 1 := by
        simpa only [map_pow, map_one] using congrArg e.symm hy2
      constructor
      · simpa using congrArg (fun z : CQ => (((z : C) : G))) hq2
      · exact hyp.Q_le_H (e.symm (y : RootGroup data.n)).2⟩
  exact
    { toFun := fun x => ⟨e (toCQ x), hto_mem x⟩
      invFun := fromRoot
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg (fun z : CQ => (z : C))
          (e.symm_apply_apply (toCQ x))
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply (y : RootGroup data.n) }

/-- In the unitary branch, Peterfalvi's parameter group `C_Q0(X)` has the
defining base-field order. -/
theorem natCard_centralizerQ0_eq_baseField_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (BaseField data.n) := by
  letI := hyp.centralizerQuotientMulAction hXV
  have hn0 : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
  calc
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card (RootGroup.centerLine data.n) :=
      Nat.card_congr
        (hyp.centralizerCQ0EquivPSUCenterLine hXV hA3 result data)
    _ = Nat.card (BaseField data.n) := by
      rw [RootGroup.natCard_centerLine data.n hn0,
        natCard_baseField data.n hn0]

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
With `ell = |C_Q0(X)|`, the actual centralizer root group has order
`ell ^ 3`. -/
theorem natCard_centralizerCQ_eq_centralizerQ0_cube_of_psu3Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  rw [hyp.natCard_centralizerCQ_eq_baseField_cube_of_psu3Target
      hXV hA3 result data,
    hyp.natCard_centralizerQ0_eq_baseField_of_psu3Target
      hXV hA3 result data]

end


end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
