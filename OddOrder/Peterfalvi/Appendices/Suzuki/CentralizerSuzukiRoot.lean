/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.RootSubgroupSuzukiType
import OddOrder.GroupTheory.SylowTransport
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge

/-!
# Peterfalvi Part II, Ch. I section 3: the Suzuki centralizer root group

In the `Sz(q)` branch of Suzuki's Theorem A, Lemma 1 makes `Q` an ambient
Sylow `2`-subgroup and places it in the normal subgroup `L`.  Transporting
that Sylow subgroup through the concrete equivalence `L equiv Sz(q)`
identifies it, up to Sylow conjugacy, with the standard Suzuki root group.

For the faithful centralizer quotient this gives an explicit equivalence

`C_Q(X) equiv RootGroup m`.

The equivalence transports the honest Appendix III Definition 1 Suzuki
`2`-group witness and the concrete Definition 2 type-A coordinates.  Its
restriction to the square-one elements identifies `C_Q0(X)` with the
central coordinate line of the standard root.  Consequently, with
`ell = |C_Q0(X)|`, the actual centralizer root has order `ell ^ 2`, exactly
as in Proposition 1(c).

The order-five assertion for the distinguished product is deliberately not
derived from the Sylow equivalence in this file: Sylow conjugacy identifies
the root subgroup but does not identify the ambient element `t` with the
standard Weyl element.  That assertion belongs to the separate distinguished
pair transport, where the structure equation retains both elements.

T. Peterfalvi, *Character Theory for the Odd Order Theorem*, Part II,
Chapter I section 3, Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.Suzuki
open OddOrder.GroupTheory.Suzuki2Group

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

section /- The Suzuki root in a concrete Theorem A target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
The root group `Q` in a concrete Suzuki induction target is multiplicatively
equivalent to the coordinate root group.

The equivalence uses only Lemma 1, restriction to the normal subgroup,
the supplied standard-group equivalence, and Sylow conjugacy. -/
noncomputable def qMulEquivSuzukiRoot (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : SuzukiInductionTarget (Omega := Omega) L) :
    hyp.Q ≃* RootGroup data.m := by
  have hcore := hyp.Q_and_residual_of_suzuki_target L hLnormal hLodd
    data.m_pos data.groupEquiv data.actionEquiv data.actionEquiv_bijective
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
      (standardRootSylow data.m)).trans <|
        (MulEquiv.subgroupCongr (coe_standardRootSylow data.m)).trans
          (rootEquivStandardRoot data.m).symm

/-- In a concrete Suzuki target, `Q` carries the honest Appendix III
Definition 2 type-A coordinates. -/
noncomputable def qStandardTypeAData_of_suzukiTarget
    (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : SuzukiInductionTarget (Omega := Omega) L) :
    StandardTypeAData hyp.Q where
  parameter := data.m
  parameter_pos := data.m_pos
  equivRootGroup := hyp.qMulEquivSuzukiRoot L hLnormal hLodd data

/-- In a concrete Suzuki target, `Q` is an honest Suzuki `2`-group. -/
theorem q_isSuzuki2Group_of_suzukiTarget (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : SuzukiInductionTarget (Omega := Omega) L) :
    IsSuzuki2Group hyp.Q :=
  IsSuzuki2Group.of_equiv (RootGroup.isSuzuki2Group data.m data.m_pos)
    (hyp.qMulEquivSuzukiRoot L hLnormal hLodd data).symm

/-- In a concrete Suzuki target, `Q` has order the square of the defining
field order. -/
theorem natCard_Q_eq_field_sq_of_suzukiTarget (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : SuzukiInductionTarget (Omega := Omega) L) :
    Nat.card hyp.Q = Nat.card (Field data.m) ^ 2 := by
  calc
    Nat.card hyp.Q = Nat.card (RootGroup data.m) :=
      Nat.card_congr
        (hyp.qMulEquivSuzukiRoot L hLnormal hLodd data).toEquiv
    _ = Nat.card (Field data.m) ^ 2 := natCard_rootGroup_eq_field_sq data.m

end

section /- Faithful centralizer quotient, Suzuki branch -/

variable (hyp : Hypothesis G Omega) {X : Subgroup G}

/-- The quotient root group in the Suzuki branch of the centralizer induction
is explicitly equivalent to the coordinate Suzuki root group. -/
noncomputable def centralizerQuotientQMulEquivSuzukiRoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    qhyp.Q ≃* RootGroup data.m := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.qMulEquivSuzukiRoot result.L result.normal result.oddIndex data

/-- The quotient root group carries concrete type-A coordinates in the
Suzuki branch. -/
noncomputable def centralizerQuotientQStandardTypeAData_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    StandardTypeAData qhyp.Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.qStandardTypeAData_of_suzukiTarget result.L result.normal
    result.oddIndex data

/-- The quotient root group is an honest Suzuki `2`-group in the Suzuki
branch. -/
theorem centralizerQuotientQ_isSuzuki2Group_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    IsSuzuki2Group qhyp.Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.q_isSuzuki2Group_of_suzukiTarget result.L result.normal
    result.oddIndex data

/-- The quotient root group has order the square of the defining field order
in the Suzuki branch. -/
theorem natCard_centralizerQuotientQ_eq_field_sq_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    Nat.card qhyp.Q = Nat.card (Field data.m) ^ 2 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.natCard_Q_eq_field_sq_of_suzukiTarget result.L result.normal
    result.oddIndex data

/-- In the Suzuki branch, the actual centralizer root group `C_Q(X)` is
equivalent to the coordinate Suzuki root group.  This is the source
equivalence `C_Q(X) equiv Qbar` followed by standard-model Sylow transport. -/
noncomputable def centralizerCQMulEquivSuzukiRoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      RootGroup data.m := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerQQuotientEquiv hXV).trans
    (hyp.centralizerQuotientQMulEquivSuzukiRoot hXV hA3 result data)

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
The actual group `C_Q(X)` carries concrete Appendix III Definition 2 type-A
coordinates. -/
noncomputable def centralizerCQStandardTypeAData_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    StandardTypeAData
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact
    { parameter := data.m
      parameter_pos := data.m_pos
      equivRootGroup :=
        hyp.centralizerCQMulEquivSuzukiRoot hXV hA3 result data }

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
The actual group `C_Q(X)` is an honest Suzuki `2`-group. -/
theorem centralizerCQ_isSuzuki2Group_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    IsSuzuki2Group
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact IsSuzuki2Group.of_equiv
    (RootGroup.isSuzuki2Group data.m data.m_pos)
      (hyp.centralizerCQMulEquivSuzukiRoot hXV hA3 result data).symm

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
The actual group `C_Q(X)` has order the square of the defining field order. -/
theorem natCard_centralizerCQ_eq_field_sq_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (Field data.m) ^ 2 := by
  letI := hyp.centralizerQuotientMulAction hXV
  calc
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card (RootGroup data.m) :=
      Nat.card_congr
        (hyp.centralizerCQMulEquivSuzukiRoot hXV hA3 result data).toEquiv
    _ = Nat.card (Field data.m) ^ 2 := natCard_rootGroup_eq_field_sq data.m

/-- The equivalence with the standard Suzuki root restricts to an equivalence
between `C_Q0(X)` and the central coordinate line.  This is valid for the
arbitrary Sylow equivalence because both sides are characterized intrinsically
as the elements whose square is one. -/
noncomputable def centralizerCQ0EquivSuzukiCenterLine
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ≃
      ↥(RootGroup.centerLine data.m) := by
  letI := hyp.centralizerQuotientMulAction hXV
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let CQ : Subgroup C := hyp.Q.subgroupOf C
  let e : CQ ≃* RootGroup data.m :=
    hyp.centralizerCQMulEquivSuzukiRoot hXV hA3 result data
  let toCQ : ↥(hyp.Q0.subgroupOf C) → CQ := fun x =>
    ⟨x, hyp.Q0_le_Q x.2⟩
  have hto_mem : ∀ x : ↥(hyp.Q0.subgroupOf C),
      e (toCQ x) ∈ RootGroup.centerLine data.m := by
    intro x
    rw [RootGroup.mem_centerLine, ← RootGroup.sq_eq_one_iff]
    have hx2 : (toCQ x) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact x.2.1
    simpa only [map_pow, map_one] using congrArg e hx2
  let fromRoot : ↥(RootGroup.centerLine data.m) →
      ↥(hyp.Q0.subgroupOf C) := fun y =>
    ⟨(e.symm y : CQ), by
      have hy2 : (y : RootGroup data.m) ^ 2 = 1 :=
        RootGroup.sq_eq_one_of_mem_centerLine y.2
      have hq2 : (e.symm (y : RootGroup data.m)) ^ 2 = 1 := by
        simpa only [map_pow, map_one] using congrArg e.symm hy2
      constructor
      · simpa using congrArg (fun z : CQ => (((z : C) : G))) hq2
      · exact hyp.Q_le_H (e.symm (y : RootGroup data.m)).2⟩
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
        exact e.apply_symm_apply (y : RootGroup data.m) }

/-- In the Suzuki branch, Peterfalvi's parameter group `C_Q0(X)` has order
the defining field order.  Thus the source parameter
`ell = |C_Q0(X)|` is the standard Suzuki field order. -/
theorem natCard_centralizerQ0_eq_field_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card (Field data.m) := by
  letI := hyp.centralizerQuotientMulAction hXV
  calc
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card (RootGroup.centerLine data.m) :=
      Nat.card_congr
        (hyp.centralizerCQ0EquivSuzukiCenterLine hXV hA3 result data)
    _ = Nat.card (Field data.m) := by
      rw [RootGroup.natCard_centerLine, natCard_field]

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
With `ell = |C_Q0(X)|`, the actual centralizer root group has order
`ell ^ 2`. -/
theorem natCard_centralizerCQ_eq_centralizerQ0_sq_of_suzukiTarget
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 2 := by
  letI := hyp.centralizerQuotientMulAction hXV
  rw [hyp.natCard_centralizerCQ_eq_field_sq_of_suzukiTarget
      hXV hA3 result data,
    hyp.natCard_centralizerQ0_eq_field_of_suzukiTarget hXV hA3 result data]

end


end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
