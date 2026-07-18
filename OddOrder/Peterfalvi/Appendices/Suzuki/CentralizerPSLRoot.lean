/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.RootGroupSylow
import OddOrder.GroupTheory.SylowTransport
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge

/-!
# Peterfalvi Part II, Ch. I section 3: the PSL centralizer root group

In the `PSL(2,q)` branch of Suzuki's Theorem A, Lemma 1 makes `Q` an
ambient Sylow `2`-subgroup and places it in the normal subgroup `L`.
Transporting that Sylow subgroup through the concrete equivalence
`L equiv PSL(2,F)` identifies it, up to Sylow conjugacy, with the standard
upper-unipotent root subgroup.  This gives the exact conclusions used in
Proposition 1(c): `Q` is elementary abelian and has order `|F|`.

The same construction is exposed directly for the faithful centralizer
quotient `C_G(X)/N(C_G(X))`, so the induction branch contains no abstract
or posited root-group carrier.

T. Peterfalvi, *Character Theory for the Odd Order Theorem*, Part II,
Chapter I section 3, Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear

open scoped LinearAlgebra.Projectivization MatrixGroups

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

section /- PSL(2,q) root transport in a Theorem A target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
The root group `Q` in a concrete `PSL(2,F)` induction target is
multiplicatively equivalent to the standard upper-unipotent root group.

The equivalence is constructed entirely from Lemma 1, subgroup restriction,
the supplied standard-group equivalence, and Sylow conjugacy. -/
noncomputable def qMulEquivPSLRoot (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSL2InductionTarget (Omega := Omega) L) :
    letI : Field data.F := data.fieldF
    letI : Finite data.F := data.finiteF
    letI : CharP data.F 2 := data.charTwoF
    hyp.Q ≃* rootSubgroup (F := data.F) := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  have hcore := hyp.Q_and_residual_of_psl2_target L hLnormal hLodd
    data.cardF_gt_two data.groupEquiv data.actionEquiv
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
    (Sylow.transportMulEquiv data.groupEquiv PL (rootSylow (F := data.F))).trans
      (MulEquiv.subgroupCongr (coe_rootSylow (F := data.F)))

/-- In the `PSL(2,F)` target, `Q` is elementary abelian of exponent two. -/
theorem q_isElementaryAbelian_of_psl2Target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSL2InductionTarget (Omega := Omega) L) :
    IsElementaryAbelian 2 hyp.Q := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  exact IsElementaryAbelian.of_mulEquiv
    (hyp.qMulEquivPSLRoot L hLnormal hLodd data).symm
      (rootSubgroup_isElementaryAbelian (F := data.F))

/-- In the `PSL(2,F)` target, the exact order of `Q` is `|F|`. -/
theorem natCard_Q_eq_field_of_psl2Target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSL2InductionTarget (Omega := Omega) L) :
    Nat.card hyp.Q = Nat.card data.F := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  calc
    Nat.card hyp.Q = Nat.card (rootSubgroup (F := data.F)) :=
      Nat.card_congr (hyp.qMulEquivPSLRoot L hLnormal hLodd data).toEquiv
    _ = Nat.card data.F := natCard_rootSubgroup

end

section /- Faithful centralizer quotient, PSL branch -/

variable (hyp : Hypothesis G Omega) {X : Subgroup G}

/-- The quotient root group in the `PSL(2,F)` branch of the centralizer
induction is the concrete standard upper-unipotent root group. -/
noncomputable def centralizerQuotientQMulEquivPSLRoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    letI : Field data.F := data.fieldF
    letI : Finite data.F := data.finiteF
    letI : CharP data.F 2 := data.charTwoF
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    qhyp.Q ≃* rootSubgroup (F := data.F) := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.qMulEquivPSLRoot result.L result.normal result.oddIndex data

/-- The centralizer quotient root group is elementary abelian in the PSL
branch of the induction conclusion. -/
theorem centralizerQuotientQ_isElementaryAbelian_of_psl2Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    IsElementaryAbelian 2 qhyp.Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.q_isElementaryAbelian_of_psl2Target result.L result.normal
    result.oddIndex data

/-- The centralizer quotient root group has exact order `|F|` in the PSL
branch of the induction conclusion. -/
theorem natCard_centralizerQuotientQ_eq_field_of_psl2Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    Nat.card qhyp.Q = Nat.card data.F := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  exact qhyp.natCard_Q_eq_field_of_psl2Target result.L result.normal
    result.oddIndex data


/-- If `C_Q(X)` is elementary abelian of exponent two, then it equals
`C_Q0(X)`.  This is the source step that identifies Peterfalvi's parameter
`ell = |C_Q0(X)|` with the order of the full centralizer root group. -/
theorem centralizerQ0_subgroupOf_eq_Q_subgroupOf_of_elementaryAbelian
    (hCQ : IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G)) =
      hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  change hyp.Q0.subgroupOf C = hyp.Q.subgroupOf C
  apply le_antisymm
  · intro x hx
    exact hyp.Q0_le_Q hx
  · intro x hx
    have hs := hCQ.pow_eq_one
      (⟨x, hx⟩ : ↥(hyp.Q.subgroupOf C))
    have hsG : ((x : G) ^ 2) = 1 := by
      simpa using congrArg
        (fun z : ↥(hyp.Q.subgroupOf C) => (((z : C) : G))) hs
    exact ⟨hsG, hyp.Q_le_H hx⟩

/-- In the PSL branch, the actual centralizer root group `C_Q(X)` is
equivalent to the standard upper-unipotent root group.  This composes the
source equivalence `C_Q(X) equiv Qbar` with the standard-group Sylow
transport above. -/
noncomputable def centralizerCQMulEquivPSLRoot
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    letI : Field data.F := data.fieldF
    letI : Finite data.F := data.finiteF
    letI : CharP data.F 2 := data.charTwoF
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      rootSubgroup (F := data.F) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerQQuotientEquiv hXV).trans
    (hyp.centralizerQuotientQMulEquivPSLRoot hXV hA3 result data)

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
The actual group `C_Q(X)` is elementary abelian. -/
theorem centralizerCQ_isElementaryAbelian_of_psl2Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  exact IsElementaryAbelian.of_mulEquiv
    (hyp.centralizerCQMulEquivPSLRoot hXV hA3 result data).symm
      (rootSubgroup_isElementaryAbelian (F := data.F))

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
The actual group `C_Q(X)` has exact order `|F|`. -/
theorem natCard_centralizerCQ_eq_field_of_psl2Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card data.F := by
  letI := hyp.centralizerQuotientMulAction hXV
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  calc
    Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card (rootSubgroup (F := data.F)) :=
      Nat.card_congr
        (hyp.centralizerCQMulEquivPSLRoot hXV hA3 result data).toEquiv
    _ = Nat.card data.F := natCard_rootSubgroup


/-- In the PSL branch, Peterfalvi's parameter group `C_Q0(X)` has exact
order `|F|`; equivalently, the source parameter `ell` is `|F|`. -/
theorem natCard_centralizerQ0_eq_field_of_psl2Target
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) =
      Nat.card data.F := by
  letI := hyp.centralizerQuotientMulAction hXV
  rw [hyp.centralizerQ0_subgroupOf_eq_Q_subgroupOf_of_elementaryAbelian
    (hyp.centralizerCQ_isElementaryAbelian_of_psl2Target hXV hA3 result data)]
  exact hyp.natCard_centralizerCQ_eq_field_of_psl2Target
    hXV hA3 result data

end


end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
