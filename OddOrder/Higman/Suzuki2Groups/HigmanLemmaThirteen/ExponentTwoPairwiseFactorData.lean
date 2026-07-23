/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseFrattini

/-!
# Higman's Lemma 13: prescribed factors inside an exponent-two pairwise join

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

For two of the three length-two factors in the exponent-two branch, this
file packages their actual subgroup-of copies inside their join as the two
complementary type-A factors required by Higman's Lemma 12.

The construction retains the original factors: it does not choose new
complements inside the join.  Normality follows from `P' ≤ Φ(P)`, the
intrinsic Frattini equality comes from the exponent-two branch, and the
common field parameter is recovered from the common ambient involution set.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), prescribed pair inside its join.**

The actual subgroups `R` and `S`, viewed inside `R ⊔ S`, form honest
complementary type-A factor data for the restricted actor. -/
theorem xiLengthThreeTypeAFactorData_pairwiseJoin_of_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiR : frattini P < R)
    (hPhiS : frattini P < S)
    (hRSinf : R ⊓ S = frattini P)
    (dataR : XiLengthTwoTypeAData.{uP, 0} R)
    (dataS : XiLengthTwoTypeAData.{uP, 0} S) :
    let hJinv : IsAInvariant Y.subtype (R ⊔ S) := hRinv.sup hSinv
    ∃ factors : XiLengthThreeTypeAFactorData
        ↥(R ⊔ S) hJinv.restrict.range,
      factors.left = R.subgroupOf (R ⊔ S) ∧
        factors.right = S.subgroupOf (R ⊔ S) := by
  dsimp only
  let J : Subgroup P := R ⊔ S
  let hJinv : IsAInvariant Y.subtype J := hRinv.sup hSinv
  let Rj : Subgroup J := R.subgroupOf J
  let Sj : Subgroup J := S.subgroupOf J
  have hRleJ : R ≤ J := le_sup_left
  have hSleJ : S ≤ J := le_sup_right
  have hRnormal : R.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiR.le)
  have hSnormal : S.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiS.le)
  have hRrange :
      IsAInvariant hJinv.restrict.range.subtype Rj :=
    (isAInvariant_range_subtype_iff hJinv.restrict Rj).2
      (hJinv.subgroupOf hRinv)
  have hSrange :
      IsAInvariant hJinv.restrict.range.subtype Sj :=
    (isAInvariant_range_subtype_iff hJinv.restrict Sj).2
      (hJinv.subgroupOf hSinv)
  have hFrattini :
      frattini J = (frattini P).subgroupOf J := by
    simpa [J] using
      frattini_sup_eq_ambientFrattini_subgroupOf
        hP hxi htwo hRinv hPhiR dataR
  have hPhiLeJ : frattini P ≤ J := hPhiR.le.trans hRleJ
  have hPhiLeft : frattini J < Rj := by
    rw [hFrattini,
      ← Subgroup.map_lt_map_iff_of_injective J.subtype_injective]
    simpa [Rj, Subgroup.map_subgroupOf_eq_of_le hPhiLeJ,
      Subgroup.map_subgroupOf_eq_of_le hRleJ] using hPhiR
  have hPhiRight : frattini J < Sj := by
    rw [hFrattini,
      ← Subgroup.map_lt_map_iff_of_injective J.subtype_injective]
    simpa [Sj, Subgroup.map_subgroupOf_eq_of_le hPhiLeJ,
      Subgroup.map_subgroupOf_eq_of_le hSleJ] using hPhiS
  have hRltJ : R < J := by
    refine lt_of_le_of_ne hRleJ ?_
    intro hRJ
    have hSleR : S ≤ R := by
      rw [hRJ]
      exact hSleJ
    apply hPhiS.ne
    calc
      frattini P = R ⊓ S := hRSinf.symm
      _ = S := inf_eq_right.mpr hSleR
  have hSltJ : S < J := by
    refine lt_of_le_of_ne hSleJ ?_
    intro hSJ
    have hRleS : R ≤ S := by
      rw [hSJ]
      exact hRleJ
    apply hPhiR.ne
    calc
      frattini P = R ⊓ S := hRSinf.symm
      _ = R := inf_eq_left.mpr hRleS
  have hLeftTop : Rj < (⊤ : Subgroup J) := by
    rw [← Subgroup.map_lt_map_iff_of_injective J.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le hRleJ]
    simpa [← MonoidHom.range_eq_map] using hRltJ
  have hRightTop : Sj < (⊤ : Subgroup J) := by
    rw [← Subgroup.map_lt_map_iff_of_injective J.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le hSleJ]
    simpa [← MonoidHom.range_eq_map] using hSltJ
  have hInf : Rj ⊓ Sj = frattini J := by
    rw [hFrattini]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← hRSinf]
    rfl
  have hSup : Rj ⊔ Sj = (⊤ : Subgroup J) := by
    change R.subgroupOf J ⊔ S.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup hRleJ hSleJ]
    exact Subgroup.subgroupOf_self J
  let dataRj : XiLengthTwoTypeAData.{uP, 0} Rj :=
    { F := dataR.F
      fieldF := dataR.fieldF
      finiteF := dataR.finiteF
      charTwoF := dataR.charTwoF
      parameter := dataR.parameter
      parameter_pos := dataR.parameter_pos
      card_field := dataR.card_field
      phi := dataR.phi
      phi_orderOf_odd := dataR.phi_orderOf_odd
      equivModel :=
        (Subgroup.subgroupOfEquivOfLe hRleJ).trans dataR.equivModel }
  let dataSj : XiLengthTwoTypeAData.{uP, 0} Sj :=
    { F := dataS.F
      fieldF := dataS.fieldF
      finiteF := dataS.finiteF
      charTwoF := dataS.charTwoF
      parameter := dataS.parameter
      parameter_pos := dataS.parameter_pos
      card_field := dataS.card_field
      phi := dataS.phi
      phi_orderOf_odd := dataS.phi_orderOf_odd
      equivModel :=
        (Subgroup.subgroupOfEquivOfLe hSleJ).trans dataS.equivModel }
  have hRneBot : R ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiR)
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  have hinvR : involutions P ⊆ R :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hRinv hRneBot
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hcardRS : (involutions R).ncard = (involutions S).ncard :=
    (involutions_ncard_subgroup_eq_of_subset R hinvR).trans
      (involutions_ncard_subgroup_eq_of_subset S hinvS).symm
  have hparam : dataR.parameter = dataS.parameter :=
    XiLengthTwoTypeAData.parameter_eq_of_involutions_ncard_eq
      dataR dataS hcardRS
  have hmultiR : ∃ x y : R,
      x ∈ involutions R ∧ y ∈ involutions R ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvR hmulti
  have hparamTwo : 2 ≤ dataR.parameter :=
    XiLengthTwoTypeAData.parameter_two_le_of_exists_distinct_involutions
      dataR hmultiR
  exact ⟨
    { left := Rj
      right := Sj
      left_normal := hRnormal.subgroupOf J
      left_invariant := hRrange
      right_normal := hSnormal.subgroupOf J
      right_invariant := hSrange
      frattini_lt_left := hPhiLeft
      left_lt_top := hLeftTop
      frattini_lt_right := hPhiRight
      right_lt_top := hRightTop
      inf_eq_frattini := hInf
      sup_eq_top := hSup
      left_model := dataRj
      right_model := dataSj
      parameter_eq := hparam
      parameter_two_le := hparamTwo }, rfl, rfl⟩

end

end OddOrder.Higman.Suzuki2Groups
