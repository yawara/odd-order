/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseCoordinates

/-!
# Higman's Lemma 13: faithfulness of the ambient exponent-two bracket

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, actor transitivity identifies the nontrivial
derived subgroup with the whole Frattini subgroup.  The same transitivity
puts that elementary-abelian Frattini subgroup in the center.  Consequently
the first positive lower-central term is `Φ(P)`, the next term is trivial,
and the denominator of the degree-one lower-central layer is trivial.

These facts do not use the length-four or prime-support hypotheses once
exponent two of `Φ(P)` is available.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

/-- In the exponent-two branch, the ambient derived subgroup is the
Frattini subgroup and this subgroup is central. -/
theorem commutator_eq_frattini_and_frattini_le_center_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    _root_.commutator P = frattini P ∧
      frattini P ≤ Subgroup.center P := by
  have hEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  have hcommNe : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcommNe
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hinvComm : involutions P ⊆ _root_.commutator P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive (IsAInvariant.commutator_self Y.subtype) hcommNe
  have hPhiComm : frattini P ≤ _root_.commutator P := by
    intro z hz
    by_cases hzOne : z = 1
    · exact hzOne ▸ (_root_.commutator P).one_mem
    · apply hinvComm
      exact ⟨congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩), hzOne⟩
  have hcommPhi : _root_.commutator P ≤ frattini P :=
    OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP
  have hcommEq : _root_.commutator P = frattini P :=
    le_antisymm hcommPhi hPhiComm
  have hinvCenter : involutions P ⊆ Subgroup.center P :=
    involutions_subset_center_of_transitive hP Y hxi.transitive
  have hPhiCenter : frattini P ≤ Subgroup.center P := by
    intro z hz
    by_cases hzOne : z = 1
    · exact hzOne ▸ (Subgroup.center P).one_mem
    · apply hinvCenter
      exact ⟨congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩), hzOne⟩
  exact ⟨hcommEq, hPhiCenter⟩

/-- The first positive lower-central term is the Frattini subgroup in the
ambient exponent-two branch. -/
theorem lowerCentralTerm_one_eq_frattini_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    lowerCentralTerm P 1 = frattini P := by
  rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one,
    (commutator_eq_frattini_and_frattini_le_center_of_exponent_two
      hP hncomm hxi htwo).1]

/-- The next lower-central term is trivial in the ambient exponent-two
branch. -/
theorem lowerCentralTerm_two_eq_bot_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    lowerCentralTerm P 2 = ⊥ := by
  have heq :=
    commutator_eq_frattini_and_frattini_le_center_of_exponent_two
      hP hncomm hxi htwo
  have hle : (⊤ : Subgroup P).lowerCentralSeries 1 ≤
      Subgroup.center P := by
    rw [Subgroup.top_lowerCentralSeries_one, heq.1]
    exact heq.2
  simpa [lowerCentralTerm] using
    (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup P) hle)

/-- The degree-one lower-central quotient has trivial denominator in the
ambient exponent-two branch. -/
theorem lowerCentralLayerKernel_one_eq_bot_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    lowerCentralLayerKernel P 1 = ⊥ := by
  have hEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  have htermOne :=
    lowerCentralTerm_one_eq_frattini_of_exponent_two
      hP hncomm hxi htwo
  have hEAOne : IsElementaryAbelian 2 (lowerCentralTerm P 1) := by
    rw [htermOne]
    exact hEA
  letI : CommGroup (lowerCentralTerm P 1) :=
    { (inferInstance : Group (lowerCentralTerm P 1)) with
      mul_comm := hEAOne.comm }
  have hAgemo : Agemo (lowerCentralTerm P 1) 2 1 = ⊥ := by
    rw [agemo_eq_range_powMonoidHom]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Subgroup.mem_bot.mpr
      simpa using hEAOne.pow_eq_one x
    · exact bot_le
  have hAmbient : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot_of_exponent_two
        hP hncomm hxi htwo,
      hAgemo]
    simp
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbient]
  simp

end OddOrder.Higman.Suzuki2Groups
