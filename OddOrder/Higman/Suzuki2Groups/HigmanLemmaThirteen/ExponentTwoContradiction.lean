/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedParameterBranches
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllIsomorphicParameterBranch

/-!
# Higman's Lemma 13: exponent-two contradiction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The three pairwise normalized coordinate packages supplied by the length-four
hypothesis have coherent copies of the three actual factor parameters.  Their
parameter coincidence refines into three aligned branches and one all-equal
nontrivial branch.  The corresponding branch contradictions therefore rule
out exponent two in the Frattini subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

/-- **Higman Lemma 13 (p. 93), exponent-two contradiction.**

If a noncommutative Suzuki 2-group has an Xi-actor of Xi-length four and its
Frattini subgroup has exponent two, the three honest pairwise coordinate
packages force one of the four parameter branches, each of which is
impossible. -/
theorem false_of_hasXiLengthFour_of_frattini_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    False := by
  classical
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive (frattini P))
  obtain ⟨X, Z, T, hXinv, hZinv, hTinv,
      hXnormal, _hlenX, dataX, hZnormal, _hlenZ, dataZ,
      hTnormal, _hlenT, dataT,
      hPhiX, _hXtop, hPhiZ, _hZtop, hPhiT, _hTtop,
      hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop,
      hXZ_Tinf, _hXZ_Tsup,
      c, ePhi, nu, _b, hnTwo, hcgen, hnuPrimitive, hconj,
      _hgenerate, _heigen, xz, xt, zt,
      hthetaX, hthetaZ, hthetaT, hcoincidence⟩ :=
    exists_threePairCoordinates_with_parameterCoincidence_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  let hMapXZ : (frattini ↥(X ⊔ Z)).map (X ⊔ Z).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hXinv hPhiX dataX
  let hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hXinv hPhiX dataX
  let hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hZinv hPhiZ dataZ
  let hXZEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ Z)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXZ).symm hPhiEA
  let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
  let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
  letI : IsMulCommutative (frattini ↥(X ⊔ Z)) :=
    IsMulCommutative.of_comm hXZEA.comm
  letI : CommGroup (frattini ↥(X ⊔ Z)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ Z))) :=
    hXZEA.zmodModule
  letI : IsMulCommutative (frattini ↥(X ⊔ T)) :=
    IsMulCommutative.of_comm hXTEA.comm
  letI : CommGroup (frattini ↥(X ⊔ T)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
    hXTEA.zmodModule
  letI : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
    IsMulCommutative.of_comm hZTEA.comm
  letI : CommGroup (frattini ↥(Z ⊔ T)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
    hZTEA.zmodModule
  rcases
      coherent_threePairCoordinates_parameterBranching
        hXinv hZinv hTinv hPhiEA hMapXZ hMapXT hMapZT
        c ePhi nu xz xt zt hthetaX hthetaZ hthetaT hcoincidence with
    halignedT | halignedZ | halignedX | hAll
  · exact
      false_of_alignedParameterBranches_exponent_two
        hP hncomm hmulti hxi hlen hprime htwo
        hXinv hZinv hTinv hXnormal hZnormal hTnormal
        hPhiX hPhiZ hPhiT hXZinf hXTinf hZTinf
        hXZtop hXTtop hZTtop hXZ_Tinf dataX dataZ dataT
        hnTwo c ePhi nu hcgen hnuPrimitive hconj
        xz xt zt (Or.inl halignedT)
  · exact
      false_of_alignedParameterBranches_exponent_two
        hP hncomm hmulti hxi hlen hprime htwo
        hXinv hZinv hTinv hXnormal hZnormal hTnormal
        hPhiX hPhiZ hPhiT hXZinf hXTinf hZTinf
        hXZtop hXTtop hZTtop hXZ_Tinf dataX dataZ dataT
        hnTwo c ePhi nu hcgen hnuPrimitive hconj
        xz xt zt (Or.inr (Or.inl halignedZ))
  · exact
      false_of_alignedParameterBranches_exponent_two
        hP hncomm hmulti hxi hlen hprime htwo
        hXinv hZinv hTinv hXnormal hZnormal hTnormal
        hPhiX hPhiZ hPhiT hXZinf hXTinf hZTinf
        hXZtop hXTtop hZTtop hXZ_Tinf dataX dataZ dataT
        hnTwo c ePhi nu hcgen hnuPrimitive hconj
        xz xt zt (Or.inr (Or.inr halignedX))
  · have hAll' :
        AllEqualNontrivialParameterData
          xt.left.theta zt.left.theta xt.right.theta := by
      rw [← hthetaX, ← hthetaZ]
      exact hAll
    exact
      false_of_allIsomorphicParameterBranch_exponent_two
        hP hncomm hmulti hxi hlen hprime htwo
        hXinv hZinv hTinv hPhiX hPhiZ hPhiT
        hXZinf hXTinf hZTinf hXTtop hZTtop hXZ_Tinf
        dataX dataZ dataT hnTwo c ePhi nu hcgen
        hnuPrimitive hconj xt zt hthetaT hAll'

end

end OddOrder.Higman.Suzuki2Groups
