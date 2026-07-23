/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedGraphContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAmbientBracketFaithfulness
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseJoinInfrastructure
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoThreeParameterBranching

/-!
# Higman's Lemma 13: contradiction in the first aligned parameter branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The first oriented parameter branch compares the actual joins X ⊔ T and
Z ⊔ T, with T as their common prescribed factor.  The honest pairwise
join theorem reconstructs all lower-central, restricted-actor, involution,
and Singer-coordinate data for both joins.  The aligned parameter package
then supplies exactly the two theta equalities and uniqueness alternative
needed by the invariant-graph contradiction.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

/-- **Higman Lemma 13 (p. 93), first aligned parameter branch.**

For the fixed orientation J = X ⊔ T and K = Z ⊔ T, an aligned pair of
normalized actual-factor packages is impossible.  All lower-central facts
for the two joins and for the ambient group are reconstructed from the
exponent-two hypotheses rather than assumed. -/
theorem false_of_firstAlignedParameterBranch_exponent_two
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
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {X Z T : Subgroup P}
    (hXinv : IsAInvariant Y.subtype X)
    (hZinv : IsAInvariant Y.subtype Z)
    (hTinv : IsAInvariant Y.subtype T)
    (hPhiX : frattini P < X)
    (hPhiZ : frattini P < Z)
    (hPhiT : frattini P < T)
    (hXZ : X ⊓ Z = frattini P)
    (hXT : X ⊓ T = frattini P)
    (hZT : Z ⊓ T = frattini P)
    (hXTtop : X ⊔ T < (⊤ : Subgroup P))
    (hZTtop : Z ⊔ T < (⊤ : Subgroup P))
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P)
    (dataX : XiLengthTwoTypeAData.{uP, 0} X)
    (dataZ : XiLengthTwoTypeAData.{uP, 0} Z)
    (dataT : XiLengthTwoTypeAData.{uP, 0} T) :
    let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
    let hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype =
        frattini P :=
      frattini_sup_map_subtype_eq_ambientFrattini
        hP hxi htwo hXinv hPhiX dataX
    let hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype =
        frattini P :=
      frattini_sup_map_subtype_eq_ambientFrattini
        hP hxi htwo hZinv hPhiZ dataZ
    let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
    let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(X ⊔ T)) :=
      IsMulCommutative.of_comm hXTEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
      hXTEA.zmodModule
    letI : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
      IsMulCommutative.of_comm hZTEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
      hZTEA.zmodModule
    ∀ {n : Nat},
    2 ≤ n →
    ∀ (c : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              Y.subtype :
                IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∀
      (xt : NormalizedActualFactorPairCoordinates
        hXinv hTinv hPhiEA hMapXT c ePhi nu)
      (zt : NormalizedActualFactorPairCoordinates
        hZinv hTinv hPhiEA hMapZT c ePhi nu),
      AlignedTwoJoinParameterData
          xt.left.theta xt.right.theta
          zt.left.theta zt.right.theta →
      False := by
  classical
  dsimp only
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  let hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hXinv hPhiX dataX
  let hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hZinv hPhiZ dataZ
  let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
  let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
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
  intro n hn c ePhi nu hcgen hnuPrimitive hconj xt zt haligned
  obtain ⟨⟨joinXT, hJoinXT, _hInvXT, _hMapXT',
      _factorsXT, _hLeftXT, _hRightXT,
      hK1XT, htermXT, hSqXT, hAgemoXT, hK0XT,
      hxiXT, hinvPhiXT, hconjXT⟩⟩ :=
    exists_pairwiseJoinLowerCentralData_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hTinv hPhiX hPhiT hXT hXTtop dataX dataT
      c ePhi nu hconj
  subst joinXT
  obtain ⟨⟨joinZT, hJoinZT, _hInvZT, _hMapZT',
      _factorsZT, _hLeftZT, _hRightZT,
      hK1ZT, htermZT, hSqZT, hAgemoZT, hK0ZT,
      hxiZT, hinvPhiZT, hconjZT⟩⟩ :=
    exists_pairwiseJoinLowerCentralData_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hZinv hTinv hPhiZ hPhiT hZT hZTtop dataZ dataT
      c ePhi nu hconj
  subst joinZT
  have hbotPhi : (⊥ : Subgroup P) < frattini P :=
    (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
        (IsAInvariant.of_characteristic Y.subtype) hbotPhi.ne'
  have hK1P : lowerCentralLayerKernel P 1 = ⊥ :=
    lowerCentralLayerKernel_one_eq_bot_of_exponent_two
      hP hncomm hxi htwo
  have htermP : lowerCentralTerm P 1 = frattini P :=
    lowerCentralTerm_one_eq_frattini_of_exponent_two
      hP hncomm hxi htwo
  exact
    false_of_alignedGraph_commonFactor_branch_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hTinv ⟨dataT⟩ hinvPhi
      hPhiX hPhiZ hPhiT hXZ hXZ_T
      rfl rfl
      (hXinv.sup hTinv) (hZinv.sup hTinv)
      hMapXT hMapZT hPhiEA hn ePhi hK1P htermP
      c hcgen xt.factors zt.factors
      xt.left xt.right zt.left zt.right
      xt.left_eq zt.left_eq xt.right_eq zt.right_eq
      hK1XT htermXT hSqXT hAgemoXT hK0XT
      hK1ZT htermZT hSqZT hAgemoZT hK0ZT
      hxiXT hxiZT hinvPhiXT hinvPhiZT
      hconjXT hconjZT
      xt.left_source xt.right_source
      zt.left_source zt.right_source
      zt.left_normalized
      xt.right_normalized zt.right_normalized
      haligned.left_eq haligned.common_eq haligned.unique
      xt.relation hnuPrimitive

end

end OddOrder.Higman.Suzuki2Groups
