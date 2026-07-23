/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorsTypeCBCrossCommutator
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniCrossCommutatorContradiction

/-!
# Higman's Lemma 13: the exponent-four type-C/type-B branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

This file closes the branch in which the normalized right factor of the first
restricted length-three Frattini cover is of type C and that of the second is
of type B.  Their canonical ambient eigenfamilies force the cross commutator
into `Φ(P)²`, contradicting the exponent-four Frattini chain.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

/-- **Higman Lemma 13 (p. 92), exponent-four C/B contradiction.**

A restricted type-C right factor and a restricted type-B right factor cannot
belong to two Frattini covers which generate the ambient group. -/
theorem false_of_typeC_typeB_sharpRestrictedFactorPairs_of_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {X Z : Subgroup P}
    (hXinv : IsAInvariant Y.subtype X)
    (hPhiX : NormalInvariantCover Y.subtype (frattini P) X)
    (hlenX : HasXiLengthThree hXinv.restrict.range.subtype)
    (hncommX : ¬ IsMulCommutative X)
    (hZinv : IsAInvariant Y.subtype Z)
    (hPhiZ : NormalInvariantCover Y.subtype (frattini P) Z)
    (hlenZ : HasXiLengthThree hZinv.restrict.range.subtype)
    (hncommZ : ¬ IsMulCommutative Z)
    (hsup : X ⊔ Z = (⊤ : Subgroup P))
    {n r : Nat} (hn : 2 ≤ n) (hr : 0 < r) (h2r1 : 2 * r + 1 = n)
    (c : Y)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hconj :
      let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
        (frattiniSquareNormalInvariant Y.subtype).2.2
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eSquare.conj (elabRepresentation 2 hSquareInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu) :
    let hXneBot : X ≠ (⊥ : Subgroup P) :=
      ne_of_gt (lt_of_le_of_lt bot_le hPhiX.lt)
    let hinvX : involutions P ⊆ X :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hXinv hXneBot
    let hxiX : IsXiActor hXinv.restrict.range :=
      restricted_range_isXiActor hxi hXinv
    let hmultiX : ∃ x y : X,
        x ∈ involutions X ∧ y ∈ involutions X ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvX hmulti
    let hprimeX : ∀ p : Nat, p.Prime →
        p ∣ Nat.card hXinv.restrict.range →
          p ∣ (involutions X).ncard :=
      restricted_range_primeSupport hXinv hinvX hprime
    let hEAX : IsElementaryAbelian 2 (frattini X) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
    let hMapX : (frattini X).map X.subtype = frattiniSquare P :=
      frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
        hP hmulti hxi hprime hPhiComm hexists hXinv hPhiX hlenX hncommX
    let hZneBot : Z ≠ (⊥ : Subgroup P) :=
      ne_of_gt (lt_of_le_of_lt bot_le hPhiZ.lt)
    let hinvZ : involutions P ⊆ Z :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hZinv hZneBot
    let hxiZ : IsXiActor hZinv.restrict.range :=
      restricted_range_isXiActor hxi hZinv
    let hmultiZ : ∃ x y : Z,
        x ∈ involutions Z ∧ y ∈ involutions Z ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvZ hmulti
    let hprimeZ : ∀ p : Nat, p.Prime →
        p ∣ Nat.card hZinv.restrict.range →
          p ∣ (involutions Z).ncard :=
      restricted_range_primeSupport hZinv hinvZ hprime
    let hEAZ : IsElementaryAbelian 2 (frattini Z) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
    let hMapZ : (frattini Z).map Z.subtype = frattiniSquare P :=
      frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
        hP hmulti hxi hprime hPhiComm hexists hZinv hPhiZ hlenZ hncommZ
    let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattini X) :=
      IsMulCommutative.of_comm hEAX.comm
    letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
    letI : IsMulCommutative (frattini Z) :=
      IsMulCommutative.of_comm hEAZ.comm
    letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    let eX := (restrictedFrattiniLinearEquivFrattiniSquare
      hEAX hSquareEA hMapX).trans eSquare
    let eZ := (restrictedFrattiniLinearEquivFrattiniSquare
      hEAZ hSquareEA hMapZ).trans eSquare
    ∀ (factorsX : XiLengthThreeTypeAFactorData X hXinv.restrict.range)
      (rightX : FactorCoordinateData factorsX.right_invariant
        factorsX.frattini_lt_right.le
        (hXinv.restrict.rangeRestrict c) eX nu),
      factorsX.left = (frattini P).subgroupOf X →
      rightX.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r →
      ∀ (factorsZ : XiLengthThreeTypeAFactorData Z hZinv.restrict.range)
        (leftZ : FactorCoordinateData factorsZ.left_invariant
          factorsZ.frattini_lt_left.le
          (hZinv.restrict.rangeRestrict c) eZ nu)
        (rightZ : FactorCoordinateData factorsZ.right_invariant
          factorsZ.frattini_lt_right.le
          (hZinv.restrict.rangeRestrict c) eZ nu),
        factorsZ.left = (frattini P).subgroupOf Z →
        leftZ.theta = 1 →
        rightZ.theta = 1 →
        False := by
  classical
  dsimp only
  let hXneBot : X ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiX.lt)
  let hinvX : involutions P ⊆ X :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hXinv hXneBot
  let hxiX : IsXiActor hXinv.restrict.range :=
    restricted_range_isXiActor hxi hXinv
  let hmultiX : ∃ x y : X,
      x ∈ involutions X ∧ y ∈ involutions X ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvX hmulti
  let hprimeX : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hXinv.restrict.range →
        p ∣ (involutions X).ncard :=
    restricted_range_primeSupport hXinv hinvX hprime
  let hEAX : IsElementaryAbelian 2 (frattini X) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  let hMapX : (frattini X).map X.subtype = frattiniSquare P :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists hXinv hPhiX hlenX hncommX
  let hZneBot : Z ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiZ.lt)
  let hinvZ : involutions P ⊆ Z :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hZinv hZneBot
  let hxiZ : IsXiActor hZinv.restrict.range :=
    restricted_range_isXiActor hxi hZinv
  let hmultiZ : ∃ x y : Z,
      x ∈ involutions Z ∧ y ∈ involutions Z ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvZ hmulti
  let hprimeZ : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hZinv.restrict.range →
        p ∣ (involutions Z).ncard :=
    restricted_range_primeSupport hZinv hinvZ hprime
  let hEAZ : IsElementaryAbelian 2 (frattini Z) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  let hMapZ : (frattini Z).map Z.subtype = frattiniSquare P :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists hZinv hPhiZ hlenZ hncommZ
  let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : IsMulCommutative (frattini X) :=
    IsMulCommutative.of_comm hEAX.comm
  letI : CommGroup (frattini X) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
  letI : IsMulCommutative (frattini Z) :=
    IsMulCommutative.of_comm hEAZ.comm
  letI : CommGroup (frattini Z) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let eX := (restrictedFrattiniLinearEquivFrattiniSquare
    hEAX hSquareEA hMapX).trans eSquare
  let eZ := (restrictedFrattiniLinearEquivFrattiniSquare
    hEAZ hSquareEA hMapZ).trans eSquare
  intro factorsX rightX hleftX hrightThetaX
    factorsZ leftZ rightZ hleftZ hleftThetaZ hrightThetaZ
  have hK1X := lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  have htermX := lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  have hSqX := lowerCentralSquaresLieInSecond_of_xiLengthThree
    (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  have hAgemoX := agemo_one_eq_frattini_of_xiLengthThree
    (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  have hK0X :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      (hP.to_subgroup X) hncommX hmultiX hxiX hlenX hprimeX
  have hK1Z := lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  have htermZ := lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  have hSqZ := lowerCentralSquaresLieInSecond_of_xiLengthThree
    (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  have hAgemoZ := agemo_one_eq_frattini_of_xiLengthThree
    (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  have hK0Z :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      (hP.to_subgroup Z) hncommZ hmultiZ hxiZ hlenZ hprimeZ
  have hPhiZneBot : frattini Z ≠ (⊥ : Subgroup Z) :=
    frattini_ne_bot_of_not_isMulCommutative
      (hP.to_subgroup Z) hncommZ
  have hinvPhiZ : involutions Z ⊆ frattini Z :=
    involutions_subset_of_nontrivial_invariant
      (hP.to_subgroup Z) hZinv.restrict.range hxiZ.transitive
      (IsAInvariant.of_characteristic hZinv.restrict.range.subtype)
      hPhiZneBot
  have heZ : eZ = (restrictedFrattiniLinearEquivFrattiniSquare
      hEAZ hSquareEA hMapZ).trans eSquare := rfl
  have hXZ : ⁅X, Z⁆ ≤ frattiniSquare P :=
    commutator_le_frattiniSquare_of_restricted_typeC_typeB_factors
      hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
      hnuPrimitive hconj
      X Z hXinv hEAX eX factorsX rightX hleftX hrightThetaX
      hK1X htermX hSqX hAgemoX hK0X
      hZinv hEAZ hMapZ hinvPhiZ eZ heZ
      factorsZ leftZ rightZ hleftZ hleftThetaZ hrightThetaZ
      hK1Z htermZ hSqZ hAgemoZ hK0Z
  exact false_of_restrictedFactor_covers_of_crossCommutator_le_frattiniSquare
    hP hmulti hxi hprime hPhiComm hfour hexists
    X Z hXinv hPhiX hlenX hncommX hZinv hPhiZ hlenZ hncommZ hsup hXZ

end OddOrder.Higman.Suzuki2Groups
