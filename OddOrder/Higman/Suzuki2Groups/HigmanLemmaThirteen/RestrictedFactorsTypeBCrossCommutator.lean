/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCanonicalAmbientFamily
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorTypeBSquareEigenNonzero
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.TypeBEigenfamilyCrossCommutator

/-!
# Higman's Lemma 13: the cross commutator of two restricted type-B factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For two restricted type-B subgroups, this file fixes their explicit canonical
ambient right-factor eigenfamilies.  Their span and eigenvalue laws, together
with the square nondegeneracy of the second family, give the cross-commutator
inclusion in the ambient square Frattini subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped commutatorElement IsMulCommutative TensorProduct

universe uP

local instance restrictedFactorsTypeBCrossLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance restrictedFactorsTypeBCrossLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance restrictedFactorsTypeBCrossLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), restricted type-B/type-B cross commutator.**

The explicit canonical ambient right-factor families of two restricted
type-B subgroups have cross commutator contained in `Φ(P)²`. -/
theorem commutator_le_frattiniSquare_of_restricted_typeB_factors
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat} (hn : 2 ≤ n) (c : Y)
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
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (X Z : Subgroup P) [Finite X] [Finite Z]
    (hXinv : IsAInvariant Y.subtype X)
    (hEAX : IsElementaryAbelian 2 (frattini X))
    (eX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      Additive (frattini X) ≃ₗ[ZMod 2] GaloisField 2 n)
    (factorsX : XiLengthThreeTypeAFactorData X hXinv.restrict.range)
    (rightX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      FactorCoordinateData factorsX.right_invariant
        factorsX.frattini_lt_right.le
        (hXinv.restrict.rangeRestrict c) eX nu)
    (hleftX : factorsX.left = (frattini P).subgroupOf X)
    (hrightThetaX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      rightX.theta = 1)
    (hK1X : lowerCentralLayerKernel X 1 = ⊥)
    (htermX : lowerCentralTerm X 1 = frattini X)
    (hSqX : LowerCentralSquaresLieInSecond X)
    (hAgemoX : Agemo X 2 1 = frattini X)
    (hK0X : lowerCentralLayerKernel X 0 =
      (frattini X).subgroupOf (lowerCentralTerm X 0))
    (hZinv : IsAInvariant Y.subtype Z)
    (hEAZ : IsElementaryAbelian 2 (frattini Z))
    (hMapZ : (frattini Z).map Z.subtype = frattiniSquare P)
    (hxiZ : IsXiActor hZinv.restrict.range)
    (hinvPhiZ : involutions Z ⊆ frattini Z)
    (eZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      Additive (frattini Z) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heZ :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eZ = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAZ hSquareEA hMapZ).trans eSquare)
    (hconjZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      eZ.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hZinv.restrict.range.subtype).restrict
              (hZinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (factorsZ : XiLengthThreeTypeAFactorData Z hZinv.restrict.range)
    (leftZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      FactorCoordinateData factorsZ.left_invariant
        factorsZ.frattini_lt_left.le
        (hZinv.restrict.rangeRestrict c) eZ nu)
    (rightZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      FactorCoordinateData factorsZ.right_invariant
        factorsZ.frattini_lt_right.le
        (hZinv.restrict.rangeRestrict c) eZ nu)
    (hleftZ : factorsZ.left = (frattini P).subgroupOf Z)
    (hleftThetaZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      leftZ.theta = 1)
    (hrightThetaZ :
      letI : IsMulCommutative (frattini Z) :=
        IsMulCommutative.of_comm hEAZ.comm
      letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
      rightZ.theta = 1)
    (hK1Z : lowerCentralLayerKernel Z 1 = ⊥)
    (htermZ : lowerCentralTerm Z 1 = frattini Z)
    (hSqZ : LowerCentralSquaresLieInSecond Z)
    (hAgemoZ : Agemo Z 2 1 = frattini Z)
    (hK0Z : lowerCentralLayerKernel Z 0 =
      (frattini Z).subgroupOf (lowerCentralTerm Z 0)) :
    ⁅X, Z⁆ ≤ frattiniSquare P := by
  classical
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  letI : IsMulCommutative (frattini X) :=
    IsMulCommutative.of_comm hEAX.comm
  letI : CommGroup (frattini X) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
  letI : IsMulCommutative (frattini Z) :=
    IsMulCommutative.of_comm hEAZ.comm
  letI : CommGroup (frattini Z) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
  letI : IsMulCommutative (lowerCentralLayer P 0) :=
    lowerCentralLayerIsMulCommutative P 0
  letI : CommGroup (lowerCentralLayer P 0) :=
    { (inferInstance : Group (lowerCentralLayer P 0)) with
      mul_comm := (lowerCentralLayer_isElementaryAbelian P 0).comm }
  letI : Module (ZMod 2) (Additive (lowerCentralLayer P 0)) :=
    lowerCentralLayerZmodModule P 0
  let eRefl := LinearEquiv.refl (ZMod 2) (GaloisField 2 n)
  let iotaX := restrictedFactorAmbientInclusion hXinv hEAX eX c rightX
    hK1X htermX hSqX hAgemoX hK0X
  let iotaZ := restrictedFactorAmbientInclusion hZinv hEAZ eZ c rightZ
    hK1Z htermZ hSqZ hAgemoZ hK0Z
  let f := factorAmbientEigenFamily eRefl iotaX
  let g := factorAmbientEigenFamily eRefl iotaZ
  have hcanonicalX :
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (f i) =
        rightX.lambda ^ (2 ^ i.val) • f i) ∧
      ∀ x : lowerCentralTerm X 0,
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom X x)) ∈
          Submodule.span (GaloisField 2 n) (Set.range f) := by
    simpa only [iotaX, f, eRefl] using
      canonicalRestrictedFactorAmbientEigenFamily_eigen_and_spans
        hP hXinv hEAX eX c factorsX rightX hleftX
        hK1X htermX hSqX hAgemoX hK0X
  have hcanonicalZ :
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (g i) =
        rightZ.lambda ^ (2 ^ i.val) • g i) ∧
      ∀ z : lowerCentralTerm Z 0,
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom Z z)) ∈
          Submodule.span (GaloisField 2 n) (Set.range g) := by
    simpa only [iotaZ, g, eRefl] using
      canonicalRestrictedFactorAmbientEigenFamily_eigen_and_spans
        hP hZinv hEAZ eZ c factorsZ rightZ hleftZ
        hK1Z htermZ hSqZ hAgemoZ hK0Z
  have hrightXLambda : rightX.lambda =
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu :=
    FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
      rightX hrightThetaX
  have hrightZLambda : rightZ.lambda =
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu :=
    FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
      rightZ hrightThetaZ
  have hf : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (f i) =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • f i := by
    intro i
    simpa only [hrightXLambda] using hcanonicalX.1 i
  have hg : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (g i) =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • g i := by
    intro i
    simpa only [hrightZLambda] using hcanonicalZ.1 i
  obtain ⟨_, _, hZsquare⟩ :=
    exists_restrictedFactorTypeBSquareEigenCommutator
      hP hxi hPhiComm hfour hexists hZinv hEAZ hMapZ hxiZ hinvPhiZ
      (by omega : 0 < n) eSquare eZ heZ nu hnuPrimitive c hconjZ
      factorsZ leftZ rightZ hleftZ hleftThetaZ hrightThetaZ
      hK1Z htermZ hSqZ hAgemoZ hK0Z
  have hsquare :
      let eMiddle :=
        frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
      let middleBasis :=
        conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
      ∀ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (g k) ≠ 0 := by
    dsimp only
    intro k
    simpa only [g, iotaZ, eRefl] using (hZsquare k).2.2
  exact commutator_le_frattiniSquare_of_typeB_eigenfamily_spans
    hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
    f g hf hg hsquare X Z hcanonicalX.2 hcanonicalZ.2

end OddOrder.Higman.Suzuki2Groups
