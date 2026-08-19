/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCanonicalAmbientFamily
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorSameMiddleZero
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorTypeCSquareEigenNonzero
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.TypeCCEigenfamilyCrossCommutator

/-!
# Higman's Lemma 13: the cross commutator of two restricted type-C factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

For two restricted type-C subgroups, this file fixes their canonical ambient
right-factor eigenfamilies.  Same-factor middle vanishing, shifted type-C
square nondegeneracy, and the span of every ground class are all proved for
those exact families.  The type-C/C Jacobi connector then places the subgroup
cross commutator in the ambient square Frattini subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped commutatorElement IsMulCommutative TensorProduct

universe uP

local instance restrictedFactorsTypeCCCrossLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance restrictedFactorsTypeCCCrossLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance restrictedFactorsTypeCCCrossLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (printed p. 93), restricted type-C/type-C cross
commutator.**

The explicit canonical ambient right-factor families of two restricted
type-C subgroups have cross commutator contained in `Φ(P)²`.
-/
theorem commutator_le_frattiniSquare_of_restricted_typeC_factors
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
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (X Z : Subgroup P) [Finite X] [Finite Z]
    (hXinv : IsAInvariant Y.subtype X)
    (hPhiX : NormalInvariantCover Y.subtype (frattini P) X)
    (hlenX : HasXiLengthThree hXinv.restrict.range.subtype)
    (hncommX : ¬ IsMulCommutative X)
    (hEAX : IsElementaryAbelian 2 (frattini X))
    (hMapX : (frattini X).map X.subtype = frattiniSquare P)
    (eX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      Additive (frattini X) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heX :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eX = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAX hSquareEA hMapX).trans eSquare)
    (factorsX : XiLengthThreeTypeAFactorData X hXinv.restrict.range)
    (leftX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      FactorCoordinateData factorsX.left_invariant
        factorsX.frattini_lt_left.le
        (hXinv.restrict.rangeRestrict c) eX nu)
    (rightX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      FactorCoordinateData factorsX.right_invariant
        factorsX.frattini_lt_right.le
        (hXinv.restrict.rangeRestrict c) eX nu)
    (hleftX : factorsX.left = (frattini P).subgroupOf X)
    (hleftThetaX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      leftX.theta = 1)
    (hrightThetaX :
      letI : IsMulCommutative (frattini X) :=
        IsMulCommutative.of_comm hEAX.comm
      letI : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
      rightX.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hZinv : IsAInvariant Y.subtype Z)
    (hPhiZ : NormalInvariantCover Y.subtype (frattini P) Z)
    (hlenZ : HasXiLengthThree hZinv.restrict.range.subtype)
    (hncommZ : ¬ IsMulCommutative Z)
    (hEAZ : IsElementaryAbelian 2 (frattini Z))
    (hMapZ : (frattini Z).map Z.subtype = frattiniSquare P)
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
      rightZ.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r) :
    ⁅X, Z⁆ ≤ frattiniSquare P := by
  classical
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let : IsMulCommutative (frattini X) :=
    IsMulCommutative.of_comm hEAX.comm
  let : CommGroup (frattini X) := inferInstance
  let : Module (ZMod 2) (Additive (frattini X)) := hEAX.zmodModule
  let : IsMulCommutative (frattini Z) :=
    IsMulCommutative.of_comm hEAZ.comm
  let : CommGroup (frattini Z) := inferInstance
  let : Module (ZMod 2) (Additive (frattini Z)) := hEAZ.zmodModule
  let : IsMulCommutative (lowerCentralLayer P 0) :=
    lowerCentralLayerIsMulCommutative P 0
  let : CommGroup (lowerCentralLayer P 0) :=
    { (inferInstance : Group (lowerCentralLayer P 0)) with
      mul_comm := (lowerCentralLayer_isElementaryAbelian P 0).comm }
  let : Module (ZMod 2) (Additive (lowerCentralLayer P 0)) :=
    lowerCentralLayerZmodModule P 0
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
      p ∣ Nat.card hXinv.restrict.range → p ∣ (involutions X).ncard :=
    restricted_range_primeSupport hXinv hinvX hprime
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
      p ∣ Nat.card hZinv.restrict.range → p ∣ (involutions Z).ncard :=
    restricted_range_primeSupport hZinv hinvZ hprime
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
  have hPhiXneBot : frattini X ≠ (⊥ : Subgroup X) :=
    frattini_ne_bot_of_not_isMulCommutative (hP.to_subgroup X) hncommX
  have hinvPhiX : involutions X ⊆ frattini X :=
    involutions_subset_of_nontrivial_invariant
      (hP.to_subgroup X) hXinv.restrict.range hxiX.transitive
      (IsAInvariant.of_characteristic hXinv.restrict.range.subtype)
      hPhiXneBot
  have hPhiZneBot : frattini Z ≠ (⊥ : Subgroup Z) :=
    frattini_ne_bot_of_not_isMulCommutative (hP.to_subgroup Z) hncommZ
  have hinvPhiZ : involutions Z ⊆ frattini Z :=
    involutions_subset_of_nontrivial_invariant
      (hP.to_subgroup Z) hZinv.restrict.range hxiZ.transitive
      (IsAInvariant.of_characteristic hZinv.restrict.range.subtype)
      hPhiZneBot
  have hconjX : eX.conj
        (elabRepresentation 2
          (IsAInvariant.of_characteristic
            hXinv.restrict.range.subtype).restrict
            (hXinv.restrict.rangeRestrict c)) =
      Algebra.lmul (ZMod 2) (GaloisField 2 n) nu := by
    simpa only [heX] using
      restrictedFrattiniSingerCoordinate_conj
        hXinv hEAX hSquareEA hMapX c eSquare nu hconj
  have hconjZ : eZ.conj
        (elabRepresentation 2
          (IsAInvariant.of_characteristic
            hZinv.restrict.range.subtype).restrict
            (hZinv.restrict.rangeRestrict c)) =
      Algebra.lmul (ZMod 2) (GaloisField 2 n) nu := by
    simpa only [heZ] using
      restrictedFrattiniSingerCoordinate_conj
        hZinv hEAZ hSquareEA hMapZ c eSquare nu hconj
  have hleftSourceX : nu = leftX.lambda * leftX.lambda := by
    calc
      nu = leftX.lambda * leftX.theta leftX.lambda :=
        leftX.kernel_eigenvalue_eq
      _ = leftX.lambda * leftX.lambda := by simp [hleftThetaX]
  have hleftSourceZ : nu = leftZ.lambda * leftZ.lambda := by
    calc
      nu = leftZ.lambda * leftZ.theta leftZ.lambda :=
        leftZ.kernel_eigenvalue_eq
      _ = leftZ.lambda * leftZ.lambda := by simp [hleftThetaZ]
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
  have hsameX :
      ∀ i j, frattiniMiddleCommutatorBilinearBaseChange
        (GaloisField 2 n) hP hxi hPhiComm hexists (f i) (f j) = 0 := by
    simpa only [f, iotaX, eRefl] using
      frattiniMiddleCommutatorBilinearBaseChange_canonicalRestrictedFactorFamily_eq_zero
        hP hmulti hxi hprime hPhiComm hexists
        hXinv hPhiX hlenX hncommX hEAX eX c rightX
        hK1X htermX hSqX hAgemoX hK0X
  have hsameZ :
      ∀ i j, frattiniMiddleCommutatorBilinearBaseChange
        (GaloisField 2 n) hP hxi hPhiComm hexists (g i) (g j) = 0 := by
    simpa only [g, iotaZ, eRefl] using
      frattiniMiddleCommutatorBilinearBaseChange_canonicalRestrictedFactorFamily_eq_zero
        hP hmulti hxi hprime hPhiComm hexists
        hZinv hPhiZ hlenZ hncommZ hEAZ eZ c rightZ
        hK1Z htermZ hSqZ hAgemoZ hK0Z
  have h2r : 2 * r ≤ n := by omega
  obtain ⟨_, _, _, _, hXsquareRaw⟩ :=
    exists_restrictedFactorTypeCSquareEigenCommutator
      hP hxi hPhiComm hfour hexists hXinv hEAX hMapX hxiX hinvPhiX
      hn eSquare eX heX nu hnuPrimitive c hconjX factorsX leftX rightX
      hleftX hleftSourceX rightX.kernel_eigenvalue_eq hr h2r hrightThetaX
      hK1X htermX hSqX hAgemoX hK0X
  obtain ⟨_, _, _, _, hZsquareRaw⟩ :=
    exists_restrictedFactorTypeCSquareEigenCommutator
      hP hxi hPhiComm hfour hexists hZinv hEAZ hMapZ hxiZ hinvPhiZ
      hn eSquare eZ heZ nu hnuPrimitive c hconjZ factorsZ leftZ rightZ
      hleftZ hleftSourceZ rightZ.kernel_eigenvalue_eq hr h2r hrightThetaZ
      hK1Z htermZ hSqZ hAgemoZ hK0Z
  have hXsquare :
      let eMiddle :=
        frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
      let middleBasis :=
        conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
      ∀ k a,
        (a.val : ZMod n) + 1 =
            (k.val : ZMod n) + (r : ZMod n) →
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (f a) ≠ 0 := by
    dsimp only
    intro k a hka
    simpa only [f, iotaX, eRefl] using hXsquareRaw k a hka
  have hZsquare :
      let eMiddle :=
        frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
      let middleBasis :=
        conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
      ∀ k a,
        (a.val : ZMod n) + 1 =
            (k.val : ZMod n) + (r : ZMod n) →
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (g a) ≠ 0 := by
    dsimp only
    intro k a hka
    simpa only [g, iotaZ, eRefl] using hZsquareRaw k a hka
  exact commutator_le_frattiniSquare_of_typeCC_eigenfamily_spans
    hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
    hnuPrimitive hconj rightX.lambda rightZ.lambda rightX.theta rightZ.theta
    rightX.kernel_eigenvalue_eq rightZ.kernel_eigenvalue_eq
    hrightThetaX hrightThetaZ f g hcanonicalX.1 hcanonicalZ.1
    hsameX hsameZ hXsquare hZsquare X Z hcanonicalX.2 hcanonicalZ.2

end OddOrder.Higman.Suzuki2Groups
