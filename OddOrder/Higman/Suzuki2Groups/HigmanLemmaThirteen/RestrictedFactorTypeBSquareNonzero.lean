/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleSupport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorMixedTermBridge
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman's Lemma 13: nonzero type-B square commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For a restricted length-three factor pair of type B/B, Lemma 12 makes the
internal mixed term a nonzero scalar multiple of field multiplication.  The
restricted mixed-term bridge transports that formula to the actual ambient
commutator `Φ(P)/Φ(P)² × P/Φ(P) → Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (p. 92), nonzero B/B square commutator.**

For two restricted factors with identity semilinear parameter, the actual
ambient `Φ(P)²`-valued commutator, expressed in the common middle and square
coordinates, is a nonzero scalar multiple of field multiplication. -/
theorem exists_restrictedFactorTypeBSquareCommutator_monomial
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    (hxiS : IsXiActor hSinv.restrict.range)
    (hinvPhiS : involutions S ⊆ frattini S)
    {n : Nat} (hn : 0 < n)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heS :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eS = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare)
    (nu : GaloisField 2 n)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (c : Y)
    (hconjS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      eS.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hSinv.restrict.range.subtype).restrict
              (hSinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (factors : XiLengthThreeTypeAFactorData S hSinv.restrict.range)
    (left :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.left_invariant
        factors.frattini_lt_left.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (right :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.right_invariant
        factors.frattini_lt_right.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hleft : factors.left = (frattini P).subgroupOf S)
    (hleftTheta :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      left.theta = 1)
    (hrightTheta :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      right.theta = 1)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
      ∀ alpha beta : GaloisField 2 n,
        eSquare
            (frattiniSquareCommutatorBilinear
              hP hxi hPhiComm hfour hexists
              ((frattiniMiddleCoordinate
                hP hxi hPhiComm hfour hexists eSquare).symm alpha)
              (restrictedFactorAmbientInclusion hSinv hEAS eS c right
                hK1S htermS hSqS hAgemoS hK0S beta)) =
          c0 * (alpha * beta) := by
  classical
  dsimp only
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
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : CommGroup (frattini S) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  let L := left.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  let R := right.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  have hleftLambda : left.lambda = middleWeight :=
    FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
      left hleftTheta
  have hrightLambda : right.lambda = middleWeight :=
    FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
      right hrightTheta
  have hprimMiddle : IsPrimitiveRoot middleWeight (2 ^ n - 1) :=
    hnuPrimitive.map_of_injective
      (frobeniusEquiv (GaloisField 2 n) 2).symm.injective
  have hordMiddle : orderOf middleWeight = 2 ^ n - 1 :=
    hprimMiddle.eq_orderOf.symm
  have hmiddleSquare : middleWeight ^ 2 = nu :=
    frobeniusEquiv_symm_pow_p (GaloisField 2 n) 2 nu
  have hmiddleSource : middleWeight ^ (1 + 2 ^ 0) = nu := by
    norm_num
    exact hmiddleSquare
  have hequiv : ∀ alpha beta : GaloisField 2 n,
      mixedTermBilinear L R (middleWeight * alpha) (middleWeight * beta) =
        nu * mixedTermBilinear L R alpha beta := by
    intro alpha beta
    simpa only [hleftLambda, hrightLambda] using
      (mixedTermBilinear_lambda_equivariance
        hEAS eS left right hK1S htermS hSqS hAgemoS hK0S hconjS
          alpha beta)
  have hM0 : ∃ alpha beta : GaloisField 2 n,
      mixedTermBilinear L R alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxiS hinvPhiS
  obtain ⟨c0, hc0, hmono⟩ :=
    mixedTerm_monomial_of_theta_one hn (mixedTermBilinear L R)
      middleWeight nu hordMiddle hmiddleSource hequiv hM0
  refine ⟨c0, hc0, fun alpha beta => ?_⟩
  rw [restrictedFactorMixedTerm_eq_frattiniSquareCommutator
    hP hxi hPhiComm hfour hexists hSinv hEAS hMap eSquare eS heS c
    factors left right hleft hK1S htermS hSqS hAgemoS hK0S]
  exact hmono alpha beta

/-- A nonzero-coordinate monomial value certifies that the underlying
ambient `Φ(P)²`-valued commutator is nonzero.  In particular, applying this
to `exists_restrictedFactorTypeBSquareCommutator_monomial` shows that every
pair of nonzero type-B field coordinates has nonzero ambient bracket. -/
theorem frattiniSquareCommutatorBilinear_ne_zero_of_coordinate_monomial
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (u : Additive (frattiniMiddleLayer P))
    (v : Additive (lowerCentralLayer P 0))
    (c0 alpha beta : GaloisField 2 n)
    (hc0 : c0 ≠ 0) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hcoordinate :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : CommGroup (frattini P) :=
        { (inferInstance : Group (frattini P)) with
          mul_comm := hPhiComm.is_comm.comm }
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eSquare
          (frattiniSquareCommutatorBilinear
            hP hxi hPhiComm hfour hexists u v) =
        c0 * (alpha * beta)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists u v ≠ 0 := by
  dsimp only at hcoordinate ⊢
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
  intro hzero
  have hproduct : c0 * (alpha * beta) ≠ 0 :=
    mul_ne_zero hc0 (mul_ne_zero halpha hbeta)
  apply hproduct
  rw [← hcoordinate, hzero]
  exact map_zero eSquare

end OddOrder.Higman.Suzuki2Groups
