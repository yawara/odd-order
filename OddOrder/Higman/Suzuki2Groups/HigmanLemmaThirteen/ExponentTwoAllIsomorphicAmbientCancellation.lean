/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedAmbientBracketCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllIsomorphicSupportCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoLambdaPrimitivity
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseJoinInfrastructure

/-!
# Higman's Lemma 13: ambient cancellation in the all-isomorphic branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exceptional exponent-two branch, the three actual type-A factors
have one common nontrivial normalized square-law automorphism.  The two
pairwise mixed terms therefore have the same two twisted supports.  After
the two copies of the common factor are aligned in the ambient zeroth
lower-central layer, its polarized square law supplies the third support
column.  The resulting coordinate cancellation is transported back to a
genuine ambient lower-central commutator.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance allIsomorphicAmbientLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance allIsomorphicAmbientLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance allIsomorphicAmbientLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), all-isomorphic ambient cancellation.**

Let `J` and `K` be the joins of `X,T` and `Z,T`, respectively.  Suppose
their four prescribed factor coordinates have one common nontrivial
normalized parameter.  Then the two copies of `T` admit a nonzero scalar
alignment, and a nontrivial combination of `X`, `Z`, and the actual `T`
factor commutes with the whole aligned `T` family in the ambient
lower-central Lie layer.

The self-bracket term is not assumed: it is obtained by polarizing the
packaged square law of the prescribed `T` inclusion. -/
theorem exists_allIsomorphic_aligned_ambientBracket_family_eq_zero
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)}
    {T J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hTJ : T ≤ J)
    (hTK : T ≤ K)
    (hMapJ : (frattini J).map J.subtype = frattini P)
    (hMapK : (frattini K).map K.subtype = frattini P)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    {n : Nat}
    (hn : 2 ≤ n)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (hK1P : lowerCentralLayerKernel P 1 = ⊥)
    (htermP : lowerCentralTerm P 1 = frattini P)
    {nu : GaloisField 2 n}
    (c : Y)
    (fJ : XiLengthThreeTypeAFactorData J hJinv.restrict.range)
    (fK : XiLengthThreeTypeAFactorData K hKinv.restrict.range) :
    let hEAJ : IsElementaryAbelian 2 (frattini J) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapJ).symm hPhiEA
    let hEAK : IsElementaryAbelian 2 (frattini K) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapK).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hEAJ.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hEAJ.zmodModule
    letI : IsMulCommutative (frattini K) :=
      IsMulCommutative.of_comm hEAK.comm
    letI : Module (ZMod 2) (Additive (frattini K)) :=
      hEAK.zmodModule
    let eJ :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMapJ).trans ePhi
    let eK :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMapK).trans ePhi
    ∀
    (dataX : FactorCoordinateData fJ.left_invariant
      fJ.frattini_lt_left.le
      (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataTJ : FactorCoordinateData fJ.right_invariant
      fJ.frattini_lt_right.le
      (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataZ : FactorCoordinateData fK.left_invariant
      fK.frattini_lt_left.le
      (hKinv.restrict.rangeRestrict c) eK nu)
    (dataTK : FactorCoordinateData fK.right_invariant
      fK.frattini_lt_right.le
      (hKinv.restrict.rangeRestrict c) eK nu)
    (_hTJcopy : fJ.right = T.subgroupOf J)
    (_hTKcopy : fK.right = T.subgroupOf K)
    (hK1J : lowerCentralLayerKernel J 1 = ⊥)
    (htermJ : lowerCentralTerm J 1 = frattini J)
    (hSqJ : LowerCentralSquaresLieInSecond J)
    (hAgemoJ : Agemo J 2 1 = frattini J)
    (hK0J : lowerCentralLayerKernel J 0 =
      (frattini J).subgroupOf (lowerCentralTerm J 0))
    (hK1K : lowerCentralLayerKernel K 1 = ⊥)
    (htermK : lowerCentralTerm K 1 = frattini K)
    (hSqK : LowerCentralSquaresLieInSecond K)
    (hAgemoK : Agemo K 2 1 = frattini K)
    (hK0K : lowerCentralLayerKernel K 0 =
      (frattini K).subgroupOf (lowerCentralTerm K 0))
    (_hxiJ : IsXiActor hJinv.restrict.range)
    (_hxiK : IsXiActor hKinv.restrict.range)
    (_hinvPhiJ : involutions J ⊆ frattini J)
    (_hinvPhiK : involutions K ⊆ frattini K)
    (_hconjJ :
      eJ.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hJinv.restrict.range.subtype :
                IsAInvariant hJinv.restrict.range.subtype
                  (frattini J)).restrict
            (hJinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (_hconjK :
      eK.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hKinv.restrict.range.subtype :
                IsAInvariant hKinv.restrict.range.subtype
                  (frattini K)).restrict
            (hKinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (_hsourceX :
      nu = dataX.lambda * dataX.theta dataX.lambda)
    (_hsourceTJ :
      nu = dataTJ.lambda * dataTJ.theta dataTJ.lambda)
    (_hsourceZ :
      nu = dataZ.lambda * dataZ.theta dataZ.lambda)
    (_hsourceTK :
      nu = dataTK.lambda * dataTK.theta dataTK.lambda)
    (_hnormTJ : IsNormalizedFactorParameter n dataTJ.theta)
    (_hthetaX : dataX.theta = dataTJ.theta)
    (_hthetaZ : dataZ.theta = dataTJ.theta)
    (_hthetaTK : dataTK.theta = dataTJ.theta)
    (_hthetaNe : dataTJ.theta ≠ 1)
    (_hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1)),
    let iX := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataX
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iZ := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataZ
        hK1K htermK hSqK hAgemoK hK0K
    let iT := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataTJ
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iT' := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataTK
        hK1K htermK hSqK hAgemoK hK0K
    ∃ t a b cT : GaloisField 2 n,
      t ≠ 0 ∧
      (a ≠ 0 ∨ b ≠ 0) ∧
      (∀ beta, iT beta = iT' (t * beta)) ∧
      ∀ beta,
        lowerCentralCommutatorBilinear P
          (iX a + iZ b + iT cT) (iT beta) = 0 := by
  classical
  dsimp only
  let hEAJ : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapJ).symm hPhiEA
  let hEAK : IsElementaryAbelian 2 (frattini K) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapK).symm hPhiEA
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hEAJ.comm
  let : CommGroup (frattini J) := inferInstance
  let : Module (ZMod 2) (Additive (frattini J)) :=
    hEAJ.zmodModule
  let : IsMulCommutative (frattini K) :=
    IsMulCommutative.of_comm hEAK.comm
  let : CommGroup (frattini K) := inferInstance
  let : Module (ZMod 2) (Additive (frattini K)) :=
    hEAK.zmodModule
  let eJ :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapJ).trans ePhi
  let eK :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapK).trans ePhi
  intro dataX dataTJ dataZ dataTK hTJcopy hTKcopy
    hK1J htermJ hSqJ hAgemoJ hK0J
    hK1K htermK hSqK hAgemoK hK0K
    hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
    hsourceX hsourceTJ hsourceZ hsourceTK hnormTJ
    hthetaX hthetaZ hthetaTK hthetaNe hnuPrimitive
  let incX := dataX.toInclusionData
    hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
  let incTJ := dataTJ.toInclusionData
    hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
  let incZ := dataZ.toInclusionData
    hEAK eK hK1K htermK hSqK hAgemoK hK0K
  let incTK := dataTK.toInclusionData
    hEAK eK hK1K htermK hSqK hAgemoK hK0K
  let M₁ := mixedTermBilinear incX incTJ
  let M₂Raw := mixedTermBilinear incZ incTK
  let M₃ := mixedTermBilinear incTJ incTJ
  let iX := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataX
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iZ := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataZ
      hK1K htermK hSqK hAgemoK hK0K
  let iT := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataTJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iT' := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataTK
      hK1K htermK hSqK hAgemoK hK0K
  have hn0 : n ≠ 0 := by omega
  have hsourceX' :
      nu = dataX.lambda * dataTJ.theta dataX.lambda := by
    simpa only [hthetaX] using hsourceX
  have hsourceZ' :
      nu = dataZ.lambda * dataTJ.theta dataZ.lambda := by
    simpa only [hthetaZ] using hsourceZ
  have hsourceTK' :
      nu = dataTK.lambda * dataTJ.theta dataTK.lambda := by
    simpa only [hthetaTK] using hsourceTK
  have hlambdaX : dataX.lambda = dataTJ.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataTJ.theta dataX.lambda dataTJ.lambda nu
      hnormTJ hnuPrimitive hsourceX' hsourceTJ
  have hlambdaZ : dataZ.lambda = dataTJ.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataTJ.theta dataZ.lambda dataTJ.lambda nu
      hnormTJ hnuPrimitive hsourceZ' hsourceTJ
  have hlambdaTK : dataTK.lambda = dataTJ.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataTJ.theta dataTK.lambda dataTJ.lambda nu
      hnormTJ hnuPrimitive hsourceTK' hsourceTJ
  have hlambdaPrimitive :
      IsPrimitiveRoot dataTJ.lambda (2 ^ n - 1) :=
    lambda_isPrimitiveRoot_of_normalized_twisted_norm
      hn0 dataTJ.theta dataTJ.lambda nu
      hnormTJ hnuPrimitive hsourceTJ
  obtain ⟨t, ht, halign⟩ :=
    exists_scalar_reparameterization_of_common_factor
      hP hJinv hKinv hTJ hTK hMapJ hMapK hn0
      hEAJ eJ hEAK eK c dataTJ dataTK
      hTJcopy hTKcopy
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
      hlambdaTK.symm hlambdaPrimitive
  let scale : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
    Algebra.lmul (ZMod 2) (GaloisField 2 n) t
  let M₂ := M₂Raw.compl₂ scale
  have hequiv₁ : ∀ alpha beta,
      M₁ (dataTJ.lambda * alpha) (dataTJ.lambda * beta) =
        nu * M₁ alpha beta := by
    intro alpha beta
    simpa only [hlambdaX] using
      (mixedTermBilinear_lambda_equivariance
        hEAJ eJ dataX dataTJ
        hK1J htermJ hSqJ hAgemoJ hK0J hconjJ alpha beta)
  have hequiv₂Raw : ∀ alpha beta,
      M₂Raw (dataZ.lambda * alpha) (dataTK.lambda * beta) =
        nu * M₂Raw alpha beta := by
    intro alpha beta
    exact mixedTermBilinear_lambda_equivariance
      hEAK eK dataZ dataTK
      hK1K htermK hSqK hAgemoK hK0K hconjK alpha beta
  have hequiv₂ : ∀ alpha beta,
      M₂ (dataTJ.lambda * alpha) (dataTJ.lambda * beta) =
        nu * M₂ alpha beta := by
    intro alpha beta
    change M₂Raw (dataTJ.lambda * alpha)
        (t * (dataTJ.lambda * beta)) =
      nu * M₂Raw alpha (t * beta)
    simpa only [hlambdaZ, hlambdaTK, mul_assoc, mul_left_comm, mul_comm] using
      hequiv₂Raw alpha (t * beta)
  have hM₁ne : ∃ alpha beta, M₁ alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero
      fJ incX incTJ hxiJ hinvPhiJ
  have hM₂RawNe : ∃ alpha beta, M₂Raw alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero
      fK incZ incTK hxiK hinvPhiK
  have hM₂ne : ∃ alpha beta, M₂ alpha beta ≠ 0 := by
    obtain ⟨alpha, beta, hne⟩ := hM₂RawNe
    refine ⟨alpha, t⁻¹ * beta, ?_⟩
    change M₂Raw alpha (t * (t⁻¹ * beta)) ≠ 0
    have htInv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    simpa only [← mul_assoc, htInv, one_mul] using hne
  have hordLambda : orderOf dataTJ.lambda = 2 ^ n - 1 :=
    orderOf_lambda_eq_of_normalized_twisted_norm
      hn0 dataTJ.theta dataTJ.lambda nu
      hnormTJ hnuPrimitive hsourceTJ
  rcases hnormTJ with hthetaOne |
      ⟨r, hr0, hrhalf, hthetaFrobenius, _hthetaOdd⟩
  · exact (hthetaNe hthetaOne).elim
  · have hrn : r < n := by omega
    have hlambdaPower : dataTJ.lambda ^ (1 + 2 ^ r) = nu := by
      have hthetaApply :
          dataTJ.theta dataTJ.lambda = dataTJ.lambda ^ 2 ^ r := by
        rw [hthetaFrobenius, frobeniusEquiv_pow_apply]
      calc
        dataTJ.lambda ^ (1 + 2 ^ r) =
            dataTJ.lambda * dataTJ.lambda ^ 2 ^ r := by
              rw [pow_add, pow_one]
        _ = dataTJ.lambda * dataTJ.theta dataTJ.lambda := by
              rw [hthetaApply]
        _ = nu := hsourceTJ.symm
    obtain ⟨A₁, A₂, _hA, hM₁Power⟩ :=
      mixedTerm_two_monomials_of_theta_eq
        (Nat.ne_of_gt hr0) hrn M₁ dataTJ.lambda nu
        hordLambda hlambdaPower hequiv₁ hM₁ne
    obtain ⟨B₁, B₂, _hB, hM₂Power⟩ :=
      mixedTerm_two_monomials_of_theta_eq
        (Nat.ne_of_gt hr0) hrn M₂ dataTJ.lambda nu
        hordLambda hlambdaPower hequiv₂ hM₂ne
    have hthetaApply (x : GaloisField 2 n) :
        dataTJ.theta x = x ^ 2 ^ r := by
      rw [hthetaFrobenius, frobeniusEquiv_pow_apply]
    have hM₁Profile : ∀ alpha beta,
        M₁ alpha beta =
          A₁ * (alpha * dataTJ.theta beta) +
            A₂ * (dataTJ.theta alpha * beta) := by
      intro alpha beta
      rw [hM₁Power alpha beta, hthetaApply beta, hthetaApply alpha]
    have hM₂Profile : ∀ alpha beta,
        M₂ alpha beta =
          B₁ * (alpha * dataTJ.theta beta) +
            B₂ * (dataTJ.theta alpha * beta) := by
      intro alpha beta
      rw [hM₂Power alpha beta, hthetaApply beta, hthetaApply alpha]
    have hM₃Profile : ∀ alpha beta,
        M₃ alpha beta =
          alpha * dataTJ.theta beta + dataTJ.theta alpha * beta := by
      intro alpha beta
      have hthetaInc : incTJ.theta = dataTJ.theta :=
        FactorCoordinateData.toInclusionData_theta
          hEAJ eJ dataTJ hK1J htermJ hSqJ hAgemoJ hK0J
      have hself :=
        incTJ.ambientCenterCoordinate_selfBracket_eq alpha beta
      rw [hthetaInc] at hself
      simpa [M₃] using hself
    obtain ⟨a, b, cT, hab, hcancel⟩ :=
      exists_nontrivial_first_pair_cancel_three_twisted_bilinear_profiles
        dataTJ.theta M₁ M₂ M₃ A₁ A₂ B₁ B₂
        hM₁Profile hM₂Profile hM₃Profile
    have hbridgeJ (alpha beta : GaloisField 2 n) :
        M₁ alpha beta =
          ambientCenterCoordinate hPhiEA hK1P htermP ePhi
            (lowerCentralCommutatorBilinear P
              (iX alpha) (iT beta)) := by
      exact pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
        hPhiEA hMapJ ePhi hK1P htermP
        hK1J htermJ hSqJ hK0J incX incTJ alpha beta
    have hbridgeK (alpha beta : GaloisField 2 n) :
        M₂Raw alpha beta =
          ambientCenterCoordinate hPhiEA hK1P htermP ePhi
            (lowerCentralCommutatorBilinear P
              (iZ alpha) (iT' beta)) := by
      exact pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
        hPhiEA hMapK ePhi hK1P htermP
        hK1K htermK hSqK hK0K incZ incTK alpha beta
    have hbridgeSelf (alpha beta : GaloisField 2 n) :
        M₃ alpha beta =
          ambientCenterCoordinate hPhiEA hK1P htermP ePhi
            (lowerCentralCommutatorBilinear P
              (iT alpha) (iT beta)) := by
      exact pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
        hPhiEA hMapJ ePhi hK1P htermP
        hK1J htermJ hSqJ hK0J incTJ incTJ alpha beta
    refine ⟨t, a, b, cT, ht, hab, halign, fun beta => ?_⟩
    apply (ambientCenterCoordinate
      hPhiEA hK1P htermP ePhi).injective
    simp only [map_zero, map_add, LinearMap.add_apply]
    rw [← hbridgeJ a beta]
    have hsecond :
        ambientCenterCoordinate hPhiEA hK1P htermP ePhi
            (lowerCentralCommutatorBilinear P
              (iZ b) (iT beta)) =
          M₂ b beta := by
      change _ = M₂Raw b (t * beta)
      rw [halign beta]
      exact (hbridgeK b (t * beta)).symm
    rw [hsecond, ← hbridgeSelf cT beta]
    exact hcancel beta

end

end OddOrder.Higman.Suzuki2Groups
