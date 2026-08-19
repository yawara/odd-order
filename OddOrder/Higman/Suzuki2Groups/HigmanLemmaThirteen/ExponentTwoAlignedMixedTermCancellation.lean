/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorScalarBridge
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoLambdaCoherence
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoLambdaPrimitivity
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseMixedTermSupport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman Lemma 13: aligned cancellation across two pairwise joins

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Suppose the actual factors `X` and `Y` have the same normalized square-law
parameter, while one actual factor `W` occurs on the right of the pairwise
joins `J` and `K`.  Their quotient eigenvalues are then coherent.  The two
coordinates on `W` differ by one nonzero scalar after inclusion in the
ambient zeroth lower-central layer.

Reparameterizing the second mixed term by this scalar puts both pairwise
mixed terms over one actual ambient `W`-coordinate.  Outside the case in
which all three parameters are the same nontrivial automorphism, the common
support calculation supplies nontrivial *input* coordinates whose mixed
terms cancel on the whole `W`-family.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance alignedCancellationLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance alignedCancellationLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance alignedCancellationLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), cancellation after aligning the common
factor.**

The two right-hand factor coordinates are first identified inside the
ambient `L₀(P)`.  After the resulting scalar reparameterization of the
second mixed term, there are nontrivial left input coordinates `a,b` for
which the two mixed-term families cancel at every common right coordinate.
-/
theorem exists_aligned_common_factor_and_cancelled_pairwise_mixedTerms
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)}
    {W J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hWJ : W ≤ J)
    (hWK : W ≤ K)
    (hMapJ : (frattini J).map J.subtype = frattini P)
    (hMapK : (frattini K).map K.subtype = frattini P)
    {n : Nat}
    (hn : 2 ≤ n)
    (hEAJ : IsElementaryAbelian 2 (frattini J))
    (eJ :
      letI : IsMulCommutative (frattini J) :=
        IsMulCommutative.of_comm hEAJ.comm
      letI : Module (ZMod 2) (Additive (frattini J)) :=
        hEAJ.zmodModule
      Additive (frattini J) ≃ₗ[ZMod 2] GaloisField 2 n)
    (hEAK : IsElementaryAbelian 2 (frattini K))
    (eK :
      letI : IsMulCommutative (frattini K) :=
        IsMulCommutative.of_comm hEAK.comm
      letI : Module (ZMod 2) (Additive (frattini K)) :=
        hEAK.zmodModule
      Additive (frattini K) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    (c : Y)
    (fJ : XiLengthThreeTypeAFactorData J hJinv.restrict.range)
    (fK : XiLengthThreeTypeAFactorData K hKinv.restrict.range)
    (dataLeftJ :
      letI : IsMulCommutative (frattini J) :=
        IsMulCommutative.of_comm hEAJ.comm
      letI : Module (ZMod 2) (Additive (frattini J)) :=
        hEAJ.zmodModule
      FactorCoordinateData fJ.left_invariant
        fJ.frattini_lt_left.le
        (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataCommonJ :
      letI : IsMulCommutative (frattini J) :=
        IsMulCommutative.of_comm hEAJ.comm
      letI : Module (ZMod 2) (Additive (frattini J)) :=
        hEAJ.zmodModule
      FactorCoordinateData fJ.right_invariant
        fJ.frattini_lt_right.le
        (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataLeftK :
      letI : IsMulCommutative (frattini K) :=
        IsMulCommutative.of_comm hEAK.comm
      letI : Module (ZMod 2) (Additive (frattini K)) :=
        hEAK.zmodModule
      FactorCoordinateData fK.left_invariant
        fK.frattini_lt_left.le
        (hKinv.restrict.rangeRestrict c) eK nu)
    (dataCommonK :
      letI : IsMulCommutative (frattini K) :=
        IsMulCommutative.of_comm hEAK.comm
      letI : Module (ZMod 2) (Additive (frattini K)) :=
        hEAK.zmodModule
      FactorCoordinateData fK.right_invariant
        fK.frattini_lt_right.le
        (hKinv.restrict.rangeRestrict c) eK nu)
    :
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hEAJ.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hEAJ.zmodModule
    letI : IsMulCommutative (frattini K) :=
      IsMulCommutative.of_comm hEAK.comm
    letI : Module (ZMod 2) (Additive (frattini K)) :=
      hEAK.zmodModule
    ∀
    (_hCommonJ : fJ.right = W.subgroupOf J)
    (_hCommonK : fK.right = W.subgroupOf K)
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
    (_hsourceLeftJ :
      nu = dataLeftJ.lambda *
        dataLeftJ.theta dataLeftJ.lambda)
    (_hsourceCommonJ :
      nu = dataCommonJ.lambda *
        dataCommonJ.theta dataCommonJ.lambda)
    (_hsourceLeftK :
      nu = dataLeftK.lambda *
        dataLeftK.theta dataLeftK.lambda)
    (_hsourceCommonK :
      nu = dataCommonK.lambda *
        dataCommonK.theta dataCommonK.lambda)
    (_hnormLeftK :
      IsNormalizedFactorParameter n dataLeftK.theta)
    (_hnormCommonJ :
      IsNormalizedFactorParameter n dataCommonJ.theta)
    (_hnormCommonK :
      IsNormalizedFactorParameter n dataCommonK.theta)
    (_hthetaLeft : dataLeftJ.theta = dataLeftK.theta)
    (_hthetaCommon : dataCommonJ.theta = dataCommonK.theta)
    (_hunique :
      dataLeftJ.theta = 1 ∨
        dataLeftJ.theta ≠ dataCommonJ.theta)
    (_hrelJ : NormalizedFactorPairRelation n
      dataLeftJ.theta dataCommonJ.theta)
    (_hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1)),
    let leftJ := dataLeftJ.toInclusionData
      hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
    let commonJ := dataCommonJ.toInclusionData
      hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
    let leftK := dataLeftK.toInclusionData
      hEAK eK hK1K htermK hSqK hAgemoK hK0K
    let commonK := dataCommonK.toInclusionData
      hEAK eK hK1K htermK hSqK hAgemoK hK0K
    let M₁ := mixedTermBilinear leftJ commonJ
    let M₂ := mixedTermBilinear leftK commonK
    let iotaJ := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataCommonJ
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iotaK := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataCommonK
        hK1K htermK hSqK hAgemoK hK0K
    ∃ t a b : GaloisField 2 n,
      t ≠ 0 ∧
      (a ≠ 0 ∨ b ≠ 0) ∧
      (∀ beta, iotaJ beta = iotaK (t * beta)) ∧
      ∀ beta, M₁ a beta + M₂ b (t * beta) = 0 := by
  classical
  dsimp only
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
  intro hCommonJ hCommonK
    hK1J htermJ hSqJ hAgemoJ hK0J
    hK1K htermK hSqK hAgemoK hK0K
    hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
    hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
    hnormLeftK hnormCommonJ hnormCommonK
    hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  let leftJ := dataLeftJ.toInclusionData
    hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
  let commonJ := dataCommonJ.toInclusionData
    hEAJ eJ hK1J htermJ hSqJ hAgemoJ hK0J
  let leftK := dataLeftK.toInclusionData
    hEAK eK hK1K htermK hSqK hAgemoK hK0K
  let commonK := dataCommonK.toInclusionData
    hEAK eK hK1K htermK hSqK hAgemoK hK0K
  let M₁ := mixedTermBilinear leftJ commonJ
  let M₂ := mixedTermBilinear leftK commonK
  let iotaJ := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iotaK := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataCommonK
      hK1K htermK hSqK hAgemoK hK0K
  have hn0 : n ≠ 0 := by omega
  have hsourceLeftJ' :
      nu = dataLeftJ.lambda *
        dataLeftK.theta dataLeftJ.lambda := by
    simpa only [hthetaLeft] using hsourceLeftJ
  have hsourceCommonJ' :
      nu = dataCommonJ.lambda *
        dataCommonK.theta dataCommonJ.lambda := by
    simpa only [hthetaCommon] using hsourceCommonJ
  have hlambdaLeft : dataLeftJ.lambda = dataLeftK.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataLeftK.theta dataLeftJ.lambda dataLeftK.lambda nu
      hnormLeftK hnuPrimitive hsourceLeftJ' hsourceLeftK
  have hlambdaCommon :
      dataCommonJ.lambda = dataCommonK.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataCommonK.theta dataCommonJ.lambda dataCommonK.lambda nu
      hnormCommonK hnuPrimitive hsourceCommonJ' hsourceCommonK
  have hcommonPrimitive :
      IsPrimitiveRoot dataCommonJ.lambda (2 ^ n - 1) :=
    lambda_isPrimitiveRoot_of_normalized_twisted_norm
      hn0 dataCommonJ.theta dataCommonJ.lambda nu
      hnormCommonJ hnuPrimitive hsourceCommonJ
  obtain ⟨t, ht, halign⟩ :=
    exists_scalar_reparameterization_of_common_factor
      hP hJinv hKinv hWJ hWK hMapJ hMapK hn0
      hEAJ eJ hEAK eK c dataCommonJ dataCommonK
      hCommonJ hCommonK
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
      hlambdaCommon hcommonPrimitive
  have hequiv₁ : ∀ alpha beta,
      M₁ (dataLeftJ.lambda * alpha)
          (dataCommonJ.lambda * beta) =
        nu * M₁ alpha beta := by
    intro alpha beta
    exact mixedTermBilinear_lambda_equivariance
      hEAJ eJ dataLeftJ dataCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J hconjJ alpha beta
  have hequiv₂Raw : ∀ alpha beta,
      M₂ (dataLeftK.lambda * alpha)
          (dataCommonK.lambda * beta) =
        nu * M₂ alpha beta := by
    intro alpha beta
    exact mixedTermBilinear_lambda_equivariance
      hEAK eK dataLeftK dataCommonK
      hK1K htermK hSqK hAgemoK hK0K hconjK alpha beta
  let scale : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
    Algebra.lmul (ZMod 2) (GaloisField 2 n) t
  let M₂' := M₂.compl₂ scale
  have hequiv₂ : ∀ alpha beta,
      M₂' (dataLeftJ.lambda * alpha)
          (dataCommonJ.lambda * beta) =
        nu * M₂' alpha beta := by
    intro alpha beta
    change M₂ (dataLeftJ.lambda * alpha)
        (t * (dataCommonJ.lambda * beta)) =
      nu * M₂ alpha (t * beta)
    rw [hlambdaLeft, hlambdaCommon]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hequiv₂Raw alpha (t * beta)
  have hM₁ : ∃ alpha beta, M₁ alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero
      fJ leftJ commonJ hxiJ hinvPhiJ
  have hM₂Raw : ∃ alpha beta, M₂ alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero
      fK leftK commonK hxiK hinvPhiK
  have hM₂ : ∃ alpha beta, M₂' alpha beta ≠ 0 := by
    obtain ⟨alpha, beta, hne⟩ := hM₂Raw
    refine ⟨alpha, t⁻¹ * beta, ?_⟩
    change M₂ alpha (t * (t⁻¹ * beta)) ≠ 0
    have htInv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    simpa only [← mul_assoc, htInv, one_mul] using hne
  obtain ⟨a, b, hab, hcancel⟩ :=
    exists_nontrivial_pair_inputs_cancel_common_right_mixedTerms
      hn hnuPrimitive hsourceLeftJ hsourceCommonJ
      hunique hrelJ M₁ M₂' hequiv₁ hequiv₂ hM₁ hM₂
  refine ⟨t, a, b, ht, hab, halign, fun beta => ?_⟩
  exact hcancel beta

end

end OddOrder.Higman.Suzuki2Groups
