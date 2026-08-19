/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedGraphPreimage
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantGraphContradiction

/-!
# Higman's Lemma 13: the aligned graph branch is impossible

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The non-isomorphic common-factor branch supplies an aligned invariant graph
whose canonical Frattini preimage is a new type-A factor.  Its aligned ambient
bracket cancellation propagates across both field coordinates, so the new
factor commutes elementwise with the original common factor.  Their exact
Frattini intersection then contradicts the ambient involution condition.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance alignedGraphContradictionLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance alignedGraphContradictionLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance alignedGraphContradictionLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), aligned common-factor contradiction.**

The aligned graph construction, restricted-factor eigenvalue laws, and exact
quotient ranges force the canonical graph preimage to commute with the common
type-A factor.  This is incompatible with their exact Frattini intersection
in the exponent-two branch. -/
theorem false_of_alignedGraph_commonFactor_branch_exponent_two
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
    {X Z W J K : Subgroup P}
    (hWinv : IsAInvariant Y.subtype W)
    (hmodelW : IsXiLengthTwoTypeA.{uP, 0} W)
    (hinvPhi : involutions P ⊆ frattini P)
    (hPhiX : frattini P < X)
    (hPhiZ : frattini P < Z)
    (hPhiW : frattini P < W)
    (hXZ : X ⊓ Z = frattini P)
    (hXZ_W : (X ⊔ Z) ⊓ W = frattini P)
    (hJ : J = X ⊔ W)
    (hK : K = Z ⊔ W)
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
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
    (hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c)
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
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    let eJ :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMapJ).trans ePhi
    let eK :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMapK).trans ePhi
    ∀
    (dataLeftJ : FactorCoordinateData fJ.left_invariant
      fJ.frattini_lt_left.le
      (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataCommonJ : FactorCoordinateData fJ.right_invariant
      fJ.frattini_lt_right.le
      (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataLeftK : FactorCoordinateData fK.left_invariant
      fK.frattini_lt_left.le
      (hKinv.restrict.rangeRestrict c) eK nu)
    (dataCommonK : FactorCoordinateData fK.right_invariant
      fK.frattini_lt_right.le
      (hKinv.restrict.rangeRestrict c) eK nu)
    (_hLeftJ : fJ.left = X.subgroupOf J)
    (_hLeftK : fK.left = Z.subgroupOf K)
    (_hCommonJ : fJ.right = W.subgroupOf J)
    (_hCommonK : fK.right = W.subgroupOf K)
    (_hK1J : lowerCentralLayerKernel J 1 = ⊥)
    (_htermJ : lowerCentralTerm J 1 = frattini J)
    (_hSqJ : LowerCentralSquaresLieInSecond J)
    (_hAgemoJ : Agemo J 2 1 = frattini J)
    (_hK0J : lowerCentralLayerKernel J 0 =
      (frattini J).subgroupOf (lowerCentralTerm J 0))
    (_hK1K : lowerCentralLayerKernel K 1 = ⊥)
    (_htermK : lowerCentralTerm K 1 = frattini K)
    (_hSqK : LowerCentralSquaresLieInSecond K)
    (_hAgemoK : Agemo K 2 1 = frattini K)
    (_hK0K : lowerCentralLayerKernel K 0 =
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
    False := by
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
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  let eJ :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapJ).trans ePhi
  let eK :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapK).trans ePhi
  intro dataLeftJ dataCommonJ dataLeftK dataCommonK
    hLeftJ hLeftK hCommonJ hCommonK
    hK1J htermJ hSqJ hAgemoJ hK0J
    hK1K htermK hSqK hAgemoK hK0K
    hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
    hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
    hnormLeftK hnormCommonJ hnormCommonK
    hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  let iX := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataLeftJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iZ := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataLeftK
      hK1K htermK hSqK hAgemoK hK0K
  let iW := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iXq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iX
  let iZq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iZ
  obtain ⟨t, a, b, U, hUinv, ht, hab, halign, hbracket,
      _hgraph, hUnormal, hPhiU, hUW, hUWtop, hlenU,
      hmodelU, hUcanonical, hUmap⟩ :=
    exists_alignedGraph_canonicalTypeAPreimage_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hWinv hPhiX hPhiZ hPhiW hXZ hXZ_W hJ hK
      hJinv hKinv hMapJ hMapK hPhiEA hn ePhi
      hK1P htermP c hcgen fJ fK
      dataLeftJ dataCommonJ dataLeftK dataCommonK
      hLeftJ hLeftK hCommonJ hCommonK
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
      hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
      hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
      hnormLeftK hnormCommonJ hnormCommonK
      hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  let iU := commonEigenvalueGraphMap iX iZ a b
  have hn0 : n ≠ 0 := by omega
  have hnormLeftJ :
      IsNormalizedFactorParameter n dataLeftJ.theta := by
    rw [hthetaLeft]
    exact hnormLeftK
  have hleftPrimitive :
      IsPrimitiveRoot dataLeftJ.lambda (2 ^ n - 1) :=
    lambda_isPrimitiveRoot_of_normalized_twisted_norm
      hn0 dataLeftJ.theta dataLeftJ.lambda nu
      hnormLeftJ hnuPrimitive hsourceLeftJ
  have hrightPrimitive :
      IsPrimitiveRoot dataCommonJ.lambda (2 ^ n - 1) :=
    lambda_isPrimitiveRoot_of_normalized_twisted_norm
      hn0 dataCommonJ.theta dataCommonJ.lambda nu
      hnormCommonJ hnuPrimitive hsourceCommonJ
  have hNpos : 0 < 2 ^ n - 1 := by
    have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrightNe : dataCommonJ.lambda ≠ 0 :=
    hrightPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  have hsourceLeftJ' :
      nu = dataLeftJ.lambda *
        dataLeftK.theta dataLeftJ.lambda := by
    simpa only [hthetaLeft] using hsourceLeftJ
  have hlambdaLeft : dataLeftJ.lambda = dataLeftK.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataLeftK.theta dataLeftJ.lambda dataLeftK.lambda nu
      hnormLeftK hnuPrimitive hsourceLeftJ' hsourceLeftK
  have hEigX : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iX alpha) =
        iX (dataLeftJ.lambda * alpha) := by
    intro alpha
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        hJinv hEAJ eJ c dataLeftJ
        hK1J htermJ hSqJ hAgemoJ hK0J alpha
  have hEigZ : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iZ alpha) =
        iZ (dataLeftJ.lambda * alpha) := by
    intro alpha
    rw [hlambdaLeft]
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        hKinv hEAK eK c dataLeftK
        hK1K htermK hSqK hAgemoK hK0K alpha
  have hEigU : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iU alpha) =
        iU (dataLeftJ.lambda * alpha) := by
    intro alpha
    exact commonEigenvalueGraphMap_eigen
      (lowerCentralLayerRepresentation Y.subtype 0 c)
      iX iZ a b dataLeftJ.lambda hEigX hEigZ alpha
  have hEigW : ∀ beta,
      lowerCentralLayerRepresentation Y.subtype 0 c (iW beta) =
        iW (dataCommonJ.lambda * beta) := by
    intro beta
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        hJinv hEAJ eJ c dataCommonJ
        hK1J htermJ hSqJ hAgemoJ hK0J beta
  have hseed : ∀ beta,
      lowerCentralCommutatorBilinear P (iU 1) (iW beta) = 0 := by
    intro beta
    simpa only [iU, commonEigenvalueGraphMap_apply, mul_one] using
      hbracket beta
  have hcomp :
      (layerZeroToFrattiniQuotientLinear P hP).comp iU =
        commonEigenvalueGraphMap iXq iZq a b := by
    apply LinearMap.ext
    intro alpha
    change layerZeroToFrattiniQuotientLinear P hP
        (commonEigenvalueGraphMap iX iZ a b alpha) =
      commonEigenvalueGraphMap iXq iZq a b alpha
    rw [commonEigenvalueGraphMap_apply,
      commonEigenvalueGraphMap_apply, map_add]
    rfl
  have hUmap' :
      U.map (QuotientGroup.mk' (frattini P)) =
        elabSubmoduleSubgroupEquiv 2
          (LinearMap.range
            ((layerZeroToFrattiniQuotientLinear P hP).comp iU)) := by
    rw [hcomp]
    exact hUmap
  have hWJ : W ≤ J := by
    rw [hJ]
    exact le_sup_right
  have hWrange :
      LinearMap.range
          ((layerZeroToFrattiniQuotientLinear P hP).comp iW) =
        (elabSubmoduleSubgroupEquiv 2).symm
          (W.map (QuotientGroup.mk' (frattini P))) :=
    restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP hJinv hWJ hEAJ eJ c dataCommonJ hCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  have hcomm : ∀ u ∈ U, ∀ w ∈ W, Commute u w :=
    invariantGraphPreimage_commutes_of_primitive_eigen_seed
      hP hncomm hxi htwo hn0 c iU iW
      dataLeftJ.lambda dataCommonJ.lambda
      hleftPrimitive hrightNe hEigU hEigW hseed
      U W hUmap' hWrange
  exact false_of_typeA_factors_inf_eq_frattini_pairwise_commute
    hxi hUinv hWinv hUW hmodelU hmodelW hinvPhi htwo
    (fun u w => hcomm u u.property w w.property)

end

end OddOrder.Higman.Suzuki2Groups
