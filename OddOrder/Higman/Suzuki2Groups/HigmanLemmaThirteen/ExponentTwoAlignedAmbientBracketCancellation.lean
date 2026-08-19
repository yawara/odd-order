/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedMixedTermCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseMixedTermAmbientBridge

/-!
# Higman Lemma 13: ambient bracket cancellation after factor alignment

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The mixed-term cancellation for two pairwise joins is initially an equality
in their common finite-field centre coordinate.  The pairwise ambient bridge
identifies each mixed term with the genuine lower-central commutator after
the two factor coordinates are included in the ambient zeroth layer.

After aligning the two copies of the common right factor, bilinearity turns
the sum of the two mixed terms into the ambient bracket of the sum of the
left vectors.  Injectivity of the ambient centre coordinate then proves that
this bracket itself vanishes on the whole common-factor family.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance alignedAmbientBracketLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance alignedAmbientBracketLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance alignedAmbientBracketLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The pairwise mixed term is the ambient lower-central bracket coordinate
after both factor inclusions are transported from `L₀(J)` to `L₀(P)`.

This is the linear-layer form of
`exists_pairwiseJoinRepresentatives_mixedTerm_eq_ambientFrattiniCommutator`.
-/
theorem pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
    {P : Type uP} [Group P] [Finite P]
    {J : Subgroup P}
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P)
    {n : Nat}
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (hK1P : lowerCentralLayerKernel P 1 = ⊥)
    (htermP : lowerCentralTerm P 1 = frattini P) :
    let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hJoinEA.zmodModule
    ∀ (hK1J : lowerCentralLayerKernel J 1 = ⊥)
      (htermJ : lowerCentralTerm J 1 = frattini J)
      (hSqJ : LowerCentralSquaresLieInSecond J)
      (hK0J : lowerCentralLayerKernel J 0 =
        (frattini J).subgroupOf (lowerCentralTerm J 0))
      {Sl Sr : Subgroup J}
      (L : FactorInclusionData Sl hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (R : FactorInclusionData Sr hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (alpha beta : GaloisField 2 n),
      mixedTermBilinear L R alpha beta =
        ambientCenterCoordinate hPhiEA hK1P htermP ePhi
          (lowerCentralCommutatorBilinear P
            (subgroupLowerCentralLayerZeroLinear J (L.incl alpha))
            (subgroupLowerCentralLayerZeroLinear J (R.incl beta))) := by
  classical
  dsimp only
  let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hJoinEA.comm
  let : CommGroup (frattini J) := inferInstance
  let : Module (ZMod 2) (Additive (frattini J)) :=
    hJoinEA.zmodModule
  intro hK1J htermJ hSqJ hK0J Sl Sr L R alpha beta
  obtain ⟨x, y, _, _, hL, hR, hMixed⟩ :=
    exists_pairwiseJoinRepresentatives_mixedTerm_eq_ambientFrattiniCommutator
      hPhiEA hMap ePhi hK1J htermJ hSqJ hK0J
        L R alpha beta
  rw [hL, hR]
  unfold layerZeroClass
  rw [subgroupLowerCentralLayerZeroLinear_mk,
    subgroupLowerCentralLayerZeroLinear_mk,
    lowerCentralCommutatorBilinear_mk, hMixed]
  change ePhi _ = ePhi _
  apply congrArg ePhi
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- **Higman Lemma 13 (p. 93), ambient bracket-family cancellation.**

Let `X` and `Y` be the left factors of two pairwise joins and let `W` be
their common right factor.  Outside the all-isomorphic parameter case there
are nontrivial left coordinates `a,b`.  After one nonzero scalar
reparameterization aligns the two copies of `W` in `L₀(P)`, the actual
ambient bracket of `iX a + iY b` with every vector in the common `W` family
vanishes.
-/
theorem exists_aligned_ambientBracket_family_eq_zero
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
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    {n : Nat}
    (hn : 2 ≤ n)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (_hK1P : lowerCentralLayerKernel P 1 = ⊥)
    (_htermP : lowerCentralTerm P 1 = frattini P)
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
    let iX := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataLeftJ
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iY := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataLeftK
        hK1K htermK hSqK hAgemoK hK0K
    let iW := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataCommonJ
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iWK := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataCommonK
        hK1K htermK hSqK hAgemoK hK0K
    ∃ t a b : GaloisField 2 n,
      t ≠ 0 ∧
      (a ≠ 0 ∨ b ≠ 0) ∧
      (∀ beta, iW beta = iWK (t * beta)) ∧
      ∀ beta,
        lowerCentralCommutatorBilinear P
          (iX a + iY b) (iW beta) = 0 := by
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
  intro dataLeftJ dataCommonJ dataLeftK dataCommonK
    hCommonJ hCommonK
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
  let iX := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataLeftJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iY := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataLeftK
      hK1K htermK hSqK hAgemoK hK0K
  let iW := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iWK := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataCommonK
      hK1K htermK hSqK hAgemoK hK0K
  obtain ⟨t, a, b, ht, hab, halign, hcancel⟩ :=
    exists_aligned_common_factor_and_cancelled_pairwise_mixedTerms
      hP hJinv hKinv hWJ hWK hMapJ hMapK hn
      hEAJ eJ hEAK eK c fJ fK
      dataLeftJ dataCommonJ dataLeftK dataCommonK
      hCommonJ hCommonK
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
      hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
      hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
      hnormLeftK hnormCommonJ hnormCommonK
      hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  have hbridgeJ (alpha beta : GaloisField 2 n) :
      M₁ alpha beta =
        ambientCenterCoordinate hPhiEA _hK1P _htermP ePhi
          (lowerCentralCommutatorBilinear P
            (iX alpha) (iW beta)) := by
    exact pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
      hPhiEA hMapJ ePhi _hK1P _htermP
      hK1J htermJ hSqJ hK0J leftJ commonJ alpha beta
  have hbridgeK (alpha beta : GaloisField 2 n) :
      M₂ alpha beta =
        ambientCenterCoordinate hPhiEA _hK1P _htermP ePhi
          (lowerCentralCommutatorBilinear P
            (iY alpha) (iWK beta)) := by
    exact pairwiseJoinMixedTerm_eq_ambientBracketCoordinate
      hPhiEA hMapK ePhi _hK1P _htermP
      hK1K htermK hSqK hK0K leftK commonK alpha beta
  refine ⟨t, a, b, ht, hab, halign, fun beta => ?_⟩
  apply (ambientCenterCoordinate
    hPhiEA _hK1P _htermP ePhi).injective
  simp only [map_zero, map_add, LinearMap.add_apply]
  rw [← hbridgeJ a beta]
  have hsecond :
      ambientCenterCoordinate hPhiEA _hK1P _htermP ePhi
          (lowerCentralCommutatorBilinear P
            (iY b) (iW beta)) =
        M₂ b (t * beta) := by
    rw [halign beta]
    exact (hbridgeK b (t * beta)).symm
  rw [hsecond]
  exact hcancel beta

end

end OddOrder.Higman.Suzuki2Groups
