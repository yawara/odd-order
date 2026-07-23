/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAlignedAmbientBracketCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantGraphPreimage
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoQuotientFactorGeometry

/-!
# Higman Lemma 13: aligned graph factor and its canonical preimage

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Two pairwise joins `J = X ⊔ W` and `K = Z ⊔ W` supply left factor
coordinates on `X` and `Z` and two coordinates on their common factor `W`.
The mixed-term calculation aligns the two copies of `W` and produces a
nonzero coefficient pair `(a,b)` whose ambient bracket with the whole
`W`-family vanishes.

Passing the two left coordinates to `P / Φ(P)` gives disjoint quotient axes.
Their actual subgroup geometry supplies directness from the image of `W`,
while quotient eigenvalue coherence makes the graph with coefficients
`(a,b)` actor-invariant.  Its canonical Frattini preimage is therefore an
actual inclusive type-A factor.  This leaf retains both constructions with
the same coefficients.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance alignedGraphPreimageLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance alignedGraphPreimageLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance alignedGraphPreimageLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), aligned graph and canonical type-A
preimage.**

The ambient cancellation vector and the quotient graph use the same
nontrivial coefficients `a,b`.  The conclusion retains the scalar alignment
on the common factor, the seed ambient bracket vanishing, the explicit graph
formula, and the literal quotient pullback/image identities of its new
type-A factor.
-/
theorem exists_alignedGraph_canonicalTypeAPreimage_exponent_two
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
    (_hK1P : lowerCentralLayerKernel P 1 = ⊥)
    (_htermP : lowerCentralTerm P 1 = frattini P)
    {nu : GaloisField 2 n}
    (c : Y)
    (_hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c)
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
    let iZ := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataLeftK
        hK1K htermK hSqK hAgemoK hK0K
    let iW := restrictedFactorAmbientInclusion
      hJinv hEAJ eJ c dataCommonJ
        hK1J htermJ hSqJ hAgemoJ hK0J
    let iWK := restrictedFactorAmbientInclusion
      hKinv hEAK eK c dataCommonK
        hK1K htermK hSqK hAgemoK hK0K
    let iXq :=
      (layerZeroToFrattiniQuotientLinear P hP).comp iX
    let iZq :=
      (layerZeroToFrattiniQuotientLinear P hP).comp iZ
    ∃ (t a b : GaloisField 2 n)
        (U : Subgroup P)
        (hUinv : IsAInvariant Y.subtype U),
      t ≠ 0 ∧
      (a ≠ 0 ∨ b ≠ 0) ∧
      (∀ beta, iW beta = iWK (t * beta)) ∧
      (∀ beta,
        lowerCentralCommutatorBilinear P
          (iX a + iZ b) (iW beta) = 0) ∧
      (let d := commonEigenvalueGraphMap iXq iZq a b
       let D :=
         elabSubmoduleSubgroupEquiv
           (K := P ⧸ frattini P) 2 (LinearMap.range d)
       (∀ alpha,
          d alpha =
            layerZeroToFrattiniQuotientLinear P hP
              (iX (a * alpha) + iZ (b * alpha))) ∧
       U.Normal ∧
       frattini P < U ∧
       U ⊓ W = frattini P ∧
       U ⊔ W < ⊤ ∧
       HasXiLengthTwo hUinv.restrict.range.subtype ∧
       IsXiLengthTwoTypeA.{uP, 0} U ∧
       U = D.comap (QuotientGroup.mk' (frattini P)) ∧
       U.map (QuotientGroup.mk' (frattini P)) = D) := by
  classical
  dsimp only
  let hEAJ : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapJ).symm hPhiEA
  let hEAK : IsElementaryAbelian 2 (frattini K) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapK).symm hPhiEA
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  letI : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hEAJ.comm
  letI : CommGroup (frattini J) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini J)) :=
    hEAJ.zmodModule
  letI : IsMulCommutative (frattini K) :=
    IsMulCommutative.of_comm hEAK.comm
  letI : CommGroup (frattini K) := inferInstance
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
  intro dataLeftJ dataCommonJ dataLeftK dataCommonK
    hLeftJ hLeftK hCommonJ hCommonK
    hK1J htermJ hSqJ hAgemoJ hK0J
    hK1K htermK hSqK hAgemoK hK0K
    hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
    hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
    hnormLeftK hnormCommonJ hnormCommonK
    hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  have hXJ : X ≤ J := by
    rw [hJ]
    exact le_sup_left
  have hWJ : W ≤ J := by
    rw [hJ]
    exact le_sup_right
  have hZK : Z ≤ K := by
    rw [hK]
    exact le_sup_left
  have hWK : W ≤ K := by
    rw [hK]
    exact le_sup_right
  let iX := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataLeftJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iZ := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataLeftK
      hK1K htermK hSqK hAgemoK hK0K
  let iW := restrictedFactorAmbientInclusion
    hJinv hEAJ eJ c dataCommonJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iWK := restrictedFactorAmbientInclusion
    hKinv hEAK eK c dataCommonK
      hK1K htermK hSqK hAgemoK hK0K
  let iXq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iX
  let iZq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iZ
  obtain ⟨t, a, b, ht, hab, halign, hbracket⟩ :=
    exists_aligned_ambientBracket_family_eq_zero
      hP hJinv hKinv hWJ hWK hMapJ hMapK hPhiEA hn ePhi
      _hK1P _htermP c fJ fK
      dataLeftJ dataCommonJ dataLeftK dataCommonK
      hCommonJ hCommonK
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
      hxiJ hxiK hinvPhiJ hinvPhiK hconjJ hconjK
      hsourceLeftJ hsourceCommonJ hsourceLeftK hsourceCommonK
      hnormLeftK hnormCommonJ hnormCommonK
      hthetaLeft hthetaCommon hunique hrelJ hnuPrimitive
  have hiX : Function.Injective iX :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP hJinv hMapJ hEAJ eJ c dataLeftJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  have hiZ : Function.Injective iZ :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP hKinv hMapK hEAK eK c dataLeftK
      hK1K htermK hSqK hAgemoK hK0K
  have hqinj :
      Function.Injective (layerZeroToFrattiniQuotientLinear P hP) :=
    layerZeroToFrattiniQuotientLinear_injective P hP
  have hiXq : Function.Injective iXq := by
    intro alpha beta habq
    apply hiX
    apply hqinj
    exact habq
  have hiZq : Function.Injective iZq := by
    intro alpha beta habq
    apply hiZ
    apply hqinj
    exact habq
  have hRangeX :
      LinearMap.range iXq =
        (elabSubmoduleSubgroupEquiv
          (K := P ⧸ frattini P) 2).symm
            (X.map (QuotientGroup.mk' (frattini P))) := by
    exact restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP hJinv hXJ hEAJ eJ c dataLeftJ hLeftJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  have hRangeZ :
      LinearMap.range iZq =
        (elabSubmoduleSubgroupEquiv
          (K := P ⧸ frattini P) 2).symm
            (Z.map (QuotientGroup.mk' (frattini P))) := by
    exact restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP hKinv hZK hEAK eK c dataLeftK hLeftK
      hK1K htermK hSqK hAgemoK hK0K
  obtain ⟨hAxesActual, hAxesWActual⟩ :=
    frattiniQuotient_factorSubmodules_direct_geometry
      hP X Z W hPhiX.le hPhiZ.le hPhiW.le hXZ hXZ_W
  have hAxes :
      LinearMap.range iXq ⊓ LinearMap.range iZq = ⊥ := by
    rw [hRangeX, hRangeZ]
    exact hAxesActual
  have hAxesW :
      (LinearMap.range iXq ⊔ LinearMap.range iZq) ⊓
          (elabSubmoduleSubgroupEquiv
            (K := P ⧸ frattini P) 2).symm
              (W.map (QuotientGroup.mk' (frattini P))) =
        ⊥ := by
    rw [hRangeX, hRangeZ]
    exact hAxesWActual
  have hn0 : n ≠ 0 := by omega
  have hsourceLeftJ' :
      nu = dataLeftJ.lambda *
        dataLeftK.theta dataLeftJ.lambda := by
    simpa only [hthetaLeft] using hsourceLeftJ
  have hlambda :
      dataLeftJ.lambda = dataLeftK.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 dataLeftK.theta dataLeftJ.lambda dataLeftK.lambda nu
      hnormLeftK hnuPrimitive hsourceLeftJ' hsourceLeftK
  have hNpos : 0 < 2 ^ n - 1 := by
    have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnuNe : nu ≠ 0 :=
    hnuPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  have hlambdaNe : dataLeftJ.lambda ≠ 0 := by
    intro hzero
    apply hnuNe
    rw [hsourceLeftJ, hzero, zero_mul]
  have hEigX : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          c (iXq alpha) =
        iXq (dataLeftJ.lambda * alpha) := by
    intro alpha
    exact
      restrictedFactorAmbientInclusion_frattiniQuotient_representation
        hP hJinv hEAJ eJ c dataLeftJ
        hK1J htermJ hSqJ hAgemoJ hK0J alpha
  have hEigZ : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          c (iZq alpha) =
        iZq (dataLeftJ.lambda * alpha) := by
    intro alpha
    rw [hlambda]
    exact
      restrictedFactorAmbientInclusion_frattiniQuotient_representation
        hP hKinv hEAK eK c dataLeftK
        hK1K htermK hSqK hAgemoK hK0K alpha
  obtain ⟨U, hUinv, hUnormal, hPhiU, hUW, hUWtop,
      hlenU, htypeAU, hUcanonical, hUmap⟩ :=
    exists_canonical_typeA_preimage_of_commonEigenvalueGraph_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo hWinv hPhiW
      n iXq iZq hiXq hiZq hAxes a b hab hAxesW
      c _hcgen dataLeftJ.lambda hlambdaNe hEigX hEigZ
  have hd (alpha : GaloisField 2 n) :
      commonEigenvalueGraphMap iXq iZq a b alpha =
        layerZeroToFrattiniQuotientLinear P hP
          (iX (a * alpha) + iZ (b * alpha)) := by
    rw [commonEigenvalueGraphMap_apply, map_add]
    rfl
  refine ⟨t, a, b, U, hUinv, ht, hab, halign, hbracket, ?_⟩
  exact ⟨hd, hUnormal, hPhiU, hUW, hUWtop,
    hlenU, htypeAU, hUcanonical, hUmap⟩

end

end OddOrder.Higman.Suzuki2Groups
