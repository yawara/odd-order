/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllIsomorphicAmbientCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAmbientBracketFaithfulness
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoQuotientFactorGeometry
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoThreeParameterBranching
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoThreeTermGraphPreimage

/-!
# Higman's Lemma 13: all-isomorphic graph and canonical preimage

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the all-isomorphic parameter branch, the actual `X`, `Z`, and `T`
factor coordinates produce a nontrivial three-term ambient cancellation.
Passing the same coordinates to the Frattini quotient gives an invariant
three-term graph.  This file constructs its canonical type-A preimage and
retains the primitive eigenfamily and seed cancellation needed to prove
that the new factor commutes with `T`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance allIsomorphicGraphPreimageLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance allIsomorphicGraphPreimageLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance
    allIsomorphicGraphPreimageLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), all-isomorphic graph-preimage assembly.**

For the actual joins `X ⊔ T` and `Z ⊔ T`, an all-equal nontrivial
parameter package supplies a genuine ambient cancellation vector
`iX(a) + iZ(b) + iT(cT)`.  The corresponding nested quotient graph has a
normal invariant canonical preimage `U`.  Besides its type-A and
intersection geometry, the conclusion retains the primitive actor
eigenfamily, quotient-range identities, and seed bracket required by the
downstream commutativity theorem.

The pairwise lower-central facts occur as existential outputs rather than
assumptions: they are reconstructed from the exponent-two length-four
hypotheses by the honest pairwise-join infrastructure. -/
theorem exists_allIsomorphicGraph_canonicalTypeAPreimage_exponent_two
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
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    ∀ {n : Nat},
    2 ≤ n →
    ∀ (g : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      (∀ y : Y, y ∈ Subgroup.zpowers g) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              Y.subtype :
                IsAInvariant Y.subtype (frattini P)).restrict g) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∀
      (xt : NormalizedActualFactorPairCoordinates
        hXinv hTinv hPhiEA hMapXT g ePhi nu)
      (zt : NormalizedActualFactorPairCoordinates
        hZinv hTinv hPhiEA hMapZT g ePhi nu),
      xt.right.theta = zt.right.theta →
      AllEqualNontrivialParameterData
        xt.left.theta zt.left.theta xt.right.theta →
      ∃
      (hK1XT : lowerCentralLayerKernel ↥(X ⊔ T) 1 = ⊥)
      (htermXT : lowerCentralTerm ↥(X ⊔ T) 1 =
        frattini ↥(X ⊔ T))
      (hSqXT : LowerCentralSquaresLieInSecond ↥(X ⊔ T))
      (hAgemoXT : Agemo ↥(X ⊔ T) 2 1 = frattini ↥(X ⊔ T))
      (hK0XT : lowerCentralLayerKernel ↥(X ⊔ T) 0 =
        (frattini ↥(X ⊔ T)).subgroupOf
          (lowerCentralTerm ↥(X ⊔ T) 0))
      (hK1ZT : lowerCentralLayerKernel ↥(Z ⊔ T) 1 = ⊥)
      (htermZT : lowerCentralTerm ↥(Z ⊔ T) 1 =
        frattini ↥(Z ⊔ T))
      (hSqZT : LowerCentralSquaresLieInSecond ↥(Z ⊔ T))
      (hAgemoZT : Agemo ↥(Z ⊔ T) 2 1 = frattini ↥(Z ⊔ T))
      (hK0ZT : lowerCentralLayerKernel ↥(Z ⊔ T) 0 =
        (frattini ↥(Z ⊔ T)).subgroupOf
          (lowerCentralTerm ↥(Z ⊔ T) 0))
      (t a b cT : GaloisField 2 n)
      (U : Subgroup P)
      (hUinv : IsAInvariant Y.subtype U),
      let eXT :=
        (pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMapXT).trans ePhi
      let eZT :=
        (pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMapZT).trans ePhi
      let iX := restrictedFactorAmbientInclusion
        (hXinv.sup hTinv) hXTEA eXT g xt.left
          hK1XT htermXT hSqXT hAgemoXT hK0XT
      let iZ := restrictedFactorAmbientInclusion
        (hZinv.sup hTinv) hZTEA eZT g zt.left
          hK1ZT htermZT hSqZT hAgemoZT hK0ZT
      let iT := restrictedFactorAmbientInclusion
        (hXinv.sup hTinv) hXTEA eXT g xt.right
          hK1XT htermXT hSqXT hAgemoXT hK0XT
      let iT' := restrictedFactorAmbientInclusion
        (hZinv.sup hTinv) hZTEA eZT g zt.right
          hK1ZT htermZT hSqZT hAgemoZT hK0ZT
      let iXq :=
        (layerZeroToFrattiniQuotientLinear P hP).comp iX
      let iZq :=
        (layerZeroToFrattiniQuotientLinear P hP).comp iZ
      let iTq :=
        (layerZeroToFrattiniQuotientLinear P hP).comp iT
      let gXZq := commonEigenvalueGraphMap iXq iZq a b
      let d := commonEigenvalueGraphMap gXZq iTq 1 cT
      let D :=
        elabSubmoduleSubgroupEquiv 2 (LinearMap.range d)
      let gXZ := commonEigenvalueGraphMap iX iZ a b
      let iU := commonEigenvalueGraphMap gXZ iT 1 cT
      t ≠ 0 ∧
        (a ≠ 0 ∨ b ≠ 0) ∧
        (∀ beta, iT beta = iT' (t * beta)) ∧
        (∀ beta,
          lowerCentralCommutatorBilinear P
            (iU 1) (iT beta) = 0) ∧
        (layerZeroToFrattiniQuotientLinear P hP).comp iU = d ∧
        IsPrimitiveRoot xt.right.lambda (2 ^ n - 1) ∧
        (∀ alpha,
          lowerCentralLayerRepresentation Y.subtype 0 g (iU alpha) =
            iU (xt.right.lambda * alpha)) ∧
        (∀ beta,
          lowerCentralLayerRepresentation Y.subtype 0 g (iT beta) =
            iT (xt.right.lambda * beta)) ∧
        U.map (QuotientGroup.mk' (frattini P)) =
          elabSubmoduleSubgroupEquiv 2
            (LinearMap.range
              ((layerZeroToFrattiniQuotientLinear P hP).comp iU)) ∧
        LinearMap.range
            ((layerZeroToFrattiniQuotientLinear P hP).comp iT) =
          (elabSubmoduleSubgroupEquiv 2).symm
            (T.map (QuotientGroup.mk' (frattini P))) ∧
        U.Normal ∧
        frattini P < U ∧
        U ⊓ T = frattini P ∧
        U ⊔ T < ⊤ ∧
        HasXiLengthTwo hUinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} U ∧
        U = D.comap (QuotientGroup.mk' (frattini P)) ∧
        U.map (QuotientGroup.mk' (frattini P)) = D := by
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
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let : IsMulCommutative (frattini ↥(X ⊔ T)) :=
    IsMulCommutative.of_comm hXTEA.comm
  let : CommGroup (frattini ↥(X ⊔ T)) := inferInstance
  let : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
    hXTEA.zmodModule
  let : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
    IsMulCommutative.of_comm hZTEA.comm
  let : CommGroup (frattini ↥(Z ⊔ T)) := inferInstance
  let : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
    hZTEA.zmodModule
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro n hn g ePhi nu hggen hnuPrimitive hconj xt zt
    hthetaTcopy hAll
  obtain ⟨⟨joinXT, hJoinXT, _hInvXT, _hMapXT',
      _factorsXT, _hLeftXT, _hRightXT,
      hK1XT, htermXT, hSqXT, hAgemoXT, hK0XT,
      hxiXT, hinvPhiXT, hconjXT⟩⟩ :=
    exists_pairwiseJoinLowerCentralData_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hTinv hPhiX hPhiT hXT hXTtop dataX dataT
      g ePhi nu hconj
  subst joinXT
  obtain ⟨⟨joinZT, hJoinZT, _hInvZT, _hMapZT',
      _factorsZT, _hLeftZT, _hRightZT,
      hK1ZT, htermZT, hSqZT, hAgemoZT, hK0ZT,
      hxiZT, hinvPhiZT, hconjZT⟩⟩ :=
    exists_pairwiseJoinLowerCentralData_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hZinv hTinv hPhiZ hPhiT hZT hZTtop dataZ dataT
      g ePhi nu hconj
  subst joinZT
  have hthetaX :
      xt.left.theta = xt.right.theta :=
    hAll.x_eq_z.trans hAll.z_eq_t
  have hthetaZ :
      zt.left.theta = xt.right.theta :=
    hAll.z_eq_t
  have hthetaTK :
      zt.right.theta = xt.right.theta :=
    hthetaTcopy.symm
  have hthetaNe : xt.right.theta ≠ 1 := by
    intro hOne
    exact hAll.ne_one (hthetaX.trans hOne)
  have hK1P : lowerCentralLayerKernel P 1 = ⊥ :=
    lowerCentralLayerKernel_one_eq_bot_of_exponent_two
      hP hncomm hxi htwo
  have htermP : lowerCentralTerm P 1 = frattini P :=
    lowerCentralTerm_one_eq_frattini_of_exponent_two
      hP hncomm hxi htwo
  obtain ⟨t, a, b, cT, ht, hab, halign, hbracket⟩ :=
    exists_allIsomorphic_aligned_ambientBracket_family_eq_zero
      (T := T) (J := X ⊔ T) (K := Z ⊔ T)
      hP (hXinv.sup hTinv) (hZinv.sup hTinv)
      le_sup_right le_sup_right hMapXT hMapZT hPhiEA hn ePhi
      hK1P htermP g xt.factors zt.factors
      xt.left xt.right zt.left zt.right
      xt.right_eq zt.right_eq
      hK1XT htermXT hSqXT hAgemoXT hK0XT
      hK1ZT htermZT hSqZT hAgemoZT hK0ZT
      hxiXT hxiZT hinvPhiXT hinvPhiZT hconjXT hconjZT
      xt.left_source xt.right_source zt.left_source zt.right_source
      xt.right_normalized hthetaX hthetaZ hthetaTK hthetaNe
      hnuPrimitive
  let eXT :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapXT).trans ePhi
  let eZT :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMapZT).trans ePhi
  let iX := restrictedFactorAmbientInclusion
    (hXinv.sup hTinv) hXTEA eXT g xt.left
      hK1XT htermXT hSqXT hAgemoXT hK0XT
  let iZ := restrictedFactorAmbientInclusion
    (hZinv.sup hTinv) hZTEA eZT g zt.left
      hK1ZT htermZT hSqZT hAgemoZT hK0ZT
  let iT := restrictedFactorAmbientInclusion
    (hXinv.sup hTinv) hXTEA eXT g xt.right
      hK1XT htermXT hSqXT hAgemoXT hK0XT
  let iT' := restrictedFactorAmbientInclusion
    (hZinv.sup hTinv) hZTEA eZT g zt.right
      hK1ZT htermZT hSqZT hAgemoZT hK0ZT
  let iXq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iX
  let iZq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iZ
  let iTq :=
    (layerZeroToFrattiniQuotientLinear P hP).comp iT
  have hiX : Function.Injective iX :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP (hXinv.sup hTinv) hMapXT hXTEA eXT g xt.left
      hK1XT htermXT hSqXT hAgemoXT hK0XT
  have hiZ : Function.Injective iZ :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP (hZinv.sup hTinv) hMapZT hZTEA eZT g zt.left
      hK1ZT htermZT hSqZT hAgemoZT hK0ZT
  have hiT : Function.Injective iT :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP (hXinv.sup hTinv) hMapXT hXTEA eXT g xt.right
      hK1XT htermXT hSqXT hAgemoXT hK0XT
  have hqinj :
      Function.Injective (layerZeroToFrattiniQuotientLinear P hP) :=
    layerZeroToFrattiniQuotientLinear_injective P hP
  have hiXq : Function.Injective iXq := hqinj.comp hiX
  have hiZq : Function.Injective iZq := hqinj.comp hiZ
  have hiTq : Function.Injective iTq := hqinj.comp hiT
  have hRangeX :
      LinearMap.range iXq =
        (elabSubmoduleSubgroupEquiv
          (K := P ⧸ frattini P) 2).symm
            (X.map (QuotientGroup.mk' (frattini P))) :=
    restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP (hXinv.sup hTinv) le_sup_left hXTEA eXT g xt.left
      xt.left_eq hK1XT htermXT hSqXT hAgemoXT hK0XT
  have hRangeZ :
      LinearMap.range iZq =
        (elabSubmoduleSubgroupEquiv
          (K := P ⧸ frattini P) 2).symm
            (Z.map (QuotientGroup.mk' (frattini P))) :=
    restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP (hZinv.sup hTinv) le_sup_left hZTEA eZT g zt.left
      zt.left_eq hK1ZT htermZT hSqZT hAgemoZT hK0ZT
  have hRangeT :
      LinearMap.range iTq =
        (elabSubmoduleSubgroupEquiv
          (K := P ⧸ frattini P) 2).symm
            (T.map (QuotientGroup.mk' (frattini P))) :=
    restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
      hP (hXinv.sup hTinv) le_sup_right hXTEA eXT g xt.right
      xt.right_eq hK1XT htermXT hSqXT hAgemoXT hK0XT
  obtain ⟨hAxesActual, hAxesTActual⟩ :=
    frattiniQuotient_factorSubmodules_direct_geometry
      hP X Z T hPhiX.le hPhiZ.le hPhiT.le hXZ hXZ_T
  have hAxes :
      LinearMap.range iXq ⊓ LinearMap.range iZq = ⊥ := by
    rw [hRangeX, hRangeZ]
    exact hAxesActual
  have hAxesT :
      (LinearMap.range iXq ⊔ LinearMap.range iZq) ⊓
          LinearMap.range iTq =
        ⊥ := by
    rw [hRangeX, hRangeZ, hRangeT]
    exact hAxesTActual
  have hn0 : n ≠ 0 := by omega
  have hsourceX' :
      nu = xt.left.lambda *
        xt.right.theta xt.left.lambda := by
    simpa only [hthetaX] using xt.left_source
  have hsourceZ' :
      nu = zt.left.lambda *
        xt.right.theta zt.left.lambda := by
    simpa only [hthetaZ] using zt.left_source
  have hlambdaX :
      xt.left.lambda = xt.right.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 xt.right.theta xt.left.lambda xt.right.lambda nu
      xt.right_normalized hnuPrimitive hsourceX' xt.right_source
  have hlambdaZ :
      zt.left.lambda = xt.right.lambda :=
    lambda_eq_of_common_primitive_twisted_norm_of_normalized
      hn0 xt.right.theta zt.left.lambda xt.right.lambda nu
      xt.right_normalized hnuPrimitive hsourceZ' xt.right_source
  have hlambdaPrimitive :
      IsPrimitiveRoot xt.right.lambda (2 ^ n - 1) :=
    lambda_isPrimitiveRoot_of_normalized_twisted_norm
      hn0 xt.right.theta xt.right.lambda nu
      xt.right_normalized hnuPrimitive xt.right_source
  have hNpos : 0 < 2 ^ n - 1 := by
    have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlambdaNe : xt.right.lambda ≠ 0 :=
    hlambdaPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  have hEigXq : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          g (iXq alpha) =
        iXq (xt.right.lambda * alpha) := by
    intro alpha
    rw [← hlambdaX]
    exact
      restrictedFactorAmbientInclusion_frattiniQuotient_representation
        hP (hXinv.sup hTinv) hXTEA eXT g xt.left
        hK1XT htermXT hSqXT hAgemoXT hK0XT alpha
  have hEigZq : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          g (iZq alpha) =
        iZq (xt.right.lambda * alpha) := by
    intro alpha
    rw [← hlambdaZ]
    exact
      restrictedFactorAmbientInclusion_frattiniQuotient_representation
        hP (hZinv.sup hTinv) hZTEA eZT g zt.left
        hK1ZT htermZT hSqZT hAgemoZT hK0ZT alpha
  have hEigTq : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          g (iTq alpha) =
        iTq (xt.right.lambda * alpha) := by
    intro alpha
    exact
      restrictedFactorAmbientInclusion_frattiniQuotient_representation
        hP (hXinv.sup hTinv) hXTEA eXT g xt.right
        hK1XT htermXT hSqXT hAgemoXT hK0XT alpha
  let gXZq := commonEigenvalueGraphMap iXq iZq a b
  let d := commonEigenvalueGraphMap gXZq iTq 1 cT
  let D :=
    elabSubmoduleSubgroupEquiv 2 (LinearMap.range d)
  obtain ⟨U, hUinv, hUnormal, hPhiU, hUT, hUTtop,
      hlenU, htypeAU, hUcanonical, hUmap⟩ :=
    exists_canonical_typeA_preimage_of_threeTermGraph_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo hTinv hPhiT
      n iXq iZq iTq hiXq hiZq hiTq hAxes hAxesT hRangeT
      a b cT hab g hggen xt.right.lambda hlambdaNe
      hEigXq hEigZq hEigTq
  have hEigX : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 g (iX alpha) =
        iX (xt.right.lambda * alpha) := by
    intro alpha
    rw [← hlambdaX]
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        (hXinv.sup hTinv) hXTEA eXT g xt.left
        hK1XT htermXT hSqXT hAgemoXT hK0XT alpha
  have hEigZ : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 g (iZ alpha) =
        iZ (xt.right.lambda * alpha) := by
    intro alpha
    rw [← hlambdaZ]
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        (hZinv.sup hTinv) hZTEA eZT g zt.left
        hK1ZT htermZT hSqZT hAgemoZT hK0ZT alpha
  have hEigT : ∀ beta,
      lowerCentralLayerRepresentation Y.subtype 0 g (iT beta) =
        iT (xt.right.lambda * beta) := by
    intro beta
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        (hXinv.sup hTinv) hXTEA eXT g xt.right
        hK1XT htermXT hSqXT hAgemoXT hK0XT beta
  let gXZ := commonEigenvalueGraphMap iX iZ a b
  let iU := commonEigenvalueGraphMap gXZ iT 1 cT
  have hEigGXZ : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 g (gXZ alpha) =
        gXZ (xt.right.lambda * alpha) := by
    intro alpha
    exact commonEigenvalueGraphMap_eigen
      (lowerCentralLayerRepresentation Y.subtype 0 g)
      iX iZ a b xt.right.lambda hEigX hEigZ alpha
  have hEigU : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 g (iU alpha) =
        iU (xt.right.lambda * alpha) := by
    intro alpha
    exact commonEigenvalueGraphMap_eigen
      (lowerCentralLayerRepresentation Y.subtype 0 g)
      gXZ iT 1 cT xt.right.lambda hEigGXZ hEigT alpha
  have hseed : ∀ beta,
      lowerCentralCommutatorBilinear P (iU 1) (iT beta) = 0 := by
    intro beta
    simpa only [iU, gXZ, commonEigenvalueGraphMap_apply,
      one_mul, mul_one] using hbracket beta
  have hcomp :
      (layerZeroToFrattiniQuotientLinear P hP).comp iU = d := by
    ext alpha
    simp only [iU, gXZ, d, gXZq,
      commonEigenvalueGraphMap_apply, one_mul,
      LinearMap.comp_apply, map_add, iXq, iZq, iTq]
  have hUmapRange :
      U.map (QuotientGroup.mk' (frattini P)) =
        elabSubmoduleSubgroupEquiv 2
          (LinearMap.range
            ((layerZeroToFrattiniQuotientLinear P hP).comp iU)) := by
    rw [hcomp]
    simpa [D] using hUmap
  refine
    ⟨hK1XT, htermXT, hSqXT, hAgemoXT, hK0XT,
      hK1ZT, htermZT, hSqZT, hAgemoZT, hK0ZT,
      t, a, b, cT, U, hUinv, ?_⟩
  exact
    ⟨ht, hab, halign, hseed, hcomp, hlambdaPrimitive,
      hEigU, hEigT, hUmapRange, hRangeT, hUnormal, hPhiU,
      hUT, hUTtop, hlenU, htypeAU, hUcanonical, hUmap⟩

end

end OddOrder.Higman.Suzuki2Groups
