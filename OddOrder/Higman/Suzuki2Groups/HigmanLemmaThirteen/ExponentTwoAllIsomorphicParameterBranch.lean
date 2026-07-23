/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllIsomorphicGraphPreimage
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllIsomorphicInvariantContradiction

/-!
# Higman's Lemma 13: contradiction in the all-isomorphic parameter branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The all-equal nontrivial parameter branch supplies the actual three-term
graph and its canonical type-A preimage.  Its bundled primitive
eigenfamilies and ambient seed force that preimage to commute with the
target factor, contradicting their exact Frattini intersection.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance allIsomorphicParameterBranchLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance allIsomorphicParameterBranchLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance
    allIsomorphicParameterBranchLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), all-isomorphic parameter branch.**

For the actual `X ⊔ T` and `Z ⊔ T` coordinate packages, equality of the
three nontrivial normalized parameters is impossible.  All pairwise
lower-central data, the three-term graph, and its canonical preimage are
constructed internally rather than assumed. -/
theorem false_of_allIsomorphicParameterBranch_exponent_two
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
      False := by
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
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  letI : IsMulCommutative (frattini ↥(X ⊔ T)) :=
    IsMulCommutative.of_comm hXTEA.comm
  letI : CommGroup (frattini ↥(X ⊔ T)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
    hXTEA.zmodModule
  letI : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
    IsMulCommutative.of_comm hZTEA.comm
  letI : CommGroup (frattini ↥(Z ⊔ T)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
    hZTEA.zmodModule
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro n hn g ePhi nu hggen hnuPrimitive hconj xt zt
    hthetaTcopy hAll
  obtain ⟨hK1XT, htermXT, hSqXT, hAgemoXT, hK0XT,
      hK1ZT, htermZT, hSqZT, hAgemoZT, hK0ZT,
      _t, a, b, cT, U, hUinv,
      _ht, _hab, _halign, hseed, _hcomp, hlambdaPrimitive,
      hEigU, hEigT, hUmapRange, hRangeT, hUnormal, hPhiU,
      hUT, hUTtop, hlenU, htypeAU, _hUcanonical, _hUmap⟩ :=
    exists_allIsomorphicGraph_canonicalTypeAPreimage_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hZinv hTinv hPhiX hPhiZ hPhiT
      hXZ hXT hZT hXTtop hZTtop hXZ_T dataX dataZ dataT
      hn g ePhi nu hggen hnuPrimitive hconj xt zt
      hthetaTcopy hAll
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
  let gXZ := commonEigenvalueGraphMap iX iZ a b
  let iU := commonEigenvalueGraphMap gXZ iT 1 cT
  have hbotPhi : (⊥ : Subgroup P) < frattini P :=
    (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
        (IsAInvariant.of_characteristic Y.subtype) hbotPhi.ne'
  have hn0 : n ≠ 0 := by omega
  have hNpos : 0 < 2 ^ n - 1 := by
    have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlambdaNe : xt.right.lambda ≠ 0 :=
    hlambdaPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  exact
    false_of_threeTermGraph_canonicalPreimage_primitive_eigen_seed
      hP hncomm hxi htwo hUinv hTinv
      hUnormal hPhiU hPhiT hUT hUTtop hlenU
      htypeAU ⟨dataT⟩ hinvPhi hn0 g iU iT
      xt.right.lambda xt.right.lambda
      hlambdaPrimitive hlambdaNe hEigU hEigT hseed
      hUmapRange hRangeT

end

end OddOrder.Higman.Suzuki2Groups
