/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFullPreimageGeometry
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorModels
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorParameters
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoParameterCoincidence

/-!
# Higman's Lemma 13: simultaneous coordinates on the three factor pairs

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, lift three independent quotient summands to
normal actor-invariant type-A factors `X`, `Z`, and `T`.  A single Singer
coordinate on the ambient Frattini subgroup is then transported to all
three pairwise joins.  Applying the witness-preserving normalized pair
classification to `X ⊔ Z`, `X ⊔ T`, and `Z ⊔ T` produces six prescribed
factor copies.

The prescribed-copy transport theorem identifies the two normalized
parameters attached to each actual ambient factor.  Consequently the three
pair relations live on one coherent triple of parameters, and Higman's
cyclic list check forces at least two of them to coincide.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative TensorProduct

noncomputable section

universe uP

/-- Normalized coordinate data for two prescribed copies of an actual
factor pair inside one pairwise join.

Besides the normalized B/C/D relation, the package retains both
`subgroupOf` identifications and both source equations
`ν = λ θ(λ)`. -/
structure NormalizedActualFactorPairCoordinates
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini ↥(R ⊔ S)).map (R ⊔ S).subtype = frattini P)
    {n : ℕ}
    (c : Y)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) where
  factors : XiLengthThreeTypeAFactorData
    ↥(R ⊔ S) (hRinv.sup hSinv).restrict.range
  left :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    FactorCoordinateData factors.left_invariant
      factors.frattini_lt_left.le
      ((hRinv.sup hSinv).restrict.rangeRestrict c)
      ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMap).trans ePhi) nu
  right :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    FactorCoordinateData factors.right_invariant
      factors.frattini_lt_right.le
      ((hRinv.sup hSinv).restrict.rangeRestrict c)
      ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMap).trans ePhi) nu
  left_eq : factors.left = R.subgroupOf (R ⊔ S)
  right_eq : factors.right = S.subgroupOf (R ⊔ S)
  left_source :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    nu = left.lambda * left.theta left.lambda
  right_source :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    nu = right.lambda * right.theta right.lambda
  left_normalized :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    IsNormalizedFactorParameter n left.theta
  right_normalized :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    IsNormalizedFactorParameter n right.theta
  relation :
    let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
      hJoinEA.zmodModule
    NormalizedFactorPairRelation n left.theta right.theta

/-- **Higman Lemma 13 (p. 93), three coherent pairwise coordinates.**

Starting only from the exponent-two length-four hypotheses, this theorem
constructs:

* three normal invariant type-A Frattini preimages with their full pairwise
  and three-factor geometry;
* one ambient Singer generator, coordinate, primitive eigenvalue, and
  Frobenius eigenbasis;
* normalized witness-preserving coordinates on all three pairwise joins;
* equality of the two prescribed-copy parameters belonging to each actual
  factor; and
* the resulting parameter-coincidence disjunction.

Thus every parameter in the final disjunction remains connected to the
actual subgroup factors and to the single ambient Singer coordinate. -/
theorem
    exists_threePairCoordinates_with_parameterCoincidence_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive (frattini P))
    ∃ (X Z T : Subgroup P)
        (hXinv : IsAInvariant Y.subtype X)
        (hZinv : IsAInvariant Y.subtype Z)
        (hTinv : IsAInvariant Y.subtype T)
        (_hXnormal : X.Normal)
        (_hlenX : HasXiLengthTwo hXinv.restrict.range.subtype)
        (dataX : XiLengthTwoTypeAData.{uP, 0} X)
        (_hZnormal : Z.Normal)
        (_hlenZ : HasXiLengthTwo hZinv.restrict.range.subtype)
        (dataZ : XiLengthTwoTypeAData.{uP, 0} Z)
        (_hTnormal : T.Normal)
        (_hlenT : HasXiLengthTwo hTinv.restrict.range.subtype)
        (_dataT : XiLengthTwoTypeAData.{uP, 0} T)
        (hPhiX : frattini P < X)
        (_hXtop : X < ⊤)
        (hPhiZ : frattini P < Z)
        (_hZtop : Z < ⊤)
        (_hPhiT : frattini P < T)
        (_hTtop : T < ⊤)
        (_hXZinf : X ⊓ Z = frattini P)
        (_hXTinf : X ⊓ T = frattini P)
        (_hZTinf : Z ⊓ T = frattini P)
        (_hXZtop : X ⊔ Z < ⊤)
        (_hXTtop : X ⊔ T < ⊤)
        (_hZTtop : Z ⊔ T < ⊤)
        (_hXZ_Tinf : (X ⊔ Z) ⊓ T = frattini P)
        (_hXZ_Tsup : X ⊔ Z ⊔ T = ⊤)
        (c : Y)
        (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
          GaloisField 2 n)
        (nu : GaloisField 2 n)
        (b : Basis (Fin n) (GaloisField 2 n)
          (TensorProduct (ZMod 2) (GaloisField 2 n)
            (Additive (frattini P))))
        (_hnTwo : 2 ≤ n)
        (_hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c)
        (_hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
        (_hconj : ePhi.conj
          (elabRepresentation 2 hPhiInv.restrict c) =
            Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
        (_hgenerate :
          Algebra.adjoin (ZMod 2) ({nu} : Set (GaloisField 2 n)) = ⊤)
        (_heigen : ∀ i,
          (elabRepresentation 2 hPhiInv.restrict c).baseChange
              (GaloisField 2 n) (b i) =
            nu ^ (2 ^ i.val) • b i),
      let hMapXZ : (frattini ↥(X ⊔ Z)).map (X ⊔ Z).subtype =
          frattini P :=
        frattini_sup_map_subtype_eq_ambientFrattini
          hP hxi htwo hXinv hPhiX dataX
      let hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype =
          frattini P :=
        frattini_sup_map_subtype_eq_ambientFrattini
          hP hxi htwo hXinv hPhiX dataX
      let hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype =
          frattini P :=
        frattini_sup_map_subtype_eq_ambientFrattini
          hP hxi htwo hZinv hPhiZ dataZ
      let hXZEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ Z)) :=
        IsElementaryAbelian.of_mulEquiv
          (pairwiseJoinFrattiniEquivAmbientFrattini hMapXZ).symm hPhiEA
      let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
        IsElementaryAbelian.of_mulEquiv
          (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
      let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
        IsElementaryAbelian.of_mulEquiv
          (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
      letI : IsMulCommutative (frattini ↥(X ⊔ Z)) :=
        IsMulCommutative.of_comm hXZEA.comm
      letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ Z))) :=
        hXZEA.zmodModule
      letI : IsMulCommutative (frattini ↥(X ⊔ T)) :=
        IsMulCommutative.of_comm hXTEA.comm
      letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
        hXTEA.zmodModule
      letI : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
        IsMulCommutative.of_comm hZTEA.comm
      letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
        hZTEA.zmodModule
      ∃ (xz : NormalizedActualFactorPairCoordinates
            hXinv hZinv hPhiEA hMapXZ c ePhi nu)
          (xt : NormalizedActualFactorPairCoordinates
            hXinv hTinv hPhiEA hMapXT c ePhi nu)
          (zt : NormalizedActualFactorPairCoordinates
            hZinv hTinv hPhiEA hMapZT c ePhi nu),
        xz.left.theta = xt.left.theta ∧
        xz.right.theta = zt.left.theta ∧
        xt.right.theta = zt.right.theta ∧
        (xz.left.theta = xz.right.theta ∨
          xz.left.theta = xt.right.theta ∨
          xz.right.theta = xt.right.theta) := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive (frattini P))
  obtain ⟨X, Z, T, hXinv, hZinv, hTinv,
      hXnormal, hlenX, hZnormal, hlenZ, hTnormal, hlenT,
      hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
      hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop,
      hXZ_Tinf, hXZ_Tsup⟩ :=
    exists_three_xiLengthTwo_frattini_preimages_with_full_geometry_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  obtain ⟨dataX⟩ :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hXinv hPhiX hlenX
  obtain ⟨dataZ⟩ :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hZinv hPhiZ hlenZ
  obtain ⟨dataT⟩ :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hTinv hPhiT hlenT
  obtain ⟨c, ePhi, nu, b, hnTwo, hcgen, hnuPrimitive, hconj,
      hgenerate, heigen⟩ :=
    exists_ambientFrattiniSingerCoordinates_of_exponent_two
      hP hncomm hmulti hxi htwo
  let hXZinv : IsAInvariant Y.subtype (X ⊔ Z) :=
    hXinv.sup hZinv
  let hXTinv : IsAInvariant Y.subtype (X ⊔ T) :=
    hXinv.sup hTinv
  let hZTinv : IsAInvariant Y.subtype (Z ⊔ T) :=
    hZinv.sup hTinv
  let hMapXZ : (frattini ↥(X ⊔ Z)).map (X ⊔ Z).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hXinv hPhiX dataX
  let hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hXinv hPhiX dataX
  let hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hZinv hPhiZ dataZ
  let hXZEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ Z)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXZ).symm hPhiEA
  let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
  let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
  letI : IsMulCommutative (frattini ↥(X ⊔ Z)) :=
    IsMulCommutative.of_comm hXZEA.comm
  letI : CommGroup (frattini ↥(X ⊔ Z)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ Z))) :=
    hXZEA.zmodModule
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
  obtain ⟨fXZ, xXZ, zXZ, hXXZ, hZXZ, hsourceXXZ, hsourceZXZ,
      hnormXXZ, hnormZXZ, hrelXZ⟩ :=
    exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hZinv hPhiX hPhiZ hXZinf hXZtop dataX dataZ
      c ePhi nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨fXT, xXT, tXT, hXXT, hTXT, hsourceXXT, hsourceTXT,
      hnormXXT, hnormTXT, hrelXT⟩ :=
    exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hTinv hPhiX hPhiT hXTinf hXTtop dataX dataT
      c ePhi nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨fZT, zZT, tZT, hZZT, hTZT, hsourceZZT, hsourceTZT,
      hnormZZT, hnormTZT, hrelZT⟩ :=
    exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hZinv hTinv hPhiZ hPhiT hZTinf hZTtop dataZ dataT
      c ePhi nu hnTwo hcgen hnuPrimitive hconj
  have hn : n ≠ 0 := by omega
  have hthetaX : xXZ.theta = xXT.theta :=
    xXZ.theta_eq_of_prescribedPairwiseFactorCopies
      hXZinv hXTinv le_sup_left le_sup_left hXXZ hXXT
      fXZ.left_invariant fXT.left_invariant c xXT hn
      hnormXXZ hnormXXT hnuPrimitive
  have hthetaZ : zXZ.theta = zZT.theta :=
    zXZ.theta_eq_of_prescribedPairwiseFactorCopies
      hXZinv hZTinv le_sup_right le_sup_left hZXZ hZZT
      fXZ.right_invariant fZT.left_invariant c zZT hn
      hnormZXZ hnormZZT hnuPrimitive
  have hthetaT : tXT.theta = tZT.theta :=
    tXT.theta_eq_of_prescribedPairwiseFactorCopies
      hXTinv hZTinv le_sup_right le_sup_right hTXT hTZT
      fXT.right_invariant fZT.right_invariant c tZT hn
      hnormTXT hnormTZT hnuPrimitive
  have hrelXT' :
      NormalizedFactorPairRelation n xXZ.theta tXT.theta := by
    rw [hthetaX]
    exact hrelXT
  have hrelZT' :
      NormalizedFactorPairRelation n zXZ.theta tXT.theta := by
    rw [hthetaZ, hthetaT]
    exact hrelZT
  have hcoincidence :
      xXZ.theta = zXZ.theta ∨
        xXZ.theta = tXT.theta ∨
        zXZ.theta = tXT.theta :=
    normalized_factorPairRelations_force_parameter_coincidence
      (by omega) hnormXXZ hnormZXZ hnormTXT
      hrelXZ hrelXT' hrelZT'
  let xz : NormalizedActualFactorPairCoordinates
      hXinv hZinv hPhiEA hMapXZ c ePhi nu :=
    { factors := fXZ
      left := xXZ
      right := zXZ
      left_eq := hXXZ
      right_eq := hZXZ
      left_source := hsourceXXZ
      right_source := hsourceZXZ
      left_normalized := hnormXXZ
      right_normalized := hnormZXZ
      relation := hrelXZ }
  let xt : NormalizedActualFactorPairCoordinates
      hXinv hTinv hPhiEA hMapXT c ePhi nu :=
    { factors := fXT
      left := xXT
      right := tXT
      left_eq := hXXT
      right_eq := hTXT
      left_source := hsourceXXT
      right_source := hsourceTXT
      left_normalized := hnormXXT
      right_normalized := hnormTXT
      relation := hrelXT }
  let zt : NormalizedActualFactorPairCoordinates
      hZinv hTinv hPhiEA hMapZT c ePhi nu :=
    { factors := fZT
      left := zZT
      right := tZT
      left_eq := hZZT
      right_eq := hTZT
      left_source := hsourceZZT
      right_source := hsourceTZT
      left_normalized := hnormZZT
      right_normalized := hnormTZT
      relation := hrelZT }
  exact ⟨X, Z, T, hXinv, hZinv, hTinv,
    hXnormal, hlenX, dataX, hZnormal, hlenZ, dataZ,
    hTnormal, hlenT, dataT,
    hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
    hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop,
    hXZ_Tinf, hXZ_Tsup,
    c, ePhi, nu, b, hnTwo, hcgen, hnuPrimitive, hconj,
    hgenerate, heigen, xz, xt, zt,
    hthetaX, hthetaZ, hthetaT, hcoincidence⟩

end

end OddOrder.Higman.Suzuki2Groups
