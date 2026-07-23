/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFirstAlignedParameterBranch
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoQuotientFactorGeometry
import OddOrder.Isaacs.Appendix.SubgroupBasics

/-!
# Higman's Lemma 13: the three aligned parameter branches

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

This leaf dispatches all three oriented aligned-parameter alternatives.  The
second and third alternatives require genuinely reversed pairwise joins; their
normalized coordinate packages are reconstructed on those literal joins.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

/-- Directness of three subgroups over a common bottom is symmetric in the
three axes of the modular subgroup lattice. -/
private theorem cyclic_sup_inf_eq_of_sup_inf_eq
    {P : Type uP} [Group P]
    {N X Z T : Subgroup P}
    [N.Normal] [X.Normal] [Z.Normal] [T.Normal]
    (hNX : N ≤ X)
    (hNZ : N ≤ Z)
    (hNT : N ≤ T)
    (hXZ : X ⊓ Z = N)
    (hXZ_T : (X ⊔ Z) ⊓ T = N) :
    (X ⊔ T) ⊓ Z = N ∧
      (Z ⊔ T) ⊓ X = N := by
  let q := QuotientGroup.mk' N
  have hxzMap :
      X.map q ⊓ Z.map q = ⊥ :=
    quotient_map_inf_eq_bot_of_inf_eq_kernel
      N X Z hNX hNZ hXZ
  have hxz_tMap :
      (X.map q ⊔ Z.map q) ⊓ T.map q = ⊥ := by
    rw [← Subgroup.map_sup]
    exact quotient_map_inf_eq_bot_of_inf_eq_kernel
      N (X ⊔ Z) T (hNX.trans le_sup_left) hNT hXZ_T
  have hxzDisjoint : Disjoint (X.map q) (Z.map q) :=
    disjoint_iff.mpr hxzMap
  have hxz_tDisjoint :
      Disjoint (X.map q ⊔ Z.map q) (T.map q) :=
    disjoint_iff.mpr hxz_tMap
  have hz_xtDisjoint :
      Disjoint (Z.map q) (X.map q ⊔ T.map q) := by
    have h :=
      OddOrder.Isaacs.Appendix.disjoint_sup_of_normal
        (A := Z.map q) (B := T.map q) (C := X.map q)
        hxzDisjoint.symm
        (by simpa [sup_comm] using hxz_tDisjoint.symm)
    simpa [sup_comm] using h
  have hx_ztDisjoint :
      Disjoint (X.map q) (Z.map q ⊔ T.map q) := by
    apply OddOrder.Isaacs.Appendix.disjoint_sup_of_normal
      (A := X.map q) (B := Z.map q) (C := T.map q)
    · exact hxz_tDisjoint.mono_left le_sup_left
    · exact hz_xtDisjoint
  have inf_eq_of_map_disjoint
      {A B : Subgroup P}
      (hNA : N ≤ A)
      (hNB : N ≤ B)
      (hdisjoint : Disjoint (A.map q) (B.map q)) :
      A ⊓ B = N := by
    have hcomap :=
      congrArg (fun H : Subgroup (P ⧸ N) => H.comap q)
        hdisjoint.eq_bot
    simpa only [Subgroup.comap_inf, q,
      QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hNA, sup_eq_right.mpr hNB,
      MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hcomap
  constructor
  · rw [← Subgroup.map_sup] at hz_xtDisjoint
    exact inf_eq_of_map_disjoint
      (hNX.trans le_sup_left) hNZ hz_xtDisjoint.symm
  · rw [← Subgroup.map_sup] at hx_ztDisjoint
    exact inf_eq_of_map_disjoint
      (hNZ.trans le_sup_left) hNX hx_ztDisjoint.symm


/-- Package the honest normalized-coordinate reconstruction theorem for one
literal oriented pairwise join. -/
private theorem
    exists_normalizedActualFactorPairCoordinates_of_exponent_two
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
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiR : frattini P < R)
    (hPhiS : frattini P < S)
    (hRS : R ⊓ S = frattini P)
    (hRStop : R ⊔ S < (⊤ : Subgroup P))
    (dataR : XiLengthTwoTypeAData.{uP, 0} R)
    (dataS : XiLengthTwoTypeAData.{uP, 0} S) :
    let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
    let hMap : (frattini ↥(R ⊔ S)).map (R ⊔ S).subtype =
        frattini P :=
      frattini_sup_map_subtype_eq_ambientFrattini
        hP hxi htwo hRinv hPhiR dataR
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
    ∀ {n : Nat} (c : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              Y.subtype :
                IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      Nonempty (NormalizedActualFactorPairCoordinates
        hRinv hSinv hPhiEA hMap c ePhi nu) := by
  classical
  dsimp only
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  let hMap : (frattini ↥(R ⊔ S)).map (R ⊔ S).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hRinv hPhiR dataR
  let hJoinEA : IsElementaryAbelian 2 (frattini ↥(R ⊔ S)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm hPhiEA
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  letI : IsMulCommutative (frattini ↥(R ⊔ S)) :=
    IsMulCommutative.of_comm hJoinEA.comm
  letI : CommGroup (frattini ↥(R ⊔ S)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(R ⊔ S))) :=
    hJoinEA.zmodModule
  intro n c ePhi nu hn hcgen hnuPrimitive hconj
  obtain ⟨factors, left, right, hleft, hright,
      hsourceLeft, hsourceRight, hnormLeft, hnormRight, hrelation⟩ :=
    exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hRinv hSinv hPhiR hPhiS hRS hRStop dataR dataS
      c ePhi nu hn hcgen hnuPrimitive hconj
  exact ⟨{
    factors := factors
    left := left
    right := right
    left_eq := hleft
    right_eq := hright
    left_source := hsourceLeft
    right_source := hsourceRight
    left_normalized := hnormLeft
    right_normalized := hnormRight
    relation := hrelation }⟩

/-- **Higman Lemma 13 (p. 93), all aligned parameter branches.**

The common-T alternative is the fixed orientation already handled by
false_of_firstAlignedParameterBranch_exponent_two.  For the common-Z and
common-X alternatives this theorem reconstructs the literal oriented joins
T ⊔ Z, Z ⊔ X, and T ⊔ X, proves their normalized parameters agree with the
corresponding prescribed copies in the coherent XZ, XT, and ZT packages,
and then applies the same fixed contradiction after permuting the axes. -/
theorem false_of_alignedParameterBranches_exponent_two
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
    (hXnormal : X.Normal)
    (hZnormal : Z.Normal)
    (hTnormal : T.Normal)
    (hPhiX : frattini P < X)
    (hPhiZ : frattini P < Z)
    (hPhiT : frattini P < T)
    (hXZ : X ⊓ Z = frattini P)
    (hXT : X ⊓ T = frattini P)
    (hZT : Z ⊓ T = frattini P)
    (hXZtop : X ⊔ Z < (⊤ : Subgroup P))
    (hXTtop : X ⊔ T < (⊤ : Subgroup P))
    (hZTtop : Z ⊔ T < (⊤ : Subgroup P))
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P)
    (dataX : XiLengthTwoTypeAData.{uP, 0} X)
    (dataZ : XiLengthTwoTypeAData.{uP, 0} Z)
    (dataT : XiLengthTwoTypeAData.{uP, 0} T) :
    let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
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
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
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
    ∀ {n : Nat},
    2 ≤ n →
    ∀ (c : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              Y.subtype :
                IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∀
      (xz : NormalizedActualFactorPairCoordinates
        hXinv hZinv hPhiEA hMapXZ c ePhi nu)
      (xt : NormalizedActualFactorPairCoordinates
        hXinv hTinv hPhiEA hMapXT c ePhi nu)
      (zt : NormalizedActualFactorPairCoordinates
        hZinv hTinv hPhiEA hMapZT c ePhi nu),
      (AlignedTwoJoinParameterData
          xt.left.theta xt.right.theta
          zt.left.theta zt.right.theta ∨
        AlignedTwoJoinParameterData
          xz.left.theta xz.right.theta
          zt.right.theta zt.left.theta ∨
        AlignedTwoJoinParameterData
          xz.right.theta xz.left.theta
          xt.right.theta xt.left.theta) →
      False := by
  classical
  dsimp only
  letI : X.Normal := hXnormal
  letI : Z.Normal := hZnormal
  letI : T.Normal := hTnormal
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
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
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
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
  intro n hn c ePhi nu hcgen hnuPrimitive hconj xz xt zt haligned
  obtain ⟨hXT_Z, hZT_X⟩ :=
    cyclic_sup_inf_eq_of_sup_inf_eq
      hPhiX.le hPhiZ.le hPhiT.le hXZ hXZ_T
  have hTZ : T ⊓ Z = frattini P := by
    simpa only [inf_comm] using hZT
  have hZX : Z ⊓ X = frattini P := by
    simpa only [inf_comm] using hXZ
  have hTX : T ⊓ X = frattini P := by
    simpa only [inf_comm] using hXT
  have hTZtop : T ⊔ Z < (⊤ : Subgroup P) := by
    simpa only [sup_comm] using hZTtop
  have hZXtop : Z ⊔ X < (⊤ : Subgroup P) := by
    simpa only [sup_comm] using hXZtop
  have hTXtop : T ⊔ X < (⊤ : Subgroup P) := by
    simpa only [sup_comm] using hXTtop
  let hMapTZ : (frattini ↥(T ⊔ Z)).map (T ⊔ Z).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hTinv hPhiT dataT
  let hMapZX : (frattini ↥(Z ⊔ X)).map (Z ⊔ X).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hZinv hPhiZ dataZ
  let hMapTX : (frattini ↥(T ⊔ X)).map (T ⊔ X).subtype =
      frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hTinv hPhiT dataT
  let hTZEA : IsElementaryAbelian 2 (frattini ↥(T ⊔ Z)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapTZ).symm hPhiEA
  let hZXEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ X)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapZX).symm hPhiEA
  let hTXEA : IsElementaryAbelian 2 (frattini ↥(T ⊔ X)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapTX).symm hPhiEA
  letI : IsMulCommutative (frattini ↥(T ⊔ Z)) :=
    IsMulCommutative.of_comm hTZEA.comm
  letI : CommGroup (frattini ↥(T ⊔ Z)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(T ⊔ Z))) :=
    hTZEA.zmodModule
  letI : IsMulCommutative (frattini ↥(Z ⊔ X)) :=
    IsMulCommutative.of_comm hZXEA.comm
  letI : CommGroup (frattini ↥(Z ⊔ X)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ X))) :=
    hZXEA.zmodModule
  letI : IsMulCommutative (frattini ↥(T ⊔ X)) :=
    IsMulCommutative.of_comm hTXEA.comm
  letI : CommGroup (frattini ↥(T ⊔ X)) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini ↥(T ⊔ X))) :=
    hTXEA.zmodModule
  obtain ⟨tz⟩ :=
    exists_normalizedActualFactorPairCoordinates_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hTinv hZinv hPhiT hPhiZ hTZ hTZtop dataT dataZ
      c ePhi nu hn hcgen hnuPrimitive hconj
  obtain ⟨zx⟩ :=
    exists_normalizedActualFactorPairCoordinates_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hZinv hXinv hPhiZ hPhiX hZX hZXtop dataZ dataX
      c ePhi nu hn hcgen hnuPrimitive hconj
  obtain ⟨tx⟩ :=
    exists_normalizedActualFactorPairCoordinates_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hTinv hXinv hPhiT hPhiX hTX hTXtop dataT dataX
      c ePhi nu hn hcgen hnuPrimitive hconj
  have hn0 : n ≠ 0 := by omega
  have hthetaT_TZ_ZT : tz.left.theta = zt.right.theta :=
    tz.left.theta_eq_of_prescribedPairwiseFactorCopies
      (hTinv.sup hZinv) (hZinv.sup hTinv)
      le_sup_left le_sup_right
      tz.left_eq zt.right_eq
      tz.factors.left_invariant zt.factors.right_invariant
      c zt.right hn0
      tz.left_normalized zt.right_normalized hnuPrimitive
  have hthetaZ_TZ_ZT : tz.right.theta = zt.left.theta :=
    tz.right.theta_eq_of_prescribedPairwiseFactorCopies
      (hTinv.sup hZinv) (hZinv.sup hTinv)
      le_sup_right le_sup_left
      tz.right_eq zt.left_eq
      tz.factors.right_invariant zt.factors.left_invariant
      c zt.left hn0
      tz.right_normalized zt.left_normalized hnuPrimitive
  have hthetaZ_ZX_XZ : zx.left.theta = xz.right.theta :=
    zx.left.theta_eq_of_prescribedPairwiseFactorCopies
      (hZinv.sup hXinv) (hXinv.sup hZinv)
      le_sup_left le_sup_right
      zx.left_eq xz.right_eq
      zx.factors.left_invariant xz.factors.right_invariant
      c xz.right hn0
      zx.left_normalized xz.right_normalized hnuPrimitive
  have hthetaX_ZX_XZ : zx.right.theta = xz.left.theta :=
    zx.right.theta_eq_of_prescribedPairwiseFactorCopies
      (hZinv.sup hXinv) (hXinv.sup hZinv)
      le_sup_right le_sup_left
      zx.right_eq xz.left_eq
      zx.factors.right_invariant xz.factors.left_invariant
      c xz.left hn0
      zx.right_normalized xz.left_normalized hnuPrimitive
  have hthetaT_TX_XT : tx.left.theta = xt.right.theta :=
    tx.left.theta_eq_of_prescribedPairwiseFactorCopies
      (hTinv.sup hXinv) (hXinv.sup hTinv)
      le_sup_left le_sup_right
      tx.left_eq xt.right_eq
      tx.factors.left_invariant xt.factors.right_invariant
      c xt.right hn0
      tx.left_normalized xt.right_normalized hnuPrimitive
  have hthetaX_TX_XT : tx.right.theta = xt.left.theta :=
    tx.right.theta_eq_of_prescribedPairwiseFactorCopies
      (hTinv.sup hXinv) (hXinv.sup hTinv)
      le_sup_right le_sup_left
      tx.right_eq xt.left_eq
      tx.factors.right_invariant xt.factors.left_invariant
      c xt.left hn0
      tx.right_normalized xt.left_normalized hnuPrimitive
  rcases haligned with hAlignedT | hAlignedZ | hAlignedX
  · exact false_of_firstAlignedParameterBranch_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hZinv hTinv
      hPhiX hPhiZ hPhiT
      hXZ hXT hZT hXTtop hZTtop hXZ_T
      dataX dataZ dataT
      hn c ePhi nu hcgen hnuPrimitive hconj
      xt zt hAlignedT
  · let hAlignedXZTZ : AlignedTwoJoinParameterData
        xz.left.theta xz.right.theta
        tz.left.theta tz.right.theta :=
      { left_eq := hAlignedZ.left_eq.trans hthetaT_TZ_ZT.symm
        common_eq := hAlignedZ.common_eq.trans hthetaZ_TZ_ZT.symm
        unique := hAlignedZ.unique }
    exact false_of_firstAlignedParameterBranch_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hXinv hTinv hZinv
      hPhiX hPhiT hPhiZ
      hXT hXZ hTZ hXZtop hTZtop hXT_Z
      dataX dataT dataZ
      hn c ePhi nu hcgen hnuPrimitive hconj
      xz tz hAlignedXZTZ
  · have hUniqueZX :
        zx.left.theta = 1 ∨
          zx.left.theta ≠ zx.right.theta := by
      rcases hAlignedX.unique with hOne | hne
      · exact Or.inl (hthetaZ_ZX_XZ.trans hOne)
      · exact Or.inr fun h =>
          hne (hthetaZ_ZX_XZ.symm.trans
            (h.trans hthetaX_ZX_XZ))
    let hAlignedZXTX : AlignedTwoJoinParameterData
        zx.left.theta zx.right.theta
        tx.left.theta tx.right.theta :=
      { left_eq := hthetaZ_ZX_XZ.trans
          (hAlignedX.left_eq.trans hthetaT_TX_XT.symm)
        common_eq := hthetaX_ZX_XZ.trans
          (hAlignedX.common_eq.trans hthetaX_TX_XT.symm)
        unique := hUniqueZX }
    exact false_of_firstAlignedParameterBranch_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hZinv hTinv hXinv
      hPhiZ hPhiT hPhiX
      hZT hZX hTX hZXtop hTXtop hZT_X
      dataZ dataT dataX
      hn c ePhi nu hcgen hnuPrimitive hconj
      zx tx hAlignedZXTX
end

end OddOrder.Higman.Suzuki2Groups
