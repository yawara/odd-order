/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.AmbientCentralExtension
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseClassification
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseFactorData

/-!
# Higman's Lemma 13: structural data for an exponent-two pairwise join

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

An actual pair of type-A factors determines its invariant proper join and all
of the intrinsic length-three infrastructure used by the coordinate
arguments.  This file packages those facts independently of any normalized
factor coordinates, so later three-pair assembly can choose coordinates only
after fixing the honest join and its prescribed factor data.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

/-- Structural and lower-central infrastructure carried by the actual join
of two exponent-two type-A factors.

The field `join_eq_sup` identifies the packaged group with the literal
ambient join.  The factor fields retain the prescribed `subgroupOf` copies,
while `singer_conj` records transport of one supplied ambient Singer
coordinate to the restricted faithful actor. -/
structure PairwiseJoinLowerCentralData
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (R S : Subgroup P)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    {n : Nat}
    (c : Y)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) where
  join : Subgroup P
  join_eq_sup : join = R ⊔ S
  invariant : IsAInvariant Y.subtype join
  frattini_map : (frattini join).map join.subtype = frattini P
  factors : XiLengthThreeTypeAFactorData
    join invariant.restrict.range
  left_eq : factors.left = R.subgroupOf join
  right_eq : factors.right = S.subgroupOf join
  kernel_one_eq_bot : lowerCentralLayerKernel join 1 = ⊥
  term_one_eq_frattini : lowerCentralTerm join 1 = frattini join
  squares_lie_in_second : LowerCentralSquaresLieInSecond join
  agemo_one_eq_frattini : Agemo join 2 1 = frattini join
  kernel_zero_eq_frattini_subgroupOf :
    lowerCentralLayerKernel join 0 =
      (frattini join).subgroupOf (lowerCentralTerm join 0)
  xiActor : IsXiActor invariant.restrict.range
  involutions_le_frattini : involutions join ⊆ frattini join
  singer_conj :
    let hJoinEA : IsElementaryAbelian 2 (frattini join) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini
          frattini_map).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini join) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini join)) :=
      hJoinEA.zmodModule
    let eJoin :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA frattini_map).trans ePhi
    eJoin.conj
        (elabRepresentation 2
          (IsAInvariant.of_characteristic
            invariant.restrict.range.subtype :
              IsAInvariant invariant.restrict.range.subtype
                (frattini join)).restrict
          (invariant.restrict.rangeRestrict c)) =
      Algebra.lmul (ZMod 2) (GaloisField 2 n) nu

/-- **Higman Lemma 13 (p. 93), honest pairwise-join infrastructure.**

Starting from two actual type-A factors and their full ambient geometry, this
constructs the prescribed length-three factor package and every intrinsic
lower-central fact needed by the aligned-graph argument.  No lower-central,
restricted-actor, or restricted-involution fact is assumed. -/
theorem exists_pairwiseJoinLowerCentralData_of_exponent_two
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
    (hRSinf : R ⊓ S = frattini P)
    (hRStop : R ⊔ S < (⊤ : Subgroup P))
    (dataR : XiLengthTwoTypeAData.{uP, 0} R)
    (dataS : XiLengthTwoTypeAData.{uP, 0} S) :
    let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              Y.subtype :
                IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      Nonempty (PairwiseJoinLowerCentralData
        R S hPhiEA c ePhi nu) := by
  classical
  dsimp only
  let J : Subgroup P := R ⊔ S
  let hJinv : IsAInvariant Y.subtype J := hRinv.sup hSinv
  let hPhiEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  let hMap : (frattini J).map J.subtype = frattini P :=
    frattini_sup_map_subtype_eq_ambientFrattini
      hP hxi htwo hRinv hPhiR dataR
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
  intro n c ePhi nu hconj
  have hRJoin : R < J := by
    apply lt_of_le_of_ne le_sup_left
    intro hEq
    have hSleR : S ≤ R := by
      rw [hEq]
      exact le_sup_right
    have hSphi : S = frattini P := by
      calc
        S = R ⊓ S := (inf_eq_right.mpr hSleR).symm
        _ = frattini P := hRSinf
    exact hPhiS.ne hSphi.symm
  have hbotPhi : (⊥ : Subgroup P) < frattini P :=
    (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hlenJ : HasXiLengthThree hJinv.restrict.range.subtype :=
    restricted_range_hasXiLengthThree_of_two_step_exponent_two
      hP hxi hlen htwo hRinv hJinv hbotPhi hPhiR hRJoin hRStop
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
        (IsAInvariant.of_characteristic Y.subtype) hbotPhi.ne'
  have hncommJ : ¬ IsMulCommutative J :=
    not_isMulCommutative_sup_of_typeA_factors
      hxi hRinv hSinv hRSinf dataR dataS hinvPhi htwo
  have hinvJ : involutions P ⊆ J := fun _ hx =>
    (le_sup_left : R ≤ J) (hPhiR.le (hinvPhi hx))
  have hmultiJ : ∃ x y : J,
      x ∈ involutions J ∧ y ∈ involutions J ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvJ hmulti
  have hxiJ : IsXiActor hJinv.restrict.range :=
    restricted_range_isXiActor hxi hJinv
  have hprimeJ : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hJinv.restrict.range →
        p ∣ (involutions J).ncard :=
    restricted_range_primeSupport hJinv hinvJ hprime
  obtain ⟨factors, hleft, hright⟩ :=
    xiLengthThreeTypeAFactorData_pairwiseJoin_of_exponent_two
      hP hmulti hxi htwo hRinv hSinv hPhiR hPhiS hRSinf
      dataR dataS
  have htermJ : lowerCentralTerm J 1 = frattini J :=
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
  have hK1J : lowerCentralLayerKernel J 1 = ⊥ :=
    lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
  have hSqJ : LowerCentralSquaresLieInSecond J :=
    lowerCentralSquaresLieInSecond_of_xiLengthThree
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
  have hAgemoJ : Agemo J 2 1 = frattini J :=
    agemo_one_eq_frattini_of_xiLengthThree
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
  have hK0J : lowerCentralLayerKernel J 0 =
      (frattini J).subgroupOf (lowerCentralTerm J 0) :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
  have hPhiJne : frattini J ≠ ⊥ := by
    intro hPhiJ
    have h := congrArg (fun A : Subgroup J => A.map J.subtype) hPhiJ
    rw [hMap, Subgroup.map_bot] at h
    exact hbotPhi.ne' h
  have hinvPhiJ : involutions J ⊆ frattini J :=
    involutions_subset_of_nontrivial_invariant
      (hP.to_subgroup J) hJinv.restrict.range hxiJ.transitive
        (IsAInvariant.of_characteristic
          hJinv.restrict.range.subtype) hPhiJne
  have hconjJ :
      ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi).conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hJinv.restrict.range.subtype :
                IsAInvariant hJinv.restrict.range.subtype
                  (frattini J)).restrict
            (hJinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu :=
    pairwiseJoinFrattiniSingerCoordinate_conj
      hJinv hPhiEA hMap c ePhi nu hconj
  exact ⟨{
    join := J
    join_eq_sup := rfl
    invariant := hJinv
    frattini_map := hMap
    factors := factors
    left_eq := hleft
    right_eq := hright
    kernel_one_eq_bot := hK1J
    term_one_eq_frattini := htermJ
    squares_lie_in_second := hSqJ
    agemo_one_eq_frattini := hAgemoJ
    kernel_zero_eq_frattini_subgroupOf := hK0J
    xiActor := hxiJ
    involutions_le_frattini := hinvPhiJ
    singer_conj := hconjJ }⟩

/-- Transport the packaged invariant join to the literal subgroup join. -/
theorem PairwiseJoinLowerCentralData.supInvariant
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    IsAInvariant Y.subtype (R ⊔ S) :=
  data.join_eq_sup ▸ data.invariant

/-- The Frattini map stored by the bundle, transported to the literal join. -/
theorem PairwiseJoinLowerCentralData.supFrattiniMap
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    (frattini ↥(R ⊔ S)).map (R ⊔ S).subtype = frattini P :=
  data.join_eq_sup ▸ data.frattini_map

/-- The lower-central kernel-one fact stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supKernelOneEqBot
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    lowerCentralLayerKernel ↥(R ⊔ S) 1 = ⊥ :=
  data.join_eq_sup ▸ data.kernel_one_eq_bot

/-- The lower-central term-one fact stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supTermOneEqFrattini
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    lowerCentralTerm ↥(R ⊔ S) 1 = frattini ↥(R ⊔ S) :=
  data.join_eq_sup ▸ data.term_one_eq_frattini

/-- The square-containment fact stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supSquaresLieInSecond
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    LowerCentralSquaresLieInSecond ↥(R ⊔ S) :=
  data.join_eq_sup ▸ data.squares_lie_in_second

/-- The first-agemo fact stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supAgemoOneEqFrattini
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    Agemo ↥(R ⊔ S) 2 1 = frattini ↥(R ⊔ S) :=
  data.join_eq_sup ▸ data.agemo_one_eq_frattini

/-- The zeroth-kernel fact stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supKernelZeroEqFrattiniSubgroupOf
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    lowerCentralLayerKernel ↥(R ⊔ S) 0 =
      (frattini ↥(R ⊔ S)).subgroupOf
        (lowerCentralTerm ↥(R ⊔ S) 0) :=
  data.join_eq_sup ▸ data.kernel_zero_eq_frattini_subgroupOf

/-- The involution containment stored by the bundle, on the literal join. -/
theorem PairwiseJoinLowerCentralData.supInvolutionsLeFrattini
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    {hPhiEA : IsElementaryAbelian 2 (frattini P)}
    {n : Nat} {c : Y}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : PairwiseJoinLowerCentralData R S hPhiEA c ePhi nu) :
    involutions ↥(R ⊔ S) ⊆ frattini ↥(R ⊔ S) :=
  data.join_eq_sup ▸ data.involutions_le_frattini

end

end OddOrder.Higman.Suzuki2Groups
