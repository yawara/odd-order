/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseFactorData
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseClassification
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.FixedFactorPairRelation

/-!
# Higman's Lemma 13: actual pairwise factors over the common coordinate

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Fix one Singer datum `(c, ePhi, nu)` on the ambient `Φ(P)`.  For a pairwise
join `J = R ⊔ S`, transport that datum to the intrinsic `Φ(J)` and construct
factor coordinates on the actual subgroup-of copies of `R` and `S`.

The returned source equations use the same scalar `nu` and the same
transported Frattini coordinate.  Thus no new ambient coordinate is chosen
when a different pairwise join is analyzed.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (p. 93), factor coordinates inside one join.**

Equip a prescribed factor package inside `R ⊔ S` with coordinates transported
from one fixed ambient Singer datum.  The explicit factor equalities and
source equations are retained in the conclusion. -/
theorem exists_factorCoordinates_on_actual_pairwiseJoin_of_exponent_two
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
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hJoinEA.zmodModule
    ∀ (factors : XiLengthThreeTypeAFactorData
          J hJinv.restrict.range),
      factors.left = R.subgroupOf J →
      factors.right = S.subgroupOf J →
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
                Y.subtype : IsAInvariant Y.subtype (frattini P)).restrict c) =
          Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
        ∃ (left : FactorCoordinateData factors.left_invariant
              factors.frattini_lt_left.le
              (hJinv.restrict.rangeRestrict c)
              ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
                hPhiEA hMap).trans ePhi) nu)
          (right : FactorCoordinateData factors.right_invariant
              factors.frattini_lt_right.le
              (hJinv.restrict.rangeRestrict c)
              ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
                hPhiEA hMap).trans ePhi) nu),
          factors.left = R.subgroupOf J ∧
          factors.right = S.subgroupOf J ∧
          nu = left.lambda * left.theta left.lambda ∧
          nu = right.lambda * right.theta right.lambda := by
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
  intro factors hleft hright n c ePhi nu hnTwo hcgen
    hnuPrimitive hconj
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
  let cJ : hJinv.restrict.range :=
    hJinv.restrict.rangeRestrict c
  let eJoin :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMap).trans ePhi
  have hcgenJ : ∀ g : hJinv.restrict.range,
      g ∈ Subgroup.zpowers cJ :=
    forall_mem_zpowers_restrictedRange_generator hJinv c hcgen
  have hconjJ :
      eJoin.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hJinv.restrict.range.subtype :
                IsAInvariant hJinv.restrict.range.subtype
                  (frattini J)).restrict cJ) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu :=
    pairwiseJoinFrattiniSingerCoordinate_conj
      hJinv hPhiEA hMap c ePhi nu hconj
  obtain ⟨left⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      (P := J) (Y := hJinv.restrict.range)
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
      factors.left_invariant factors.frattini_lt_left
      factors.left_lt_top cJ eJoin nu hnTwo hcgenJ
      hnuPrimitive hconjJ
  obtain ⟨right⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      (P := J) (Y := hJinv.restrict.range)
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
      factors.right_invariant factors.frattini_lt_right
      factors.right_lt_top cJ eJoin nu hnTwo hcgenJ
      hnuPrimitive hconjJ
  exact ⟨left, right, hleft, hright,
    left.kernel_eigenvalue_eq, right.kernel_eigenvalue_eq⟩

/-- **Higman Lemma 13 (p. 93), actual pairwise factor coordinates.**

Construct the prescribed factor package and equip exactly those two factors
with coordinates over a supplied ambient Singer datum. -/
theorem exists_actualPairwiseFactorCoordinates_of_exponent_two
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
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
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
              Y.subtype : IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (factors : XiLengthThreeTypeAFactorData
            J hJinv.restrict.range)
        (left : FactorCoordinateData factors.left_invariant
            factors.frattini_lt_left.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu)
        (right : FactorCoordinateData factors.right_invariant
            factors.frattini_lt_right.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu),
        factors.left = R.subgroupOf J ∧
        factors.right = S.subgroupOf J ∧
        nu = left.lambda * left.theta left.lambda ∧
        nu = right.lambda * right.theta right.lambda := by
  classical
  dsimp only
  intro n c ePhi nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨factors, hleft, hright⟩ :=
    xiLengthThreeTypeAFactorData_pairwiseJoin_of_exponent_two
      hP hmulti hxi htwo hRinv hSinv hPhiR hPhiS hRSinf dataR dataS
  obtain ⟨left, right, hleft', hright', hsourceL, hsourceR⟩ :=
    exists_factorCoordinates_on_actual_pairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hRinv hSinv hPhiR hPhiS hRSinf hRStop dataR dataS
      factors hleft hright c ePhi nu hnTwo hcgen hnuPrimitive hconj
  exact ⟨factors, left, right, hleft', hright', hsourceL, hsourceR⟩

/-- **Higman Lemma 13 (p. 93), normalized relation on one actual pair.**

The actual two factors are retained while their fixed-coordinate data are
normalized into Higman's oriented B/C/D parameter relation. -/
theorem exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
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
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
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
              Y.subtype : IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (factors : XiLengthThreeTypeAFactorData
            J hJinv.restrict.range)
        (left' : FactorCoordinateData factors.left_invariant
            factors.frattini_lt_left.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu)
        (right' : FactorCoordinateData factors.right_invariant
            factors.frattini_lt_right.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu),
        factors.left = R.subgroupOf J ∧
        factors.right = S.subgroupOf J ∧
        nu = left'.lambda * left'.theta left'.lambda ∧
        nu = right'.lambda * right'.theta right'.lambda ∧
        (left'.theta = 1 ∨
          ∃ rL : ℕ, 0 < rL ∧ 2 * rL ≤ n ∧
            left'.theta =
              frobeniusEquiv (GaloisField 2 n) 2 ^ rL ∧
            Odd (orderOf left'.theta)) ∧
        (right'.theta = 1 ∨
          ∃ rR : ℕ, 0 < rR ∧ 2 * rR ≤ n ∧
            right'.theta =
              frobeniusEquiv (GaloisField 2 n) 2 ^ rR ∧
            Odd (orderOf right'.theta)) ∧
        NormalizedFactorPairRelation n left'.theta right'.theta := by
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
  intro n c ePhi nu hnTwo hcgen hnuPrimitive hconj
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
  let cJ : hJinv.restrict.range :=
    hJinv.restrict.rangeRestrict c
  let eJoin :=
    (pairwiseJoinFrattiniLinearEquivAmbientFrattini
      hPhiEA hMap).trans ePhi
  have hconjJ :
      eJoin.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hJinv.restrict.range.subtype :
                IsAInvariant hJinv.restrict.range.subtype
                  (frattini J)).restrict cJ) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu :=
    pairwiseJoinFrattiniSingerCoordinate_conj
      hJinv hPhiEA hMap c ePhi nu hconj
  obtain ⟨factors, left, right, hleft, hright, _hsourceL, _hsourceR⟩ :=
    exists_actualPairwiseFactorCoordinates_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hRinv hSinv hPhiR hPhiS hRSinf hRStop dataR dataS
      c ePhi nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨left', right', hsourceL', hsourceR',
      hleftCase, hrightCase, hrelation⟩ :=
    factors.exists_normalizedFactorPairRelation_with_witnesses_of_fixedCoordinates
      (hP.to_subgroup J) hncommJ hmultiJ hxiJ hlenJ hprimeJ
      cJ eJoin nu hnTwo hnuPrimitive hconjJ
      left right
  exact ⟨factors, left', right', hleft, hright,
    hsourceL', hsourceR', hleftCase, hrightCase, hrelation⟩
end

end OddOrder.Higman.Suzuki2Groups

namespace OddOrder.Higman.Suzuki2Groups
universe uP

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative

noncomputable section

/-- **Higman Lemma 13 (p. 93), normalized relation on one actual pair.**

Compatibility view of the witness-preserving theorem that retains the
original relation-only result. -/
theorem exists_normalizedFactorPairRelation_on_actualPairwiseJoin_of_exponent_two
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
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
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
              Y.subtype : IsAInvariant Y.subtype (frattini P)).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (factors : XiLengthThreeTypeAFactorData
            J hJinv.restrict.range)
        (left' : FactorCoordinateData factors.left_invariant
            factors.frattini_lt_left.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu)
        (right' : FactorCoordinateData factors.right_invariant
            factors.frattini_lt_right.le
            (hJinv.restrict.rangeRestrict c)
            ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
              hPhiEA hMap).trans ePhi) nu),
        factors.left = R.subgroupOf J ∧
        factors.right = S.subgroupOf J ∧
        NormalizedFactorPairRelation n left'.theta right'.theta := by
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
  intro n c ePhi nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨factors, left', right', hleft, hright,
      -, -, -, -, hrelation⟩ :=
    exists_normalizedFactorPairRelation_with_witnesses_on_actualPairwiseJoin_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hRinv hSinv hPhiR hPhiS hRSinf hRStop dataR dataS
      c ePhi nu hnTwo hcgen hnuPrimitive hconj
  exact ⟨factors, left', right', hleft, hright, hrelation⟩

end

end OddOrder.Higman.Suzuki2Groups
