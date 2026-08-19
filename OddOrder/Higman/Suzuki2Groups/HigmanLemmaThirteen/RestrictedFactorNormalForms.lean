/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch

/-!
# Higman's Lemma 13: normalized restricted-factor coordinates

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The outer length-two factor inside a restricted length-three factor is put
in Higman's Frobenius half-range normalization.  The coordinate flip changes
only the quotient coordinate, so the common generator, the transported
`Φ(P)²` kernel coordinate, and the primitive scalar stay fixed.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (p. 92), normalized coordinates on one restricted
factor.**

The prescribed left factor is the actual `Φ(P) ≤ S` and has identity
automorphism.  The complementary right factor is either commutative or has
automorphism `Frob^r` with `0 < r ≤ n/2`.  All data remain indexed by the
same restricted Singer generator, transported common-square coordinate, and
primitive scalar. -/
theorem
    exists_normalizedRestrictedFactorPairCoordinates_of_frattiniSquareSinger
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S) :
    let hSneBot : S ≠ (⊥ : Subgroup P) :=
      ne_of_gt (lt_of_le_of_lt bot_le hPhiS.lt)
    let hinvS : involutions P ⊆ S :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hSinv hSneBot
    let hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi hSinv
    let hmultiS : ∃ x y : S,
        x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvS hmulti
    let hprimeS : ∀ p : Nat, p.Prime →
        p ∣ Nat.card hSinv.restrict.range →
          p ∣ (involutions S).ncard :=
      restricted_range_primeSupport hSinv hinvS hprime
    let hEAS : IsElementaryAbelian 2 (frattini S) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
    let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    let hMap : (frattini S).map S.subtype = frattiniSquare P :=
      frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
        hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hEAS.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (eSquare : Additive (frattiniSquare P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      eSquare.conj
          (elabRepresentation 2
            ((frattiniSquareNormalInvariant Y.subtype).2.2).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (factors : XiLengthThreeTypeAFactorData
          S hSinv.restrict.range)
        (left : FactorCoordinateData factors.left_invariant
          factors.frattini_lt_left.le
          (hSinv.restrict.rangeRestrict c)
          ((restrictedFrattiniLinearEquivFrattiniSquare
            hEAS hSquareEA hMap).trans eSquare) nu)
        (right : FactorCoordinateData factors.right_invariant
          factors.frattini_lt_right.le
          (hSinv.restrict.rangeRestrict c)
          ((restrictedFrattiniLinearEquivFrattiniSquare
            hEAS hSquareEA hMap).trans eSquare) nu),
        factors.left = (frattini P).subgroupOf S ∧
        left.theta = 1 ∧
        nu = left.lambda * left.lambda ∧
        nu = right.lambda * right.theta right.lambda ∧
        (right.theta = 1 ∨
          ∃ r : Nat, 0 < r ∧ 2 * r ≤ n ∧
            right.theta =
              frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
            Odd (orderOf right.theta)) := by
  classical
  dsimp only
  let hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS.lt)
  let hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  let hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  let hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  let hprimeS : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  let hEAS : IsElementaryAbelian 2 (frattini S) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
  let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : CommGroup (frattini S) := inferInstance
  let : Module (ZMod 2) (Additive (frattini S)) :=
    hEAS.zmodModule
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro n c eSquare nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨factors, left, right, hleft, hleftTheta, hleftSource,
      hrightSource⟩ :=
    exists_restrictedFactorPairCoordinates_of_frattiniSquareSinger
      hP hmulti hxi hprime hPhiComm hfour hexists
      hSinv hPhiS hlenS hncommS c eSquare nu hnTwo hcgen
      hnuPrimitive hconj
  have hn0 : n ≠ 0 := by omega
  obtain ⟨right', hrightSource', hrightCase⟩ :=
    right.exists_normalized_frobenius_le_half hn0
  exact ⟨factors, left, right', hleft, hleftTheta, hleftSource,
    hrightSource', hrightCase⟩

end OddOrder.Higman.Suzuki2Groups
