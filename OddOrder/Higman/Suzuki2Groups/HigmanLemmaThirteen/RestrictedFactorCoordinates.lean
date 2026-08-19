/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFrattiniCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates

/-!
# Higman's Lemma 13: coordinates on a restricted factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The common Singer coordinate on `Φ(P)²` is transported to the internal
Frattini subgroup of a restricted length-three factor.  The prescribed-factor
form of Lemma 12 can then choose both of its length-two factors over that same
coordinate.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- Transporting the common Singer coordinate through the restricted
Frattini equivalence preserves its scalar normal form. -/
theorem restrictedFrattiniSingerCoordinate_conj
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hFrattiniEA : IsElementaryAbelian 2 (frattini S))
    (hSquareEA : IsElementaryAbelian 2 (frattiniSquare P))
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    {n : Nat}
    (c : Y)
    (eSquare :
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
    (hconj :
      let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
        (frattiniSquareNormalInvariant Y.subtype).2.2
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eSquare.conj (elabRepresentation 2 hSquareInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu) :
    let hFrattiniInv :
        IsAInvariant hSinv.restrict.range.subtype (frattini S) :=
      IsAInvariant.of_characteristic hSinv.restrict.range.subtype
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hFrattiniEA.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hFrattiniEA.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    let cS : hSinv.restrict.range := hSinv.restrict.rangeRestrict c
    let eFrattini :=
      (restrictedFrattiniLinearEquivFrattiniSquare
        hFrattiniEA hSquareEA hMap).trans eSquare
    eFrattini.conj
        (elabRepresentation 2 hFrattiniInv.restrict cS) =
      Algebra.lmul (ZMod 2) (GaloisField 2 n) nu := by
  classical
  dsimp only
  let hFrattiniInvY : IsAInvariant hSinv.restrict (frattini S) :=
    IsAInvariant.of_characteristic hSinv.restrict
  let hFrattiniInv :
      IsAInvariant hSinv.restrict.range.subtype (frattini S) :=
    IsAInvariant.of_characteristic hSinv.restrict.range.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hFrattiniEA.comm
  let : CommGroup (frattini S) := inferInstance
  let : Module (ZMod 2) (Additive (frattini S)) :=
    hFrattiniEA.zmodModule
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let E := restrictedFrattiniLinearEquivFrattiniSquare
    hFrattiniEA hSquareEA hMap
  let cS : hSinv.restrict.range := hSinv.restrict.rangeRestrict c
  let eFrattini := E.trans eSquare
  have hSquareCompat : ∀ w,
      eSquare (elabRepresentation 2 hSquareInv.restrict c w) =
        nu * eSquare w := by
    intro w
    have h := DFunLike.congr_fun hconj (eSquare w)
    simpa [LinearEquiv.conj_apply] using h
  have hFrattiniCompat : ∀ v,
      eFrattini (elabRepresentation 2 hFrattiniInv.restrict cS v) =
        nu * eFrattini v := by
    intro v
    have hRangeAction :
        elabRepresentation 2 hFrattiniInv.restrict cS v =
          elabRepresentation 2 hFrattiniInvY.restrict c v := by
      apply Additive.toMul.injective
      change hFrattiniInv.restrict cS v.toMul =
        hFrattiniInvY.restrict c v.toMul
      apply Subtype.ext
      simp [cS, IsAInvariant.restrict_apply_val]
    change eSquare
        (E (elabRepresentation 2 hFrattiniInv.restrict cS v)) =
      nu * eSquare (E v)
    rw [hRangeAction, show E
        (elabRepresentation 2 hFrattiniInvY.restrict c v) =
        elabRepresentation 2 hSquareInv.restrict c (E v) by
      simpa [E] using
        restrictedFrattiniLinearEquivFrattiniSquare_equivariant
          hSinv hFrattiniEA hSquareEA hMap c v]
    exact hSquareCompat _
  apply LinearMap.ext
  intro beta
  change eFrattini
      (elabRepresentation 2 hFrattiniInv.restrict cS
        (eFrattini.symm beta)) = nu * beta
  rw [hFrattiniCompat]
  simp

/-- **Higman Lemma 13 (p. 92), factor coordinates over the common
`Φ(P)²` Singer datum.**

For one restricted length-three factor `S`, retain the actual subgroup
`Φ(P) ≤ S` as the left length-two factor.  Both complementary factor
coordinates use the restricted image of the same ambient generator, the
coordinate transported from `Φ(P)²`, and the same primitive scalar.  The
left factor is commutative, so its field automorphism is the identity and
its source equation is `ν = λ²`. -/
theorem exists_restrictedFactorPairCoordinates_of_frattiniSquareSinger
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
        nu = right.lambda * right.theta right.lambda := by
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
  let hMap : (frattini S).map S.subtype = frattiniSquare P :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
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
  let hPhiInvS : IsAInvariant hSinv.restrict.range.subtype
      (frattini S) :=
    IsAInvariant.of_characteristic hSinv.restrict.range.subtype
  let E := restrictedFrattiniLinearEquivFrattiniSquare
    hEAS hSquareEA hMap
  let eS := E.trans eSquare
  let cS : hSinv.restrict.range := hSinv.restrict.rangeRestrict c
  have hconjS : eS.conj
      (elabRepresentation 2 hPhiInvS.restrict cS) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu :=
    restrictedFrattiniSingerCoordinate_conj
      hSinv hEAS hSquareEA hMap c eSquare nu hconj
  have hcgenS : ∀ g : hSinv.restrict.range,
      g ∈ Subgroup.zpowers cS :=
    forall_mem_zpowers_restrictedRange_generator hSinv c hcgen
  let A : Subgroup S := (frattini P).subgroupOf S
  have hAmap : A.map S.subtype = frattini P :=
    Subgroup.map_subgroupOf_eq_of_le hPhiS.le
  have hPhiA : frattini S < A := by
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective,
      hMap, hAmap]
    exact frattiniSquare_lt_frattini hPhiComm hfour hexists
  have hAtop : A < (⊤ : Subgroup S) := by
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective,
      hAmap]
    simpa [← MonoidHom.range_eq_map] using hPhiS.lt
  have hAY : IsAInvariant hSinv.restrict A :=
    hSinv.subgroupOf (IsAInvariant.of_characteristic Y.subtype)
  have hArange : IsAInvariant hSinv.restrict.range.subtype A :=
    (isAInvariant_range_subtype_iff hSinv.restrict A).2 hAY
  have hAcomm : IsMulCommutative A := by
    refine IsMulCommutative.of_comm fun a b => ?_
    let aPhi : frattini P := ⟨((a : S) : P), a.property⟩
    let bPhi : frattini P := ⟨((b : S) : P), b.property⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((aPhi * bPhi : frattini P) : P) =
      ((bPhi * aPhi : frattini P) : P)
    exact congrArg Subtype.val (hPhiComm.is_comm.comm aPhi bPhi)
  obtain ⟨factors, hleft⟩ :=
    xiLengthThreeTypeAFactorData_exists_with_left
      (P := S) (Y := hSinv.restrict.range)
      (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
      hArange hPhiA hAtop
  obtain ⟨left⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      (P := S) (Y := hSinv.restrict.range)
      (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
      factors.left_invariant factors.frattini_lt_left
      factors.left_lt_top cS eS nu hnTwo hcgenS hnuPrimitive hconjS
  obtain ⟨right⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      (P := S) (Y := hSinv.restrict.range)
      (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
      factors.right_invariant factors.frattini_lt_right
      factors.right_lt_top cS eS nu hnTwo hcgenS hnuPrimitive hconjS
  have hleftComm : IsMulCommutative factors.left := by
    rw [hleft]
    exact hAcomm
  have hleftTheta : left.theta = 1 := by
    cases left with
    | commutative _ => rfl
    | noncommutative hleftNcomm _ =>
        exact (hleftNcomm hleftComm).elim
  have hleftSource : nu = left.lambda * left.lambda := by
    calc
      nu = left.lambda * left.theta left.lambda :=
        left.kernel_eigenvalue_eq
      _ = left.lambda * left.lambda := by simp [hleftTheta]
  exact ⟨factors, left, right, hleft, hleftTheta, hleftSource,
    right.kernel_eigenvalue_eq⟩

end OddOrder.Higman.Suzuki2Groups
