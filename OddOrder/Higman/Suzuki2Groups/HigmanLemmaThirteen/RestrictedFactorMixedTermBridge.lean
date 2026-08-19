/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCommutators
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseSplitBCD

/-!
# Higman's Lemma 13: restricted mixed terms in the ambient Frattini square

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For a restricted length-three subgroup `S`, Lemma 12 computes the mixed
commutator of its complementary factors in the internal Frattini coordinate.
The left factor is the actual subgroup `Φ(P) ≤ S`.  This file identifies that
mixed term with the ambient square-valued bracket
`Φ(P)/Φ(P)² × P/Φ(P) → Φ(P)²`, using the common middle coordinate on the left
and the natural ambient inclusion of the right factor on the right.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

local instance restrictedFactorMixedTermLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance restrictedFactorMixedTermLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance restrictedFactorMixedTermLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 92), restricted mixed-term bridge.**

After transporting the left restricted-factor coordinate through the common
middle coordinate and the right coordinate through the natural map
`L₀(S) → L₀(P)`, the actual ambient `Φ(P)²`-valued commutator has exactly the
same field coordinate as Lemma 12's internal mixed term. -/
theorem restrictedFactorMixedTerm_eq_frattiniSquareCommutator
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heS :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eS = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare)
    {nu : GaloisField 2 n}
    (c : Y)
    (factors : XiLengthThreeTypeAFactorData S hSinv.restrict.range)
    (left :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.left_invariant
        factors.frattini_lt_left.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (right :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.right_invariant
        factors.frattini_lt_right.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hleft : factors.left = (frattini P).subgroupOf S)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0))
    (alpha beta : GaloisField 2 n) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    eSquare
        (frattiniSquareCommutatorBilinear hP hxi hPhiComm hfour hexists
          ((frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare).symm
            alpha)
          (restrictedFactorAmbientInclusion hSinv hEAS eS c right
            hK1S htermS hSqS hAgemoS hK0S beta)) =
      mixedTermBilinear
        (left.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S)
        (right.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S)
        alpha beta := by
  classical
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : CommGroup (frattini S) := inferInstance
  let : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  have heS' : eS =
      (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare := heS
  have heS_apply (v : Additive (frattini S)) :
      eS v = eSquare
        (restrictedFrattiniLinearEquivFrattiniSquare
          hEAS hSquareEA hMap v) := by
    rw [heS']
    rfl
  have hleftComm : IsMulCommutative factors.left := by
    rw [hleft]
    refine IsMulCommutative.of_comm fun a b => ?_
    let aPhi : frattini P := ⟨((a : S) : P), a.property⟩
    let bPhi : frattini P := ⟨((b : S) : P), b.property⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((aPhi * bPhi : frattini P) : P) =
      ((bPhi * aPhi : frattini P) : P)
    exact congrArg Subtype.val (hPhiComm.is_comm.comm aPhi bPhi)
  cases left with
  | noncommutative hncomm d => exact (hncomm hleftComm).elim
  | commutative d =>
      have := d.fintypeIndex
      obtain ⟨gL, hgL⟩ :=
        QuotientGroup.mk_surjective (d.eQuot.symm alpha).toMul
      have halpha : alpha =
          d.eQuot (Additive.ofMul (QuotientGroup.mk gL)) := by
        rw [hgL]
        exact (d.eQuot.apply_symm_apply alpha).symm
      have hgLPhi :
          (((factors.left.subtype gL : S) : P)) ∈ frattini P := by
        have hg : factors.left.subtype gL ∈
            (frattini P).subgroupOf S := by
          rw [← hleft]
          exact gL.property
        exact hg
      let z : frattini P :=
        ⟨((factors.left.subtype gL : S) : P), hgLPhi⟩
      have hcoord :
          frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
              (Additive.ofMul (QuotientGroup.mk z)) = alpha := by
        rw [frattiniMiddleCoordinate_mk, halpha, d.eQuot_eq, d.eKernel_eq,
          heS_apply]
        congr 3
      have hmiddle :
          (frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare).symm
              alpha = Additive.ofMul (QuotientGroup.mk z) := by
        apply (frattiniMiddleCoordinate
          hP hxi hPhiComm hfour hexists eSquare).injective
        simp only [LinearEquiv.apply_symm_apply]
        exact hcoord.symm
      let L :=
        (FactorCoordinateData.commutative d).toInclusionData
          hEAS eS hK1S htermS hSqS hAgemoS hK0S
      let R := right.toInclusionData
        hEAS eS hK1S htermS hSqS hAgemoS hK0S
      let xS : lowerCentralTerm S 0 :=
        ambientTermZeroHom factors.left.subtype gL
      have hLincl : L.incl alpha = layerZeroClass xS := by
        change commFactorInclusion d hK0S alpha = layerZeroClass xS
        rw [halpha]
        exact commFactorInclusion_eQuot_mk d hK0S gL
      let := R.group
      let := R.normal
      let := R.quotComm
      let := R.quotModule
      obtain ⟨gR, hgR⟩ :=
        QuotientGroup.mk'_surjective R.N (R.eQuot.symm beta).toMul
      have hbeta : beta =
          R.eQuot (Additive.ofMul (QuotientGroup.mk' R.N gR)) := by
        rw [hgR]
        exact (R.eQuot.apply_symm_apply beta).symm
      let yS : lowerCentralTerm S 0 := ambientTermZeroHom R.f gR
      have hRincl : R.incl beta = layerZeroClass yS := by
        rw [hbeta]
        exact factorInclusion_eQuot_mk R.f hK0S R.hf R.eQuot gR
      have hRambient :
          restrictedFactorAmbientInclusion hSinv hEAS eS c right
              hK1S htermS hSqS hAgemoS hK0S beta =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom S yS)) := by
        change subgroupLowerCentralLayerZeroLinear S (R.incl beta) = _
        rw [hRincl]
        exact subgroupLowerCentralLayerZeroLinear_mk S yS
      rw [hmiddle, hRambient, frattiniSquareCommutatorBilinear_mk,
        mixedTermBilinear_apply, hLincl, hRincl]
      unfold layerZeroClass
      rw [lowerCentralCommutatorBilinear_mk]
      rw [heS']
      change eSquare _ = eSquare
        (restrictedFrattiniLinearEquivFrattiniSquare
          hEAS hSquareEA hMap
          (ambientLayerOneLinearEquivFrattini hEAS hK1S htermS
            (Additive.ofMul (lowerCentralCommutatorValue S xS yS))))
      apply congrArg eSquare
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl

/-- **Higman Lemma 13 (p. 92), bundled restricted mixed-term bridge.**

The ambient square-valued commutator, precomposed with the common middle
coordinate and the right restricted-factor inclusion and postcomposed with
the common square coordinate, is Lemma 12's internal mixed bilinear map. -/
theorem restrictedFactorMixedTerm_bilinear_eq_frattiniSquareCommutator
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heS :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eS = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare)
    {nu : GaloisField 2 n}
    (c : Y)
    (factors : XiLengthThreeTypeAFactorData S hSinv.restrict.range)
    (left :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.left_invariant
        factors.frattini_lt_left.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (right :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.right_invariant
        factors.frattini_lt_right.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hleft : factors.left = (frattini P).subgroupOf S)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    ((frattiniSquareCommutatorBilinear hP hxi hPhiComm hfour hexists).compl₁₂
        (frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists
          eSquare).symm.toLinearMap
        (restrictedFactorAmbientInclusion hSinv hEAS eS c right
          hK1S htermS hSqS hAgemoS hK0S)).compr₂ eSquare.toLinearMap =
      mixedTermBilinear
        (left.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S)
        (right.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S) := by
  classical
  dsimp only
  apply LinearMap.ext
  intro alpha
  apply LinearMap.ext
  intro beta
  exact restrictedFactorMixedTerm_eq_frattiniSquareCommutator
    hP hxi hPhiComm hfour hexists hSinv hEAS hMap eSquare eS heS c
    factors left right hleft hK1S htermS hSqS hAgemoS hK0S alpha beta

end OddOrder.Higman.Suzuki2Groups
