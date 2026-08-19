/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseSplitBCD

/-!
# Higman Lemma 13: pairwise mixed terms as ambient commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, Higman's Lemma 12 computes the mixed term of two
actual factors inside their pairwise join `J`.  The intrinsic Frattini
coordinate on `J` was obtained by transporting one fixed coordinate on the
ambient `Φ(P)`.  This file records that the mixed term is therefore exactly
the common ambient coordinate of the commutator of representatives in `P`.

The final representative form retains membership in the two actual factors.
It is the bridge needed to turn the coordinate support cancellation in
Lemma 13 into a subgroup commuting with the third factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance pairwiseMixedTermBridgeLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance pairwiseMixedTermBridgeLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance pairwiseMixedTermBridgeLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- A commutator in a pairwise join lies in the actual ambient Frattini
subgroup once the intrinsic Frattini subgroup maps onto `Φ(P)`. -/
theorem pairwiseJoin_commutator_mem_ambientFrattini
    {P : Type uP} [Group P]
    {J : Subgroup P}
    (hMap : (frattini J).map J.subtype = frattini P)
    (htermJ : lowerCentralTerm J 1 = frattini J)
    (x y : lowerCentralTerm J 0) :
    ⁅((x : J) : P), ((y : J) : P)⁆ ∈ frattini P := by
  have hxyJ : ⁅(x : J), (y : J)⁆ ∈ frattini J := by
    rw [← htermJ]
    exact (lowerCentralCommutator J x y).property
  rw [← hMap]
  refine ⟨⁅(x : J), (y : J)⁆, hxyJ, ?_⟩
  exact map_commutatorElement J.subtype (x : J) (y : J)

/-- **Higman Lemma 13 (p. 93), pairwise mixed-term ambient bridge.**

If `x` and `y` represent the two field coordinates in the zeroth
lower-central layer of a pairwise join, then Lemma 12's intrinsic mixed term
is the fixed ambient `Φ(P)`-coordinate of their genuine commutator in `P`. -/
theorem pairwiseJoinMixedTerm_eq_ambientFrattiniCommutator
    {P : Type uP} [Group P]
    {J : Subgroup P} [Finite J]
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P)
    {n : Nat}
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n) :
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
    ∀ (hK1J : lowerCentralLayerKernel J 1 = ⊥)
      (htermJ : lowerCentralTerm J 1 = frattini J)
      (hSqJ : LowerCentralSquaresLieInSecond J)
      (hK0J : lowerCentralLayerKernel J 0 =
        (frattini J).subgroupOf (lowerCentralTerm J 0))
      {Sl Sr : Subgroup J}
      (L : FactorInclusionData Sl hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (R : FactorInclusionData Sr hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (alpha beta : GaloisField 2 n)
      (x y : lowerCentralTerm J 0),
      L.incl alpha = layerZeroClass x →
      R.incl beta = layerZeroClass y →
      mixedTermBilinear L R alpha beta =
        ePhi (Additive.ofMul
          ⟨⁅((x : J) : P), ((y : J) : P)⁆,
            pairwiseJoin_commutator_mem_ambientFrattini
              hMap htermJ x y⟩) := by
  classical
  dsimp only
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
  intro hK1J htermJ hSqJ hK0J Sl Sr L R alpha beta x y hL hR
  rw [mixedTermBilinear_apply, hL, hR]
  unfold layerZeroClass
  rw [lowerCentralCommutatorBilinear_mk]
  change ePhi
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini hPhiEA hMap
        (ambientLayerOneLinearEquivFrattini hJoinEA hK1J htermJ
          (Additive.ofMul (lowerCentralCommutatorValue J x y)))) =
    ePhi (Additive.ofMul
      ⟨⁅((x : J) : P), ((y : J) : P)⁆,
        pairwiseJoin_commutator_mem_ambientFrattini hMap htermJ x y⟩)
  apply congrArg ePhi
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- **Higman Lemma 13 (p. 93), actual pairwise representatives.**

Every pair of field coordinates has representatives in the two actual
factors of the pairwise join, and their mixed term is the ambient Frattini
coordinate of the commutator of those representatives. -/
theorem exists_pairwiseJoinRepresentatives_mixedTerm_eq_ambientFrattiniCommutator
    {P : Type uP} [Group P]
    {J : Subgroup P} [Finite J]
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P)
    {n : Nat}
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n) :
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
    ∀ (hK1J : lowerCentralLayerKernel J 1 = ⊥)
      (htermJ : lowerCentralTerm J 1 = frattini J)
      (hSqJ : LowerCentralSquaresLieInSecond J)
      (hK0J : lowerCentralLayerKernel J 0 =
        (frattini J).subgroupOf (lowerCentralTerm J 0))
      {Sl Sr : Subgroup J}
      (L : FactorInclusionData Sl hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (R : FactorInclusionData Sr hJoinEA
        ((pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap).trans ePhi)
        hK1J htermJ hSqJ hK0J)
      (alpha beta : GaloisField 2 n),
      ∃ x y : lowerCentralTerm J 0,
        (x : J) ∈ Sl ∧
        (y : J) ∈ Sr ∧
        L.incl alpha = layerZeroClass x ∧
        R.incl beta = layerZeroClass y ∧
        mixedTermBilinear L R alpha beta =
          ePhi (Additive.ofMul
            ⟨⁅((x : J) : P), ((y : J) : P)⁆,
              pairwiseJoin_commutator_mem_ambientFrattini
                hMap htermJ x y⟩) := by
  classical
  dsimp only
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
  intro hK1J htermJ hSqJ hK0J Sl Sr L R alpha beta
  let := L.group
  let := L.normal
  let := L.quotComm
  let := L.quotModule
  let := R.group
  let := R.normal
  let := R.quotComm
  let := R.quotModule
  have hAlphaRange : L.incl alpha ∈
      LinearMap.range (factorInclusion L.f hK0J L.hf L.eQuot) :=
    ⟨alpha, rfl⟩
  obtain ⟨x, hxRange, hxLayer⟩ :=
    (factorInclusion_range_eq
      L.f hK0J L.hf L.eQuot (L.incl alpha)).mp hAlphaRange
  have hBetaRange : R.incl beta ∈
      LinearMap.range (factorInclusion R.f hK0J R.hf R.eQuot) :=
    ⟨beta, rfl⟩
  obtain ⟨y, hyRange, hyLayer⟩ :=
    (factorInclusion_range_eq
      R.f hK0J R.hf R.eQuot (R.incl beta)).mp hBetaRange
  rw [L.range_eq] at hxRange
  rw [R.range_eq] at hyRange
  refine ⟨x, y, hxRange, hyRange, hxLayer.symm, hyLayer.symm, ?_⟩
  exact pairwiseJoinMixedTerm_eq_ambientFrattiniCommutator
    hPhiEA hMap ePhi hK1J htermJ hSqJ hK0J
    L R alpha beta x y hxLayer.symm hyLayer.symm

end OddOrder.Higman.Suzuki2Groups
