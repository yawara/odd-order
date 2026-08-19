/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman Lemma 13: the ambient range of one common pairwise factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

One actual factor `W ≤ P` occurs in two different pairwise joins.  Lemma 12
may equip its two `subgroupOf` copies with different field coordinates, but
both restricted factor inclusions have the same image in the ambient zeroth
lower-central layer.

The proof does not posit compatibility of the coordinates.  Starting with a
coordinate in one join, it recovers an actual representative in the
prescribed factor, regards the same ambient element as an element of the
other join, and then uses the second factor coordinate's surjectivity onto
that prescribed factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

local instance commonFactorRangeLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance commonFactorRangeLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance commonFactorRangeLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), common-factor ambient range.**

If prescribed factors in two pairwise joins are the two `subgroupOf` copies
of one actual ambient factor `W`, then their genuine Lemma 12 inclusions have
the same range after transport to `L₀(P)`. -/
theorem restrictedFactorAmbientInclusion_range_eq_of_common_factor
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {W J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hWJ : W ≤ J)
    (hWK : W ≤ K)
    {n : Nat}
    (hEAJ : IsElementaryAbelian 2 (frattini J))
    (eJ :
      letI : IsMulCommutative (frattini J) :=
        IsMulCommutative.of_comm hEAJ.comm
      letI : Module (ZMod 2) (Additive (frattini J)) :=
        hEAJ.zmodModule
      Additive (frattini J) ≃ₗ[ZMod 2] GaloisField 2 n)
    (hEAK : IsElementaryAbelian 2 (frattini K))
    (eK :
      letI : IsMulCommutative (frattini K) :=
        IsMulCommutative.of_comm hEAK.comm
      letI : Module (ZMod 2) (Additive (frattini K)) :=
        hEAK.zmodModule
      Additive (frattini K) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {FJ : Subgroup J}
    {FK : Subgroup K}
    {hFJinv : IsAInvariant hJinv.restrict.range.subtype FJ}
    {hFKinv : IsAInvariant hKinv.restrict.range.subtype FK}
    {hPhiFJ : frattini J ≤ FJ}
    {hPhiFK : frattini K ≤ FK}
    (c : Y)
    (dataJ :
      letI : IsMulCommutative (frattini J) :=
        IsMulCommutative.of_comm hEAJ.comm
      letI : Module (ZMod 2) (Additive (frattini J)) :=
        hEAJ.zmodModule
      FactorCoordinateData hFJinv hPhiFJ
        (hJinv.restrict.rangeRestrict c) eJ nu)
    (dataK :
      letI : IsMulCommutative (frattini K) :=
        IsMulCommutative.of_comm hEAK.comm
      letI : Module (ZMod 2) (Additive (frattini K)) :=
        hEAK.zmodModule
      FactorCoordinateData hFKinv hPhiFK
        (hKinv.restrict.rangeRestrict c) eK nu)
    (hFJ : FJ = W.subgroupOf J)
    (hFK : FK = W.subgroupOf K)
    (hK1J : lowerCentralLayerKernel J 1 = ⊥)
    (htermJ : lowerCentralTerm J 1 = frattini J)
    (hSqJ : LowerCentralSquaresLieInSecond J)
    (hAgemoJ : Agemo J 2 1 = frattini J)
    (hK0J : lowerCentralLayerKernel J 0 =
      (frattini J).subgroupOf (lowerCentralTerm J 0))
    (hK1K : lowerCentralLayerKernel K 1 = ⊥)
    (htermK : lowerCentralTerm K 1 = frattini K)
    (hSqK : LowerCentralSquaresLieInSecond K)
    (hAgemoK : Agemo K 2 1 = frattini K)
    (hK0K : lowerCentralLayerKernel K 0 =
      (frattini K).subgroupOf (lowerCentralTerm K 0)) :
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hEAJ.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hEAJ.zmodModule
    letI : IsMulCommutative (frattini K) :=
      IsMulCommutative.of_comm hEAK.comm
    letI : Module (ZMod 2) (Additive (frattini K)) :=
      hEAK.zmodModule
    LinearMap.range
        (restrictedFactorAmbientInclusion hJinv hEAJ eJ c dataJ
          hK1J htermJ hSqJ hAgemoJ hK0J) =
      LinearMap.range
        (restrictedFactorAmbientInclusion hKinv hEAK eK c dataK
          hK1K htermK hSqK hAgemoK hK0K) := by
  classical
  let : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hEAJ.comm
  let : CommGroup (frattini J) := inferInstance
  let : Module (ZMod 2) (Additive (frattini J)) :=
    hEAJ.zmodModule
  let : IsMulCommutative (frattini K) :=
    IsMulCommutative.of_comm hEAK.comm
  let : CommGroup (frattini K) := inferInstance
  let : Module (ZMod 2) (Additive (frattini K)) :=
    hEAK.zmodModule
  let dJ :=
    dataJ.toInclusionData hEAJ eJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let dK :=
    dataK.toInclusionData hEAK eK
      hK1K htermK hSqK hAgemoK hK0K
  let := dJ.group
  let := dJ.normal
  let := dJ.quotComm
  let := dJ.quotModule
  let := dK.group
  let := dK.normal
  let := dK.quotComm
  let := dK.quotModule
  let iotaJ :=
    restrictedFactorAmbientInclusion hJinv hEAJ eJ c dataJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iotaK :=
    restrictedFactorAmbientInclusion hKinv hEAK eK c dataK
      hK1K htermK hSqK hAgemoK hK0K
  apply le_antisymm
  · rintro _ ⟨alpha, rfl⟩
    have hAlphaRange : dJ.incl alpha ∈
        LinearMap.range
          (factorInclusion dJ.f hK0J dJ.hf dJ.eQuot) :=
      ⟨alpha, rfl⟩
    obtain ⟨xJ, hxJRange, hxJLayer⟩ :=
      (factorInclusion_range_eq
        dJ.f hK0J dJ.hf dJ.eQuot (dJ.incl alpha)).mp hAlphaRange
    rw [dJ.range_eq, hFJ] at hxJRange
    have hxJW : ((xJ : J) : P) ∈ W := hxJRange
    let w : W := ⟨((xJ : J) : P), hxJW⟩
    let wK : K := ⟨(w : P), hWK w.property⟩
    let xK : lowerCentralTerm K 0 :=
      ⟨wK, by simp [lowerCentralTerm]⟩
    have hxKFK : (xK : K) ∈ FK := by
      rw [hFK]
      exact w.property
    obtain ⟨beta, hBeta⟩ := dK.exists_incl_eq xK hxKFK
    refine ⟨beta, ?_⟩
    change subgroupLowerCentralLayerZeroLinear K (dK.incl beta) =
      subgroupLowerCentralLayerZeroLinear J (dJ.incl alpha)
    rw [hBeta, ← hxJLayer]
    unfold layerZeroClass
    rw [subgroupLowerCentralLayerZeroLinear_mk,
      subgroupLowerCentralLayerZeroLinear_mk]
    apply congrArg Additive.ofMul
    apply congrArg
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
    apply Subtype.ext
    rfl
  · rintro _ ⟨alpha, rfl⟩
    have hAlphaRange : dK.incl alpha ∈
        LinearMap.range
          (factorInclusion dK.f hK0K dK.hf dK.eQuot) :=
      ⟨alpha, rfl⟩
    obtain ⟨xK, hxKRange, hxKLayer⟩ :=
      (factorInclusion_range_eq
        dK.f hK0K dK.hf dK.eQuot (dK.incl alpha)).mp hAlphaRange
    rw [dK.range_eq, hFK] at hxKRange
    have hxKW : ((xK : K) : P) ∈ W := hxKRange
    let w : W := ⟨((xK : K) : P), hxKW⟩
    let wJ : J := ⟨(w : P), hWJ w.property⟩
    let xJ : lowerCentralTerm J 0 :=
      ⟨wJ, by simp [lowerCentralTerm]⟩
    have hxJFJ : (xJ : J) ∈ FJ := by
      rw [hFJ]
      exact w.property
    obtain ⟨beta, hBeta⟩ := dJ.exists_incl_eq xJ hxJFJ
    refine ⟨beta, ?_⟩
    change subgroupLowerCentralLayerZeroLinear J (dJ.incl beta) =
      subgroupLowerCentralLayerZeroLinear K (dK.incl alpha)
    rw [hBeta, ← hxKLayer]
    unfold layerZeroClass
    rw [subgroupLowerCentralLayerZeroLinear_mk,
      subgroupLowerCentralLayerZeroLinear_mk]
    apply congrArg Additive.ofMul
    apply congrArg
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
    apply Subtype.ext
    rfl

end OddOrder.Higman.Suzuki2Groups
