/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorAmbientInclusion
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorRange
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoScalarReparameterization

/-!
# Higman Lemma 13: scalar alignment of a common pairwise factor

G. Higman, *Suzuki 2-groups*, p. 93.  One actual factor occurs in two
different pairwise joins.  Its two prescribed factor-coordinate inclusions
are faithful in the ambient zeroth lower-central layer and have the same
range.  Once their quotient eigenvalues are identified with one primitive
Singer scalar, the two ambient inclusions differ only by a nonzero scalar
reparameterization of the field coordinate.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance commonFactorScalarBridgeLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance commonFactorScalarBridgeLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance commonFactorScalarBridgeLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), scalar alignment of one common factor.**

Prescribed copies of one actual factor in two pairwise joins have ambient
factor inclusions which agree after multiplication of the second field
coordinate by one nonzero scalar. -/
theorem exists_scalar_reparameterization_of_common_factor
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)}
    {W J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hWJ : W ≤ J)
    (hWK : W ≤ K)
    (hMapJ : (frattini J).map J.subtype = frattini P)
    (hMapK : (frattini K).map K.subtype = frattini P)
    {n : Nat}
    (hn : n ≠ 0)
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
    dataJ.lambda = dataK.lambda →
    IsPrimitiveRoot dataJ.lambda (2 ^ n - 1) →
    ∃ a : GaloisField 2 n, a ≠ 0 ∧
      ∀ alpha,
        restrictedFactorAmbientInclusion hJinv hEAJ eJ c dataJ
            hK1J htermJ hSqJ hAgemoJ hK0J alpha =
          restrictedFactorAmbientInclusion hKinv hEAK eK c dataK
            hK1K htermK hSqK hAgemoK hK0K (a * alpha) := by
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
  intro hlambda hprim
  let iotaJ :=
    restrictedFactorAmbientInclusion hJinv hEAJ eJ c dataJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  let iotaK :=
    restrictedFactorAmbientInclusion hKinv hEAK eK c dataK
      hK1K htermK hSqK hAgemoK hK0K
  have hinjJ : Function.Injective iotaJ :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP hJinv hMapJ hEAJ eJ c dataJ
      hK1J htermJ hSqJ hAgemoJ hK0J
  have hinjK : Function.Injective iotaK :=
    restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
      hP hKinv hMapK hEAK eK c dataK
      hK1K htermK hSqK hAgemoK hK0K
  have hrange : LinearMap.range iotaJ = LinearMap.range iotaK :=
    restrictedFactorAmbientInclusion_range_eq_of_common_factor
      hJinv hKinv hWJ hWK hEAJ eJ hEAK eK c dataJ dataK hFJ hFK
      hK1J htermJ hSqJ hAgemoJ hK0J
      hK1K htermK hSqK hAgemoK hK0K
  let A : Module.End (ZMod 2) (Additive (lowerCentralLayer P 0)) :=
    lowerCentralLayerRepresentation Y.subtype 0 c
  have heigJ : ∀ alpha,
      A (iotaJ alpha) = iotaJ (dataJ.lambda * alpha) := by
    intro alpha
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        hJinv hEAJ eJ c dataJ
        hK1J htermJ hSqJ hAgemoJ hK0J alpha
  have heigK : ∀ alpha,
      A (iotaK alpha) = iotaK (dataJ.lambda * alpha) := by
    intro alpha
    rw [hlambda]
    simpa only [smul_eq_mul] using
      restrictedFactorAmbientInclusion_representation
        hKinv hEAK eK c dataK
        hK1K htermK hSqK hAgemoK hK0K alpha
  exact exists_scalar_reparameterization_of_equal_range
    hn dataJ.lambda hprim A iotaJ iotaK
    hinjJ hinjK hrange heigJ heigK

end

end OddOrder.Higman.Suzuki2Groups
