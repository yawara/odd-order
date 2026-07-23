/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman Lemma 13: faithful inclusion of a pairwise factor into the ambient layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, the intrinsic Frattini subgroup of every pairwise
join maps onto the same ambient subgroup `Φ(P)`.  Since the zeroth
lower-central denominator of a finite `2`-group is its Frattini subgroup, the
natural map `L₀(J) → L₀(P)` is injective for such a join.

Consequently, composing a genuine Lemma 12 factor inclusion with this natural
map does not identify distinct field coordinates.  This is the first
cross-join compatibility needed to compare one actual factor in two pairwise
joins.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

local instance commonFactorAmbientLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance commonFactorAmbientLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance commonFactorAmbientLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), faithful pairwise-layer inclusion.**

For an ambient finite `2`-group, if the intrinsic Frattini subgroup of `J`
maps onto `Φ(P)`, then the natural map `L₀(J) → L₀(P)` is injective. -/
theorem subgroupLowerCentralLayerZeroLinear_injective_of_frattini_map_eq
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (J : Subgroup P)
    (hMap : (frattini J).map J.subtype = frattini P) :
    Function.Injective (subgroupLowerCentralLayerZeroLinear J) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective
      (lowerCentralLayerKernel J 0) v.toMul
  have hvEq :
      v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel J 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  rw [hvEq, subgroupLowerCentralLayerZeroLinear_mk] at hv
  have hxKernelP :
      subgroupLowerCentralTermZeroHom J x ∈
        lowerCentralLayerKernel P 0 := by
    exact (QuotientGroup.eq_one_iff _).mp (ofMul_eq_zero.mp hv)
  have hxPhiP : ((x : J) : P) ∈ frattini P := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0] at hxKernelP
    change ((x : J) : P) ∈
      lowerCentralLayerKernelInAmbient P 0 at hxKernelP
    rwa [lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP] at hxKernelP
  have hxPhiJ : (x : J) ∈ frattini J := by
    apply (Subgroup.mem_map_iff_mem J.subtype_injective).mp
    rw [hMap]
    exact hxPhiP
  have hxKernelJ : x ∈ lowerCentralLayerKernel J 0 := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf J 0]
    change (x : J) ∈ lowerCentralLayerKernelInAmbient J 0
    rw [lowerCentralLayerKernelInAmbient_zero_eq_frattini
      J (hP.to_subgroup J)]
    exact hxPhiJ
  rw [hvEq]
  exact ofMul_eq_zero.mpr
    ((QuotientGroup.eq_one_iff _).mpr hxKernelJ)

/-- **Higman Lemma 13 (p. 93), faithful ambient factor coordinate.**

A Lemma 12 factor coordinate is injective in the pairwise join, and remains
injective after transport to `L₀(P)` whenever the pairwise Frattini subgroup
maps onto the ambient one. -/
theorem restrictedFactorAmbientInclusion_injective_of_frattini_map_eq
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hMap : (frattini S).map S.subtype = frattini P)
    {n : Nat}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) :=
        hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {T : Subgroup S}
    {hTinv : IsAInvariant hSinv.restrict.range.subtype T}
    {hPhiT : frattini S ≤ T}
    (c : Y)
    (data :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) :=
        hEAS.zmodModule
      FactorCoordinateData hTinv hPhiT
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    Function.Injective
      (restrictedFactorAmbientInclusion hSinv hEAS eS c data
        hK1S htermS hSqS hAgemoS hK0S) := by
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : CommGroup (frattini S) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini S)) :=
    hEAS.zmodModule
  let d :=
    data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  letI := d.group
  letI := d.normal
  letI := d.quotComm
  letI := d.quotModule
  have hd : Function.Injective d.incl := by
    exact factorInclusion_injective
      d.f hK0S d.hf d.eQuot d.hfexact
  have hsub :
      Function.Injective (subgroupLowerCentralLayerZeroLinear S) :=
    subgroupLowerCentralLayerZeroLinear_injective_of_frattini_map_eq
      hP S hMap
  intro alpha beta hab
  apply hd
  apply hsub
  exact hab

end OddOrder.Higman.Suzuki2Groups
