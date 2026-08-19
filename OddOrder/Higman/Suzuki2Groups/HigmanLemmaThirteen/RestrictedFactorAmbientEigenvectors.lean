/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedLayerZeroTransport

/-!
# Higman's Lemma 13: ambient eigenvectors of a restricted factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

Inside a restricted length-three subgroup `S`, Lemma 12 supplies genuine
factor inclusions into `L₀(S)`.  This file composes one such inclusion with the
natural map `L₀(S) → L₀(P)`, proves that its actor eigenvalue is unchanged, and
constructs the corresponding Frobenius-conjugate eigenfamily after scalar
extension.  The family span contains every ground tensor coming from the
factor, both in field coordinates and as an actual group element.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative TensorProduct

universe uP

local instance restrictedFactorAmbientEigenvectorsLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance restrictedFactorAmbientEigenvectorsLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance
    restrictedFactorAmbientEigenvectorsLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- A restricted factor's genuine inclusion into `L₀(S)`, followed by the
natural denominator-respecting map `L₀(S) → L₀(P)`. -/
noncomputable def restrictedFactorAmbientInclusion
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    {n : Nat}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {T : Subgroup S}
    {hTinv : IsAInvariant hSinv.restrict.range.subtype T}
    {hPhiT : frattini S ≤ T}
    (c : Y)
    (data :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData hTinv hPhiT
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    GaloisField 2 n →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) := by
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  exact (subgroupLowerCentralLayerZeroLinear S).comp
    (data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S).incl

/-- The ambient restricted-factor inclusion retains the ground eigenvalue
`data.lambda` of the original inclusion inside `L₀(S)`. -/
theorem restrictedFactorAmbientInclusion_representation
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    {n : Nat}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {T : Subgroup S}
    {hTinv : IsAInvariant hSinv.restrict.range.subtype T}
    {hPhiT : frattini S ≤ T}
    (c : Y)
    (data :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData hTinv hPhiT
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0))
    (alpha : GaloisField 2 n) :
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    lowerCentralLayerRepresentation Y.subtype 0 c
        (restrictedFactorAmbientInclusion hSinv hEAS eS c data
          hK1S htermS hSqS hAgemoS hK0S alpha) =
      restrictedFactorAmbientInclusion hSinv hEAS eS c data
        hK1S htermS hSqS hAgemoS hK0S (data.lambda • alpha) := by
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  rw [restrictedFactorAmbientInclusion,
    LinearMap.comp_apply, LinearMap.comp_apply,
    ← subgroupLowerCentralLayerZeroLinear_equivariant hSinv c]
  apply congrArg (subgroupLowerCentralLayerZeroLinear S)
  change
    lowerCentralLayerRepresentation hSinv.restrict.range.subtype 0
        (hSinv.restrict.rangeRestrict c)
          ((data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS
            hK0S).incl alpha) =
      (data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS
        hK0S).incl (data.lambda • alpha)
  exact FactorCoordinateData.toInclusionData_incl_representation
    hEAS eS data hK1S htermS hSqS hAgemoS hK0S alpha

/-- **Higman Lemma 13 (pp. 92–93), restricted-factor eigenfamily.**

A restricted factor supplies a Frobenius-conjugate ambient eigenfamily.
Its span contains every field-coordinate ground tensor and every ground tensor
represented by an actual element of the factor. -/
theorem exists_restrictedFactorAmbientEigenFamily
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    {n : Nat}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {T : Subgroup S}
    {hTinv : IsAInvariant hSinv.restrict.range.subtype T}
    {hPhiT : frattini S ≤ T}
    (c : Y)
    (data :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData hTinv hPhiT
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    ∃ family : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
        GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
        data.lambda ^ (2 ^ i.val) • family i) ∧
      (∀ alpha : GaloisField 2 n,
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            restrictedFactorAmbientInclusion hSinv hEAS eS c data
              hK1S htermS hSqS hAgemoS hK0S alpha ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) ∧
      (∀ (x : lowerCentralTerm S 0), (x : S) ∈ T →
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom S x)) ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) := by
  classical
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  let eRefl := LinearEquiv.refl (ZMod 2) (GaloisField 2 n)
  let d := data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  let iota := restrictedFactorAmbientInclusion hSinv hEAS eS c data
    hK1S htermS hSqS hAgemoS hK0S
  let Aq : Module.End (ZMod 2) (GaloisField 2 n) :=
    Algebra.lmul (ZMod 2) (GaloisField 2 n) data.lambda
  have hAq : ∀ v, eRefl (Aq v) = data.lambda * eRefl v := by
    intro v
    rfl
  have hiota : ∀ v, iota (Aq v) =
      lowerCentralLayerRepresentation Y.subtype 0 c (iota v) := by
    intro v
    rw [show Aq v = data.lambda • v by rfl]
    exact (restrictedFactorAmbientInclusion_representation
      hSinv hEAS eS c data hK1S htermS hSqS hAgemoS hK0S v).symm
  let family := factorAmbientEigenFamily eRefl iota
  refine ⟨family, ?_, ?_, ?_⟩
  · intro i
    exact factorAmbientEigenFamily_eigen c eRefl Aq data.lambda hAq
      iota hiota i
  · intro alpha
    exact one_tmul_mem_span_factorAmbientEigenFamily eRefl iota alpha
  · intro x hx
    obtain ⟨alpha, halpha⟩ := d.exists_incl_eq x hx
    have hiotaClass : iota alpha =
        Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
            (subgroupLowerCentralTermZeroHom S x)) := by
      change subgroupLowerCentralLayerZeroLinear S (d.incl alpha) = _
      rw [halpha]
      exact subgroupLowerCentralLayerZeroLinear_mk S x
    rw [← hiotaClass]
    exact one_tmul_mem_span_factorAmbientEigenFamily eRefl iota alpha

end OddOrder.Higman.Suzuki2Groups
