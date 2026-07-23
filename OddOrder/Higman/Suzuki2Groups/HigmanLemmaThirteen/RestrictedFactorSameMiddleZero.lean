/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman's Lemma 13: same-factor middle brackets after scalar extension

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

Two outer vectors coming from one restricted length-three factor have
commutator in the common subgroup `Phi(P)^2`, so their middle Frattini bracket
vanishes.  This file lifts the representative-level statement through the
natural map `L₀(S) → L₀(P)` and extension of scalars.  The final theorem is
stated directly on the canonical ambient Frobenius family used by the
type-C/C Jacobi argument.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP uF uQ

local instance restrictedFactorSameMiddleZeroLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance restrictedFactorSameMiddleZeroLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The middle bracket vanishes on the image of the restricted zeroth layer.

This is the quotient-level form of
`frattiniMiddleCommutatorBilinear_eq_zero_of_mem_restricted_factor`: arbitrary
classes of `L₀(S)` are represented by elements of `S`, and their images in
`L₀(P)` therefore have zero middle bracket. -/
theorem frattiniMiddleCommutatorBilinear_eq_zero_on_restrictedLayer
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    (u v : Additive (lowerCentralLayer S 0)) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists
        (subgroupLowerCentralLayerZeroLinear S u)
        (subgroupLowerCentralLayerZeroLinear S v) = 0 := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (lowerCentralLayerKernel S 0) u.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (lowerCentralLayerKernel S 0) v.toMul
  have hu :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel S 0) x) = u := by
    rw [hx]
    rfl
  have hv :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel S 0) y) = v := by
    rw [hy]
    rfl
  rw [← hu, ← hv, subgroupLowerCentralLayerZeroLinear_mk,
    subgroupLowerCentralLayerZeroLinear_mk]
  apply frattiniMiddleCommutatorBilinear_eq_zero_of_mem_restricted_factor
    hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
  · exact (x : S).property
  · exact (y : S).property

/-- Scalar extension preserves same-restricted-factor middle vanishing.

The statement covers the whole scalar-extended image of `L₀(S)`, rather than
only a chosen family.  It is the reusable tensor/base-change bridge needed by
the two type-C/C Jacobi branches. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_eq_zero_on_restrictedLayer
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    (x y : F ⊗[ZMod 2] Additive (lowerCentralLayer S 0)) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinearBaseChange F
        hP hxi hPhiComm hexists
        ((subgroupLowerCentralLayerZeroLinear S).baseChange F x)
        ((subgroupLowerCentralLayerZeroLinear S).baseChange F y) = 0 := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      simp only [LinearMap.baseChange_tmul]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
          simp only [LinearMap.baseChange_tmul,
            frattiniMiddleCommutatorBilinearBaseChange_tmul]
          rw [frattiniMiddleCommutatorBilinear_eq_zero_on_restrictedLayer
            hP hmulti hxi hprime hPhiComm hexists
            hSinv hPhiS hlenS hncommS u v]
          simp
      | add y z hy hz => simp [hy, hz]
  | add x z hx hz => simp [hx, hz]

/-- A canonical ambient eigenfamily transported from one restricted layer has
zero middle bracket on every pair of family vectors. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_factorAmbientEigenFamily_eq_zero
    (F : Type uF) [Field F] [Finite F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    {Q : Type uQ} [AddCommGroup Q] [Module (ZMod 2) Q]
    (eQ : Q ≃ₗ[ZMod 2] F)
    (iotaS : Q →ₗ[ZMod 2] Additive (lowerCentralLayer S 0))
    (i j : Fin (Module.finrank (ZMod 2) F)) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinearBaseChange F
        hP hxi hPhiComm hexists
        (factorAmbientEigenFamily eQ
          ((subgroupLowerCentralLayerZeroLinear S).comp iotaS) i)
        (factorAmbientEigenFamily eQ
          ((subgroupLowerCentralLayerZeroLinear S).comp iotaS) j) = 0 := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let b := conjugateTensorBasisOfLinearEquiv F eQ
  have hzero :=
    frattiniMiddleCommutatorBilinearBaseChange_eq_zero_on_restrictedLayer
      F hP hmulti hxi hprime hPhiComm hexists
      hSinv hPhiS hlenS hncommS
      (iotaS.baseChange F (b i)) (iotaS.baseChange F (b j))
  simpa only [factorAmbientEigenFamily, b, LinearMap.baseChange_comp,
    LinearMap.comp_apply] using hzero

/-- **Higman Lemma 13 (printed p. 93), same restricted-factor family zero.**

For the canonical ambient family built by `restrictedFactorAmbientInclusion`,
every two family vectors have zero middle bracket.  This is the form consumed
directly by the type-C/C Jacobi argument. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_canonicalRestrictedFactorFamily_eq_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
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
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    let iota := restrictedFactorAmbientInclusion hSinv hEAS eS c data
      hK1S htermS hSqS hAgemoS hK0S
    let family := factorAmbientEigenFamily
      (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
    ∀ i j, frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hexists (family i) (family j) = 0 := by
  classical
  dsimp only
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  intro i j
  let d := data.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  have hzero :=
    frattiniMiddleCommutatorBilinearBaseChange_factorAmbientEigenFamily_eq_zero
      (GaloisField 2 n) hP hmulti hxi hprime hPhiComm hexists
      hSinv hPhiS hlenS hncommS
      (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) d.incl i j
  simpa only [restrictedFactorAmbientInclusion, d] using hzero

end OddOrder.Higman.Suzuki2Groups
