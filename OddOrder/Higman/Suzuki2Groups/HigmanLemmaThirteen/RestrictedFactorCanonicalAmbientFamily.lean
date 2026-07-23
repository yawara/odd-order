/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman's Lemma 13: the canonical ambient family of a restricted factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

This file exposes the canonical `factorAmbientEigenFamily` itself, rather than
an existentially packaged family.  Its actor eigenvalue law and its span of all
ambient ground classes from the restricted subgroup can therefore be combined
definitionally with the square-bracket calculation for the same family.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative TensorProduct

universe uP

local instance restrictedFactorCanonicalAmbientFamilyLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance restrictedFactorCanonicalAmbientFamilyLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance
    restrictedFactorCanonicalAmbientFamilyLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (pp. 92–93), canonical restricted-factor family.**

When the left complementary factor in `S` is the ambient Frattini subgroup,
the explicit canonical eigenfamily of the right factor has its expected actor
eigenvalues and spans the ambient ground class represented by every element of
`S`. -/
theorem canonicalRestrictedFactorAmbientEigenFamily_eigen_and_spans
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P} [Finite S]
    (hP : IsPGroup 2 P)
    (hSinv : IsAInvariant Y.subtype S)
    {n : Nat}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    (c : Y)
    (factors : XiLengthThreeTypeAFactorData S hSinv.restrict.range)
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
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    let iota :=
      restrictedFactorAmbientInclusion hSinv hEAS eS c right
        hK1S htermS hSqS hAgemoS hK0S
    let family := factorAmbientEigenFamily
      (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
    (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) (family i) =
      right.lambda ^ (2 ^ i.val) • family i) ∧
    ∀ x : lowerCentralTerm S 0,
      (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
              (subgroupLowerCentralTermZeroHom S x)) ∈
        Submodule.span (GaloisField 2 n) (Set.range family) := by
  classical
  dsimp only
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  let eRefl := LinearEquiv.refl (ZMod 2) (GaloisField 2 n)
  let d := right.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  let iota := restrictedFactorAmbientInclusion hSinv hEAS eS c right
    hK1S htermS hSqS hAgemoS hK0S
  let Aq : Module.End (ZMod 2) (GaloisField 2 n) :=
    Algebra.lmul (ZMod 2) (GaloisField 2 n) right.lambda
  have hAq : ∀ v, eRefl (Aq v) = right.lambda * eRefl v := by
    intro v
    rfl
  have hiota : ∀ v, iota (Aq v) =
      lowerCentralLayerRepresentation Y.subtype 0 c (iota v) := by
    intro v
    rw [show Aq v = right.lambda • v by rfl]
    exact (restrictedFactorAmbientInclusion_representation
      hSinv hEAS eS c right hK1S htermS hSqS hAgemoS hK0S v).symm
  let family := factorAmbientEigenFamily eRefl iota
  have hfamily : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
        right.lambda ^ (2 ^ i.val) • family i := by
    intro i
    exact factorAmbientEigenFamily_eigen c eRefl Aq right.lambda hAq
      iota hiota i
  refine ⟨hfamily, ?_⟩
  have hright : ∀ (x : lowerCentralTerm S 0), (x : S) ∈ factors.right →
      (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
              (subgroupLowerCentralTermZeroHom S x)) ∈
        Submodule.span (GaloisField 2 n) (Set.range family) := by
    intro x hx
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
  intro x
  have hxSup : (x : S) ∈ factors.left ⊔ factors.right := by
    rw [factors.sup_eq_top]
    exact Subgroup.mem_top _
  letI : factors.right.Normal := factors.right_normal
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hxSup
  let xa : lowerCentralTerm S 0 := ⟨a, Subgroup.mem_top a⟩
  let xb : lowerCentralTerm S 0 := ⟨b, Subgroup.mem_top b⟩
  have hxaMulXb : xa * xb = x := by
    apply Subtype.ext
    exact hab
  have haPhi : ((a : S) : P) ∈ frattini P := by
    have ha' : a ∈ (frattini P).subgroupOf S := by
      rw [← hleft]
      exact ha
    exact ha'
  have hxaKernel : subgroupLowerCentralTermZeroHom S xa ∈
      lowerCentralLayerKernel P 0 := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0]
    change ((a : S) : P) ∈ lowerCentralLayerKernelInAmbient P 0
    rwa [lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP]
  have hxaClass :
      QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (subgroupLowerCentralTermZeroHom S xa) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hxaKernel
  have hxClass :
      QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (subgroupLowerCentralTermZeroHom S x) =
        QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (subgroupLowerCentralTermZeroHom S xb) := by
    rw [← hxaMulXb, map_mul, map_mul, hxaClass, one_mul]
  rw [hxClass]
  exact hright xb hb

end OddOrder.Higman.Suzuki2Groups
