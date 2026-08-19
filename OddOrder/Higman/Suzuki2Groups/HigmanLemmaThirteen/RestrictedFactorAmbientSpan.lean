/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman's Lemma 13: ambient span of a restricted factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

When one complementary factor of the restricted group `S` is the ambient
Frattini subgroup `Φ(P)`, that factor vanishes in `L₀(P)`.  Consequently the
ambient eigenfamily supplied by the other factor spans the image of every
element of `S`, not only elements represented directly by that factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative TensorProduct

universe uP

local instance restrictedFactorAmbientSpanLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance restrictedFactorAmbientSpanLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance restrictedFactorAmbientSpanLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (pp. 92–93), restricted-group ambient span.**

Suppose the left member of a complementary factor pair in `S` is precisely
the ambient Frattini subgroup.  The canonical ambient eigenfamily of the
right factor retains its Frobenius eigenvalue laws and field-coordinate span,
and its span contains the ambient ground tensor represented by every element
of `S`. -/
theorem exists_restrictedFactorAmbientEigenFamily_spanning_restrictedSubgroup
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
    ∃ family : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
        GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
        right.lambda ^ (2 ^ i.val) • family i) ∧
      (∀ alpha : GaloisField 2 n,
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            restrictedFactorAmbientInclusion hSinv hEAS eS c right
              hK1S htermS hSqS hAgemoS hK0S alpha ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) ∧
      (∀ (x : lowerCentralTerm S 0), (x : S) ∈ factors.right →
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom S x)) ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) ∧
      (∀ x : lowerCentralTerm S 0,
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                (subgroupLowerCentralTermZeroHom S x)) ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) := by
  classical
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  obtain ⟨family, hfamily, hcoordinate, hright⟩ :=
    exists_restrictedFactorAmbientEigenFamily
      hSinv hEAS eS c right hK1S htermS hSqS hAgemoS hK0S
  refine ⟨family, hfamily, hcoordinate, hright, ?_⟩
  intro x
  have hxSup : (x : S) ∈ factors.left ⊔ factors.right := by
    rw [factors.sup_eq_top]
    exact Subgroup.mem_top _
  let : factors.right.Normal := factors.right_normal
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
