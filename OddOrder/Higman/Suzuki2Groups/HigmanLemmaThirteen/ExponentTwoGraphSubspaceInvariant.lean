/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import OddOrder.GroupTheory.RepresentationTheory.AInvariantSubrep
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoQuotientLayerBridge
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman's Lemma 13: invariant graph subspaces

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Two factor coordinates with the same nonzero eigenvalue determine graph
maps

`α ↦ iX (a * α) + iY (b * α)`.

Their ranges are stable under the generator action.  Nonzeroness of the
common eigenvalue gives stability under the inverse generator, and a
`zpowers` generator then upgrades this to a genuine subrepresentation.
The final bridge transports that subrepresentation back to an actual
actor-invariant subgroup through `elabSubmoduleSubgroupEquiv`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uR uK uV uC uQ uP

local instance graphSubspaceInvariantLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance graphSubspaceInvariantLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance graphSubspaceInvariantLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The linear graph map associated to two factor embeddings and two
coefficients. -/
def commonEigenvalueGraphMap
    {R : Type uR} {K : Type uK} {V : Type uV}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid V] [Module R V]
    (iX iY : K →ₗ[R] V) (a b : K) :
    K →ₗ[R] V :=
  iX.comp (Algebra.lmul R K a) +
    iY.comp (Algebra.lmul R K b)

@[simp]
theorem commonEigenvalueGraphMap_apply
    {R : Type uR} {K : Type uK} {V : Type uV}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid V] [Module R V]
    (iX iY : K →ₗ[R] V) (a b alpha : K) :
    commonEigenvalueGraphMap iX iY a b alpha =
      iX (a * alpha) + iY (b * alpha) :=
  rfl

/-- Composing a zeroth-layer eigenvector map with the canonical map to the
Frattini quotient preserves its eigenvalue for the induced linear action. -/
theorem layerZeroToFrattiniQuotientLinear_comp_eigen
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {C : Type uC} [Group C]
    (phi : C →* MulAut P) (c : C)
    {K : Type uK} [CommSemiring K] [Algebra (ZMod 2) K]
    (i : K →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (lambda : K)
    (hi : ∀ alpha,
      lowerCentralLayerRepresentation phi 0 c (i alpha) =
        i (lambda * alpha))
    (alpha : K) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    elabRepresentation 2
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic phi :
            IsAInvariant phi (frattini P)))
        c
        ((layerZeroToFrattiniQuotientLinear P hP).comp i alpha) =
      (layerZeroToFrattiniQuotientLinear P hP).comp i
        (lambda * alpha) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  change
    Additive.ofMul
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic phi :
            IsAInvariant phi (frattini P))
          c
          (layerZeroToFrattiniQuotientLinear P hP (i alpha)).toMul) =
      layerZeroToFrattiniQuotientLinear P hP
        (i (lambda * alpha))
  rw [← layerZeroToFrattiniQuotientLinear_equivariant P hP phi c,
    hi]

/-- A restricted factor inclusion retains its scalar eigenvalue after
passage from `L₀(P)` to the Frattini quotient of `P`. -/
theorem restrictedFactorAmbientInclusion_frattiniQuotient_representation
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)} {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
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
      (frattini S).subgroupOf (lowerCentralTerm S 0))
    (alpha : GaloisField 2 n) :
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hEAS.zmodModule
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    elabRepresentation 2
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)))
        c
        ((layerZeroToFrattiniQuotientLinear P hP).comp
          (restrictedFactorAmbientInclusion hSinv hEAS eS c data
            hK1S htermS hSqS hAgemoS hK0S) alpha) =
      (layerZeroToFrattiniQuotientLinear P hP).comp
        (restrictedFactorAmbientInclusion hSinv hEAS eS c data
          hK1S htermS hSqS hAgemoS hK0S)
        (data.lambda * alpha) := by
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : Module (ZMod 2) (Additive (frattini S)) :=
    hEAS.zmodModule
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  apply layerZeroToFrattiniQuotientLinear_comp_eigen
    hP Y.subtype c
  intro beta
  simpa only [smul_eq_mul] using
    restrictedFactorAmbientInclusion_representation
      hSinv hEAS eS c data hK1S htermS hSqS hAgemoS hK0S beta

/-- If both coordinate maps have the same eigenvalue, their graph map has
that eigenvalue as well. -/
theorem commonEigenvalueGraphMap_eigen
    {R : Type uR} {K : Type uK} {V : Type uV}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid V] [Module R V]
    (A : Module.End R V)
    (iX iY : K →ₗ[R] V) (a b lambda : K)
    (hX : ∀ alpha, A (iX alpha) = iX (lambda * alpha))
    (hY : ∀ alpha, A (iY alpha) = iY (lambda * alpha))
    (alpha : K) :
    A (commonEigenvalueGraphMap iX iY a b alpha) =
      commonEigenvalueGraphMap iX iY a b (lambda * alpha) := by
  rw [commonEigenvalueGraphMap_apply, map_add, hX, hY,
    commonEigenvalueGraphMap_apply]
  congr 1 <;> ac_rfl

/-- The range of a common-eigenvalue graph map is stable under the
corresponding linear operator. -/
theorem commonEigenvalueGraphMap_range_stable
    {R : Type uR} {K : Type uK} {V : Type uV}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid V] [Module R V]
    (A : Module.End R V)
    (iX iY : K →ₗ[R] V) (a b lambda : K)
    (hX : ∀ alpha, A (iX alpha) = iX (lambda * alpha))
    (hY : ∀ alpha, A (iY alpha) = iY (lambda * alpha)) :
    ∀ v ∈ LinearMap.range (commonEigenvalueGraphMap iX iY a b),
      A v ∈ LinearMap.range (commonEigenvalueGraphMap iX iY a b) := by
  rintro _ ⟨alpha, rfl⟩
  exact ⟨lambda * alpha,
    (commonEigenvalueGraphMap_eigen
      A iX iY a b lambda hX hY alpha).symm⟩

/-- For a representation generator, a nonzero common graph eigenvalue also
gives stability under the inverse generator. -/
theorem commonEigenvalueGraphMap_range_inv_stable
    {R : Type uR} {K : Type uK} {V : Type uV}
    {C : Type uC}
    [CommSemiring R] [Field K] [Algebra R K]
    [AddCommMonoid V] [Module R V]
    [Group C]
    (rho : Representation R C V) (c : C)
    (iX iY : K →ₗ[R] V) (a b lambda : K)
    (hlambda : lambda ≠ 0)
    (hX : ∀ alpha, rho c (iX alpha) = iX (lambda * alpha))
    (hY : ∀ alpha, rho c (iY alpha) = iY (lambda * alpha)) :
    ∀ v ∈ LinearMap.range (commonEigenvalueGraphMap iX iY a b),
      rho c⁻¹ v ∈
        LinearMap.range (commonEigenvalueGraphMap iX iY a b) := by
  rintro _ ⟨alpha, rfl⟩
  refine ⟨lambda⁻¹ * alpha, ?_⟩
  calc
    commonEigenvalueGraphMap iX iY a b (lambda⁻¹ * alpha) =
        rho c⁻¹
          (rho c
            (commonEigenvalueGraphMap iX iY a b
              (lambda⁻¹ * alpha))) := by simp
    _ = rho c⁻¹
        (commonEigenvalueGraphMap iX iY a b
          (lambda * (lambda⁻¹ * alpha))) := by
      rw [commonEigenvalueGraphMap_eigen
        (rho c) iX iY a b lambda hX hY]
    _ = rho c⁻¹
        (commonEigenvalueGraphMap iX iY a b alpha) := by
      rw [← mul_assoc, mul_inv_cancel₀ hlambda, one_mul]

/-- A submodule stable under a cyclic generator and its inverse is a
subrepresentation of the whole cyclic action.

The generator is supplied in the same explicit `zpowers` form used by the
Higman coordinate packages. -/
def cyclicGeneratorSubrepresentation
    {R : Type uR} {V : Type uV} {C : Type uC}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    [Group C]
    (rho : Representation R C V)
    (c : C) (hcgen : ∀ g : C, g ∈ Subgroup.zpowers c)
    (W : Submodule R V)
    (hc : ∀ v ∈ W, rho c v ∈ W)
    (hcinv : ∀ v ∈ W, rho c⁻¹ v ∈ W) :
    Subrepresentation rho where
  toSubmodule := W
  apply_mem_toSubmodule := by
    intro g v hv
    let stabilizer : Subgroup C := {
      carrier := {x | ∀ w, w ∈ W ↔ rho x w ∈ W}
      one_mem' := by
        intro w
        simp
      mul_mem' := by
        intro x y hx hy w
        rw [map_mul]
        exact (hy w).trans (hx (rho y w))
      inv_mem' := by
        intro x hx w
        simpa using (hx (rho x⁻¹ w)).symm
    }
    have hcStabilizer : c ∈ stabilizer := by
      intro w
      constructor
      · exact hc w
      · intro hcw
        have := hcinv (rho c w) hcw
        simpa using this
    have hgStabilizer : g ∈ stabilizer :=
      (Subgroup.zpowers_le.mpr hcStabilizer) (hcgen g)
    exact (hgStabilizer v).mp hv

@[simp]
theorem cyclicGeneratorSubrepresentation_toSubmodule
    {R : Type uR} {V : Type uV} {C : Type uC}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    [Group C]
    (rho : Representation R C V)
    (c : C) (hcgen : ∀ g : C, g ∈ Subgroup.zpowers c)
    (W : Submodule R V)
    (hc : ∀ v ∈ W, rho c v ∈ W)
    (hcinv : ∀ v ∈ W, rho c⁻¹ v ∈ W) :
    (cyclicGeneratorSubrepresentation
      rho c hcgen W hc hcinv).toSubmodule = W :=
  rfl

/-- Reverse direction of `aInvariantSubrep`: a subrepresentation of the
elementary-abelian linear action corresponds to an actual invariant
subgroup. -/
theorem isAInvariant_elabSubmoduleSubgroupEquiv_of_subrepresentation
    {C : Type uC} {Q : Type uQ}
    [Group C] [CommGroup Q]
    {p : ℕ} [Module (ZMod p) (Additive Q)]
    {phi : C →* MulAut Q}
    (W : Subrepresentation (elabRepresentation p phi)) :
    IsAInvariant phi
      (elabSubmoduleSubgroupEquiv p W.toSubmodule) := by
  rw [isAInvariant_iff_smul_mem]
  intro c x hx
  apply (mem_elabSubmoduleSubgroupEquiv
    W.toSubmodule (phi c x)).2
  have hx' : Additive.ofMul x ∈ W.toSubmodule :=
    (mem_elabSubmoduleSubgroupEquiv W.toSubmodule x).1 hx
  simpa only [elabRepresentation_apply] using
    W.apply_mem_toSubmodule c hx'

/-- A common nonzero generator eigenvalue makes the graph range an actual
actor-invariant subgroup.

This is the quotient-side form needed in Higman Lemma 13: the source field
coordinate need not be actor-equivariant on all elements a priori; the
explicit cyclic generator and the nonzero common eigenvalue supply the
full invariance. -/
theorem commonEigenvalueGraphMap_range_isAInvariant
    {C : Type uC} {Q : Type uQ} {K : Type uK}
    [Group C] [CommGroup Q]
    {p : ℕ} [Module (ZMod p) (Additive Q)]
    [Field K] [Algebra (ZMod p) K]
    (phi : C →* MulAut Q)
    (c : C) (hcgen : ∀ g : C, g ∈ Subgroup.zpowers c)
    (iX iY : K →ₗ[ZMod p] Additive Q)
    (a b lambda : K) (hlambda : lambda ≠ 0)
    (hX : ∀ alpha,
      elabRepresentation p phi c (iX alpha) =
        iX (lambda * alpha))
    (hY : ∀ alpha,
      elabRepresentation p phi c (iY alpha) =
        iY (lambda * alpha)) :
    IsAInvariant phi
      (elabSubmoduleSubgroupEquiv p
        (LinearMap.range
          (commonEigenvalueGraphMap iX iY a b))) := by
  let rho := elabRepresentation p phi
  let d := commonEigenvalueGraphMap iX iY a b
  have hc :
      ∀ v ∈ LinearMap.range d, rho c v ∈ LinearMap.range d :=
    commonEigenvalueGraphMap_range_stable
      (rho c) iX iY a b lambda hX hY
  have hcinv :
      ∀ v ∈ LinearMap.range d, rho c⁻¹ v ∈ LinearMap.range d :=
    commonEigenvalueGraphMap_range_inv_stable
      rho c iX iY a b lambda hlambda hX hY
  let W :=
    cyclicGeneratorSubrepresentation
      rho c hcgen (LinearMap.range d) hc hcinv
  simpa [W, d] using
    isAInvariant_elabSubmoduleSubgroupEquiv_of_subrepresentation W

end

end OddOrder.Higman.Suzuki2Groups
