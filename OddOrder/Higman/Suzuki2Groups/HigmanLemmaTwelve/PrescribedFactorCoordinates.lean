/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.AmbientCentralExtension

/-!
# Higman's Lemma 12: factor coordinates over the prescribed common centre

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
pp. 89--90.

The common coordinate on `Φ(P)` is chosen before either factor coordinate.
This leaf assembles the equality-tracked Frobenius normalizations from
Higman's Lemma 11 without changing that kernel coordinate.  The quotient
coordinate alone is adjusted, first to undo the tracked shifts and then to
absorb the remaining nonzero type-A coefficient.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group

universe uH uC uF

noncomputable section

local instance prescribedFactorLayerCommGroup
    (H : Type uH) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance prescribedFactorLayerModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- Restore a prescribed kernel coordinate after a field automorphism has
been used to normalize the second layer.  The returned quotient eigenvalue
is measured in the restored coordinate, and square-map equivariance gives
the exact source relation `nu = lambda' * theta(lambda')`. -/
theorem exists_typeAQuotientCoordinates_of_prescribedKernel_from_shiftedNormalForm
    {H : Type uH} [Group H]
    {C : Type uC} [Group C]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (actor : C →* MulAut H) (c : C)
    (hSq : LowerCentralSquaresLieInSecond H)
    (eQuot : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (lambda nu : F)
    (hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation actor 0 c v) =
        lambda * eQuot v)
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation actor 1 c v) =
        nu * eKernel v)
    (sigma : F ≃ₐ[ZMod 2] F)
    (theta : RingAut F)
    (hsigmaTheta : ∀ x : F, sigma (theta x) = theta (sigma x))
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hshiftedNormal : ∀ alpha : F,
      (eKernel.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive H hSq (eQuot.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ (eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
      (lambda' epsilon' : F),
      epsilon' ≠ 0 ∧
      (∀ v,
        eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
          lambda' * eQuot' v) ∧
      (∀ beta : F,
        eKernel
            (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
          epsilon' * (beta * theta beta)) ∧
      nu = lambda' * theta lambda' := by
  let eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F :=
    eQuot.trans sigma.toLinearEquiv.symm
  let lambda' : F := sigma.symm lambda
  let epsilon' : F := sigma.symm epsilon
  have hepsilon' : epsilon' ≠ 0 := by
    intro hzero
    apply hepsilon
    apply sigma.symm.injective
    simpa only [map_zero] using hzero
  have hcompatQuot' : ∀ v,
      eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
        lambda' * eQuot' v := by
    intro v
    change sigma.symm
        (eQuot (lowerCentralLayerRepresentation actor 0 c v)) =
      sigma.symm lambda * sigma.symm (eQuot v)
    rw [hcompatQuot, map_mul]
  have hnormal' : ∀ beta : F,
      eKernel
          (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
        epsilon' * (beta * theta beta) := by
    intro beta
    have h := congrArg sigma.symm (hshiftedNormal (sigma beta))
    have htheta : sigma.symm (theta (sigma beta)) = theta beta := by
      rw [← hsigmaTheta beta, sigma.symm_apply_apply]
    have h' : eKernel
          (lowerCentralSquareMapAdditive H hSq
            (eQuot.symm (sigma beta))) =
        epsilon' * (beta * theta beta) := by
      simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_coe,
        AlgEquiv.toLinearEquiv_apply, map_mul, htheta,
        sigma.symm_apply_apply] using h
    have heQuot : eQuot'.symm beta = eQuot.symm (sigma beta) := by
      apply eQuot'.injective
      simp only [eQuot', LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply]
      exact (sigma.symm_apply_apply beta).symm
    rw [heQuot]
    exact h'
  have hnorm : nu = lambda' * theta lambda' :=
    kernel_eigenvalue_eq_typeANorm_of_normalForm
      actor c hSq eQuot' eKernel lambda' nu theta epsilon' hepsilon'
      hcompatQuot' hcompatKernel hnormal'
  exact ⟨eQuot', lambda', epsilon', hepsilon',
    hcompatQuot', hnormal', hnorm⟩

/-- Restore the prescribed kernel coordinate and then absorb the remaining
nonzero coefficient by rescaling only the quotient coordinate.  The actor
eigenvalue and the relation `nu = lambda' * theta(lambda')` are unchanged. -/
theorem exists_typeAQuotientCoordinates_of_prescribedKernel
    {H : Type uH} [Group H]
    {C : Type uC} [Group C]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (actor : C →* MulAut H) (c : C)
    (hSq : LowerCentralSquaresLieInSecond H)
    (eQuot : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (lambda nu : F)
    (hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation actor 0 c v) =
        lambda * eQuot v)
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation actor 1 c v) =
        nu * eKernel v)
    (sigma : F ≃ₐ[ZMod 2] F)
    (theta : RingAut F) (htheta : Odd (orderOf theta))
    (hsigmaTheta : ∀ x : F, sigma (theta x) = theta (sigma x))
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hshiftedNormal : ∀ alpha : F,
      (eKernel.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive H hSq (eQuot.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ (eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
      (lambda' : F),
      (∀ v,
        eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
          lambda' * eQuot' v) ∧
      (∀ beta : F,
        eKernel
            (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
          beta * theta beta) ∧
      nu = lambda' * theta lambda' := by
  obtain ⟨eQuotOne, lambda', epsilon', hepsilon',
      hcompatOne, hnormalOne, hnorm⟩ :=
    exists_typeAQuotientCoordinates_of_prescribedKernel_from_shiftedNormalForm
      actor c hSq eQuot eKernel lambda nu hcompatQuot hcompatKernel
      sigma theta hsigmaTheta epsilon hepsilon hshiftedNormal
  obtain ⟨u, hu, hunorm⟩ :=
    exists_ne_zero_mul_apply_eq_of_typeA theta htheta epsilon' hepsilon'
  let uUnit : Fˣ := Units.mk0 u hu
  let scale : F ≃ₗ[ZMod 2] F :=
    (uUnit.mulLeftLinearEquiv F F).restrictScalars (ZMod 2)
  let eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F :=
    eQuotOne.trans scale
  have hcompat' : ∀ v,
      eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
        lambda' * eQuot' v := by
    intro v
    change u *
        eQuotOne (lowerCentralLayerRepresentation actor 0 c v) =
      lambda' * (u * eQuotOne v)
    rw [hcompatOne]
    ring
  have hnormal' : ∀ beta : F,
      eKernel
          (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
        beta * theta beta := by
    intro beta
    let alpha : F := scale.symm beta
    have hscale : u * alpha = beta := by
      have h := scale.apply_symm_apply beta
      change u * alpha = beta at h
      exact h
    calc
      eKernel
            (lowerCentralSquareMapAdditive H hSq
              (eQuot'.symm beta)) =
          epsilon' * (alpha * theta alpha) := by
        change eKernel
            (lowerCentralSquareMapAdditive H hSq
              (eQuotOne.symm (scale.symm beta))) = _
        exact hnormalOne alpha
      _ = beta * theta beta := by
        rw [← hunorm, ← hscale, map_mul]
        ring
  exact ⟨eQuot', lambda', hcompat', hnormal', hnorm⟩

end

end OddOrder.Higman.Suzuki2Groups
