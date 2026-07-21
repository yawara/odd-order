/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedTermValue

/-!
# Higman Lemma 12: case-dispatch normalizations

G. Higman, *Suzuki 2-groups*, pp. 90--92.  Higman's case split on the factor
automorphism pair `(θ, φ)` uses a normalization freedom before the exponent
arithmetic: `A(n, θ)` and `A(n, θ⁻¹)` are isomorphic (p. 91), so the
Frobenius exponent of a noncommutative factor may be assumed to lie in
`0 < r ≤ n/2`.

* `ringAutLinearEquiv` — a ring automorphism of a `ZMod 2`-algebra, viewed as
  a `ZMod 2`-linear equivalence.
* `NoncommutativeFactorCoordinateData.flip` — the `A(n, θ) ≅ A(n, θ⁻¹)`
  isomorphism at the coordinate level: compose the quotient coordinate with
  `θ`, leaving the prescribed ambient kernel coordinate `ePhi` untouched.
  The type-A parameters transform as `θ ↦ θ⁻¹`, `λ ↦ θ(λ)`.
* `NoncommutativeFactorCoordinateData.exists_flip_frobenius_le_half` — the
  resulting "we may suppose that `0 < r ≤ ½n`": every noncommutative factor
  admits coordinates (itself or its flip) whose `θ` is `Frob^r` with
  `0 < r`, `2r ≤ n`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uH

noncomputable section

local instance caseDispatchLayerCommGroup
    (H : Type uH) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance caseDispatchLayerModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ### Ring automorphisms as `ZMod 2`-linear equivalences -/

/-- A ring automorphism of a `ZMod 2`-module ring is `ZMod 2`-linear. -/
def ringAutLinearEquiv {F : Type*} [Ring F] [Module (ZMod 2) F]
    (theta : RingAut F) : F ≃ₗ[ZMod 2] F :=
  { theta.toAddEquiv with
    map_smul' := ZMod.map_smul theta.toRingHom.toAddMonoidHom }

@[simp] theorem ringAutLinearEquiv_apply {F : Type*} [Ring F]
    [Module (ZMod 2) F] (theta : RingAut F) (x : F) :
    ringAutLinearEquiv theta x = theta x := rfl

@[simp] theorem ringAutLinearEquiv_symm_apply {F : Type*} [Ring F]
    [Module (ZMod 2) F] (theta : RingAut F) (x : F) :
    (ringAutLinearEquiv theta).symm x = theta⁻¹ x := rfl

/-! ### The `A(n, θ) ≅ A(n, θ⁻¹)` flip -/

variable {P : Type uH} [Group P]
  {Y : Subgroup (MulAut P)}
  [IsMulCommutative ↑(frattini P)]
  [Module (ZMod 2) (Additive ↑(frattini P))]
  {S : Subgroup P}
  {hSinv : IsAInvariant Y.subtype S}
  {hPhiS : frattini P ≤ S}
  {c : Y} {n : Nat}
  {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
  {nu : GaloisField 2 n}

/-- **Higman p. 91, "`A(n, θ)` and `A(n, θ⁻¹)` are isomorphic."**  Flip a
noncommutative factor coordinate by composing the quotient coordinate with
`θ`; the prescribed ambient kernel coordinate is untouched.  The type-A
parameters transform as `θ ↦ θ⁻¹`, `λ ↦ θ(λ)`, and the source relation
`ν = λ θ(λ)` is preserved. -/
def NoncommutativeFactorCoordinateData.flip
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu where
  hK1 := data.hK1
  hterm := data.hterm
  hSq := data.hSq
  eKernel := data.eKernel
  eKernel_eq := data.eKernel_eq
  theta := data.theta⁻¹
  eQuot := data.eQuot.trans (ringAutLinearEquiv data.theta)
  lambda := data.theta data.lambda
  theta_ne_one := fun h => data.theta_ne_one (inv_eq_one.mp h)
  theta_order_odd := by
    rw [orderOf_inv]
    exact data.theta_order_odd
  kernel_compatible := data.kernel_compatible
  quotient_compatible := fun v => by
    simp only [LinearEquiv.trans_apply, ringAutLinearEquiv_apply,
      data.quotient_compatible v, map_mul]
  square_normal := fun beta => by
    have hcancel : data.theta (data.theta⁻¹ beta) = beta := by
      rw [← RingAut.mul_apply, mul_inv_cancel, RingAut.one_apply]
    have harg : (data.eQuot.trans (ringAutLinearEquiv data.theta)).symm beta
        = data.eQuot.symm (data.theta⁻¹ beta) := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, ringAutLinearEquiv_apply, hcancel]
    rw [harg, data.square_normal, hcancel]
    exact mul_comm _ _
  kernel_eigenvalue_eq := by
    have hcancel : data.theta⁻¹ (data.theta data.lambda) = data.lambda := by
      rw [← RingAut.mul_apply, inv_mul_cancel, RingAut.one_apply]
    rw [hcancel, mul_comm]
    exact data.kernel_eigenvalue_eq

@[simp] theorem NoncommutativeFactorCoordinateData.flip_theta
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.theta = data.theta⁻¹ := rfl

@[simp] theorem NoncommutativeFactorCoordinateData.flip_lambda
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.lambda = data.theta data.lambda := rfl

@[simp] theorem NoncommutativeFactorCoordinateData.flip_eKernel
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.eKernel = data.eKernel := rfl

/-! ### The `0 < r ≤ n/2` normalization -/

/-- The Frobenius exponent of a noncommutative factor automorphism is
nonzero: `θ = Frob^r ≠ 1` forces `r ≢ 0`. -/
theorem NoncommutativeFactorCoordinateData.frobenius_exponent_ne_zero
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    {r : Fin n}
    (hr : data.theta = (frobeniusEquiv (GaloisField 2 n) 2) ^ (r : ℕ)) :
    (r : ℕ) ≠ 0 := by
  intro h0
  apply data.theta_ne_one
  rw [hr, h0, pow_zero]

/-- **Higman p. 91, "we may suppose that `0 < r ≤ ½n`."**  Every
noncommutative factor admits coordinates — itself or its flip — whose
automorphism is `Frob^r` with `0 < r` and `2r ≤ n`.  The flip realises
`A(n, θ) ≅ A(n, θ⁻¹)` without moving the prescribed ambient kernel
coordinate, so the two candidate coordinates share `ePhi` and `ν`. -/
theorem NoncommutativeFactorCoordinateData.exists_flip_frobenius_le_half
    (hn : n ≠ 0)
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    ∃ (data' : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
      (r : ℕ), 0 < r ∧ 2 * r ≤ n ∧
      data'.theta = (frobeniusEquiv (GaloisField 2 n) 2) ^ r := by
  obtain ⟨r0, hr0⟩ := exists_frobenius_pow_eq_of_ringAut n hn data.theta
  have hr0ne : (r0 : ℕ) ≠ 0 := data.frobenius_exponent_ne_zero hr0
  by_cases h2r : 2 * (r0 : ℕ) ≤ n
  · exact ⟨data, r0, Nat.pos_of_ne_zero hr0ne, h2r, hr0⟩
  · -- flip: `θ⁻¹ = Frob^(n - r₀)` with `2(n - r₀) ≤ n`
    have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
      simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
    have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
      have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
        orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
      calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
          = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
        _ = 1 := pow_orderOf_eq_one _
    have hmul : (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - (r0 : ℕ))
        * (frobeniusEquiv (GaloisField 2 n) 2) ^ (r0 : ℕ) = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt r0.2)]
      exact hfrobn
    have hinv : data.theta⁻¹
        = (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - (r0 : ℕ)) := by
      rw [hr0]
      exact (eq_inv_of_mul_eq_one_left hmul).symm
    refine ⟨data.flip, n - (r0 : ℕ), ?_, ?_, ?_⟩
    · have := r0.2
      omega
    · have := r0.2
      omega
    · rw [data.flip_theta, hinv]

end

end OddOrder.Higman.Suzuki2Groups
