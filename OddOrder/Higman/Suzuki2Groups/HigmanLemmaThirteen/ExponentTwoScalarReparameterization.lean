/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoLambdaCoherence

/-!
# Higman Lemma 13: scalar reparameterization of a common factor

G. Higman, *Suzuki 2-groups*, p. 93.  Two coordinate systems on the same
factor give injective `F₂`-linear maps with one common ambient image.  If the
ambient actor has the same primitive Singer eigenvalue in both coordinates,
the transition commutes with multiplication by that eigenvalue.  Since every
nonzero field element is a power of the primitive eigenvalue, the transition
is multiplication by one nonzero scalar.

This is the linear-algebra core of the cross-join alignment.  A downstream
bridge supplies the two inclusions from the actual prescribed factor copies.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

noncomputable section

/-- **Higman Lemma 13 (p. 93), scalar coordinate reparameterization.**

Two injective field-coordinate inclusions with the same range and the same
primitive actor eigenvalue differ by multiplication by a nonzero field
scalar. -/
theorem exists_scalar_reparameterization_of_equal_range
    {n : ℕ} (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (lambda : GaloisField 2 n)
    (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (A : Module.End (ZMod 2) V)
    (iotaJ iotaK : GaloisField 2 n →ₗ[ZMod 2] V)
    (hinjJ : Function.Injective iotaJ)
    (hinjK : Function.Injective iotaK)
    (hrange : LinearMap.range iotaJ = LinearMap.range iotaK)
    (heigJ : ∀ alpha, A (iotaJ alpha) = iotaJ (lambda * alpha))
    (heigK : ∀ alpha, A (iotaK alpha) = iotaK (lambda * alpha)) :
    ∃ a : GaloisField 2 n, a ≠ 0 ∧
      ∀ alpha, iotaJ alpha = iotaK (a * alpha) := by
  let eJ :
      GaloisField 2 n ≃ₗ[ZMod 2] LinearMap.range iotaJ :=
    LinearEquiv.ofInjective iotaJ hinjJ
  let eK :
      GaloisField 2 n ≃ₗ[ZMod 2] LinearMap.range iotaK :=
    LinearEquiv.ofInjective iotaK hinjK
  let tau : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n :=
    (eJ.trans (LinearEquiv.ofEq _ _ hrange)).trans eK.symm
  have hiota : ∀ alpha, iotaK (tau alpha) = iotaJ alpha := by
    intro alpha
    have h := congrArg Subtype.val
      (eK.apply_symm_apply
        ((LinearEquiv.ofEq
          (LinearMap.range iotaJ) (LinearMap.range iotaK) hrange)
            (eJ alpha)))
    exact h
  have hsemi : ∀ alpha, tau (lambda * alpha) = lambda * tau alpha := by
    intro alpha
    apply hinjK
    calc
      iotaK (tau (lambda * alpha)) =
          iotaJ (lambda * alpha) := hiota _
      _ = A (iotaJ alpha) := (heigJ alpha).symm
      _ = A (iotaK (tau alpha)) := by rw [hiota]
      _ = iotaK (lambda * tau alpha) := heigK _
  have hpow : ∀ (k : ℕ) (alpha : GaloisField 2 n),
      tau (lambda ^ k * alpha) = lambda ^ k * tau alpha := by
    intro k
    induction k with
    | zero =>
        intro alpha
        simp
    | succ k ih =>
        intro alpha
        rw [pow_succ', mul_assoc, hsemi, ih, mul_assoc]
  have hNpos : 0 < 2 ^ n - 1 := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpowTwo : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  let : NeZero (2 ^ n - 1) := ⟨hNpos.ne'⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n hn
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hscalar : ∀ (c alpha : GaloisField 2 n),
      tau (c * alpha) = c * tau alpha := by
    intro c alpha
    by_cases hc : c = 0
    · simp [hc]
    · have hcPow : c ^ (2 ^ n - 1) = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one c hc
        rwa [← Nat.card_eq_fintype_card, hcard] at h
      obtain ⟨k, _hk, hk⟩ := hprim.eq_pow_of_pow_eq_one hcPow
      rw [← hk]
      exact hpow k alpha
  let a : GaloisField 2 n := tau 1
  have ha : a ≠ 0 := by
    intro ha
    have hzero : tau (1 : GaloisField 2 n) = tau 0 := by
      simp [a, ha]
    exact one_ne_zero (tau.injective hzero)
  refine ⟨a, ha, fun alpha => ?_⟩
  rw [← hiota]
  congr 1
  calc
    tau alpha = tau (alpha * 1) := by rw [mul_one]
    _ = alpha * tau 1 := hscalar alpha 1
    _ = a * alpha := by simpa [a] using (mul_comm alpha (tau 1))

end

end OddOrder.Higman.Suzuki2Groups
