/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The defining field and Tits twist for Suzuki groups

For `m : ℕ`, the Suzuki group `Sz(q)` is defined over the finite field of order
`q = 2 ^ (2 * m + 1)`.  Its matrix formulas use the Tits twist
`θ : x ↦ x ^ (2 ^ (m + 1))`.  The fundamental identity is `θ (θ x) = x ^ 2`.

This is shared infrastructure for the Suzuki target in **Peterfalvi, Part II,
Chapter I, Theorem A** (pp. 97–98).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

/-- The defining field of the Suzuki group with parameter `m`, of order
`2 ^ (2 * m + 1)`. -/
abbrev Field (m : ℕ) := GaloisField 2 (2 * m + 1)

/-- The defining field has order `2 ^ (2 * m + 1)`. -/
theorem natCard_field (m : ℕ) : Nat.card (Field m) = 2 ^ (2 * m + 1) := by
  exact GaloisField.card 2 (2 * m + 1) (by omega)

/-- The Tits twist `θ : x ↦ x ^ (2 ^ (m + 1))`. -/
noncomputable def titsTwist (m : ℕ) : Field m ≃+* Field m :=
  iterateFrobeniusEquiv (Field m) 2 (m + 1)

/-- Evaluation formula for the Tits twist. -/
theorem titsTwist_apply (m : ℕ) (x : Field m) :
    titsTwist m x = x ^ (2 ^ (m + 1)) := by
  rfl

/-- One full Frobenius period acts trivially on the defining field. -/
theorem iterateFrobeniusEquiv_period (m : ℕ) (x : Field m) :
    iterateFrobeniusEquiv (Field m) 2 (2 * m + 1) x = x := by
  let := Fintype.ofFinite (Field m)
  rw [iterateFrobeniusEquiv_def, ← natCard_field m]
  simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card x

/-- The inverse Tits twist is the `m`-fold Frobenius equivalence. -/
theorem titsTwist_symm (m : ℕ) :
    (titsTwist m).symm = iterateFrobeniusEquiv (Field m) 2 m := by
  ext x
  apply (titsTwist m).injective
  rw [RingEquiv.apply_symm_apply]
  change x = iterateFrobeniusEquiv (Field m) 2 (m + 1)
      (iterateFrobeniusEquiv (Field m) 2 m x)
  rw [← iterateFrobeniusEquiv_add_apply]
  have hsum : m + 1 + m = 2 * m + 1 := by omega
  rw [hsum, iterateFrobeniusEquiv_period]

/-- Evaluation formula for the inverse Tits twist. -/
theorem titsTwist_symm_apply (m : ℕ) (x : Field m) :
    (titsTwist m).symm x = x ^ (2 ^ m) := by
  rw [titsTwist_symm, iterateFrobeniusEquiv_def]

/-- The square of the Tits twist is the characteristic-two Frobenius map. -/
theorem titsTwist_twice (m : ℕ) (x : Field m) :
    titsTwist m (titsTwist m x) = x ^ 2 := by
  rw [titsTwist, ← iterateFrobeniusEquiv_add_apply]
  have hsum : m + 1 + (m + 1) = 1 + (2 * m + 1) := by omega
  rw [hsum, iterateFrobeniusEquiv_add_apply, iterateFrobeniusEquiv_period,
    iterateFrobeniusEquiv_one_apply]

/-- As ring equivalences, `θ²` is the characteristic-two Frobenius equivalence. -/
theorem titsTwist_sq (m : ℕ) :
    titsTwist m ^ 2 = frobeniusEquiv (Field m) 2 := by
  ext x
  simpa [pow_two, frobenius_def] using titsTwist_twice m x

/-- `a θ(a)` vanishes only at `a = 0`. -/
theorem mul_titsTwist_eq_zero_iff (m : ℕ) {a : Field m} :
    a * titsTwist m a = 0 ↔ a = 0 := by
  refine ⟨fun ha => ?_, fun ha => by rw [ha, map_zero, mul_zero]⟩
  rcases mul_eq_zero.mp ha with h | h
  · exact h
  · exact (titsTwist m).injective (by rw [h, map_zero])

/-- **The quadratic map `a ↦ a θ(a)` is injective.**

This is the multiplication rule for squares in the Suzuki root group
(`RootGroup.sq_eq`), so injectivity says that squaring in a Suzuki `2`-group of
type A is injective modulo the central line — the step Peterfalvi uses in
Part II, Ch. III §1, Proposition, case (3) ("since `C_S(P)` is of type A, it
follows that `y ∈ x Ω₁ C_S(P)`", p. 117).

The proof needs only the defining identity `θ(θ x) = x²`
(`titsTwist_twice`): applying `θ` to `a θ(a) = b θ(b)` gives
`θ(a) a² = θ(b) b²`, and multiplying the original by `a` turns the left-hand
side into `a b θ(b)`, so `a b θ(b) = b² θ(b)` and `b`, `θ(b)` cancel.

Restricted to units this is the injectivity of the torus weight
(`torusWeightUnit_injective`), which is what Ch. I §3 Lemma 1 needs; the
statement here covers `0` as well, which is what the square map on the whole
root group needs. -/
theorem mul_titsTwist_injective (m : ℕ) :
    Function.Injective (fun a : Field m => a * titsTwist m a) := by
  intro a b hab
  simp only at hab
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, mul_zero] at hab
    exact (mul_titsTwist_eq_zero_iff m).mp hab
  have hθb : titsTwist m b ≠ 0 := fun h =>
    hb ((titsTwist m).injective (by rw [h, map_zero]))
  have h2 : titsTwist m a * a ^ 2 = titsTwist m b * b ^ 2 := by
    have h := congrArg (titsTwist m) hab
    rwa [map_mul, map_mul, titsTwist_twice, titsTwist_twice] at h
  have hkey : b * (a * titsTwist m b) = b * (b * titsTwist m b) :=
    calc b * (a * titsTwist m b) = a * (b * titsTwist m b) := by ring
      _ = a * (a * titsTwist m a) := by rw [hab]
      _ = titsTwist m a * a ^ 2 := by ring
      _ = titsTwist m b * b ^ 2 := h2
      _ = b * (b * titsTwist m b) := by ring
  exact mul_right_cancel₀ hθb (mul_left_cancel₀ hb hkey)

end OddOrder.GroupTheory.SpecificGroups.Suzuki
