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
  letI := Fintype.ofFinite (Field m)
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

end OddOrder.GroupTheory.SpecificGroups.Suzuki
