/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Peterfalvi Part II, Ch. IV §4: solving (5) and (6)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 133.

Writing `X` for the quotient coordinate `f(ω s^b)‾` and `Y` for its `η`-image, the
book's equations read

* **(5)** `ζ X = a^{-2μ} Y + ω̄`,
* **(6)** `b² X = ζ⁻¹ Y + ω̄`,

and "suitable linear combinations of (5) and (6) then show that `a^{2μ} + b² ≠ 0` and
that"

* **(7)** `X = (a^{2μ} + ζ) / (ζ (a^{2μ} + b²)) · ω̄`,
* **(8)** `Y = (b² + ζ) / (b² a^{-2μ} + 1) · ω̄`.

This file is that linear algebra, in a field of characteristic `2` — two linear
equations in the two unknowns `X`, `Y`.  Writing `A = a^{2μ}`, `B = b²` and `c = ζ`:
multiplying (5) by `A` and (6) by `c` clears the inverses, and adding the two (the
characteristic being `2`) eliminates `Y`.

`sectionFour_eq_of_add_eq_zero` is the other half of the quoted sentence: the
denominator can only vanish when `A = c`, which the group theory then excludes.

The book's `(8)` is written with the denominator `b² a^{-2μ} + 1`; multiplying
numerator and denominator by `a^{2μ}` gives the form used here, which avoids inverses.

## Main results

* `sectionFour_solve` — (5) and (6) with `Y` eliminated, in inverse-free form.
* `sectionFour_seven`, `sectionFour_eight` — the displayed (7) and (8).
* `sectionFour_eq_of_add_eq_zero` — a vanishing denominator forces `a^{2μ} = ζ`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section SectionFourArithmetic

variable {E : Type*} [Field E]

/-- **Peterfalvi Part II, Ch. IV §4, (5) and (6) with `Y` eliminated** (p. 133).

Multiplying (5) by `A` gives `A c X = Y + A ω̄` and (6) by `c` gives `c B X = Y + c ω̄`;
adding them kills `Y` because the characteristic is `2`.  Feeding the result back into
the first gives the companion equation for `Y`.

Both conclusions are stated without inverses, so that the divided forms (7) and (8)
follow by a single cancellation. -/
theorem sectionFour_solve (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0) (hc : c ≠ 0)
    (h5 : c * X = A⁻¹ * Y + w) (h6 : B * X = c⁻¹ * Y + w) :
    c * ((A + B) * X) = (A + c) * w ∧ (A + B) * Y = A * ((B + c) * w) := by
  have hA' : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hc' : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have e5 : A * c * X = Y + A * w := by
    calc A * c * X = A * (c * X) := by ring
      _ = A * (A⁻¹ * Y + w) := by rw [h5]
      _ = A * A⁻¹ * Y + A * w := by ring
      _ = Y + A * w := by rw [hA', one_mul]
  have e6 : c * B * X = Y + c * w := by
    calc c * B * X = c * (B * X) := by ring
      _ = c * (c⁻¹ * Y + w) := by rw [h6]
      _ = c * c⁻¹ * Y + c * w := by ring
      _ = Y + c * w := by rw [hc', one_mul]
  have e7 : c * ((A + B) * X) = (A + c) * w := by
    linear_combination e5 + e6 + Y * h2
  refine ⟨e7, ?_⟩
  have hYval : Y = A * c * X + A * w := by
    linear_combination -e5 - (A * w) * h2
  rw [hYval]
  linear_combination A * e7 + (A * A * w) * h2

/-- **Peterfalvi Part II, Ch. IV §4, (7)** (p. 133). -/
theorem sectionFour_seven (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0) (hc : c ≠ 0)
    (hAB : A + B ≠ 0) (h5 : c * X = A⁻¹ * Y + w) (h6 : B * X = c⁻¹ * Y + w) :
    X = (A + c) / (c * (A + B)) * w := by
  have e7 := (sectionFour_solve h2 hA hc h5 h6).1
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hc hAB)]
  linear_combination e7

/-- **Peterfalvi Part II, Ch. IV §4, (8)** (p. 133).

The book writes the right-hand side as `(b² + ζ) / (b² a^{-2μ} + 1) · ω̄`; multiplying
numerator and denominator by `a^{2μ}` gives the inverse-free form used here. -/
theorem sectionFour_eight (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0) (hc : c ≠ 0)
    (hAB : A + B ≠ 0) (h5 : c * X = A⁻¹ * Y + w) (h6 : B * X = c⁻¹ * Y + w) :
    Y = A * (B + c) / (A + B) * w := by
  have e8 := (sectionFour_solve h2 hA hc h5 h6).2
  rw [div_mul_eq_mul_div, eq_div_iff hAB]
  linear_combination e8

/-- **The denominator of (7) and (8) vanishes only when `a^{2μ} = ζ`** (Peterfalvi
Part II, Ch. IV §4, p. 133: "suitable linear combinations of (5) and (6) then show that
`a^{2μ} + b² ≠ 0`").

If `A + B = 0` then the left-hand side of `sectionFour_solve` vanishes, so `(A + c) ω̄`
does; and `ω̄ ≠ 0` because `ω ∉ Q₀`. -/
theorem sectionFour_eq_of_add_eq_zero (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0)
    (hc : c ≠ 0) (hw : w ≠ 0) (h5 : c * X = A⁻¹ * Y + w) (h6 : B * X = c⁻¹ * Y + w)
    (hAB : A + B = 0) : A = c := by
  have e7 := (sectionFour_solve h2 hA hc h5 h6).1
  rw [hAB, zero_mul, mul_zero] at e7
  have hAc : A + c = 0 := by
    rcases mul_eq_zero.mp e7.symm with h | h
    · exact h
    · exact absurd h hw
  linear_combination hAc - c * h2

end SectionFourArithmetic

end OddOrder.Peterfalvi.Appendices.Suzuki
