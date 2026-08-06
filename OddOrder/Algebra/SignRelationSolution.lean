/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The last step of Brauer–Suzuki: three sign relations force `χ_1(t) = χ_1(1)`

Navarro closes the proof of the `Q₈` case of Brauer–Suzuki on p. 145 with a substitution.  With
signs `δ_1, δ_2 = ±1` and the two characters `χ_1, χ_2` surviving the "analysis at `t`", the
relations reached on pp. 143 and 145 are

* (6)  `1 + δ_1 χ_1(t) - δ_2 χ_2(t) = 0`,
* (7)  `1 + δ_1 χ_1(1) + δ_2 χ_2(1) = 0`,
* (10) `χ_1(1) χ_2(1) + δ_1 χ_1(t)² χ_2(1) + δ_2 χ_2(t)² χ_1(1) = 0`.

Solving (6) and (7) for `χ_2(t)` and `χ_2(1)` and substituting into (10) collapses it to
`-δ_2 δ_1 (χ_1(1) - χ_1(t))² = 0`, so `t ∈ ker χ_1` and `ker χ_1` is the proper normal subgroup
the induction asks for.

The whole step is a ring identity in six elements, with `δ_i² = 1` as the only side condition, so
it is stated here with no group theory attached.  (10) itself comes from Burnside's class-sum
formula applied to the class of `t` — the product of two involutions has odd order, so no
`2`-singular element is such a product.

## Main results

* `OddOrder.Algebra.eq_of_sign_relations`
-/

namespace OddOrder.Algebra

/-- **Navarro p. 145**: the three relations (6), (7), (10) force `a = b`, i.e. `χ_1(1) = χ_1(t)`.

`a = χ_1(1)`, `b = χ_1(t)`, `c₁ = χ_2(1)`, `c₂ = χ_2(t)`, and `δ₁, δ₂` are the two signs. -/
theorem eq_of_sign_relations {R : Type*} [CommRing R] [IsDomain R] {δ₁ δ₂ a b c₁ c₂ : R}
    (hδ₁ : δ₁ * δ₁ = 1) (hδ₂ : δ₂ * δ₂ = 1)
    (h6 : 1 + δ₁ * b - δ₂ * c₂ = 0)
    (h7 : 1 + δ₁ * a + δ₂ * c₁ = 0)
    (h10 : a * c₁ + δ₁ * b ^ 2 * c₁ + δ₂ * c₂ ^ 2 * a = 0) :
    a = b := by
  have hc₁ : c₁ = -δ₂ * (1 + δ₁ * a) := by linear_combination δ₂ * h7 - c₁ * hδ₂
  have hc₂ : c₂ = δ₂ * (1 + δ₁ * b) := by linear_combination (-δ₂) * h6 - c₂ * hδ₂
  subst hc₁
  subst hc₂
  have key : δ₂ * δ₁ * (a - b) ^ 2 = 0 := by
    linear_combination (-1 : R) * h10 + (δ₂ * (1 + δ₁ * b) ^ 2 * a) * hδ₂
  have hsq : (a - b) ^ 2 = 0 := by
    linear_combination (δ₂ * δ₁) * key - ((a - b) ^ 2 * δ₁ ^ 2) * hδ₂ - ((a - b) ^ 2) * hδ₁
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq)

end OddOrder.Algebra
