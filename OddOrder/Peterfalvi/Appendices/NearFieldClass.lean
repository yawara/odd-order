/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Near-fields: the `NearField` class

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), Appendix C,
p. 137.  A *(right) near-field* is a set `F` with `+` and `·` such that `(F, +)` is a commutative
group, `(F ∖ {0}, ·)` is a group, and the **right** distributive law `(a + b) c = a c + b c` holds.

This tiny leaf isolates just the `class NearField` (plus the two immediate consequences of the
right distributive law) so that the abstract Zassenhaus construction
(`OddOrder/GroupTheory/NearFieldFromSharplyTransitive.lean`) can depend on the class *without*
pulling in the heavy near-field development in `NearFields.lean` — which in turn lets `NearFields`
import that construction to prove Appendix C, Proposition 1.  The namespace is unchanged
(`OddOrder.Peterfalvi.Appendices.NearFields`), so downstream references `NearFields.NearField`
resolve exactly as before.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields

/-- A **(right) near-field** (Peterfalvi, Appendix C, p. 137): a set `F` with `+` and `·` such that
`(F, +)` is a commutative group, `(F, ·)` is a group with zero — i.e. `(F ∖ {0}, ·)` is a group —
and the **right** distributive law `(a + b) c = a c + b c` holds.  (Left distributivity and
`·`-commutativity may fail; a field is the special case where both also hold.)

Modeled as `AddCommGroup F` + `GroupWithZero F` + right distributivity, so the full multiplicative
group-with-zero API (`mul_inv_cancel₀`, `zero_mul`, `mul_zero`, `zero_ne_one`, …) is inherited. -/
class NearField (F : Type*) extends AddCommGroup F, GroupWithZero F where
  /-- The right distributive law `(a + b) * c = a * c + b * c`. -/
  protected right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c

/-- The right distributive law in a near-field. -/
theorem NearField.add_mul {F : Type*} [NearField F] (a b c : F) :
    (a + b) * c = a * c + b * c := NearField.right_distrib a b c

/-- **A near-field with commutative multiplication is a field** (the meaning of the first
alternative in Peterfalvi, Appendix C, Proposition 2).  A near-field only postulates the *right*
distributive law; if multiplication is commutative the left law follows, so `F` is a commutative
division ring, i.e. a field. -/
theorem NearField.mul_add_of_mul_comm {F : Type*} [NearField F]
    (hcomm : ∀ x y : F, x * y = y * x) (a b c : F) : a * (b + c) = a * b + a * c := by
  rw [hcomm a (b + c), NearField.add_mul, hcomm b a, hcomm c a]

end OddOrder.Peterfalvi.Appendices.NearFields
