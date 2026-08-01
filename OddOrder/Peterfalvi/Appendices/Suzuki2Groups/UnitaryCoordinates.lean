/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.HermitianCocycle
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions

/-!
# The unitary coordinates of a Hermitian twisted product

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4), p. 131.

Stage (4) of §3 is stated in the coordinates of `PSU(3, q)`: an element of `Q` is a
pair `(a, y)` of elements of `E` with `Tr y = a ā`, and

  `(a, y) (c, w) = (a + c, y + w + a c̄)`.

The twisted product `BilinearTwistedProduct (hermitianCocycle …)` is the same group
written with its second coordinate in the subfield `F`; the dictionary is
`y = z + u a ā`, whose inverse is `z = y + u a ā` (characteristic two).

Rather than introduce a second carrier type, this file provides that dictionary as a
*coordinate function* `unitaryCoord` together with its two defining properties, plus
the reverse construction `ofUnitary`.  So the book's formulas can be read and written
directly on the twisted product of Chapter III §3.

## Main results

* `unitaryCoord` — the second unitary coordinate `y = z + u a ā`.
* `unitaryCoord_frobTrace` — `Tr y = a ā`, the defining relation of the coordinates.
* `unitaryCoord_mul` — the multiplication rule `y + w + a c̄` of `PSU(3, q)`.
* `ofUnitary` — the element with prescribed unitary coordinates, and
  `eq_of_unitaryCoord_eq` — those coordinates determine it.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.FiniteField

section UnitaryCoordinates

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E] (m : ℕ)

/-- **The unitary second coordinate** of a twisted-product element: correcting the
`F`-valued central coordinate by the norm produces the `E`-valued coordinate of
`PSU(3, q)`. -/
def unitaryCoord (u : E)
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    (p : BilinearTwistedProduct φ) : E :=
  (p.central : E) + u * (p.quotient * p.quotient ^ 2 ^ m)

/-- **The defining relation of the unitary coordinates**: `Tr y = a ā`.

The central coordinate is traceless because it lies in `F`, and `Tr (u a ā) = a ā`
because the norm lies in `F` and `Tr u = 1`. -/
theorem unitaryCoord_frobTrace (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    (p : BilinearTwistedProduct φ) :
    frobTrace (E := E) m (unitaryCoord m u p)
      = p.quotient * p.quotient ^ 2 ^ m := by
  rw [unitaryCoord, map_add,
    (frobTrace_eq_zero_iff m (p.central : E)).mpr p.central.2, zero_add,
    mul_comm u, frobTrace_mul_of_mem m (norm_mem_frobFixed m hcard p.quotient) u, hu,
    mul_one]

/-- **The multiplication rule of `PSU(3, q)`** in the unitary coordinates:
`(a, y)(c, w) = (a + c, y + w + a c̄)`.

The correction `a ↦ u a ā` fails to be additive by exactly the trace term by which the
corrected cocycle differs from the Hermitian one (`norm_cocycle`); the two cancel. -/
theorem unitaryCoord_mul (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (p q : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    unitaryCoord m u (p * q)
      = unitaryCoord m u p + unitaryCoord m u q
        + p.quotient * q.quotient ^ 2 ^ m := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hc := norm_cocycle m hcard u p.quotient q.quotient
  have hval : ((hermitianCocycle m hcard hu p.quotient q.quotient :
      ↥(frobFixedSubfield E 2 m)) : E)
      = p.quotient * q.quotient ^ 2 ^ m
        + u * frobTrace (E := E) m (p.quotient * q.quotient ^ 2 ^ m) :=
    hermitianCocycle_apply m hcard hu _ _
  change ((p * q).central : E) + u * ((p * q).quotient * (p * q).quotient ^ 2 ^ m) = _
  have hq : ((p * q).quotient : E) = p.quotient + q.quotient := rfl
  have hcen : (((p * q).central : ↥(frobFixedSubfield E 2 m)) : E)
      = ((hermitianCocycle m hcard hu p.quotient q.quotient :
          ↥(frobFixedSubfield E 2 m)) : E)
        + (p.central : E) + (q.central : E) := rfl
  rw [hq, hcen, hval, unitaryCoord, unitaryCoord]
  linear_combination hc
    + (u * frobTrace (E := E) m (p.quotient * q.quotient ^ 2 ^ m)
      - u * (p.quotient * p.quotient ^ 2 ^ m)
      - u * (q.quotient * q.quotient ^ 2 ^ m)) * h2

/-- **The element with prescribed unitary coordinates.**  The correction lands back in
`F` because `Tr y = a ā` is exactly what makes `y + u a ā` traceless. -/
def ofUnitary (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (a y : E)
    (h : frobTrace (E := E) m y = a * a ^ 2 ^ m) :
    BilinearTwistedProduct (hermitianCocycle m hcard hu) where
  quotient := a
  central :=
    ⟨y + u * (a * a ^ 2 ^ m), by
      rw [← frobTrace_eq_zero_iff, map_add, h, mul_comm u,
        frobTrace_mul_of_mem m (norm_mem_frobFixed m hcard a) u, hu, mul_one]
      exact CharTwo.add_self_eq_zero _⟩

@[simp] theorem ofUnitary_quotient (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (a y : E)
    (h : frobTrace (E := E) m y = a * a ^ 2 ^ m) :
    (ofUnitary m hcard hu a y h).quotient = a :=
  rfl

@[simp] theorem ofUnitary_unitaryCoord (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (a y : E)
    (h : frobTrace (E := E) m y = a * a ^ 2 ^ m) :
    unitaryCoord m u (ofUnitary m hcard hu a y h) = y := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  change (y + u * (a * a ^ 2 ^ m)) + u * (a * a ^ 2 ^ m) = y
  linear_combination (u * (a * a ^ 2 ^ m)) * h2

/-- **The unitary coordinates determine the element.** -/
theorem eq_of_unitaryCoord_eq {u : E}
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    {p p' : BilinearTwistedProduct φ} (hq : p.quotient = p'.quotient)
    (hy : unitaryCoord m u p = unitaryCoord m u p') : p = p' := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  refine BilinearTwistedProduct.ext hq (Subtype.ext ?_)
  rw [unitaryCoord, unitaryCoord, hq] at hy
  linear_combination hy

end UnitaryCoordinates

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
