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

/-- **The unitary coordinate of an element of the centre is its central coordinate** —
the correction `u a ā` vanishes with `a`.  Stated through the quotient coordinate rather
than the constructor, for elements arriving as images of `Z(Q)`. -/
theorem unitaryCoord_of_quotient_eq_zero (u : E)
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    {p : BilinearTwistedProduct φ} (hp : p.quotient = 0) :
    unitaryCoord m u p = (p.central : E) := by
  rw [unitaryCoord, hp, zero_mul, mul_zero, add_zero]

/-- The unitary coordinate of a central element is its central coordinate. -/
@[simp] theorem unitaryCoord_central (u : E)
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    (w : ↥(frobFixedSubfield E 2 m)) :
    unitaryCoord m u (⟨0, w⟩ : BilinearTwistedProduct φ) = (w : E) := by
  change (w : E) + u * ((0 : E) * (0 : E) ^ 2 ^ m) = (w : E)
  rw [zero_mul, mul_zero, add_zero]

@[simp] theorem unitaryCoord_one (u : E)
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)} :
    unitaryCoord m u (1 : BilinearTwistedProduct φ) = 0 := by
  change ((0 : ↥(frobFixedSubfield E 2 m)) : E) + u * ((0 : E) * (0 : E) ^ 2 ^ m) = 0
  rw [zero_mul, mul_zero, add_zero]
  rfl

/-- **Multiplying by a central element shifts the unitary coordinate.**  This is how
the book moves along the fibre `{y : Tr y = a ā}` in §3 (4): `ω s^a` has unitary
coordinate `x + a`. -/
theorem unitaryCoord_mul_central (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu))
    (w : ↥(frobFixedSubfield E 2 m)) :
    unitaryCoord m u (p * ⟨0, w⟩) = unitaryCoord m u p + (w : E) := by
  have hz : (0 : E) ^ 2 ^ m = 0 := zero_pow (by positivity)
  rw [unitaryCoord_mul m hcard hu, unitaryCoord_central]
  change _ = unitaryCoord m u p + (w : E)
  rw [show p.quotient * (0 : E) ^ 2 ^ m = 0 by rw [hz, mul_zero], add_zero]

/-- **Multiplying by an element of the centre just adds its coordinate** — the cocycle
term drops out because a central element has quotient coordinate `0`.

Stated through the quotient coordinate rather than the constructor `⟨0, w⟩`, for the
central elements that arrive as images of `Z(Q)`; that is the form §3 (4) and (5) meet
them in (`ω s^a`, and the factor `(0, a⁻¹)` of §2 (2)). -/
theorem unitaryCoord_mul_of_quotient_eq_zero (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (p q : BilinearTwistedProduct (hermitianCocycle m hcard hu))
    (hq : q.quotient = 0) :
    unitaryCoord m u (p * q) = unitaryCoord m u p + unitaryCoord m u q := by
  rw [unitaryCoord_mul m hcard hu, hq, zero_pow (by positivity), mul_zero, add_zero]

/-- **The square is central with unitary coordinate the norm** — the relation
`ω² = (0, ω̄^{1+q})` of §3 (3). -/
theorem unitaryCoord_sq (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    unitaryCoord m u (p ^ 2) = p.quotient * p.quotient ^ 2 ^ m := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  rw [pow_two, unitaryCoord_mul m hcard hu]
  change (p.central : E) + u * (p.quotient * p.quotient ^ 2 ^ m)
    + ((p.central : E) + u * (p.quotient * p.quotient ^ 2 ^ m))
    + p.quotient * p.quotient ^ 2 ^ m = _
  linear_combination ((p.central : E) + u * (p.quotient * p.quotient ^ 2 ^ m)) * h2

/-- **Inversion conjugates the unitary coordinate**: `(a, y)⁻¹ = (a, ȳ)`.

The relation `Tr u = 1` enters as `u^q = u + 1`, which converts the shift by the norm
into the `q`-power. -/
theorem unitaryCoord_inv (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    unitaryCoord m u p⁻¹ = (unitaryCoord m u p) ^ 2 ^ m := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hnegq : -p.quotient = p.quotient := by linear_combination (-p.quotient) * h2
  have huq : u ^ 2 ^ m = u + 1 := by
    rw [frobTrace_apply] at hu
    linear_combination hu - u * h2
  have hzq : ((p.central : E)) ^ 2 ^ m = (p.central : E) :=
    mem_frobFixedSubfield.mp p.central.2
  have hNq : (p.quotient * p.quotient ^ 2 ^ m) ^ 2 ^ m
      = p.quotient * p.quotient ^ 2 ^ m :=
    mem_frobFixedSubfield.mp (norm_mem_frobFixed m hcard p.quotient)
  have hval : unitaryCoord m u p⁻¹
      = ((hermitianCocycle m hcard hu p.quotient p.quotient :
          ↥(frobFixedSubfield E 2 m)) : E) - (p.central : E)
        + u * (-p.quotient * (-p.quotient) ^ 2 ^ m) := rfl
  have hexp : ((p.central : E) + u * (p.quotient * p.quotient ^ 2 ^ m)) ^ 2 ^ m
      = (p.central : E) + (u + 1) * (p.quotient * p.quotient ^ 2 ^ m) := by
    rw [add_pow_char_pow, mul_pow, hzq, huq, hNq]
  rw [hval, hermitianCocycle_diag m hcard hu, hnegq, unitaryCoord, hexp]
  linear_combination (-(p.central : E)) * h2

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

/-- **A scaling automorphism scales the centre by the norm of its quotient scalar**
(Peterfalvi Part II, Ch. IV §3, p. 131: the torus element acting as `d` on the first
coordinate acts as `d^{1+q}` on the second).

The hypothesis is only that the cocycle's diagonal is a nonzero multiple of the norm,
which is what Ch. III §3's model provides (`cocycle_diag_eq_norm`).  The two scalars
are then linked by squaring `(1, 0)`: its square is central with coordinate `φ(1,1)`,
and the image of that square is central with coordinate `φ(a, a) = φ(1,1) a^{1+q}`.

This is the missing half of the dictionary between the model action of `K W` — whose
central scalar is recorded as an opaque power `μ(k,1)^d` — and the unitary
coordinates. -/
theorem centralScale_eq_norm_of_quotientScale
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    (hone : ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) ≠ 0)
    (hdiag : ∀ x : E, ((φ x x : ↥(frobFixedSubfield E 2 m)) : E)
      = ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) * x ^ (2 ^ m + 1))
    (σ : BilinearTwistedProduct φ ≃* BilinearTwistedProduct φ) {a ν : E}
    (hq : ∀ p : BilinearTwistedProduct φ, (σ p).quotient = a * p.quotient)
    (hc : ∀ p : BilinearTwistedProduct φ,
      (((σ p).central : ↥(frobFixedSubfield E 2 m)) : E)
        = ν * ((p.central : ↥(frobFixedSubfield E 2 m)) : E)) :
    ν = a ^ (2 ^ m + 1) := by
  set p : BilinearTwistedProduct φ := ⟨1, 0⟩ with hp
  have hpq : p.quotient = 1 := rfl
  have hpc : ((p.central : ↥(frobFixedSubfield E 2 m)) : E) = 0 := rfl
  have hσq : (σ p).quotient = a := by rw [hq, hpq, mul_one]
  have hσc : (((σ p).central : ↥(frobFixedSubfield E 2 m)) : E) = 0 := by
    rw [hc, hpc, mul_zero]
  have hL : (((σ (p * p)).central : ↥(frobFixedSubfield E 2 m)) : E)
      = ν * ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) := by
    rw [hc (p * p)]
    congr 1
    change ((φ p.quotient p.quotient + p.central + p.central :
      ↥(frobFixedSubfield E 2 m)) : E) = _
    push_cast
    rw [hpq, hpc]
    ring
  have hR : (((σ p * σ p).central : ↥(frobFixedSubfield E 2 m)) : E)
      = ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) * a ^ (2 ^ m + 1) := by
    change ((φ (σ p).quotient (σ p).quotient + (σ p).central + (σ p).central :
      ↥(frobFixedSubfield E 2 m)) : E) = _
    push_cast
    rw [hσq, hσc, hdiag a]
    ring
  rw [map_mul, hR] at hL
  exact mul_left_cancel₀ hone (by linear_combination -hL)

/-- **The torus scales the unitary coordinate by the norm**: `(a, y)^d = (d a, d^{1+q} y)`
(Peterfalvi Part II, p. 131, the display in the proof of stage (5)).

Stated through the two coordinates of the scaled element rather than through the
automorphism itself, so that it applies to whatever realization of the action is at
hand. -/
theorem unitaryCoord_of_scaled {u : E}
    {φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m)}
    (d : E) {p q : BilinearTwistedProduct φ} (hq1 : q.quotient = d * p.quotient)
    (hq2 : (q.central : E) = d * d ^ 2 ^ m * (p.central : E)) :
    unitaryCoord m u q = d * d ^ 2 ^ m * unitaryCoord m u p := by
  rw [unitaryCoord, unitaryCoord, hq1, hq2, mul_pow]
  ring

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
