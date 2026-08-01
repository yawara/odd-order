/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AnisotropicNormForm

/-!
# The Hermitian cocycle of a quadratic extension, corrected into the subfield

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 130–131.

For `E = 𝐅_{q²}` of characteristic `2` with subfield `F = 𝐅_q`, the unitary
coordinates of `PSU(3, q)` present the unipotent group as pairs `(a, b)` of elements of
`E` with `Tr b = a ā`, multiplying by `(a, b)(c, d) = (a + c, b + d + a c̄)`.  The
cocycle `a c̄` is `E`-valued, whereas Chapter III §3's model has a cocycle valued in
`F`.  The dictionary between the two corrects the second coordinate by the norm:

  `b ↦ b + u a ā` (`Tr u = 1`),

which lands in `F` and turns the `E`-valued cocycle `a c̄` into `a c̄ + u Tr(a c̄)`.

This file develops that over an arbitrary quadratic extension; the case
`E = ProjectiveUnitary.Field n` is
`OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.rootBilin`, where `x ↦ x^q` is
written `star`.

## Main results

* `OddOrder.FiniteField.frobPow_frobPow` — `x^{q²} = x`.
* `OddOrder.FiniteField.norm_mem_frobFixed` — the Hermitian norm `a ā` lies in `F`.
* `OddOrder.FiniteField.norm_cocycle` — the coboundary of `a ↦ u a ā` is `u Tr(a c̄)`.
* `OddOrder.FiniteField.hermitianCocycle` — the corrected cocycle `x ȳ + u Tr(x ȳ)`,
  as an `F`-valued bilinear map, with diagonal the norm
  (`hermitianCocycle_diag`).
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

section HermitianCocycle

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E] (m : ℕ)

omit [Algebra (ZMod 2) E] in
/-- **The `q`-power map is an involution** on a field of order `q²`. -/
theorem frobPow_frobPow (hcard : Nat.card E = (2 ^ m) ^ 2) (x : E) :
    (x ^ 2 ^ m) ^ 2 ^ m = x := by
  have h := congrFun (congrArg (fun σ : RingAut E => (σ : E → E)) (qFrobenius_sq hcard)) x
  simpa only [RingAut.mul_apply, qFrobenius_apply, RingAut.one_apply] using
    (by
      have h2 : (qFrobenius E 2 m ^ 2) x = x := by
        rw [qFrobenius_sq hcard]; rfl
      rw [pow_two, RingAut.mul_apply, qFrobenius_apply, qFrobenius_apply] at h2
      exact h2)

omit [Algebra (ZMod 2) E] in
/-- **The Hermitian norm lands in `F`**: `(a ā)^q = ā a`. -/
theorem norm_mem_frobFixed (hcard : Nat.card E = (2 ^ m) ^ 2) (a : E) :
    a * a ^ 2 ^ m ∈ frobFixedSubfield E 2 m := by
  rw [mem_frobFixedSubfield, mul_pow, frobPow_frobPow m hcard]
  ring

/-- **The coboundary of `a ↦ u a ā` is the trace term**: expanding `(a+c)(ā+c̄)` leaves
`a c̄ + c ā = Tr (a c̄)`.  This is what turns the `E`-valued Hermitian cocycle into an
`F`-valued one. -/
theorem norm_cocycle (hcard : Nat.card E = (2 ^ m) ^ 2) (u a c : E) :
    u * (a * a ^ 2 ^ m) + u * (c * c ^ 2 ^ m)
        + u * ((a + c) * (a + c) ^ 2 ^ m)
      = u * frobTrace (E := E) m (a * c ^ 2 ^ m) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hadd : (a + c) ^ 2 ^ m = a ^ 2 ^ m + c ^ 2 ^ m := by rw [add_pow_char_pow]
  rw [frobTrace_apply, hadd, mul_pow, frobPow_frobPow m hcard]
  linear_combination (u * (a * a ^ 2 ^ m) + u * (c * c ^ 2 ^ m)) * h2

/-! ## The corrected cocycle -/

/-- The Hermitian cocycle `(x, y) ↦ x ȳ`, as a `ZMod 2`-bilinear map. -/
noncomputable def hermitianBilin (m : ℕ) :
    LinearMap.BilinMap (ZMod 2) E E where
  toFun x :=
    { toFun := fun y => x * y ^ 2 ^ m
      map_add' := fun y y' => by rw [add_pow_char_pow, mul_add]
      map_smul' := fun c y => by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;>
          simp }
  map_add' x x' := LinearMap.ext fun y => by simp [add_mul]
  map_smul' c x := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;>
      exact LinearMap.ext fun y => by simp

omit [Finite E] in
@[simp] theorem hermitianBilin_apply (x y : E) :
    hermitianBilin (E := E) m x y = x * y ^ 2 ^ m := rfl

/-- The trace correction `x ȳ + u Tr(x ȳ)` of the Hermitian cocycle: it has the same
diagonal and, when `Tr u = 1`, takes its values in `F`. -/
noncomputable def correctedBilin (m : ℕ) (u : E) :
    LinearMap.BilinMap (ZMod 2) E E :=
  hermitianBilin m + u • (hermitianBilin m).compr₂ (frobTrace (E := E) m)

@[simp] theorem correctedBilin_apply (u x y : E) :
    correctedBilin m u x y
      = x * y ^ 2 ^ m + u * frobTrace (E := E) m (x * y ^ 2 ^ m) := by
  simp only [correctedBilin, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.compr₂_apply, hermitianBilin_apply, smul_eq_mul]

/-- **The corrected cocycle is `F`-valued** when `Tr u = 1`. -/
theorem correctedBilin_mem (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x y : E) :
    correctedBilin m u x y ∈ frobFixedSubfield E 2 m := by
  rw [← frobTrace_eq_zero_iff, correctedBilin_apply, map_add,
    mul_comm u (frobTrace (E := E) m (x * y ^ 2 ^ m)),
    frobTrace_mul_of_mem m (frobTrace_mem m hcard (x * y ^ 2 ^ m)) u, hu, mul_one]
  exact CharTwo.add_self_eq_zero _

/-- **The Hermitian cocycle of `E / F`**, corrected to take its values in `F`: the
cocycle of the unitary coordinates of `PSU(3, q)` in the shape that
`BilinearTwistedProduct` consumes. -/
noncomputable def hermitianCocycle (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) :
    LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m) :=
  bilinCodRestrict m (correctedBilin m u) (correctedBilin_mem m hcard hu)

@[simp] theorem hermitianCocycle_apply (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x y : E) :
    ((hermitianCocycle m hcard hu x y : ↥(frobFixedSubfield E 2 m)) : E)
      = x * y ^ 2 ^ m + u * frobTrace (E := E) m (x * y ^ 2 ^ m) := by
  rw [hermitianCocycle]
  change correctedBilin m u x y = _
  rw [correctedBilin_apply]

/-- **The diagonal of the Hermitian cocycle is the norm**: the correction vanishes
there, since `a ā` already lies in `F`. -/
@[simp] theorem hermitianCocycle_diag (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x : E) :
    ((hermitianCocycle m hcard hu x x : ↥(frobFixedSubfield E 2 m)) : E)
      = x * x ^ 2 ^ m := by
  rw [hermitianCocycle_apply,
    (frobTrace_eq_zero_iff m (x * x ^ 2 ^ m)).mpr (norm_mem_frobFixed m hcard x),
    mul_zero, add_zero]

/-- **The Hermitian cocycle scales by the norm**: `φ (d x) (d y) = d^{1+q} φ x y`.

This is the action of the torus of `PSU(3, q)` on the unipotent group,
`(x, y)^d = (d x, d^{1+q} y)`; the scalar `d^{1+q}` lies in `F`, which is why it passes
through the trace correction unchanged. -/
theorem hermitianCocycle_smul (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (d x y : E) :
    ((hermitianCocycle m hcard hu (d * x) (d * y) :
      ↥(frobFixedSubfield E 2 m)) : E)
      = d * d ^ 2 ^ m * ((hermitianCocycle m hcard hu x y :
        ↥(frobFixedSubfield E 2 m)) : E) := by
  have hsplit : (d * x) * (d * y) ^ 2 ^ m = (d * d ^ 2 ^ m) * (x * y ^ 2 ^ m) := by
    rw [mul_pow]
    ring
  rw [hermitianCocycle_apply, hermitianCocycle_apply, hsplit,
    frobTrace_mul_of_mem m (norm_mem_frobFixed m hcard d)]
  ring

end HermitianCocycle

end OddOrder.FiniteField
