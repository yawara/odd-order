/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Additive subgroups of a field that are closed under inversion

An additive subgroup `W` of a field which is also closed under inversion is very rigid: after
rescaling by any nonzero `s ∈ W`, it becomes a *subring*.  The mechanism is **Hua's identity**

`x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x² / y`,

which expresses `x² / y` using only additions and inversions, so `W` is closed under `(x, y) ↦
x²/y`.  Taking `y = s` shows that `K = {v : s * v ∈ W}` is closed under squaring, and in
characteristic three `u * v = u² + v² - (u + v)²` turns that into closure under multiplication.

## Where this is used

This is the algebraic core of the *same-coset obstruction* for BG Appendix C, Problem 1
(`notes/bg/appC_problem1_partial_resolution.md`, issue 0180).  There one shows that

`W = {s : x and the second-layer element b(s t^E) commute for every t}`

is an additive subgroup closed under `s ↦ s⁻¹`.  Since `𝔽_{3^q}` with `q` prime has no
intermediate subfield, `W` is then forced to be either the prime field — which pins the collision
value to `-1` and makes its trace non-zero — or all of `𝔽_{3^q}`, which makes the two layers
centralise each other and contradicts the perfectness of `N`.  Either way no witness survives, and
crucially *no* hypothesis on the trace is needed.

## Main results

* `hua_identity` — `x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x² / y`.
* `sq_div_mem` — an inversion-closed additive subgroup is closed under `(x, y) ↦ x² / y`.
* `scaledSubring` — `{v : s * v ∈ W}` as a `Subring`, in characteristic three.
* `scaledSubfield` — the same, as a `Subfield`; `eq_smul_scaledSubfield` recovers `W = s • K`.
-/

namespace OddOrder.InverseClosed

variable {F : Type*} [Field F]

/-- **Hua's identity** in a commutative field: `x² / y` is built from `x` and `y` by additions and
inversions alone.  (In `mathlib`'s convention `0⁻¹ = 0`, but the identity is stated where all the
inverses are genuine.) -/
theorem hua_identity {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x ^ 2 / y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hval : x⁻¹ + (y - x)⁻¹ = y / (x * (y - x)) := by
    field_simp
    ring
  rw [hval, inv_div]
  field_simp
  ring

variable (W : AddSubgroup F)

/-- **Closure under `(x, y) ↦ x² / y`.**  This is Hua's identity read inside `W`: every term on
its right-hand side is an inverse or a difference of elements of `W`. -/
theorem sq_div_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {x y : F} (hx : x ∈ W) (hy : y ∈ W) (hy0 : y ≠ 0) :
    x ^ 2 / y ∈ W := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne x y with rfl | hxy
  · rw [sq, mul_div_assoc, div_self hx0, mul_one]
    exact hx
  rw [← hua_identity hx0 hy0 hxy]
  exact W.sub_mem hx (hinv _ (W.add_mem (hinv _ hx) (hinv _ (W.sub_mem hy hx))))

/-- Rescaling by a fixed `s ∈ W` turns closure under `x² / y` into closure under squaring. -/
theorem mul_sq_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {s v : F} (hs : s ∈ W) (hs0 : s ≠ 0)
    (hv : s * v ∈ W) : s * v ^ 2 ∈ W := by
  have key : (s * v) ^ 2 / s = s * v ^ 2 := by
    field_simp
  rw [← key]
  exact sq_div_mem W hinv hv hs hs0

/-- In characteristic three, `u * v = u² + v² - (u + v)²`, so closure under squaring upgrades to
closure under multiplication. -/
theorem mul_mul_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s u v : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) (hu : s * u ∈ W) (hv : s * v ∈ W) : s * (u * v) ∈ W := by
  have hsum : s * (u + v) ∈ W := by
    have : s * (u + v) = s * u + s * v := by ring
    rw [this]
    exact W.add_mem hu hv
  have key : s * (u * v) = s * u ^ 2 + s * v ^ 2 - s * (u + v) ^ 2 := by
    linear_combination (s * u * v) * h3
  rw [key]
  exact W.sub_mem (W.add_mem (mul_sq_mem W hinv hs hs0 hu) (mul_sq_mem W hinv hs hs0 hv))
    (mul_sq_mem W hinv hs hs0 hsum)

/-- **The rescaled subgroup is a subring.**  For an inversion-closed additive subgroup `W` of a
field of characteristic three and a nonzero `s ∈ W`, the set `{v : s * v ∈ W}` is a subring. -/
def scaledSubring (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) : Subring F where
  carrier := {v | s * v ∈ W}
  zero_mem' := by
    change s * (0 : F) ∈ W
    simp
  one_mem' := by
    change s * (1 : F) ∈ W
    simpa using hs
  add_mem' := by
    intro u v hu hv
    change s * (u + v) ∈ W
    have h : s * (u + v) = s * u + s * v := by ring
    rw [h]
    exact W.add_mem hu hv
  neg_mem' := by
    intro u hu
    change s * (-u) ∈ W
    have h : s * (-u) = -(s * u) := by ring
    rw [h]
    exact W.neg_mem hu
  mul_mem' := fun hu hv => mul_mul_mem W hinv h3 hs hs0 hu hv

@[simp]
theorem mem_scaledSubring (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) {v : F} : v ∈ scaledSubring W hinv h3 hs hs0 ↔ s * v ∈ W := Iff.rfl

/-- **The rescaled subgroup is a subfield.**  Inverses come for free: `s * v⁻¹ = s² / (s * v)`,
which `sq_div_mem` supplies.  (No finiteness is needed.) -/
def scaledSubfield (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F}
    (hs : s ∈ W) (hs0 : s ≠ 0) : Subfield F :=
  { scaledSubring W hinv h3 hs hs0 with
    inv_mem' := by
      intro v hv
      rcases eq_or_ne v 0 with rfl | hv0
      · change s * (0 : F)⁻¹ ∈ W
        simp
      change s * v⁻¹ ∈ W
      have hsv : s * v ∈ W := hv
      have key : s ^ 2 / (s * v) = s * v⁻¹ := by
        rw [sq, mul_div_mul_left _ _ hs0, div_eq_mul_inv]
      rw [← key]
      exact sq_div_mem W hinv hs hsv (mul_ne_zero hs0 hv0) }

@[simp]
theorem mem_scaledSubfield (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) {v : F} : v ∈ scaledSubfield W hinv h3 hs hs0 ↔ s * v ∈ W := Iff.rfl

/-- **The subgroup is recovered from the subfield**: `W = s • K`. -/
theorem eq_smul_scaledSubfield (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) {w : F} : w ∈ W ↔ ∃ v ∈ scaledSubfield W hinv h3 hs hs0, w = s * v := by
  constructor
  · intro hw
    refine ⟨s⁻¹ * w, ?_, ?_⟩
    · change s * (s⁻¹ * w) ∈ W
      rwa [← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    · rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  · rintro ⟨v, hv, rfl⟩
    exact hv

end OddOrder.InverseClosed
