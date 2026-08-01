/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3RootGroupModel

/-!
# Peterfalvi Part II, Ch. IV §3 (4): `f` is inversion in the unitary coordinates

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4)–(5), pp. 130–131.

Stage (4) says that on the fibre of `ω̄` — the elements `(ω̄, y)` of `Q` with
`y + y^q = ω̄^{1+q}` — the map `f` is

  `f(ω̄, y) = (ω̄/y, 1/y)`,

and stage (5) removes the restriction to that one fibre.  The proof of (4) reads
stage (1) in the unitary coordinates: writing `ω = (ω̄, x)` and
`f(ω̄, x + a) = (ω̄/(a + ζ⁻¹), γ(a))` (the first coordinate being stage (2)),
comparison of the *second* entries of

  `f(ω̄, x+a)^{ζ⁻¹ a} (0, a) = f(ω̄, x+a)^{ζ⁻²} (ω̄, x)^{ζ⁻¹}`

gives the book's

  `(∗∗)   (a² + 1) γ(a) = x + a + (1 + ζ⁻²)/(a + ζ⁻¹)`   for `a ∈ F − {0}`,

whose `a = 1` instance pins `x = ζ⁻¹` and whose remaining instances then collapse to
`γ(a) = 1/(a + ζ⁻¹)`.

This file carries the arithmetic of that argument, which is where all of its content
sits: once the two coordinate formulas are in hand, `(∗∗)` and its consequences are
statements about the field `E` alone.

## Main results

* `star_of_secondEntry` — the second-entry comparison *is* `(∗∗)`.
* `eq_and_inv_of_star` — `(∗∗)` forces `x = ζ⁻¹` and `γ(a) = 1/(a + ζ⁻¹)`.
* `gamma_eq_inv_of_secondEntry` — the two combined, in the form stage (4) consumes:
  the second unitary coordinate of `f(ω̄, x + a)` is `1/(x + a)`, for `a ∈ F − {0, 1}`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section StepFourArithmetic

variable {E : Type*} [Field E]

/-- **The second-entry comparison of stage (4) is the book's `(∗∗)`** (Peterfalvi
Part II, p. 131).

The left-hand entry is `a² γ(a) + a`: conjugating by `ζ⁻¹ a` scales the unitary
coordinate by the norm `(ζ⁻¹ a)^{1+q} = a²` (`ζ` has norm one, `a` lies in `F`), and
right multiplication by the central `(0, a)` adds `a`.  The right-hand entry is
`γ(a) + x + A C̄`, where `A = ζ⁻² ω̄/(a + ζ⁻¹)` and `C = ζ⁻¹ ω̄` are the two quotient
coordinates — the cocycle term of the unitary multiplication rule.

That cocycle term is where `ζ` and `ω̄` disappear: `A C̄ = ζ⁻² ζ ω̄^{1+q}/(a + ζ⁻¹)`,
using `ζ^{-q} = ζ`, and `ω̄^{1+q} = ζ + ζ⁻¹` by stage (3), leaving
`(1 + ζ⁻²)/(a + ζ⁻¹)`. -/
theorem star_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} {ζ ω x a γa : E}
    (hζ : ζ ≠ 0) (hζnorm : ζ * ζ ^ 2 ^ m = 1) (hω : ω * ω ^ 2 ^ m = ζ + ζ⁻¹)
    (hchain : a ^ 2 * γa + a
      = γa + x + (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m) :
    (a ^ 2 + 1) * γa = x + a + (1 + ζ⁻¹ ^ 2) / (a + ζ⁻¹) := by
  have hζinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  have hζq : ζ ^ 2 ^ m = ζ⁻¹ := by
    field_simp
    linear_combination hζnorm
  have hζinvq : (ζ⁻¹) ^ 2 ^ m = ζ := by rw [inv_pow, hζq, inv_inv]
  -- the cocycle term collapses to `(1 + ζ⁻²)/(a + ζ⁻¹)`
  have hnum : ζ⁻¹ ^ 2 * ω * (ζ * ω ^ 2 ^ m) = 1 + ζ⁻¹ ^ 2 :=
    calc ζ⁻¹ ^ 2 * ω * (ζ * ω ^ 2 ^ m)
        = ζ⁻¹ ^ 2 * ζ * (ω * ω ^ 2 ^ m) := by ring
      _ = ζ⁻¹ ^ 2 * ζ * (ζ + ζ⁻¹) := by rw [hω]
      _ = (ζ * ζ⁻¹) ^ 2 + (ζ * ζ⁻¹) * ζ⁻¹ ^ 2 := by ring
      _ = 1 + ζ⁻¹ ^ 2 := by rw [hζinv]; ring
  have hcoc : (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m
      = (1 + ζ⁻¹ ^ 2) / (a + ζ⁻¹) := by
    rw [mul_pow, hζinvq, div_mul_eq_mul_div, hnum]
  rw [hcoc] at hchain
  linear_combination hchain + (γa - a) * h2

/-- **`(∗∗)` forces `x = w` and `γ(a) = 1/(a + w)`** (Peterfalvi Part II, p. 131,
with `w = ζ⁻¹`).

Only two features of `w` are used: it lies outside the subfield `S = F` (so that `a + w`
never vanishes for `a ∈ S`), and `1 ∈ S`.  Both steps are the same manipulation,
`(a + w)² = a² + w²` in characteristic two:

* at `a = 1` the left side vanishes and `(1 + w²)/(1 + w) = 1 + w`, giving `x = w`;
* at `a ∉ {0, 1}` the right side becomes `[(a + w)² + 1 + w²]/(a + w) = (a² + 1)/(a + w)`,
  and `a² + 1 = (a + 1)²` is invertible.

The excluded value `a = 1` is exactly the one the book recovers at the end of (4) by
replacing `ω` with `ω⁻¹` and `ζ` with `ζ⁻¹`. -/
theorem eq_and_inv_of_star (h2 : (2 : E) = 0) (S : Subfield E) {w x : E} {γ : E → E}
    (hw : w ∉ S)
    (hstar : ∀ a ∈ S, a ≠ 0 → (a ^ 2 + 1) * γ a = x + a + (1 + w ^ 2) / (a + w)) :
    x = w ∧ ∀ a ∈ S, a ≠ 0 → a ≠ 1 → γ a = (a + w)⁻¹ := by
  have hne : ∀ a ∈ S, a + w ≠ 0 := by
    intro a ha hc
    refine hw ?_
    have hwa : w = a := by linear_combination hc - a * h2
    rw [hwa]
    exact ha
  have hone : (1 : E) ∈ S := S.one_mem
  -- the instance `a = 1` pins `x`
  have hx : x = w := by
    have h := hstar 1 hone one_ne_zero
    have h1w : (1 : E) + w ≠ 0 := hne 1 hone
    have hsq : (1 : E) + w ^ 2 = (1 + w) * (1 + w) := by linear_combination (-w) * h2
    have hzero : ((1 : E) ^ 2 + 1) * γ 1 = 0 := by
      rw [show ((1 : E) ^ 2 + 1) = 0 by linear_combination h2, zero_mul]
    rw [hsq, mul_div_assoc, div_self h1w, mul_one, hzero] at h
    linear_combination -h + (-w - 1) * h2
  refine ⟨hx, fun a ha ha0 ha1 => ?_⟩
  have haw : a + w ≠ 0 := hne a ha
  have hsq : a ^ 2 + 1 ≠ 0 := by
    intro hc
    refine ha1 ?_
    have hfac : (a + 1) * (a + 1) = 0 := by linear_combination hc + a * h2
    rcases mul_eq_zero.mp hfac with h | h <;>
      exact (by linear_combination h - h2 : a = 1)
  -- the right-hand side is `(a² + 1)/(a + w)`
  have hnum : (a ^ 2 + 1 : E) = (w + a) * (a + w) + (1 + w ^ 2) := by
    linear_combination (-(a * w) - w ^ 2) * h2
  have hrhs : (a ^ 2 + 1) / (a + w) = w + a + (1 + w ^ 2) / (a + w) := by
    rw [hnum, add_div, mul_div_assoc, div_self haw, mul_one]
  have h := hstar a ha ha0
  rw [hx, ← hrhs, div_eq_mul_inv] at h
  exact mul_left_cancel₀ hsq h

/-- **Stage (4), as an identity between the unitary coordinates** (Peterfalvi Part II,
p. 131).

Combining the two previous lemmas: the second entry of `f(ω̄, x + a)` is `1/(x + a)`,
since `x = ζ⁻¹` turns `a + ζ⁻¹` into `x + a`.  Together with stage (2)'s first entry
`ω̄/(a + ζ⁻¹) = ω̄/(x + a)` this is the book's `f(ω̄, y) = (ω̄/y, 1/y)`, for
`y = x + a` with `a ∈ F − {0, 1}`. -/
theorem gamma_eq_inv_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} (S : Subfield E)
    {ζ ω x : E} {γ : E → E} (hζ : ζ ≠ 0) (hζnorm : ζ * ζ ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = ζ + ζ⁻¹) (hζS : ζ⁻¹ ∉ S)
    (hchain : ∀ a ∈ S, a ≠ 0 → a ^ 2 * γ a + a
      = γ a + x + (ζ⁻¹ ^ 2 * ω / (a + ζ⁻¹)) * (ζ⁻¹ * ω) ^ 2 ^ m) :
    x = ζ⁻¹ ∧ ∀ a ∈ S, a ≠ 0 → a ≠ 1 → γ a = (x + a)⁻¹ := by
  obtain ⟨hx, hγ⟩ := eq_and_inv_of_star h2 S (w := ζ⁻¹) (x := x) (γ := γ) hζS
    fun a ha ha0 => star_of_secondEntry h2 hζ hζnorm hω (hchain a ha ha0)
  exact ⟨hx, fun a ha ha0 ha1 => by rw [hγ a ha ha0 ha1, hx, add_comm a ζ⁻¹]⟩

end StepFourArithmetic

end OddOrder.Peterfalvi.Appendices.Suzuki
