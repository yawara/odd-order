/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import OddOrder.Algebra.FixedPointDensity

/-!
# Peterfalvi Part II, Ch. IV §4: solving (5) and (6)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, pp. 133-134.

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
* `sectionFour_seven_book`, `sectionFour_eight_book`, `sectionFour_nine` — the same in
  the book's displayed shape, with the common denominator `1 + b² a^{-2μ}`, and (9).
* `sectionFour_fixed_of_shift`, `sectionFour_sq_eq_id` — the closing shift trick of
  p. 134: writing (10) at `X + 1` and subtracting leaves `X^{μ²} = X`, and that on
  enough points forces `μ² = id`.
* `sectionFour_lambda_eq_one` — `λ = 1` and `b² + a^{-2μ²} = ζ + ζ⁻¹`, from `ζ ∉ F`.
* `eq_one_of_sq_eq_one_of_odd_pow` — `μ² = 1` and odd order give `μ = 1`.
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

/-! ### (7), (8) in the book's displayed shape, and (9)

Dividing numerator and denominator by `A = a^{2μ}` turns (7) and (8) into the forms the
book displays, in which the *same* denominator `1 + b² a^{-2μ}` occurs on both sides of
(9).
-/

/-- `1 + b² a^{-2μ}` is nonzero, being `(a^{2μ} + b²) a^{-2μ}`. -/
theorem one_add_mul_inv_ne_zero {A B : E} (hA : A ≠ 0) (hAB : A + B ≠ 0) :
    1 + B * A⁻¹ ≠ 0 := by
  have hkey : (A + B) * A⁻¹ = 1 + B * A⁻¹ := by field_simp
  rw [← hkey]
  exact mul_ne_zero hAB (inv_ne_zero hA)

/-- **(7) in the book's displayed shape** (Peterfalvi Part II, Ch. IV §4, p. 133):

  `f(ω s^b)‾ = (ζ⁻¹ + a^{-2μ}) / (1 + b² a^{-2μ}) · ω̄`.

This is the expression whose `μ`-image stands on the left of (9). -/
theorem sectionFour_seven_book (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0)
    (hc : c ≠ 0) (hAB : A + B ≠ 0) (h5 : c * X = A⁻¹ * Y + w)
    (h6 : B * X = c⁻¹ * Y + w) :
    X = (c⁻¹ + A⁻¹) / (1 + B * A⁻¹) * w := by
  have hD := one_add_mul_inv_ne_zero hA hAB
  rw [sectionFour_seven h2 hA hc hAB h5 h6]
  congr 1
  rw [div_eq_div_iff (mul_ne_zero hc hAB) hD]
  field_simp

/-- **(8) in the book's displayed shape** (Peterfalvi Part II, Ch. IV §4, p. 133):

  `(f(ω s^b)‾)^η = (b² + ζ) / (1 + b² a^{-2μ}) · ω̄`. -/
theorem sectionFour_eight_book (h2 : (2 : E) = 0) {X Y w A B c : E} (hA : A ≠ 0)
    (hc : c ≠ 0) (hAB : A + B ≠ 0) (h5 : c * X = A⁻¹ * Y + w)
    (h6 : B * X = c⁻¹ * Y + w) :
    Y = (B + c) / (1 + B * A⁻¹) * w := by
  have hD := one_add_mul_inv_ne_zero hA hAB
  rw [sectionFour_eight h2 hA hc hAB h5 h6]
  congr 1
  rw [div_eq_div_iff hAB hD]
  field_simp

/-- **Peterfalvi Part II, Ch. IV §4, (9)** (p. 134).

`η` acts on `E = Q/Q₀` as a `μ`-semilinear map (Appendix I, Proposition 2) and fixes
`ω̄`, because step (2) chooses `η` centralizing `ω`.  Applying it to (7) therefore gives
`(f(ω s^b)‾)^η = Z^μ ω̄`, with `Z` the scalar of `sectionFour_seven_book`; comparing with
(8) and cancelling `ω̄ ≠ 0` leaves (9).

`hsemi` is exactly that group-theoretic input, isolated: `Z` stands for the `μ`-image of
the scalar of (7). -/
theorem sectionFour_nine (h2 : (2 : E) = 0) {X Y w A B c Z : E} (hA : A ≠ 0) (hc : c ≠ 0)
    (hAB : A + B ≠ 0) (hw : w ≠ 0) (h5 : c * X = A⁻¹ * Y + w)
    (h6 : B * X = c⁻¹ * Y + w) (hsemi : Y = Z * w) :
    Z = (B + c) / (1 + B * A⁻¹) := by
  have h8 := sectionFour_eight_book h2 hA hc hAB h5 h6
  rw [hsemi] at h8
  exact mul_right_cancel₀ hw h8

/-! ### (10) and the shift trick

The book's (10) (p. 134) reads

  `(ζ + ζ⁻¹ + X^μ) X = (ζ + ζ⁻¹ + X^{μ²}) X^μ`  for `X ∈ F − {0, α^{2τ}}`,

and it is closed by: "Writing (10) with `X + 1` in place of `X` and subtracting (10)
from the result, we see that `X^{μ²} = X`."
-/

/-- **The shift trick of Peterfalvi Part II, Ch. IV §4** (p. 134).

Writing (10) at `X + 1` and subtracting (10) at `X`, every quadratic term cancels — `μ`
being a ring map, `(X+1)^μ = X^μ + 1` — and what is left is `X^{μ²} = X`.

No characteristic hypothesis is needed: the cancellation is an identity of commutative
rings. -/
theorem sectionFour_fixed_of_shift (μ : E →+* E) {s X : E}
    (hX : (s + μ X) * X = (s + μ (μ X)) * μ X)
    (hX1 : (s + μ (X + 1)) * (X + 1) = (s + μ (μ (X + 1))) * μ (X + 1)) :
    μ (μ X) = X := by
  simp only [map_add, map_one] at hX1
  linear_combination hX - hX1

/-- **(10) forces `μ² = id`** (Peterfalvi Part II, Ch. IV §4, p. 134).

`T` collects the points where (10) — at `X` or at `X + 1` — is unavailable; the book's
is `{0, α^{2τ}, 1, α^{2τ} + 1}`.  The shift trick fixes every point outside `T`, and the
fixed points of the additive map `μ²` form a subgroup, so `μ² = id` as soon as `T` is
smaller than half of `F` (`eq_id_of_fixes_compl`).

In §4 that hypothesis is comfortable: there `|F| = q = ℓ^p` with `ℓ > 2` and `p` an odd
prime, so `q ≥ 64` while `|T| = 4`. -/
theorem sectionFour_sq_eq_id [Finite E] (μ : E ≃+* E) {s : E} (T : Finset E)
    (hten : ∀ X : E, X ∉ T →
      (s + μ X) * X = (s + μ (μ X)) * μ X ∧
        (s + μ (X + 1)) * (X + 1) = (s + μ (μ (X + 1))) * μ (X + 1))
    (hcard : 2 * T.card < Nat.card E) (X : E) :
    μ (μ X) = X :=
  OddOrder.FiniteField.eq_id_of_fixes_compl
    (μ.toRingHom.toAddMonoidHom.comp μ.toRingHom.toAddMonoidHom) T
    (fun y hy => sectionFour_fixed_of_shift μ.toRingHom (hten y hy).1 (hten y hy).2)
    hcard X

/-! ### `ζ` is quadratic over `F`

Peterfalvi Part II, Ch. IV §4, p. 134, reads off `λ = 1` and `b² + a^{-2μ²} = ζ + ζ⁻¹`
from

  `λ ζ² + (λ b² + a^{-2μ²}) ζ + 1 = 0`,

"as `ζ^{1+q} = 1` and `ζ ∉ F`".  The content is that `ζ ∉ F` makes `1`, `ζ` independent
over `F`, while `ζ` satisfies the quadratic `ζ² + (ζ + ζ⁻¹) ζ + 1 = 0` whose
coefficients lie in `F` — in characteristic `2` that quadratic is an identity, needing
only `ζ ≠ 0`.
-/

/-- **`1` and `ζ` are independent over a subfield missing `ζ`.** -/
theorem eq_zero_of_add_mul_eq_zero {F : Subfield E} {ζ u v : E} (hζ : ζ ∉ F)
    (hu : u ∈ F) (hv : v ∈ F) (h : u + v * ζ = 0) : u = 0 ∧ v = 0 := by
  have hv0 : v = 0 := by
    by_contra hne
    refine hζ ?_
    have hz : v * ζ = -u := by linear_combination h
    have hζeq : ζ = v⁻¹ * -u := by
      rw [← hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hζeq]
    exact F.mul_mem (F.inv_mem hv) (F.neg_mem hu)
  refine ⟨?_, hv0⟩
  rw [hv0, zero_mul, add_zero] at h
  exact h

/-- **The quadratic satisfied by `ζ`** — an identity in characteristic `2`, since
`(ζ + ζ⁻¹) ζ = ζ² + 1`. -/
theorem sq_add_traceCoeff_mul_add_one (h2 : (2 : E) = 0) {ζ : E} (hζ : ζ ≠ 0) :
    ζ ^ 2 + (ζ + ζ⁻¹) * ζ + 1 = 0 := by
  have hinv : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hζ
  linear_combination hinv + (ζ ^ 2 + 1) * h2

/-- **Peterfalvi Part II, Ch. IV §4** (p. 134): `λ = 1`, and `b² + a^{-2μ²} = ζ + ζ⁻¹`.

Substituting the quadratic `ζ² = s ζ + 1` into `λ ζ² + (λ β + α) ζ + 1 = 0` collapses it
to `(λ + 1) + (λ s + λ β + α) ζ = 0`, whose two `F`-coefficients must vanish separately
because `ζ ∉ F`. -/
theorem sectionFour_lambda_eq_one (h2 : (2 : E) = 0) {F : Subfield E} {ζ s lam α β : E}
    (hζ : ζ ∉ F) (hs : s ∈ F) (hlam : lam ∈ F) (hα : α ∈ F) (hβ : β ∈ F)
    (hmin : ζ ^ 2 + s * ζ + 1 = 0)
    (heq : lam * ζ ^ 2 + (lam * β + α) * ζ + 1 = 0) :
    lam = 1 ∧ β + α = s := by
  have hlin : (lam + 1) + (lam * s + lam * β + α) * ζ = 0 := by
    linear_combination heq - lam * hmin + (lam + lam * s * ζ) * h2
  obtain ⟨h1, h3⟩ := eq_zero_of_add_mul_eq_zero hζ (F.add_mem hlam F.one_mem)
    (F.add_mem (F.add_mem (F.mul_mem hlam hs) (F.mul_mem hlam hβ)) hα) hlin
  have hlam1 : lam = 1 := by linear_combination h1 - h2
  refine ⟨hlam1, ?_⟩
  rw [hlam1] at h3
  linear_combination h3 - s * h2

/-! ### From `μ² = 1` to `μ = 1` -/

/-- **An element squaring to `1` and killed by an odd power is trivial.**

This is the one place where Peterfalvi Part II, Ch. IV §4 (p. 134) uses that `μ` has odd
order: `μ² = 1` from the shift trick, `μ^p = 1` because `μ` comes from `η ∈ P` of odd
prime order `p`.  Writing `n = 2k + 1` makes `x^n = (x²)^k x` read `x = 1` outright. -/
theorem eq_one_of_sq_eq_one_of_odd_pow {G : Type*} [Monoid G] {x : G} {n : ℕ}
    (hn : Odd n) (hsq : x ^ 2 = 1) (hpow : x ^ n = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : x ^ (2 * k) = 1 := by rw [pow_mul, hsq, one_pow]
  rw [pow_add, hk, one_mul, pow_one] at hpow
  exact hpow

end SectionFourArithmetic

end OddOrder.Peterfalvi.Appendices.Suzuki
