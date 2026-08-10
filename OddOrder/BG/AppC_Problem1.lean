/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Basic

/-!
# BG Appendix C, Problem 1: the group-theoretic core

Bender--Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix C, p. 152, Problem 1
(= Glauberman--Norton, Proc. Amer. Math. Soc. **119** (1993), p. 1094, "Problem (Péterfalvi)"):

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

This is **open** (since 1993); it is not a formalization debt.  What *is* settled — and what this
file carries — are the two elementary group-theoretic steps behind the partial resolution
recorded in `notes/bg/appC_problem1_partial_resolution.md` (issue 0180):

* **Lemma A′** (`pow_three_mul_eq_pow_three_of_commute`): if `x³ = 1` and `c` commutes with its
  conjugate `x⁻¹cx`, then `(x * c * x)³ = (x * c)³`.  Both sides expand to the three conjugates
  `c^{x²}`, `c^x`, `c` in opposite orders, so one commutation identifies them.

  Applied to a witness of hypothesis (B) with `x` a generator of `σ(P₀)`, `g = x^y` and
  `c = x⁻¹g = ⁅x, y⁆ ∈ Q`, this reads `(g * x)³ = g³ = 1`: since `Q` is *abelian* the hypothesis
  is automatic.  So (B) forces the product of the two order-three elements `g` and `x` to have
  order dividing three again — the single non-trivial relation that (B) yields, and the seed of
  everything downstream.

* **Lemma C** (`cross_commute_of_three_relations`): a pure cancellation.  Three "layered"
  relations `a₂a₁a₀ = 1`, `b₂b₁b₀ = 1`, `(a₂b₂)(a₁b₁)(a₀b₀) = 1` together with the two same-layer
  commutations force the *cross-layer* commutation `a₁b₀ = b₀a₁`.

  In the application the layers are `P`, `P^g`, `P^{g²}`, the three relations are the
  `σ(U)`-conjugates of `(g * x)³ = 1` taken at `s`, `t` and `s + t` inside the set `S` of squares
  of `𝔽_{3^q}`, and the same-layer commutations hold because each layer is abelian.  The
  conclusion is the vanishing cross-commutator `⁅t, (s^e)^g⁆ = 1` that drives the partial
  resolution.

## Main results

* `pow_three_mul_eq_pow_three_of_commute` — Lemma A′.
* `pow_three_mul_pow_three_eq_one` — the form used downstream: `(g * x)³ = 1`.
* `cross_commute_of_three_relations` — Lemma C.
-/

namespace OddOrder.BG.AppC.Problem1

variable {G : Type*} [Group G]

section LemmaA

variable {x c : G}

/-- `x³ = 1`, unfolded. -/
private theorem mul_mul_eq_one_of_pow_three (hx : x ^ 3 = 1) : x * (x * x) = 1 := by
  rw [pow_succ, pow_succ, pow_one] at hx
  rwa [← mul_assoc]

/-- With `x³ = 1` the inverse of `x` is `x * x`. -/
private theorem inv_eq_mul_self (hx : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_left (by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [mul_assoc])

/-- Cancelling a block `x * x * x` anywhere inside a right-associated product. -/
private theorem cancel_three (hx : x ^ 3 = 1) (r : G) : x * (x * (x * r)) = r := by
  have h : x * x * x = 1 := by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [← mul_assoc] at h
  rw [← mul_assoc, ← mul_assoc, h, one_mul]

/-- **Lemma A′.**  Let `x` have order dividing three and let `c` commute with its conjugate
`x⁻¹cx`.  Then

`(x * c * x)³ = (x * c)³`.

Indeed both sides equal `c^{x²} · c^x · c` up to the order of the last two factors:
`(x * c)³ = c^{x²} c^{x} c` and `(x * c * x)³ = c^{x²} c c^{x}`.

This is the first step of the partial resolution of BG Appendix C, Problem 1: for a witness of
hypothesis (B) one takes `c = ⁅x, y⁆`, which lies in the abelian subgroup `Q`, so the commutation
hypothesis is free and the conclusion says `(g * x)³ = g³` for `g = x * c`. -/
theorem pow_three_mul_eq_pow_three_of_commute (hx : x ^ 3 = 1)
    (h : Commute c (x⁻¹ * c * x)) : (x * c * x) ^ 3 = (x * c) ^ 3 := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  have e₁ : (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  have e₂ : (x * c * x) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * (c * (x⁻¹ * c * x)) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  rw [e₁, e₂, h.eq]

/-- The shape used downstream.  If `g = x * c` has order dividing three — automatic when `g` is a
conjugate of the order-three element `x` — and `c` commutes with `x⁻¹cx`, then the product
`g * x` also has order dividing three. -/
theorem pow_three_mul_pow_three_eq_one (hx : x ^ 3 = 1) (h : Commute c (x⁻¹ * c * x))
    (hg : (x * c) ^ 3 = 1) : (x * c * x) ^ 3 = 1 := by
  rw [pow_three_mul_eq_pow_three_of_commute hx h, hg]

end LemmaA

section LemmaC

variable {a₀ a₁ a₂ b₀ b₁ b₂ : G}

/-- **Lemma C** (the cancellation behind the partial resolution of BG Appendix C, Problem 1).

Suppose three "layered" relations hold,

* `a₂ * a₁ * a₀ = 1`,
* `b₂ * b₁ * b₀ = 1`,
* `(a₂ * b₂) * (a₁ * b₁) * (a₀ * b₀) = 1`,

and that same-layer elements commute, `a₁ * b₁ = b₁ * a₁` and `a₀ * b₀ = b₀ * a₀`.  Then the
*cross-layer* pair commutes as well: `a₁ * b₀ = b₀ * a₁`.

Solving the first two relations for the top layer turns the third into
`(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`; cancelling `b₁` on the left and `a₀` on the right — each licensed
by one of the same-layer commutations — leaves exactly `a₁b₀ = b₀a₁`.

In the application the three layers are `P`, `P^g` and `P^{g²}` for an element `g` of order three,
and the three relations are the `σ(U)`-conjugates of `(g * x)³ = 1` evaluated at `s`, `t` and
`s + t` in the set of squares of `𝔽_{3^q}`; the hypotheses hold because each layer is abelian and
because conjugation is additive on `P`. -/
theorem cross_commute_of_three_relations (ha : a₂ * a₁ * a₀ = 1) (hb : b₂ * b₁ * b₀ = 1)
    (hab : a₂ * b₂ * (a₁ * b₁) * (a₀ * b₀) = 1) (h₁ : a₁ * b₁ = b₁ * a₁)
    (h₀ : a₀ * b₀ = b₀ * a₀) : a₁ * b₀ = b₀ * a₁ := by
  -- Solve the first two relations for the top layer.
  have ha₂ : a₂ = (a₁ * a₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact ha
  have hb₂ : b₂ = (b₁ * b₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact hb
  -- Substituting them turns the third relation into `(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`.
  have key : a₁ * b₁ * (a₀ * b₀) = b₁ * b₀ * (a₁ * a₀) := by
    rw [ha₂, hb₂] at hab
    have h : (a₁ * a₀)⁻¹ * ((b₁ * b₀)⁻¹ * (a₁ * b₁ * (a₀ * b₀))) = 1 := by
      simpa [mul_assoc] using hab
    exact inv_mul_eq_iff_eq_mul.mp (inv_mul_eq_one.mp h).symm
  -- Cancel `b₁` on the left, using `a₁b₁ = b₁a₁`.
  have step : a₁ * (a₀ * b₀) = b₀ * (a₁ * a₀) := by
    have hL : a₁ * b₁ * (a₀ * b₀) = b₁ * (a₁ * (a₀ * b₀)) := by
      rw [h₁, mul_assoc]
    have hR : b₁ * b₀ * (a₁ * a₀) = b₁ * (b₀ * (a₁ * a₀)) := mul_assoc _ _ _
    rw [hL, hR] at key
    exact mul_left_cancel key
  -- Cancel `a₀` on the right, using `a₀b₀ = b₀a₀`.
  have step₂ : a₁ * b₀ * a₀ = b₀ * a₁ * a₀ := by
    rw [mul_assoc, mul_assoc, ← h₀]
    exact step
  exact mul_right_cancel step₂

end LemmaC

end OddOrder.BG.AppC.Problem1
