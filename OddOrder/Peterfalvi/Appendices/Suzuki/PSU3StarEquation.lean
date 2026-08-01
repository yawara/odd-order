/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3RootGroupModel

/-!
# Peterfalvi Part II, Ch. IV §3: the equation `(∗∗)` and its consequences

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4)–(5), pp. 130–131.

The arithmetic of stages (4) and (5).  Once the group-theoretic identities of §2 and §3
are read in the unitary coordinates, everything that remains is an identity in the field
`E`: the second-entry comparison of stage (1) *is* the book's

  `(∗∗)   (a² + 1) γ(a) = x + a + (1 + ζ⁻²)/(a + ζ⁻¹)`,

whose instance at `a = 1` pins `x = ζ⁻¹` and whose remaining instances give
`γ(a) = 1/(a + ζ⁻¹)`; and stage (5)'s second case is a two-line computation in which
characteristic two enters as `x + a + x = a`.

The book's `ζ⁻¹` is carried throughout as a single letter `w`, a norm-one element —
that is how it arrives from the model, as the scalar `μ(1, ζ)`.

The group-theoretic side is `PSU3InverseFormula`, which imports this file.

## Main results

* `star_of_secondEntry` — the second-entry comparison *is* `(∗∗)`.
* `eq_of_star_at_one`, `inv_of_star` — `(∗∗)` forces `x = w`, and then
  `γ(a) = 1/(a + w)` one `a` at a time.
* `stepFive_secondCase`, `stepFive_secondCase_compose` — stage (5)'s second case.
* `inverseFormula_symm` — the inversion formula is self-inverse.
* `secondEntry_of_chain`, `star_of_chain` — the bridge from a two-factor identity in
  the twisted product to `(∗∗)`, which is how stage (1) enters.
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

That cocycle term is where `w` and `ω̄` disappear: `A C̄ = w² w^{-1} ω̄^{1+q}/(a + w)`,
and `ω̄^{1+q} = w + w⁻¹` by stage (3), leaving `(1 + w²)/(a + w)`.

The book's `ζ⁻¹` is carried as a single letter `w`, a norm-one element — that is how it
arrives from the model, as the scalar `μ(1, ζ)`. -/
theorem star_of_secondEntry (h2 : (2 : E) = 0) {m : ℕ} {w ω x a γa : E}
    (hw : w ≠ 0) (hwnorm : w * w ^ 2 ^ m = 1) (hω : ω * ω ^ 2 ^ m = w + w⁻¹)
    (hchain : a ^ 2 * γa + a
      = γa + x + (w ^ 2 * ω / (a + w)) * (w * ω) ^ 2 ^ m) :
    (a ^ 2 + 1) * γa = x + a + (1 + w ^ 2) / (a + w) := by
  have hwinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  have hwq : w ^ 2 ^ m = w⁻¹ := by
    field_simp
    linear_combination hwnorm
  -- the cocycle term collapses to `(1 + w²)/(a + w)`
  have hnum : w ^ 2 * ω * (w⁻¹ * ω ^ 2 ^ m) = 1 + w ^ 2 :=
    calc w ^ 2 * ω * (w⁻¹ * ω ^ 2 ^ m)
        = w ^ 2 * w⁻¹ * (ω * ω ^ 2 ^ m) := by ring
      _ = w ^ 2 * w⁻¹ * (w + w⁻¹) := by rw [hω]
      _ = (w * w⁻¹) * w ^ 2 + (w * w⁻¹) * (w * w⁻¹) := by ring
      _ = 1 + w ^ 2 := by rw [hwinv]; ring
  have hcoc : (w ^ 2 * ω / (a + w)) * (w * ω) ^ 2 ^ m = (1 + w ^ 2) / (a + w) := by
    rw [mul_pow, hwq, div_mul_eq_mul_div, hnum]
  rw [hcoc] at hchain
  linear_combination hchain + (γa - a) * h2

/-- **`(∗∗)` at `a = 1` pins `x`** (Peterfalvi Part II, p. 131: "For `a = 1`, this
becomes `0 = x + 1 + (1 + ζ⁻¹) = x + ζ⁻¹`").

The left side vanishes in characteristic two, and `(1 + w²)/(1 + w) = 1 + w`. -/
theorem eq_of_star_at_one (h2 : (2 : E) = 0) {w x v : E} (hw : (1 : E) + w ≠ 0)
    (hstar : ((1 : E) ^ 2 + 1) * v = x + 1 + (1 + w ^ 2) / (1 + w)) :
    x = w := by
  have hsq : (1 : E) + w ^ 2 = (1 + w) * (1 + w) := by linear_combination (-w) * h2
  have hzero : ((1 : E) ^ 2 + 1) * v = 0 := by
    rw [show ((1 : E) ^ 2 + 1) = 0 by linear_combination h2, zero_mul]
  rw [hsq, mul_div_assoc, div_self hw, mul_one, hzero] at hstar
  linear_combination -hstar + (-w - 1) * h2

/-- **`(∗∗)` away from `a ∈ {0, 1}` gives the value** (Peterfalvi Part II, p. 131:
"Thus, for `a ∈ F − {0,1}`, `γ(a) = 1/(a + ζ⁻¹)`").

Once `x = w` is known the right side collapses:
`w + a + (1 + w²)/(a + w) = [(a + w)² + 1 + w²]/(a + w) = (a² + 1)/(a + w)`, and
`a² + 1 = (a + 1)²` is invertible.

Stated for one `a` at a time — the value `v` is whatever the group side produces there,
so no indexing function is needed. -/
theorem inv_of_star (h2 : (2 : E) = 0) {w x a v : E} (haw : a + w ≠ 0) (ha1 : a ≠ 1)
    (hx : x = w) (hstar : (a ^ 2 + 1) * v = x + a + (1 + w ^ 2) / (a + w)) :
    v = (a + w)⁻¹ := by
  have hsq : a ^ 2 + 1 ≠ 0 := by
    intro hc
    refine ha1 ?_
    have hfac : (a + 1) * (a + 1) = 0 := by linear_combination hc + a * h2
    rcases mul_eq_zero.mp hfac with h | h <;>
      exact (by linear_combination h - h2 : a = 1)
  have hnum : (a ^ 2 + 1 : E) = (w + a) * (a + w) + (1 + w ^ 2) := by
    linear_combination (-(a * w) - w ^ 2) * h2
  have hrhs : (a ^ 2 + 1) / (a + w) = w + a + (1 + w ^ 2) / (a + w) := by
    rw [hnum, add_div, mul_div_assoc, div_self haw, mul_one]
  rw [hx, ← hrhs, div_eq_mul_inv] at hstar
  exact mul_left_cancel₀ hsq hstar

/-- **The computation closing stage (5)'s second case** (Peterfalvi Part II, p. 131, the
last display).

When `ρ̄` is *not* in the `K W`-orbit of `ω̄`, the book instead arranges that `f(ρ)` is,
and reads the formula backwards: from `ρ = (ρ̄, x) = f(ω̄', x') = (ω̄'/x', 1/x')` it gets
`ω̄' = ρ̄/x` and `x' = 1/x`.  Stage (2) of §2 then expresses `f(ρ̄, x + a)` as
`f(ω̄', x' + a⁻¹)^{a⁻¹} (0, a⁻¹)`, and substituting the known value of the inner `f`
gives, coordinate by coordinate,

  `a⁻¹ ω̄'/(x' + a⁻¹) = ρ̄/(x + a)`,
  `a⁻² /(x' + a⁻¹) + a⁻¹ = 1/(x + a)`,

the conjugation by `a⁻¹` scaling the second coordinate by the norm `a⁻²` (`a ∈ F`) and
the central factor `(0, a⁻¹)` adding `a⁻¹`.  The second identity is where characteristic
two enters: `x + a + x = a`. -/
theorem stepFive_secondCase (h2 : (2 : E) = 0) {r x a : E}
    (ha : a ≠ 0) (hx : x ≠ 0) (hxa : x + a ≠ 0) :
    a⁻¹ * ((r / x) / (x⁻¹ + a⁻¹)) = r / (x + a) ∧
      (a⁻¹) ^ 2 * (1 / (x⁻¹ + a⁻¹)) + a⁻¹ = (x + a)⁻¹ := by
  have hinv : x⁻¹ + a⁻¹ ≠ 0 := by
    intro hc
    refine hxa ?_
    field_simp at hc
    linear_combination hc
  have hsum : x⁻¹ + a⁻¹ = (x + a) / (x * a) := by
    field_simp
    ring
  rw [hsum]
  constructor
  · rw [div_div_eq_mul_div, eq_div_iff hxa]
    field_simp
  · rw [one_div_div, inv_eq_one_div (x + a), eq_div_iff hxa]
    field_simp
    linear_combination x * h2

/-- **Stage (5)'s second case, composed** (Peterfalvi Part II, p. 131).

The two inputs are §2 (2) read in coordinates — `q_L = A q_R`, `y_L = A² y_R + A`, where
`A = μ(a²)` is the conjugating scalar — and the inversion formula already known at
`f(ρ) s^a = (ω̄', x' + A)`, with `ω̄' = ρ̄/x` and `x' = 1/x` supplied by
`inverseFormula_symm`.  Out comes the formula at `ρ s^{a⁻¹} = (ρ̄, x + A⁻¹)`.

The book's parameter is `A⁻¹`, the coordinate of the shift on the left; that is why
`stepFive_secondCase` is instantiated there. -/
theorem stepFive_secondCase_compose (h2 : (2 : E) = 0) {r x A qL yL qR yR : E}
    (hA : A ≠ 0) (hx : x ≠ 0) (hxA : x + A⁻¹ ≠ 0)
    (hLq : qL = A * qR) (hLy : yL = A ^ 2 * yR + A)
    (hRq : qR = (r / x) / (x⁻¹ + A)) (hRy : yR = (x⁻¹ + A)⁻¹) :
    qL = r / (x + A⁻¹) ∧ yL = (x + A⁻¹)⁻¹ := by
  obtain ⟨e1, e2⟩ :=
    stepFive_secondCase (r := r) (x := x) (a := A⁻¹) h2 (inv_ne_zero hA) hx hxA
  rw [inv_inv] at e1 e2
  rw [one_div] at e2
  exact ⟨by rw [hLq, hRq]; exact e1, by rw [hLy, hRy]; exact e2⟩

/-- **The inversion formula is self-inverse** (Peterfalvi Part II, p. 131: "Then
`(ρ̄, x) = f(ω̄', x') = (ω̄'/x', 1/x')` and so `ω̄' = ρ̄/x` and `x' = 1/x`").

If `f` carries `(r_σ, y_σ)` to `(r_ρ, y_ρ)` by the formula, then it carries
`(r_ρ, y_ρ)` back to `(r_σ, y_σ)` by the same formula.  Stage (5) uses this in the
direction the book does: knowing `f` at `f(ρ)` — which is where the orbit argument puts
one — determines `f(ρ)` from `ρ`, since `f` is an involution (H2). -/
theorem inverseFormula_symm {rρ yρ rσ yσ : E} (hyσ : yσ ≠ 0)
    (h1 : rρ = rσ / yσ) (h2 : yρ = yσ⁻¹) :
    rσ = rρ / yρ ∧ yσ = yρ⁻¹ := by
  subst h1
  subst h2
  exact ⟨by field_simp, (inv_inv yσ).symm⟩

end StepFourArithmetic

section ChainBridge

open OddOrder.FiniteField Suzuki2Groups

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]

/-- **Reading a two-factor identity on its second unitary entries** — the shape stage
(1) arrives in (Peterfalvi Part II, p. 131).

Both sides of the chain are products of two elements, and the multiplication rule of the
unitary coordinates contributes a cocycle term `p̄ q̄^q` to each.  On the left that term
vanishes, the second factor being central; on the right it survives, and it is the term
the book evaluates using `ω̄^{1+q} = ζ + ζ⁻¹`. -/
theorem secondEntry_of_chain (m : ℕ) (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    {L₁ L₂ R₁ R₂ : BilinearTwistedProduct (hermitianCocycle m hcard hu)}
    (hL₂ : L₂.quotient = 0) (heq : L₁ * L₂ = R₁ * R₂) :
    unitaryCoord m u L₁ + unitaryCoord m u L₂
      = unitaryCoord m u R₁ + unitaryCoord m u R₂
        + R₁.quotient * R₂.quotient ^ 2 ^ m := by
  have hL := unitaryCoord_mul m hcard hu L₁ L₂
  rw [heq, unitaryCoord_mul m hcard hu R₁ R₂, hL₂, zero_pow (by positivity),
    mul_zero, add_zero] at hL
  exact hL.symm

/-- **Stage (1), read in the unitary coordinates, is `(∗∗)`** (Peterfalvi Part II,
p. 131).

The hypotheses are the coordinates of the four factors of the chain

  `f(ω̄, x+a)^{ζ⁻¹ a} · (0, a) = f(ω̄, x+a)^{ζ⁻²} · (ω̄, x)^{ζ⁻¹}`,

each obtained from `exists_unitaryModel_conj` (the conjugations scale the two
coordinates by `μ` and its norm) together with stage (2) for the quotient coordinate of
`f(ω̄, x+a)`.  The three norms involved are `(ζ⁻¹a)^{1+q} = a²` and
`(ζ⁻²)^{1+q} = (ζ⁻¹)^{1+q} = 1`. -/
theorem star_of_chain (m : ℕ) (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (h2 : (2 : E) = 0)
    {L₁ L₂ R₁ R₂ : BilinearTwistedProduct (hermitianCocycle m hcard hu)}
    {w ω x a γa : E} (hw : w ≠ 0) (hwnorm : w * w ^ 2 ^ m = 1)
    (hω : ω * ω ^ 2 ^ m = w + w⁻¹)
    (hL₂q : L₂.quotient = 0)
    (hL₁y : unitaryCoord m u L₁ = a ^ 2 * γa) (hL₂y : unitaryCoord m u L₂ = a)
    (hR₁y : unitaryCoord m u R₁ = γa)
    (hR₁q : R₁.quotient = w ^ 2 * ω / (a + w))
    (hR₂y : unitaryCoord m u R₂ = x) (hR₂q : R₂.quotient = w * ω)
    (heq : L₁ * L₂ = R₁ * R₂) :
    (a ^ 2 + 1) * γa = x + a + (1 + w ^ 2) / (a + w) := by
  have h := secondEntry_of_chain m hcard hu hL₂q heq
  rw [hL₁y, hL₂y, hR₁y, hR₂y, hR₁q, hR₂q] at h
  exact star_of_secondEntry h2 hw hwnorm hω h

end ChainBridge

end OddOrder.Peterfalvi.Appendices.Suzuki
