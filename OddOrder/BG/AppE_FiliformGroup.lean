/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_FiliformCounterexample
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.PGroup

/-!
# The Lazard group of `Q₆`: the group-level counterexample to BG Proposition E.4

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, Proposition E.4 (p. 162).

This leaf is **Tier 2** of the counterexample programme (issue 3027; Tier 1 =
`OddOrder/BG/AppE_FiliformCounterexample.lean`): it constructs the **Lazard group**
`S = Exp(L)` of the exceptional filiform Lie ring `Q₆` over `𝔽₁₉₇` as an honest
`Group` in Lean, so that the printed Proposition E.4 can be refuted against the
repo's own `RegularOperatorSetup` — eliminating the last prose gap (the Lazard
correspondence) left by Tier 1.

## The group law

`Q6` is `V = Fin 6 → ZMod 197` equipped with the truncated Baker–Campbell–Hausdorff
multiplication `gmul` in coordinates of the first kind, **rescaled** by
`diag(1, 1, 2, 12, 24, 720)` so that every coefficient is a small integer.  The
rescaling matters: it turns all the group identities below into polynomial
identities with *integer* coefficients that hold over `ℚ` (verified symbolically),
hence over `ℤ`, hence over every commutative ring — so plain `ring` closes them,
with no characteristic-`197` coefficient arithmetic anywhere.

The polynomials were computed in the truncated universal enveloping algebra
`U(L)/(weight > 5)` (PBW straightening; session scripts `derive_group_law.py`,
`emit_scaled.py`, issue 3027), where the following were verified over `ℚ` before
the rescaling: the Friedrichs criterion (`log(exp x · exp y)` is a Lie element —
the internal consistency check of the computation), associativity, the unit and
inverse laws, `gmul (c • x) x = (c + 1) • x`, and the exact weight-grading of every
monomial.  Lean re-verifies all of these from scratch; the symbolic derivation is
scaffolding, not a trusted input.

Because the law is graded-polynomial with linear top layer and `x ^ n = n • x`,
this group is the exponent-`197`, order-`197⁶`, class-`5` Lazard group of `Q₆` —
but nothing below relies on the correspondence; all group facts are proved directly
against `gmul`.
-/

namespace OddOrder.BG.AppE.Filiform

/-! ### The (rescaled) truncated BCH group law -/

/-- The Lazard group law of `Q₆` over `𝔽₁₉₇`: truncated BCH in first-kind
coordinates, rescaled by `diag(1,1,2,12,24,720)` to clear all denominators.
Every group identity below is an integer polynomial identity, so `ring` applies. -/
def gmul (x y : V) : V := fun k =>
  if k = 0 then x 0 + y 0
  else if k = 1 then x 1 + y 1
  else if k = 2 then x 0 * y 1 - x 1 * y 0 + x 2 + y 2
  else if k = 3 then
    x 0 * x 1 * y 1 - x 0 * y 1 * y 1 - x 1 * x 1 * y 0 + x 1 * y 0 * y 1 +
      3 * x 1 * y 2 - 3 * x 2 * y 1 + x 3 + y 3
  else if k = 4 then
    -x 0 * x 1 * y 1 * y 1 + x 1 * x 1 * y 0 * y 1 + x 1 * x 1 * y 2 - x 1 * x 2 * y 1 -
      x 1 * y 1 * y 2 + x 1 * y 3 + x 2 * y 1 * y 1 - x 3 * y 1 + x 4 + y 4
  else
    -x 0 * x 0 * x 1 * x 1 * y 1 - 6 * x 0 * x 0 * x 1 * y 1 * y 1 -
      2 * x 0 * x 0 * y 1 * y 1 * y 1 + x 0 * x 1 * x 1 * x 1 * y 0 +
      8 * x 0 * x 1 * x 1 * y 0 * y 1 + 8 * x 0 * x 1 * y 0 * y 1 * y 1 -
      15 * x 0 * x 1 * y 1 * y 2 + 5 * x 0 * x 1 * y 3 - 10 * x 0 * x 3 * y 1 +
      x 0 * y 0 * y 1 * y 1 * y 1 + 5 * x 0 * y 1 * y 3 + 15 * x 0 * y 4 -
      2 * x 1 * x 1 * x 1 * y 0 * y 0 - 6 * x 1 * x 1 * y 0 * y 0 * y 1 +
      15 * x 1 * x 2 * y 0 * y 1 + 15 * x 1 * x 2 * y 2 + 5 * x 1 * x 3 * y 0 -
      x 1 * y 0 * y 0 * y 1 * y 1 - 10 * x 1 * y 0 * y 3 - 15 * x 1 * y 2 * y 2 -
      15 * x 2 * x 2 * y 1 + 15 * x 2 * y 1 * y 2 + 15 * x 2 * y 3 +
      5 * x 3 * y 0 * y 1 - 15 * x 3 * y 2 - 15 * x 4 * y 0 + x 5 + y 5

theorem gmul_zero_right (x : V) : gmul x 0 = x := by
  funext k
  fin_cases k <;> simp [gmul]

theorem gmul_zero_left (y : V) : gmul 0 y = y := by
  funext k
  fin_cases k <;> simp [gmul]

theorem gmul_neg_left (x : V) : gmul (-x) x = 0 := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-- **Associativity of the BCH law** — coordinatewise, integer polynomial
identities (the mod-`197` shadow of the rational BCH identities, made integral by
the rescaling), closed by `ring`. -/
theorem gmul_assoc (x y z : V) : gmul (gmul x y) z = gmul x (gmul y z) := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-! ### The group `Q6` -/

/-- The Lazard group `S = Exp(Q₆)`: order `197⁶`, exponent `197`, nilpotency
class `5` — the group-level carrier of the counterexample to BG Prop E.4. -/
@[ext]
structure Q6 : Type where
  /-- first-kind (rescaled BCH) coordinates -/
  co : V

instance : One Q6 := ⟨⟨0⟩⟩
instance : Mul Q6 := ⟨fun x y => ⟨gmul x.co y.co⟩⟩
instance : Inv Q6 := ⟨fun x => ⟨-x.co⟩⟩

@[simp] theorem co_mul (x y : Q6) : (x * y).co = gmul x.co y.co := rfl
@[simp] theorem co_one : (1 : Q6).co = 0 := rfl
@[simp] theorem co_inv (x : Q6) : (x⁻¹).co = -x.co := rfl

instance : Group Q6 :=
  Group.ofLeftAxioms
    (fun _ _ _ => Q6.ext (by simp [gmul_assoc]))
    (fun _ => Q6.ext (by simp [gmul_zero_left]))
    (fun _ => Q6.ext (by simp [gmul_neg_left]))

instance : Finite Q6 :=
  Finite.of_injective Q6.co fun _ _ h => Q6.ext h

/-- `|S| = 197⁶`. -/
theorem card_q6 : Nat.card Q6 = 197 ^ 6 := by
  rw [Nat.card_eq_of_bijective (fun x : Q6 => x.co)
    ⟨fun _ _ h => Q6.ext h, fun f => ⟨⟨f⟩, rfl⟩⟩]
  simp [Nat.card_pi, Nat.card_zmod]

/-! ### Powers are scalar multiples: exponent `197` -/

theorem gmul_smul_self (c : K) (x : V) : gmul (c • x) x = (c + 1) • x := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-- `x ^ n = n • x` in BCH coordinates. -/
theorem co_pow (x : Q6) (n : ℕ) : (x ^ n).co = (n : K) • x.co := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show gmul (x ^ n).co x.co = _
    rw [ih, gmul_smul_self]
    congr 1
    push_cast
    ring

/-- `S` has exponent `197`. -/
theorem pow_card_eq_one (x : Q6) : x ^ 197 = 1 := by
  ext k
  rw [co_pow, show ((197 : ℕ) : K) = 0 from by decide, zero_smul]
  rfl

/-- `S` is a `197`-group. -/
theorem isPGroup_q6 : IsPGroup 197 Q6 :=
  fun g => ⟨1, by rw [pow_one]; exact pow_card_eq_one g⟩

/-! ### The distinguished elements -/

/-- `v = a + b` as a group element: the generator of `R₀`. -/
def vg : Q6 := ⟨v⟩

/-- `e₅` (rescaled) as a group element: the generator of `R₁ ≤ Z(S)`. -/
def e5g : Q6 := ⟨e5⟩

/-- `b` as a group element: a witness in `T = C_S(Z₂(S))`. -/
def bg : Q6 := ⟨eB⟩

/-- `e₂` (rescaled) as a group element: the other witness in `T`. -/
def e2g : Q6 := ⟨e2⟩

/-- `e₄` (rescaled) as a group element: a generator of `Z₂(S)` used to cut `T`
out. -/
def e4g : Q6 := ⟨e4⟩

theorem vg_ne_one : vg ≠ 1 := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 0) (by decide)

theorem e5g_ne_one : e5g ≠ 1 := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 5) (by decide)

theorem orderOf_vg : orderOf vg = 197 :=
  orderOf_eq_prime (pow_card_eq_one vg) vg_ne_one

theorem orderOf_e5g : orderOf e5g = 197 :=
  orderOf_eq_prime (pow_card_eq_one e5g) e5g_ne_one

/-- **`T` is not abelian, at the group level**: `b` and `e₂` do not commute
(their group commutator is `≡ e₃` modulo higher weight; concretely the third
coordinate of `b * e₂` and `e₂ * b` differ by `6 ≠ 0`). -/
theorem bg_e2g_not_commute : bg * e2g ≠ e2g * bg := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 3) (by decide)

end OddOrder.BG.AppE.Filiform
