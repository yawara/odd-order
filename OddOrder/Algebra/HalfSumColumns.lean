/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The three half-sum columns of Navarro p. 142

Navarro's proof of the `Z*`-theorem builds three integer columns out of four given ones,

`2u_1 = a + b - c - d`,  `2u_2 = a + b - c + d`,  `2u_3 = a + b + c - d`,

where `a = D^y_0` and `b, c, d = D^t_0, D^t_1, D^t_2` satisfy the pairing table

`(a,a) = (b,b) = (c,c) = (d,d) = 4`,  `(b,c) = (b,d) = (c,d) = 2`,  `(a,b) = (a,c) = (a,d) = 0`,

and are all orthogonal to the column `g = χ(1)` of degrees.  He then reads off

`(u_i, u_j) = 1 + 2δ_ij`,  `(g, u_i) = 0`,  `(a, u_i) = 2`.

That step is pure bilinear algebra over `ℤ`, with no representation theory in it, and this file
isolates it.  Together with `ThreeNormColumn` — norm `3` plus orthogonality to the degrees forces
the entries `{1, 1, -1}` — it is the whole content of p. 142.

The `u_i` are supplied as data with `2 * u_i k = …` as a hypothesis rather than by dividing: over
`ℤ` the division is only legitimate because the four columns are congruent mod `2`, which is a
separate (character-theoretic) input.

## Main results

* `OddOrder.Algebra.dotProduct_of_halfSum` — the pairing table of the `u_i`
* `OddOrder.Algebra.dotProduct_degree_of_halfSum` — `(χ(1), u_i) = 0`
-/

namespace OddOrder.Algebra

variable {S : Type*} [Fintype S] {a b c d g : S → ℤ}

/-- The pairing of two half-sums, expanded in the ten pairings of `a, b, c, d`.

`εc`, `εd`, `ηc`, `ηd` are the signs of `c` and `d` in the two combinations; the coefficients are
those of `(a + b + εc c + εd d)(a + b + ηc c + ηd d)`. -/
theorem four_mul_sum_mul_of_halfSum {x y : S → ℤ} {εc εd ηc ηd : ℤ}
    (hx : ∀ k, 2 * x k = a k + b k + εc * c k + εd * d k)
    (hy : ∀ k, 2 * y k = a k + b k + ηc * c k + ηd * d k) :
    4 * (∑ k, x k * y k)
      = (∑ k, a k * a k) + (∑ k, b k * b k) + (εc * ηc) * (∑ k, c k * c k)
        + (εd * ηd) * (∑ k, d k * d k) + 2 * (∑ k, a k * b k)
        + (εc + ηc) * (∑ k, a k * c k) + (εd + ηd) * (∑ k, a k * d k)
        + (εc + ηc) * (∑ k, b k * c k) + (εd + ηd) * (∑ k, b k * d k)
        + (εc * ηd + εd * ηc) * (∑ k, c k * d k) := by
  have h4 : 4 * (∑ k, x k * y k) = ∑ k, (2 * x k) * (2 * y k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h4]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [hx k, hy k]; ring

/-- The pairing of a fixed column with a half-sum. -/
theorem two_mul_sum_mul_of_halfSum {y : S → ℤ} {ηc ηd : ℤ} (h : S → ℤ)
    (hy : ∀ k, 2 * y k = a k + b k + ηc * c k + ηd * d k) :
    2 * (∑ k, h k * y k)
      = (∑ k, h k * a k) + (∑ k, h k * b k) + ηc * (∑ k, h k * c k)
        + ηd * (∑ k, h k * d k) := by
  have h2 : 2 * (∑ k, h k * y k) = ∑ k, h k * (2 * y k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [hy k]; ring

variable (haa : ∑ k, a k * a k = 4) (hbb : ∑ k, b k * b k = 4) (hcc : ∑ k, c k * c k = 4)
  (hdd : ∑ k, d k * d k = 4) (hab : ∑ k, a k * b k = 0) (hac : ∑ k, a k * c k = 0)
  (had : ∑ k, a k * d k = 0) (hbc : ∑ k, b k * c k = 2) (hbd : ∑ k, b k * d k = 2)
  (hcd : ∑ k, c k * d k = 2)
  (hga : ∑ k, g k * a k = 0) (hgb : ∑ k, g k * b k = 0) (hgc : ∑ k, g k * c k = 0)
  (hgd : ∑ k, g k * d k = 0)

include haa hbb hcc hdd hab hac had hbc hbd hcd in
/-- **Navarro p. 142, the pairing table of the three half-sums.**

`(u_i, u_j) = 1 + 2δ_ij` and `(a, u_i) = 2` for the three sign patterns `(-,-)`, `(-,+)`, `(+,-)`.
The fourth pattern `(+,+)` is excluded: it gives norm `7`, not `3`. -/
theorem dotProduct_of_halfSum {u : Fin 3 → S → ℤ}
    (hu0 : ∀ k, 2 * u 0 k = a k + b k - c k - d k)
    (hu1 : ∀ k, 2 * u 1 k = a k + b k - c k + d k)
    (hu2 : ∀ k, 2 * u 2 k = a k + b k + c k - d k) :
    (∀ i j, (∑ k, u i k * u j k) = 1 + 2 * (if i = j then 1 else 0))
      ∧ (∀ i, (∑ k, a k * u i k) = 2) := by
  have hu : ∀ (i : Fin 3) (k : S), 2 * u i k
      = a k + b k + (![-1, -1, 1] : Fin 3 → ℤ) i * c k
        + (![-1, 1, -1] : Fin 3 → ℤ) i * d k := by
    intro i k
    fin_cases i <;> simp <;> linarith [hu0 k, hu1 k, hu2 k]
  have key : ∀ i j : Fin 3, 4 * (∑ k, u i k * u j k)
      = 4 * (1 + 2 * (if i = j then 1 else 0)) := by
    intro i j
    rw [four_mul_sum_mul_of_halfSum (hu i) (hu j), haa, hbb, hcc, hdd, hab, hac, had, hbc, hbd,
      hcd]
    fin_cases i <;> fin_cases j <;> norm_num
  have keya : ∀ i : Fin 3, 2 * (∑ k, a k * u i k) = 2 * 2 := by
    intro i
    rw [two_mul_sum_mul_of_halfSum a (hu i), haa, hab, hac, had]
    fin_cases i <;> norm_num
  exact ⟨fun i j => by have := key i j; omega, fun i => by have := keya i; omega⟩

include hga hgb hgc hgd in
/-- **`(χ(1), u_i) = 0`** — the degrees are orthogonal to all four columns, hence to the
half-sums. -/
theorem dotProduct_degree_of_halfSum {u : Fin 3 → S → ℤ}
    (hu0 : ∀ k, 2 * u 0 k = a k + b k - c k - d k)
    (hu1 : ∀ k, 2 * u 1 k = a k + b k - c k + d k)
    (hu2 : ∀ k, 2 * u 2 k = a k + b k + c k - d k) :
    ∀ i, (∑ k, g k * u i k) = 0 := by
  have hu : ∀ (i : Fin 3) (k : S), 2 * u i k
      = a k + b k + (![-1, -1, 1] : Fin 3 → ℤ) i * c k
        + (![-1, 1, -1] : Fin 3 → ℤ) i * d k := by
    intro i k
    fin_cases i <;> simp <;> linarith [hu0 k, hu1 k, hu2 k]
  have key : ∀ i : Fin 3, 2 * (∑ k, g k * u i k) = 0 := by
    intro i
    rw [two_mul_sum_mul_of_halfSum g (hu i), hga, hgb, hgc, hgd]
    fin_cases i <;> norm_num
  exact fun i => by have := key i; omega

end OddOrder.Algebra
