/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs

/-!
# The noncommutative binomial expansion

In a ring where `x` and `y` need not commute, `(x + y) ^ n` expands as the sum over all
`2 ^ n` *words* of length `n` in the two letters of the corresponding ordered product.  This is
the starting point of Brauer's count of irreducible modular representations: in characteristic
`p` the non-constant words fall into rotation orbits of size `p`, and cyclic rotation does not
change a product modulo the commutator subspace, so `(x + y) ^ p ≡ x ^ p + y ^ p`.

## Main results

* `OddOrder.wordProd` — the ordered product along a word
* `OddOrder.add_pow_eq_sum_wordProd` — the expansion
-/

namespace OddOrder

variable {R : Type*} [Ring R]

/-- The ordered product of the letters of a word: `w i = true` selects `x`, `false` selects
`y`. -/
def wordProd (x y : R) {n : ℕ} (w : Fin n → Bool) : R :=
  (List.ofFn fun i => if w i then x else y).prod

@[simp]
theorem wordProd_zero (x y : R) (w : Fin 0 → Bool) : wordProd x y w = 1 := by
  simp [wordProd]

theorem wordProd_cons (x y : R) {n : ℕ} (b : Bool) (v : Fin n → Bool) :
    wordProd x y (Fin.cons b v) = (if b then x else y) * wordProd x y v := by
  simp [wordProd, List.ofFn_succ]

/-- **The noncommutative binomial expansion.**  `(x + y) ^ n` is the sum, over all words of
length `n` in the letters `x` and `y`, of the ordered product of the word. -/
theorem add_pow_eq_sum_wordProd (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ w : Fin n → Bool, wordProd x y w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, Finset.mul_sum,
      ← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp (fun w => wordProd x y w),
      Fintype.sum_prod_type]
    have hcons : ∀ (b : Bool) (v : Fin n → Bool),
        (Fin.consEquiv fun _ : Fin (n + 1) => Bool) (b, v) = Fin.cons b v := fun _ _ => rfl
    simp only [hcons, wordProd_cons, Fintype.sum_bool, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by simp [add_mul]

end OddOrder
