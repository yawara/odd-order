/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subgroup.Defs

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

/-! ### Cyclic rotation -/

section Rotate

variable {n : ℕ}

/-- Rotating a word: move the first letter to the end. -/
def rotateWord (w : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (Fin.tail w) (w 0)

theorem wordProd_snoc (x y : R) (v : Fin n → Bool) (b : Bool) :
    wordProd x y (Fin.snoc v b) = wordProd x y v * (if b then x else y) := by
  rw [wordProd, wordProd, List.ofFn_succ']
  simp

theorem wordProd_eq_head_mul (x y : R) (w : Fin (n + 1) → Bool) :
    wordProd x y w = (if w 0 then x else y) * wordProd x y (Fin.tail w) := by
  conv_lhs => rw [← Fin.cons_self_tail w]
  rw [wordProd_cons]

theorem wordProd_rotateWord (x y : R) (w : Fin (n + 1) → Bool) :
    wordProd x y (rotateWord w) = wordProd x y (Fin.tail w) * (if w 0 then x else y) := by
  rw [rotateWord, wordProd_snoc]

/-- **Cyclic rotation changes a word product by a commutator.**  Modulo any additive subgroup
containing all commutators, the product along a word depends only on its cyclic class. -/
theorem wordProd_rotateWord_sub_mem (x y : R) (w : Fin (n + 1) → Bool) (T : AddSubgroup R)
    (hT : ∀ a b : R, a * b - b * a ∈ T) :
    wordProd x y (rotateWord w) - wordProd x y w ∈ T := by
  rw [wordProd_rotateWord, wordProd_eq_head_mul]
  exact hT _ _

end Rotate

end OddOrder
