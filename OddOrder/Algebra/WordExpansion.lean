/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.Group.Fin.Basic

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

/-! ### Rotation is the cyclic shift, and its periods -/

section Period

variable {n : ℕ}

theorem rotateWord_apply (w : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    rotateWord w i = w (i + 1) := by
  refine Fin.lastCases ?_ ?_ i
  · rw [rotateWord, Fin.snoc_last]
    congr 1
    ext
    simp
  · intro j
    rw [rotateWord, Fin.snoc_castSucc]
    change w j.succ = _
    congr 1
    ext
    simp [Fin.val_succ]

/-- Iterating the shift on indices. -/
theorem val_iterate_add_one (i : Fin (n + 1)) (m : ℕ) :
    ((fun j : Fin (n + 1) => j + 1)^[m] i).val = (i.val + m) % (n + 1) := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply', Fin.val_add, ih, Fin.val_one', ← Nat.add_mod,
      Nat.add_assoc]

theorem iterate_rotateWord_apply (w : Fin (n + 1) → Bool) (m : ℕ) (i : Fin (n + 1)) :
    rotateWord^[m] w i = w ((fun j : Fin (n + 1) => j + 1)^[m] i) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply', rotateWord_apply]

/-- A full turn is the identity. -/
theorem isPeriodicPt_rotateWord (w : Fin (n + 1) → Bool) :
    Function.IsPeriodicPt rotateWord (n + 1) w := by
  funext i
  rw [iterate_rotateWord_apply]
  congr 1
  refine Fin.ext ?_
  rw [val_iterate_add_one, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- A word fixed by one rotation is constant. -/
theorem const_of_isFixedPt_rotateWord {w : Fin (n + 1) → Bool} (h : rotateWord w = w)
    (i j : Fin (n + 1)) : w i = w j := by
  have hiter : ∀ (m : ℕ) (i : Fin (n + 1)),
      w ((fun j : Fin (n + 1) => j + 1)^[m] i) = w i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro i
      rw [Function.iterate_succ_apply, ih]
      have hi := congrFun h i
      rw [rotateWord_apply] at hi
      exact hi
  have key : ∀ j : Fin (n + 1), w j = w 0 := by
    intro j
    have hj : (fun j : Fin (n + 1) => j + 1)^[j.val] 0 = j := by
      refine Fin.ext ?_
      rw [val_iterate_add_one]
      simp [Nat.mod_eq_of_lt j.isLt]
    rw [← hj, hiter]
  rw [key i, key j]

/-- **Non-constant words have full rotation period.**  If some rotation by an amount prime to
`p` fixes a word of length `p`, the word is constant. -/
theorem const_of_iterate_rotateWord_eq {p : ℕ} (hp : p.Prime) (hn : n + 1 = p)
    {w : Fin (n + 1) → Bool} {k : ℕ} (hk : ¬ p ∣ k) (h : rotateWord^[k] w = w)
    (i j : Fin (n + 1)) : w i = w j := by
  have hdvdk : Function.minimalPeriod rotateWord w ∣ k :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp h
  have hdvdp : Function.minimalPeriod rotateWord w ∣ p :=
    hn ▸ Function.isPeriodicPt_iff_minimalPeriod_dvd.mp (isPeriodicPt_rotateWord w)
  rcases (Nat.dvd_prime hp).mp hdvdp with h1 | hpe
  · exact const_of_isFixedPt_rotateWord
      (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) i j
  · exact absurd (hpe ▸ hdvdk) hk

end Period

/-! ### Orbits of a map of finite order

A sum over a set on which iteration of `σ` acts freely with period `p` is `p` times something;
in a ring of characteristic `p` such a sum vanishes.  This is what kills the non-constant words
in the expansion of `(x + y) ^ p`.
-/

section Orbits

variable {α : Type*}

/-- Iterating a map of period `p` only depends on the exponent modulo `p`. -/
theorem iterate_mod_of_period (σ : α → α) {p : ℕ} (hper : ∀ v, σ^[p] v = v) (m : ℕ) (w : α) :
    σ^[m] w = σ^[m % p] w := by
  conv_lhs => rw [← Nat.mod_add_div m p]
  rw [Function.iterate_add_apply, Function.iterate_mul]
  congr 1
  induction m / p with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih]; exact hper _

variable [DecidableEq α]

/-- The orbit of `w` under the first `p` iterates of `σ`. -/
def iterateOrbit (σ : α → α) (p : ℕ) (w : α) : Finset α :=
  (Finset.range p).image fun k => σ^[k] w

theorem mem_iterateOrbit_iff {σ : α → α} {p : ℕ} {w v : α} :
    v ∈ iterateOrbit σ p w ↔ ∃ k < p, σ^[k] w = v := by
  simp [iterateOrbit, Finset.mem_image, Finset.mem_range]

theorem self_mem_iterateOrbit (σ : α → α) {p : ℕ} (hp : 0 < p) (w : α) :
    w ∈ iterateOrbit σ p w :=
  mem_iterateOrbit_iff.mpr ⟨0, hp, rfl⟩

theorem iterate_mem_iterateOrbit (σ : α → α) {p : ℕ} (hp : 0 < p) (hper : ∀ v, σ^[p] v = v)
    (m : ℕ) (w : α) : σ^[m] w ∈ iterateOrbit σ p w :=
  mem_iterateOrbit_iff.mpr ⟨m % p, Nat.mod_lt _ hp, (iterate_mod_of_period σ hper m w).symm⟩

/-- The orbit finset does not change along the action. -/
theorem iterateOrbit_apply (σ : α → α) {p : ℕ} (hp : 0 < p) (hper : ∀ v, σ^[p] v = v) (w : α) :
    iterateOrbit σ p (σ w) = iterateOrbit σ p w := by
  ext v
  rw [mem_iterateOrbit_iff, mem_iterateOrbit_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [← Function.iterate_succ_apply]
    exact ⟨(k + 1) % p, Nat.mod_lt _ hp, (iterate_mod_of_period σ hper (k + 1) w).symm⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(j + (p - 1)) % p, Nat.mod_lt _ hp, ?_⟩
    rw [← Function.iterate_succ_apply, iterate_mod_of_period σ hper _ w,
      Nat.succ_eq_add_one, Nat.mod_add_mod, show j + (p - 1) + 1 = j + p by omega,
      Nat.add_mod_right, ← iterate_mod_of_period σ hper j w]

theorem iterateOrbit_iterate (σ : α → α) {p : ℕ} (hp : 0 < p) (hper : ∀ v, σ^[p] v = v)
    (k : ℕ) (w : α) : iterateOrbit σ p (σ^[k] w) = iterateOrbit σ p w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', iterateOrbit_apply σ hp hper, ih]

/-- The orbit of any of its own members is the same finset. -/
theorem iterateOrbit_of_mem (σ : α → α) {p : ℕ} (hp : 0 < p) (hper : ∀ v, σ^[p] v = v)
    {w v : α} (hv : v ∈ iterateOrbit σ p w) : iterateOrbit σ p v = iterateOrbit σ p w := by
  obtain ⟨k, _, rfl⟩ := mem_iterateOrbit_iff.mp hv
  exact iterateOrbit_iterate σ hp hper k w

end Orbits

end OddOrder
