/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.OrderOfElement

/-!
# Automorphisms of order three of a Klein four group

`Aut(ℤ/2 × ℤ/2) ≅ Sym(3)`, so an automorphism of order `3` permutes the three involutions
cyclically.  Navarro uses this in the proof of (7.2): when `N_G(P)/C_G(P)` has order `3` for a
Klein four Sylow `2`-subgroup `P`, the three involutions of `P` are `G`-conjugate and `G` has a
single class of involutions.

Only the cyclic action is needed, so the full isomorphism with `Sym(3)` is not built.  The whole
argument rests on the description of a Klein four group as `{1, a, b, ab}` for any two distinct
involutions `a`, `b`.

## Main results

* `OddOrder.GroupTheory.eq_one_or_eq_or_eq_or_eq_of_klein` — `P = {1, a, b, ab}`
* `OddOrder.GroupTheory.eq_of_fixed_of_klein` — an endomorphism whose cube is the identity and
  which fixes an involution is the identity
* `OddOrder.GroupTheory.eq_or_eq_or_eq_iterate_of_klein` — an automorphism of order `3` is
  transitive on the involutions
-/

namespace OddOrder.GroupTheory

variable {P : Type*} [Group P]

/-- **A Klein four group is `{1, a, b, ab}`** for any two distinct involutions `a`, `b`. -/
theorem eq_one_or_eq_or_eq_or_eq_of_klein (hcard : Nat.card P = 4) (hexp : ∀ x : P, x * x = 1)
    {a b : P} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (x : P) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  haveI : Fintype P := Fintype.ofFinite P
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have h1 : a⁻¹ = b := mul_eq_one_iff_inv_eq.mp h
    have h2 : a⁻¹ = a := mul_eq_one_iff_inv_eq.mp (hexp a)
    exact h2.symm.trans h1)
  have haab : a ≠ a * b := fun h => hb (by
    have h1 : a * 1 = a * b := by rw [mul_one]; exact h
    exact (mul_left_cancel h1).symm)
  have hbab : b ≠ a * b := fun h => ha (by
    have h1 : 1 * b = a * b := by rw [one_mul]; exact h
    exact (mul_right_cancel h1).symm)
  have huniv : ({1, a, b, a * b} : Finset P) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Nat.card_eq_fintype_card] at hcard
    rw [hcard, Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb, Ne.symm hab1]),
      Finset.card_insert_of_notMem (by simp [hab, haab]),
      Finset.card_insert_of_notMem (by simp [hbab]), Finset.card_singleton]
  have hx : x ∈ ({1, a, b, a * b} : Finset P) := huniv ▸ Finset.mem_univ x
  simpa using hx

/-- In a Klein four group every involution has a companion: another involution distinct from
it. -/
theorem exists_ne_ne_one_of_klein (hcard : Nat.card P = 4) {a : P} (ha : a ≠ 1) :
    ∃ b : P, b ≠ 1 ∧ b ≠ a := by
  classical
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  haveI : Fintype P := Fintype.ofFinite P
  by_contra hcon
  have hall : ∀ x : P, x ≠ 1 → x = a := fun x hx => by
    by_contra hxa
    exact hcon ⟨x, hx, hxa⟩
  have huniv : ({1, a} : Finset P) = Finset.univ :=
    Finset.eq_univ_of_forall fun x => by
      rcases eq_or_ne x 1 with h | h
      · simp [h]
      · simp [hall x h]
  have h2 : (2 : ℕ) = 4 := by
    rw [← hcard, Nat.card_eq_fintype_card, ← Finset.card_univ, ← huniv,
      Finset.card_insert_of_notMem (by simp [Ne.symm ha]), Finset.card_singleton]
  exact absurd h2 (by decide)

/-- **An endomorphism whose cube is the identity and which fixes an involution is the identity.**
It then fixes a companion involution too: the only other possibility sends `y` to `xy`, and then
the cube moves `y`. -/
theorem eq_of_fixed_of_klein (hcard : Nat.card P = 4) (hexp : ∀ x : P, x * x = 1) (f : P →* P)
    (hf3 : ∀ x : P, f (f (f x)) = x) {x : P} (hx : x ≠ 1) (hfx : f x = x) (z : P) : f z = z := by
  obtain ⟨y, hy1, hyx⟩ := exists_ne_ne_one_of_klein hcard hx
  have hfinj : Function.Injective f := fun u v h => by
    have hu := hf3 u
    rw [h] at hu
    exact hu.symm.trans (hf3 v)
  have hfy1 : f y ≠ 1 := fun h => hy1 (by
    have h3 := hf3 y
    rw [h, map_one, map_one] at h3
    exact h3.symm)
  have hfyx : f y ≠ x := fun h => hyx (hfinj (h.trans hfx.symm))
  have hfyy : f y = y := by
    rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp hx hy1 (Ne.symm hyx) (f y) with
      h | h | h | h
    · exact absurd h hfy1
    · exact absurd h hfyx
    · exact h
    · exfalso
      have hfxy : f (x * y) = y := by
        rw [map_mul, hfx, h, ← mul_assoc, hexp x, one_mul]
      have h3 : f (f (f y)) = x * y := by rw [h, hfxy, h]
      have hxy : x * y = y := h3.symm.trans (hf3 y)
      have h1 : x * y = 1 * y := by rw [one_mul]; exact hxy
      exact hx (mul_right_cancel h1)
  rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp hx hy1 (Ne.symm hyx) z with h | h | h | h
  · rw [h, map_one]
  · rw [h, hfx]
  · rw [h, hfyy]
  · rw [h, map_mul, hfx, hfyy]

/-- **An automorphism of order three of a Klein four group is transitive on the involutions.**
It has no fixed involution (`eq_of_fixed_of_klein`), so `a`, `f a`, `f² a` are three distinct
involutions — hence all of them. -/
theorem eq_or_eq_or_eq_iterate_of_klein (hcard : Nat.card P = 4) (hexp : ∀ x : P, x * x = 1)
    (f : P →* P) (hf3 : ∀ x : P, f (f (f x)) = x) (hfne : ∃ x : P, f x ≠ x)
    {a b : P} (ha : a ≠ 1) (hb : b ≠ 1) :
    b = a ∨ b = f a ∨ b = f (f a) := by
  have hnofix : ∀ x : P, x ≠ 1 → f x ≠ x := fun x hx hfx => by
    obtain ⟨z, hz⟩ := hfne
    exact hz (eq_of_fixed_of_klein hcard hexp f hf3 hx hfx z)
  have hfa1 : f a ≠ 1 := fun h => ha (by
    have h3 := hf3 a
    rw [h, map_one, map_one] at h3
    exact h3.symm)
  have hffa1 : f (f a) ≠ 1 := fun h => ha (by
    have h3 := hf3 a
    rw [h, map_one] at h3
    exact h3.symm)
  have hne1 : f a ≠ a := hnofix a ha
  have hne2 : f (f a) ≠ f a := hnofix (f a) hfa1
  have hne3 : f (f a) ≠ a := fun h => hne1 (by
    have h3 := hf3 a
    rw [h] at h3
    exact h3)
  rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp ha hfa1 (Ne.symm hne1) b with h | h | h | h
  · exact absurd h hb
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp ha hfa1 (Ne.symm hne1) (f (f a)) with
      h' | h' | h' | h'
    · exact absurd h' hffa1
    · exact absurd h' hne3
    · exact absurd h' hne2
    · rw [h, h']

end OddOrder.GroupTheory
