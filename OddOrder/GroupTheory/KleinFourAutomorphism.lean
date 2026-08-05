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
* `OddOrder.GroupTheory.eq_of_fixed_two_of_klein` — an endomorphism fixing two distinct
  involutions is the identity
* `OddOrder.GroupTheory.forall_cube_eq_self_of_klein` — a nontrivial endomorphism with an odd
  iterate equal to the identity has cube the identity
* `OddOrder.GroupTheory.eq_or_eq_or_eq_iterate_of_klein` — an automorphism of order `3` is
  transitive on the involutions
* `OddOrder.GroupTheory.eq_or_eq_or_eq_iterate_of_odd_of_klein` — the two combined, in the form
  Navarro (7.2) uses
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

/-- **An endomorphism fixing two distinct involutions is the identity**: they generate. -/
theorem eq_of_fixed_two_of_klein (hcard : Nat.card P = 4) (hexp : ∀ x : P, x * x = 1)
    (f : P →* P) {a b : P} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (hfa : f a = a)
    (hfb : f b = b) (z : P) : f z = z := by
  rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp ha hb hab z with h | h | h | h
  · rw [h, map_one]
  · rw [h, hfa]
  · rw [h, hfb]
  · rw [h, map_mul, hfa, hfb]

/-- **A nontrivial endomorphism of a Klein four group with an odd iterate equal to the identity
has cube the identity.**  This is `Aut(ℤ/2 × ℤ/2) ≅ Sym(3)` in the only form Navarro's (7.2)
needs: the image of `N_G(P)` in `Aut(P)` has odd order, so a nontrivial element of it cubes to
`1`.

If `f` moved `a` but `f² a = a`, then `f²` would fix the two distinct involutions `a` and `f a`,
hence be the identity, and an odd iterate of an involution is itself — so `f` would be the
identity. -/
theorem forall_cube_eq_self_of_klein (hcard : Nat.card P = 4) (hexp : ∀ x : P, x * x = 1)
    (f : P →* P) {m : ℕ} (hm : Odd m) (hfm : ∀ x : P, (⇑f)^[m] x = x)
    (hfne : ∃ x : P, f x ≠ x) (z : P) : f (f (f z)) = z := by
  obtain ⟨k, hk⟩ := hm
  subst hk
  have hfinj : Function.Injective f := by
    have hleft : Function.LeftInverse ((⇑f)^[2 * k]) f := fun u => by
      have hu := hfm u
      rw [Function.iterate_add_apply, Function.iterate_one] at hu
      exact hu
    exact hleft.injective
  obtain ⟨a, hfa⟩ := hfne
  have ha : a ≠ 1 := fun h => hfa (by rw [h, map_one])
  have hfa1 : f a ≠ 1 := fun h => ha (hfinj (h.trans (map_one f).symm))
  have hne1 : f a ≠ a := hfa
  -- `f²` cannot fix `a`
  have hne2 : f (f a) ≠ a := by
    intro h
    have hsq : ∀ z : P, f (f z) = z :=
      eq_of_fixed_two_of_klein hcard hexp (f.comp f) ha hfa1 (Ne.symm hne1) h
        (by simpa using congrArg f h)
    have hiter : ∀ n : ℕ, ∀ z : P, (⇑f)^[2 * n] z = z := by
      intro n
      induction n with
      | zero => intro z; simp
      | succ n ih =>
          intro z
          rw [Nat.mul_succ, Function.iterate_add_apply,
            show (⇑f)^[2] z = f (f z) from rfl, hsq z]
          exact ih z
    exact hne1 (by
      have hfin := hfm a
      rw [Function.iterate_add_apply, Function.iterate_one, hiter k (f a)] at hfin
      exact hfin)
  have hne3 : f (f a) ≠ f a := fun h => hne1 (hfinj h)
  have hffa1 : f (f a) ≠ 1 := fun h => hfa1 (hfinj (h.trans (map_one f).symm))
  -- `f³` fixes `a`
  have hcube : f (f (f a)) = a := by
    have hne4 : f (f (f a)) ≠ f a := fun h => hne2 (hfinj h)
    have hne5 : f (f (f a)) ≠ f (f a) := fun h => hne3 (hfinj h)
    have hfff1 : f (f (f a)) ≠ 1 := fun h => hffa1 (hfinj (h.trans (map_one f).symm))
    rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp ha hfa1 (Ne.symm hne1)
      (f (f (f a))) with h | h | h | h
    · exact absurd h hfff1
    · exact h
    · exact absurd h hne4
    · exfalso
      refine hne5 (h.trans ?_)
      rcases eq_one_or_eq_or_eq_or_eq_of_klein hcard hexp ha hfa1 (Ne.symm hne1)
        (f (f a)) with h' | h' | h' | h'
      · exact absurd h' hffa1
      · exact absurd h' hne2
      · exact absurd h' hne3
      · exact h'.symm
  exact eq_of_fixed_two_of_klein hcard hexp (f.comp (f.comp f)) ha hfa1 (Ne.symm hne1) hcube
    (by simpa using congrArg f hcube) z

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

/-- **A nontrivial endomorphism of odd order is transitive on the involutions.**  This is the
form Navarro (7.2) uses: `N_G(P)/C_G(P)` has odd order, so a `g ∈ N_G(P)` not centralising `P`
conjugates the three involutions of `P` cyclically. -/
theorem eq_or_eq_or_eq_iterate_of_odd_of_klein (hcard : Nat.card P = 4)
    (hexp : ∀ x : P, x * x = 1) (f : P →* P) {m : ℕ} (hm : Odd m)
    (hfm : ∀ x : P, (⇑f)^[m] x = x) (hfne : ∃ x : P, f x ≠ x)
    {a b : P} (ha : a ≠ 1) (hb : b ≠ 1) :
    b = a ∨ b = f a ∨ b = f (f a) :=
  eq_or_eq_or_eq_iterate_of_klein hcard hexp f
    (forall_cube_eq_self_of_klein hcard hexp f hm hfm hfne) hfne ha hb

end OddOrder.GroupTheory
