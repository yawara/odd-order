/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.GroupTheory.RepresentationTheory.IsReal
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

/-!
# Brauer's permutation lemma

For a finite group `G`, [Is] Thm 6.32 states:

> The number of real irreducible characters of `G` equals the number of self-inverse
> conjugacy classes of `G`.

The classical proof uses invertibility of the character table (Schur orthogonality) and
the compatibility of two involutions:

* on `ConjClasses G`, `C ↦ C⁻¹` (inversion of class representatives);
* on `Irr G`, `χ ↦ χ̄` (complex conjugation of values).

This module provides the inversion involution on `ConjClasses G`, the predicate
`ConjClasses.IsReal`, and states the main theorem. The proof requires character
orthogonality infrastructure (second orthogonality / column relations), which is
scheduled for the follow-up Wave 1a `SecondOrthogonality.lean` module, and is therefore
left as `sorry` here.

## Main definitions

* `ConjClasses.inv` — `⟦g⟧ ↦ ⟦g⁻¹⟧`. Involutive.
* `ConjClasses.IsReal` — `C` is real iff `inv C = C`.

## Main results

* `OddOrder.RepresentationTheory.brauer_permutation_lemma` — equality of cardinalities
  (proof deferred).

## References

* Isaacs, *Character Theory of Finite Groups*, Theorem 6.32.
* Peterfalvi §3 (1.1) — uses this lemma in the proof of "odd order ⇒ no non-trivial real
  irreducibles".
* Peterfalvi §6 (4.5.b) — same usage at higher level.
-/

namespace ConjClasses

variable {G : Type*} [Group G]

private theorem commute_of_sq_commute_of_odd_card [Finite G] (hodd : Odd (Nat.card G))
    {x g : G} (hcomm : Commute (x ^ 2) g) : Commute x g := by
  have hcop_card : Nat.Coprime 2 (Nat.card G) := hodd.coprime_two_left
  have hcop_order : Nat.Coprime 2 (orderOf x) :=
    hcop_card.coprime_dvd_right (orderOf_dvd_natCard x)
  rcases exists_pow_eq_self_of_coprime (x := x) hcop_order with ⟨m, hm⟩
  rw [← hm]
  exact hcomm.pow_left m

/-- In a finite group of odd order, an element conjugate to its inverse is trivial. -/
theorem eq_one_of_isConj_inv_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) {g : G}
    (hg : IsConj g⁻¹ g) : g = 1 := by
  rw [isConj_iff] at hg
  rcases hg with ⟨x, hx⟩
  have hx_inv : x * g * x⁻¹ = g⁻¹ := by
    have h := congrArg Inv.inv hx
    simpa [mul_assoc] using h
  have hx_sq_conj : x ^ 2 * g * (x ^ 2)⁻¹ = g := by
    calc
      x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
        rw [pow_two]
        group
      _ = x * g⁻¹ * x⁻¹ := by rw [hx_inv]
      _ = g := hx
  have hx_sq_comm : Commute (x ^ 2) g := by
    rw [commute_iff_eq]
    calc
      x ^ 2 * g = (x ^ 2 * g * (x ^ 2)⁻¹) * x ^ 2 := by group
      _ = g * x ^ 2 := by rw [hx_sq_conj]
  have hx_comm : Commute x g := commute_of_sq_commute_of_odd_card hodd hx_sq_comm
  have hg_self_inv : g = g⁻¹ := by
    calc
      g = x * g⁻¹ * x⁻¹ := hx.symm
      _ = g⁻¹ := by
        rw [(hx_comm.inv_right).eq]
        group
  have hg_sq : g ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun y : G => g * y) hg_self_inv).trans (mul_inv_cancel g)
  have hcop_card : Nat.Coprime 2 (Nat.card G) := hodd.coprime_two_left
  have hcop_order : Nat.Coprime 2 (orderOf g) :=
    hcop_card.coprime_dvd_right (orderOf_dvd_natCard g)
  have horder_dvd_two : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg_sq
  have horder_one : orderOf g = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order horder_dvd_two (dvd_refl (orderOf g))
  exact orderOf_eq_one_iff.mp horder_one

/-- Conjugacy is preserved by inversion: if `a ~ b`, then `a⁻¹ ~ b⁻¹`. -/
theorem isConj_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  rw [isConj_iff] at h ⊢
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, by group⟩

/-- The inversion involution on conjugacy classes: `⟦g⟧ ↦ ⟦g⁻¹⟧`. -/
def inv : ConjClasses G → ConjClasses G :=
  Quotient.lift (fun g : G => ConjClasses.mk g⁻¹) fun _ _ h =>
    mk_eq_mk_iff_isConj.2 (isConj_inv h)

@[simp] theorem inv_mk (g : G) : inv (ConjClasses.mk g) = ConjClasses.mk g⁻¹ := rfl

@[simp] theorem inv_one : inv (1 : ConjClasses G) = 1 := by
  change inv (ConjClasses.mk 1) = ConjClasses.mk 1
  simp [inv_mk]

@[simp] theorem inv_inv (C : ConjClasses G) : inv (inv C) = C := by
  induction C using Quotient.inductionOn with
  | _ g =>
    change inv (inv (ConjClasses.mk g)) = ConjClasses.mk g
    simp [inv_mk]

theorem inv_involutive : Function.Involutive (inv : ConjClasses G → ConjClasses G) :=
  inv_inv

/-- A conjugacy class is **real** (self-inverse) when its inversion equals itself,
i.e. `g` and `g⁻¹` are conjugate for any representative `g`. -/
def IsReal (C : ConjClasses G) : Prop := inv C = C

theorem isReal_iff (C : ConjClasses G) : IsReal C ↔ inv C = C := Iff.rfl

theorem isReal_mk_iff (g : G) : IsReal (ConjClasses.mk g) ↔ IsConj g⁻¹ g := by
  unfold IsReal
  rw [inv_mk, mk_eq_mk_iff_isConj]

@[simp] theorem isReal_one : IsReal (1 : ConjClasses G) := inv_one

/-- In a finite group of odd order, the only real conjugacy class is the
identity class. -/
theorem eq_one_of_isReal_of_odd_card [Finite G] (hodd : Odd (Nat.card G))
    {C : ConjClasses G} (hC : IsReal C) : C = 1 := by
  induction C using Quotient.inductionOn with
  | _ g =>
    have hg_conj : IsConj g⁻¹ g := (isReal_mk_iff g).mp hC
    have hg_one : g = 1 := eq_one_of_isConj_inv_of_odd_card hodd hg_conj
    change ConjClasses.mk g = ConjClasses.mk (1 : G)
    simp [hg_one]

/-- In a finite group of odd order, the subtype of real conjugacy classes is
subsingleton. -/
theorem subsingleton_realClasses_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) :
    Subsingleton { C : ConjClasses G // IsReal C } where
  allEq A B := by
    exact Subtype.ext (by
      rw [eq_one_of_isReal_of_odd_card hodd A.property,
        eq_one_of_isReal_of_odd_card hodd B.property])

/-- In a finite group of odd order, there is exactly one real conjugacy class:
the identity class. -/
theorem card_realClasses_eq_one_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) :
    Nat.card { C : ConjClasses G // IsReal C } = 1 := by
  letI := subsingleton_realClasses_of_odd_card (G := G) hodd
  exact Nat.card_of_subsingleton ⟨1, isReal_one⟩

end ConjClasses

namespace OddOrder.RepresentationTheory

/-- **Brauer's permutation lemma** ([Is] Thm 6.32).

For a finite group `G`, the number of real irreducible complex characters equals the
number of self-inverse conjugacy classes:

`# { χ ∈ Irr G | χ̄ = χ } = # { C ∈ ConjClasses G | C⁻¹ = C }`.

The classical proof uses the invertibility of the character table (Schur orthogonality)
to relate the two compatible involutions `χ ↦ χ̄` on `Irr G` and `C ↦ C⁻¹` on
`ConjClasses G`.

(Proof deferred: requires the Wave 1a `SecondOrthogonality` module + a finite indexing
API for `irreducibleCharacters G`.) -/
theorem brauer_permutation_lemma {G : Type*} [Group G] [Finite G] :
    Nat.card { χ : IrreducibleCharacter G //
                 ClassFunction.IsReal (χ : ClassFunction G ℂ) } =
    Nat.card { C : ConjClasses G // ConjClasses.IsReal C } := by
  sorry

/-- Odd-order cardinal specialization of Brauer's permutation lemma.

In a finite group of odd order, there is exactly one real irreducible character.
This is the cardinal form of Peterfalvi §3 (1.1); identifying the unique
character with the trivial character is left to the later trivial-character API. -/
theorem card_realIrreducibleCharacters_eq_one_of_odd_card {G : Type*} [Group G]
    [Finite G] (hodd : Odd (Nat.card G)) :
    Nat.card { χ : IrreducibleCharacter G //
                 ClassFunction.IsReal (χ : ClassFunction G ℂ) } = 1 := by
  rw [brauer_permutation_lemma, ConjClasses.card_realClasses_eq_one_of_odd_card hodd]

end OddOrder.RepresentationTheory
