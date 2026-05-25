/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Conj
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

end OddOrder.RepresentationTheory
