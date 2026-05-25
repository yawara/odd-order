/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Real (self-conjugate) class functions

For a `StarRing k` (typically `k = ℂ` with complex conjugation), the **conjugate**
of a class function `φ : ClassFunction G k` is the class function `φ.conj` defined
by `φ.conj g = star (φ g)`. A class function `φ` is **real** when `φ.conj = φ`.

Peterfalvi §3 (1.1) Odd-order theorem: `|G|` odd, `χ ∈ Irr(G), χ ≠ 1_G ⇒ χ̄ ≠ χ`.
Statement-level handling of `χ̄ = χ` (`IsReal χ`) は本モジュールの目的.

## mathlib v4.29.1 状況

mathlib に「class function の複素共役」を直接扱う API は不在 (`StarRingEnd` は
ringhom レベルのみ). 本モジュールで `ClassFunction.conj` と `IsReal` を提供.

## Main definitions

* `ClassFunction.conj` — `φ ↦ (g ↦ star (φ g))`. Involutive `StarAddMonoid` 操作.
* `ClassFunction.IsReal` — `φ.conj = φ`.

## TODO

- `Irr G` 型完成後, (1.1) の statement (`|G| odd → ∀ χ ∈ Irr G, χ ≠ 1 → ¬ IsReal χ`).
- Brauer permutation lemma ([Is] Thm 6.32) → (1.1) の証明には別 module 要.

## References

* Peterfalvi §3 (1.1), §2 (`χ̄`).
* Audit: §3 (1.1) bucket = "new helper 要".

-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k] [StarRing k]

/-- **Conjugate** of a class function: `φ.conj g = star (φ g)`.

Over `k = ℂ` this is the usual `χ ↦ χ̄`. -/
def conj (φ : ClassFunction G k) : ClassFunction G k :=
  ⟨fun g => star (φ g), fun g h => by
    change star (φ (h * g * h⁻¹)) = star (φ g)
    rw [φ.conj_eq]⟩

@[simp] theorem conj_apply (φ : ClassFunction G k) (g : G) :
    φ.conj g = star (φ g) := rfl

@[simp] theorem conj_conj (φ : ClassFunction G k) : φ.conj.conj = φ := by
  ext g
  simp

@[simp] theorem conj_zero : (0 : ClassFunction G k).conj = 0 := by
  ext g
  simp

theorem conj_add (φ ψ : ClassFunction G k) : (φ + ψ).conj = φ.conj + ψ.conj := by
  ext g
  simp [star_add]

theorem conj_neg (φ : ClassFunction G k) : (-φ).conj = -(φ.conj) := by
  ext g
  simp

theorem conj_sub (φ ψ : ClassFunction G k) : (φ - ψ).conj = φ.conj - ψ.conj := by
  ext g
  simp [star_sub]

/-- A class function `φ` is **real** if it equals its conjugate (`φ̄ = φ`).

Over `k = ℂ` this means `φ(g) ∈ ℝ` for all `g : G`. -/
def IsReal (φ : ClassFunction G k) : Prop := φ.conj = φ

theorem IsReal.iff_forall (φ : ClassFunction G k) :
    φ.IsReal ↔ ∀ g, star (φ g) = φ g := by
  constructor
  · intro h g
    have := congrArg (fun ψ : ClassFunction G k => ψ g) h
    simpa using this
  · intro h
    ext g
    simpa using h g

theorem isReal_zero : (0 : ClassFunction G k).IsReal := conj_zero

theorem IsReal.add {φ ψ : ClassFunction G k} (hφ : φ.IsReal) (hψ : ψ.IsReal) :
    (φ + ψ).IsReal := by
  unfold IsReal at *
  rw [conj_add, hφ, hψ]

theorem IsReal.neg {φ : ClassFunction G k} (hφ : φ.IsReal) : (-φ).IsReal := by
  unfold IsReal at *
  rw [conj_neg, hφ]

theorem IsReal.sub {φ ψ : ClassFunction G k} (hφ : φ.IsReal) (hψ : ψ.IsReal) :
    (φ - ψ).IsReal := by
  unfold IsReal at *
  rw [conj_sub, hφ, hψ]

end ClassFunction

end OddOrder.RepresentationTheory
