/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction
import OddOrder.GroupTheory.RepresentationTheory.GaloisCharacter
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

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

- trivial character API 完成後, (1.1) の pointwise statement
  (`|G| odd → ∀ χ ∈ Irr G, χ ≠ 1 → ¬ IsReal χ`).
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

/-- Conjugation does not move the support: `star x = 0 ↔ x = 0`. -/
@[simp] theorem conj_support (φ : ClassFunction G k) : φ.conj.support = φ.support := by
  ext g
  simp [ClassFunction.mem_support, star_eq_zero]

/-- `ClassFunction.conj` **is** the coefficientwise complex conjugation
(`mapRingEquiv Complex.conjAe`): both are pointwise `star`. -/
theorem conj_eq_mapRingEquiv_conjAe {G : Type*} [Group G] (φ : ClassFunction G ℂ) :
    φ.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ :=
  ClassFunction.ext fun _ => rfl

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

variable {G : Type*} [Group G]

@[simp] theorem trivialClassFunction_isReal :
    ClassFunction.IsReal (trivialClassFunction G) := by
  unfold ClassFunction.IsReal
  ext g
  simp [trivialClassFunction]

/-- The type of real irreducible complex characters of `G`.

This is Peterfalvi's `χ ∈ Irr(G)` with `χ̄ = χ`, named so that Brauer's
permutation lemma and the odd-order specializations do not repeat the raw
subtype expression. -/
abbrev RealIrreducibleCharacter (G : Type*) [Group G] :=
  {χ : IrreducibleCharacter G // ClassFunction.IsReal (χ : ClassFunction G ℂ)}

/-- The trivial real irreducible character of `G`. -/
def trivialRealIrreducibleCharacter (G : Type*) [Group G] :
    RealIrreducibleCharacter G :=
  ⟨trivialIrreducibleCharacter G, by simp⟩

namespace RealIrreducibleCharacter

variable {G : Type*} [Group G]

instance : Coe (RealIrreducibleCharacter G) (IrreducibleCharacter G) :=
  ⟨fun χ => χ.1⟩

instance : Coe (RealIrreducibleCharacter G) (ClassFunction G ℂ) :=
  ⟨fun χ => (χ.1 : ClassFunction G ℂ)⟩

@[simp] theorem coe_mk (χ : IrreducibleCharacter G)
    (hχ : ClassFunction.IsReal (χ : ClassFunction G ℂ)) :
    ((⟨χ, hχ⟩ : RealIrreducibleCharacter G) : IrreducibleCharacter G) = χ :=
  rfl

@[simp] theorem coe_trivialRealIrreducibleCharacter :
    ((trivialRealIrreducibleCharacter G : RealIrreducibleCharacter G) :
      IrreducibleCharacter G) = trivialIrreducibleCharacter G :=
  rfl

@[simp] theorem coe_mk_classFunction (χ : IrreducibleCharacter G)
    (hχ : ClassFunction.IsReal (χ : ClassFunction G ℂ)) :
    ((⟨χ, hχ⟩ : RealIrreducibleCharacter G) : ClassFunction G ℂ) =
      (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem isReal (χ : RealIrreducibleCharacter G) :
    ClassFunction.IsReal (χ : ClassFunction G ℂ) :=
  χ.2

@[simp] theorem isIrreducible (χ : RealIrreducibleCharacter G) :
    IsIrreducibleCharacter (χ : ClassFunction G ℂ) :=
  χ.1.isIrreducible

@[ext] theorem ext {χ ψ : RealIrreducibleCharacter G}
    (h : (χ : IrreducibleCharacter G) = (ψ : IrreducibleCharacter G)) : χ = ψ :=
  Subtype.ext h

end RealIrreducibleCharacter

end OddOrder.RepresentationTheory
