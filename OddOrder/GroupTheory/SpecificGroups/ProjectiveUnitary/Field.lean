/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.Coset.Basic

/-!
# The quadratic field for three-dimensional projective unitary groups

For `q = 2 ^ n`, this file constructs the canonical quadratic extension
`GF(q²) / GF(q)`, equips it with the `q`-Frobenius star operation, and proves
the exact fixed-field and trace-fiber counts.  In particular, every equation

`b + star b = a * star a`

has exactly `q` solutions in `b`.  This is the coordinate input for the
Hermitian unital and the unitary root group of order `q³`.

This is shared infrastructure for **Peterfalvi, Part II, Chapter I §3,
Lemma 1 and Proposition 1(c)** (pp. 104–106).  Peterfalvi's `PSU(3,q)` is
Huppert's `PSU(3,q²)`; the standard unitary model is cited as Huppert,
Kapitel II, Satz 10.12 (p. 242).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

/-- The base field of order `2 ^ n`. -/
abbrev BaseField (n : ℕ) := GaloisField 2 n

/-- The canonical quadratic extension of the base field. -/
abbrev Field (n : ℕ) := FiniteField.Extension (BaseField n) 2 2

instance instCharP (n : ℕ) : CharP (Field n) 2 :=
  charP_of_injective_algebraMap' (BaseField n) 2

/-- The base field has order `2 ^ n` when `n` is positive. -/
theorem natCard_baseField (n : ℕ) (hn : 0 < n) :
    Nat.card (BaseField n) = 2 ^ n := by
  exact GaloisField.card 2 n hn.ne'

/-- The quadratic field has order `2 ^ (2 * n)`. -/
theorem natCard_field (n : ℕ) (hn : 0 < n) :
    Nat.card (Field n) = 2 ^ (2 * n) := by
  rw [FiniteField.natCard_extension, natCard_baseField n hn, ← pow_mul]
  congr 1
  omega

/-- The `2 ^ n`-Frobenius automorphism of the quadratic extension. -/
noncomputable def conjugation (n : ℕ) : Field n ≃ₐ[BaseField n] Field n :=
  FiniteField.Extension.frob (BaseField n) 2 2

/-- Conjugation is the `2 ^ n`-power map. -/
theorem conjugation_apply (n : ℕ) (hn : 0 < n) (x : Field n) :
    conjugation n x = x ^ (2 ^ n) := by
  rw [conjugation, FiniteField.Extension.frob_apply, natCard_baseField n hn]

/-- Quadratic conjugation has order two. -/
theorem conjugation_twice (n : ℕ) (x : Field n) :
    conjugation n (conjugation n x) = x := by
  change (FiniteField.Extension.frob (BaseField n) 2 2 ^ 2) x = x
  rw [FiniteField.Extension.frob_iterate_apply, ← FiniteField.natCard_extension]
  letI : Fintype (Field n) := Fintype.ofFinite (Field n)
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

noncomputable instance instStar (n : ℕ) : Star (Field n) where
  star := conjugation n

noncomputable instance instStarRing (n : ℕ) : StarRing (Field n) where
  star_involutive := conjugation_twice n
  star_mul x y := by
    change conjugation n (x * y) = conjugation n y * conjugation n x
    rw [map_mul, mul_comm]
  star_add x y := by
    change conjugation n (x + y) = conjugation n x + conjugation n y
    exact map_add (conjugation n) x y

@[simp]
theorem star_eq_conjugation (n : ℕ) (x : Field n) :
    star x = conjugation n x := rfl

/-- The field trace is `x + star x` after embedding into the quadratic field. -/
theorem algebraMap_trace_eq_add_star (n : ℕ) (x : Field n) :
    algebraMap (BaseField n) (Field n) (Algebra.trace (BaseField n) (Field n) x) =
      x + star x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.finrank_extension]
  simp [Finset.sum_range_succ, star_eq_conjugation, conjugation,
    FiniteField.Extension.frob_apply]

/-- The field norm is `x * star x` after embedding into the quadratic field. -/
theorem algebraMap_norm_eq_mul_star (n : ℕ) (x : Field n) :
    algebraMap (BaseField n) (Field n) (Algebra.norm (BaseField n) x) =
      x * star x := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, FiniteField.finrank_extension]
  simp [Finset.prod_range_succ, star_eq_conjugation, conjugation,
    FiniteField.Extension.frob_apply]

/-- The field trace has a one-dimensional kernel over the base field. -/
theorem finrank_trace_ker (n : ℕ) :
    Module.finrank (BaseField n)
        (LinearMap.ker (Algebra.trace (BaseField n) (Field n))) = 1 := by
  have hrank :=
    (Algebra.trace (BaseField n) (Field n)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (Algebra.trace_surjective (BaseField n) (Field n)),
    finrank_top, FiniteField.finrank_extension] at hrank
  rw [CommSemiring.finrank_self] at hrank
  omega

/-- The additive kernel of the field trace has exactly `2 ^ n` elements. -/
theorem natCard_trace_ker (n : ℕ) (hn : 0 < n) :
    Nat.card (LinearMap.ker (Algebra.trace (BaseField n) (Field n))) = 2 ^ n := by
  rw [Module.natCard_eq_pow_finrank (K := BaseField n), finrank_trace_ker, pow_one,
    natCard_baseField n hn]

/-- Every fiber of the quadratic field trace has exactly `2 ^ n` elements. -/
theorem natCard_trace_fiber (n : ℕ) (hn : 0 < n) (a : BaseField n) :
    Nat.card {x : Field n // Algebra.trace (BaseField n) (Field n) x = a} = 2 ^ n := by
  let tr : Field n →+ BaseField n :=
    (Algebra.trace (BaseField n) (Field n)).toAddMonoidHom
  let e₁ : {x : Field n // Algebra.trace (BaseField n) (Field n) x = a} ≃
      tr ⁻¹' ({a} : Set (BaseField n)) :=
    Equiv.subtypeEquiv (Equiv.refl (Field n)) (by simp [tr])
  calc
    Nat.card {x : Field n // Algebra.trace (BaseField n) (Field n) x = a} =
        Nat.card (tr ⁻¹' ({a} : Set (BaseField n))) := Nat.card_congr e₁
    _ = Nat.card tr.ker := Nat.card_congr <|
      tr.fiberEquivKerOfSurjective
        (Algebra.trace_surjective (BaseField n) (Field n)) a
    _ = Nat.card (LinearMap.ker (Algebra.trace (BaseField n) (Field n))) := by
      rfl
    _ = 2 ^ n := natCard_trace_ker n hn

/-- An element is fixed by conjugation exactly when its field trace vanishes. -/
theorem trace_eq_zero_iff_star_eq (n : ℕ) (x : Field n) :
    Algebra.trace (BaseField n) (Field n) x = 0 ↔ star x = x := by
  constructor
  · intro hx
    have h : x + star x = 0 := by
      rw [← algebraMap_trace_eq_add_star, hx, map_zero]
    exact (CharTwo.add_eq_zero.mp h).symm
  · intro hx
    apply (algebraMap (BaseField n) (Field n)).injective
    rw [map_zero, algebraMap_trace_eq_add_star, hx, CharTwo.add_self_eq_zero]

/-- The fixed elements of quadratic conjugation form a set of cardinality `2 ^ n`. -/
theorem natCard_fixedByConjugation (n : ℕ) (hn : 0 < n) :
    Nat.card {x : Field n // star x = x} = 2 ^ n := by
  let e : {x : Field n // star x = x} ≃
      LinearMap.ker (Algebra.trace (BaseField n) (Field n)) := {
    toFun x := ⟨x, (trace_eq_zero_iff_star_eq n x).mpr x.2⟩
    invFun x := ⟨x, (trace_eq_zero_iff_star_eq n x).mp x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  rw [Nat.card_congr e, natCard_trace_ker n hn]

/-- Positive-degree quadratic conjugation is genuinely nontrivial. -/
theorem exists_not_fixed_conjugation (n : ℕ) (hn : 0 < n) :
    ∃ x : Field n, star x ≠ x := by
  by_contra h
  push Not at h
  let e : Field n ≃ {x : Field n // star x = x} := {
    toFun x := ⟨x, h x⟩
    invFun x := x
    left_inv _ := rfl
    right_inv _ := rfl
  }
  have hcard := Nat.card_congr e
  rw [natCard_field n hn, natCard_fixedByConjugation n hn] at hcard
  have hexp := Nat.pow_right_injective (by omega : 1 < 2) hcard
  omega

/-- Every Hermitian norm value is a trace, in the embedded coordinate form. -/
theorem exists_add_star_eq_mul_star (n : ℕ) (a : Field n) :
    ∃ b : Field n, b + star b = a * star a := by
  obtain ⟨b, hb⟩ :=
    Algebra.trace_surjective (BaseField n) (Field n)
      (Algebra.norm (BaseField n) a)
  refine ⟨b, ?_⟩
  rw [← algebraMap_trace_eq_add_star, hb, algebraMap_norm_eq_mul_star]

/-- For each first coordinate, the Hermitian trace equation has exactly `2 ^ n` solutions. -/
theorem natCard_add_star_eq_mul_star (n : ℕ) (hn : 0 < n) (a : Field n) :
    Nat.card {b : Field n // b + star b = a * star a} = 2 ^ n := by
  let e : {b : Field n // b + star b = a * star a} ≃
      {b : Field n // Algebra.trace (BaseField n) (Field n) b =
        Algebra.norm (BaseField n) a} := {
    toFun b := ⟨b, (algebraMap (BaseField n) (Field n)).injective <| by
      simpa only [algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star] using b.2⟩
    invFun b := ⟨b, by
      rw [← algebraMap_trace_eq_add_star, ← algebraMap_norm_eq_mul_star, b.2]⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  rw [Nat.card_congr e, natCard_trace_fiber n hn]

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
