/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SemilinearFieldAut

/-!
# A bilinear lift of a quadratic map, adapted to a scaling law

Peterfalvi Part II, Ch. III §3, p. 121, step (3) needs a *bilinear* `φ` with
`φ(x, x) = χ(x)` that inherits the scaling law of `χ` in the split form

    φ (a x) (b y) = α(a) · β(b) · φ (x, y).

The Appendix III Lemma 2(c) expansion `χ = ∑ c_{στ} σ·τ`, once normalized so that
every surviving coefficient is pinned by the scaling relations
(`exists_scaling_pinned_expansion`), gives `φ(x, y) = ∑ c_{στ} σ(x) τ(y)` — but
only after each surviving pair is *put in the right order*, since a pair
contributes `{σ|_A, τ|_A} = {α|_A, β|_A}` as an unordered pair.

That reordering is all this file does: given the restriction hypothesis, choose for
each pair the order matching `(α, β)` and sum.  Both orders have the same diagonal
(`σ(x) τ(x) = τ(x) σ(x)`), so the choice is invisible on the diagonal and `φ` is
still a lift of `χ`.

The number-theoretic input — that the surviving pairs really do all restrict to
`{α, β}` — is `OddOrder.FiniteField.frobIndex_pair_eq_of_pow_mul_eq`; it is a
hypothesis here.

## Main results

* `exists_bilinear_lift_of_pinned_restriction` — the reordered bilinear lift.
-/

set_option autoImplicit false

namespace OddOrder.RepresentationTheory

open scoped BigOperators

section BilinearLift

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

open scoped Classical in
/-- **The bilinear lift attached to a pinned expansion.**

Given an expansion `χ = ∑ c_{στ} σ·τ` all of whose surviving pairs restrict, on a
set `A` of scalars, to the unordered pair `{α, β}`, the sum

    φ(x, y) = ∑ c_{στ} · ρ₁(x) ρ₂(y),   (ρ₁, ρ₂) the order matching (α, β),

is bilinear, lifts `χ` (both orders agree on the diagonal), and satisfies
`φ (a x) (b y) = α(a) β(b) φ(x, y)` for `a, b ∈ A`.

This is Peterfalvi Part II, Ch. III §3, p. 121: with `A = F^×`, `α = 1` and
`β = θ`, it is the book's cocycle property `φ(a x, b y) = a b^θ φ(x, y)`. -/
theorem exists_bilinear_lift_of_pinned_restriction [Finite F]
    (χ : QuadraticMap (ZMod 2) F F)
    (c : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F) → F)
    (hexp : ∀ y : F,
      haveI : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
      χ y = ∑ στ : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F), c στ * (στ.1 y * στ.2 y))
    (A : Set F) (α β : F ≃ₐ[ZMod 2] F)
    (hres : ∀ στ : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F), c στ ≠ 0 →
      (∀ a ∈ A, στ.1 a = α a ∧ στ.2 a = β a) ∨
        (∀ a ∈ A, στ.1 a = β a ∧ στ.2 a = α a)) :
    ∃ φ : LinearMap.BilinMap (ZMod 2) F F,
      (∀ x : F, φ x x = χ x) ∧
      (∀ a ∈ A, ∀ b ∈ A, ∀ x y : F, φ (a * x) (b * y) = α a * β b * φ x y) ∧
      ∀ a b : F,
        (∀ στ : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F), c στ ≠ 0 → στ.1 a * στ.2 a = b) →
        ∀ x y : F, φ (a * x) (a * y) = b * φ x y := by
  classical
  let : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  have : SMulCommClass F (ZMod 2) F := SMulCommClass.symm _ _ _
  -- put each pair in the order matching `(α, β)`
  set P : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F) → Prop := fun στ =>
    ∀ a ∈ A, στ.1 a = α a ∧ στ.2 a = β a with hP
  set g : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F) → (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F) :=
    fun στ => if P στ then στ else (στ.2, στ.1) with hg
  refine ⟨∑ στ : (F ≃ₐ[ZMod 2] F) × (F ≃ₐ[ZMod 2] F),
    c στ • algAutMulBilin F 2 (g στ).1 (g στ).2, fun x => ?_,
    fun a ha b hb x y => ?_, fun a b hab x y => ?_⟩
  · -- the two orders agree on the diagonal
    rw [hexp x]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, algAutMulBilin_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun στ _ => ?_
    by_cases h : P στ
    · simp only [hg, if_pos h]
    · simp only [hg, if_neg h]
      ring
  · -- each surviving term picks up exactly `α a · β b`
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, algAutMulBilin_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun στ _ => ?_
    rcases eq_or_ne (c στ) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul, mul_zero]
    · have hgres : (g στ).1 a = α a ∧ (g στ).2 b = β b := by
        rcases hres στ h0 with h | h
        · have hPστ : P στ := h
          simp only [hg, if_pos hPστ]
          exact ⟨(h a ha).1, (h b hb).2⟩
        · by_cases hPστ : P στ
          · simp only [hg, if_pos hPστ]
            exact ⟨(hPστ a ha).1, (hPστ b hb).2⟩
          · simp only [hg, if_neg hPστ]
            exact ⟨(h a ha).2, (h b hb).1⟩
      rw [map_mul, map_mul, hgres.1, hgres.2]
      ring
  · -- the *diagonal* scaling needs no reordering: `ρ₁(a) ρ₂(a)` is order-independent
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, algAutMulBilin_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun στ _ => ?_
    rcases eq_or_ne (c στ) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul, mul_zero]
    · have hdiag : (g στ).1 a * (g στ).2 a = b := by
        by_cases hPστ : P στ
        · simp only [hg, if_pos hPστ]
          exact hab στ h0
        · simp only [hg, if_neg hPστ]
          rw [mul_comm]
          exact hab στ h0
      rw [map_mul, map_mul]
      calc c στ * ((g στ).1 a * (g στ).1 x * ((g στ).2 a * (g στ).2 y))
          = c στ * (((g στ).1 a * (g στ).2 a) * ((g στ).1 x * (g στ).2 y)) := by ring
        _ = b * (c στ * ((g στ).1 x * (g στ).2 y)) := by rw [hdiag]; ring

end BilinearLift

end OddOrder.RepresentationTheory
