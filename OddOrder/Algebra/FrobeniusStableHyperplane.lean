/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Trace
import OddOrder.Algebra.PaleySpanning
import OddOrder.Algebra.RelationLattice

/-!
# The kernel of the trace is the only Frobenius-stable hyperplane

Let `F` be a finite field of characteristic `p` and `K = 𝔽_p` its prime field.  A `K`-subspace
`W ≤ F` is *Frobenius-stable* when `x ∈ W → x^p ∈ W`; equivalently `W` is a submodule for the
action of `K[Frob] ≅ K[X]/(X^n - 1)`, `n = [F : K]`.  The trace kernel is always such a
hyperplane, and for `p = 3` with `|F| ≡ 3 (mod 4)` it is the **only** one:

> if a non-zero `𝔽₃`-functional `ℓ` on `F` satisfies `ℓ x = 0 → ℓ (x³) = 0`, then
> `ker ℓ = ker Tr`.

The proof is elementary.  Trace duality writes `ℓ = Tr(c · −)`; Frobenius-stability turns into
`ℓ ∘ Frob = μ · ℓ` for a scalar `μ ∈ 𝔽₃`, which by duality reads `c^{|F|/3} = μ c`, i.e.
`c = μ c³`.  Then `μ = 0` forces `c = 0`, `μ = 1` gives `c² = 1`, and `μ = -1` gives `c² = -1`,
exhibiting `-1` as a square — impossible when `|F| ≡ 3 (mod 4)`
(`OddOrder.Paley.not_isSquare_neg_one`, the same input that drives Lemma B of
`notes/bg/appC_problem1_partial_resolution.md`).  So `c = ±1` and `ker ℓ = ker Tr`.

**Why this matters** (BG Appendix C, Problem 1).  The `S`-values produced by the collisions of
`D(p) = p^E - (p-1)^E` span a Frobenius-stable subspace of `𝔽_{3^q}`
(`OddOrder.BG.AppC.Problem1.CollisionPair.frobenius`), so the *span* criterion
`false_of_collisionSet_spanning` asks that span to be everything, while the *trace* criterion
`false_of_collisionPair_trace_ne_zero` only asks it not to lie inside `ker Tr`.  The theorem
below says `ker Tr` is the unique Frobenius-stable hyperplane, which is exactly why the second is
strictly weaker: a Frobenius-stable proper subspace can avoid `ker Tr` only by having
codimension at least two.

## Main results

* `trace_pow_char` — `Tr(y^p) = Tr(y)`.
* `ker_eq_ker_trace_of_frobenius_stable` — the uniqueness statement above.
* `frobeniusStableHyperplane_unique` — the same, phrased for subspaces.
-/

namespace OddOrder.FrobeniusStable

open Finset

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]

section Trace

/-- **The trace is Frobenius-invariant**: `Tr(y^p) = Tr(y)`.

`algebraMap (Tr y)` is the sum of the Frobenius conjugates
(`FiniteField.algebraMap_trace_eq_sum_pow`), raising to the `p`-th power is additive and permutes
those conjugates, and `Tr y` lies in the prime field where `x ↦ x^p` is the identity. -/
theorem trace_pow_char (y : F) :
    Algebra.trace (ZMod p) F (y ^ p) = Algebra.trace (ZMod p) F y := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  have hcard : Nat.card (ZMod p) = p := by simp
  have hsum : ∀ (n : ℕ) (f : ℕ → F), (∑ i ∈ Finset.range n, f i) ^ p
      = ∑ i ∈ Finset.range n, f i ^ p := by
    intro n f
    induction n with
    | zero => simp [(Fact.out : p.Prime).ne_zero]
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, add_pow_char, ih]
  apply (algebraMap (ZMod p) F).injective
  have e1 : algebraMap (ZMod p) F (Algebra.trace (ZMod p) F (y ^ p))
      = ∑ i ∈ Finset.range (Module.finrank (ZMod p) F), (y ^ p) ^ p ^ i := by
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hcard]
  have e2 : algebraMap (ZMod p) F (Algebra.trace (ZMod p) F y)
      = ∑ i ∈ Finset.range (Module.finrank (ZMod p) F), y ^ p ^ i := by
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hcard]
  have e3 : ∀ i : ℕ, (y ^ p) ^ p ^ i = (y ^ p ^ i) ^ p := fun i => by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [e1, e2]
  simp only [e3]
  rw [← hsum, ← e2, ← map_pow, ZMod.pow_card]

/-- The Frobenius `x ↦ x^p` as a `𝔽_p`-linear endomorphism of `F`. -/
noncomputable def frobLin : F →ₗ[ZMod p] F where
  toFun x := x ^ p
  map_add' x y := by
    haveI : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
    rw [add_pow_char]
  map_smul' a x := by
    simp only [Algebra.smul_def, RingHom.id_apply, mul_pow, ← map_pow, ZMod.pow_card]

omit [Finite F] in
@[simp]
theorem frobLin_apply (x : F) : (frobLin (p := p) x) = x ^ p := rfl

end Trace

section Uniqueness

variable [Algebra.IsSeparable (ZMod p) F]

private theorem zmod3_trichotomy : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide

private theorem zmod3_two_eq_neg_one : (2 : ZMod 3) = -1 := by decide

/-- **`ker Tr` is the only Frobenius-stable hyperplane** of a finite field of characteristic three
whose order is `≡ 3 (mod 4)`.

If `ℓ ≠ 0` is an `𝔽₃`-functional whose kernel is stable under `x ↦ x³`, then `ker ℓ = ker Tr`. -/
theorem ker_eq_ker_trace_of_frobenius_stable [Fintype F] (hp : p = 3)
    (h4 : Fintype.card F % 4 = 3) (ℓ : F →ₗ[ZMod p] ZMod p) (hℓ : ℓ ≠ 0)
    (hstab : ∀ x : F, ℓ x = 0 → ℓ (x ^ p) = 0) :
    LinearMap.ker ℓ = LinearMap.ker (Algebra.trace (ZMod p) F) := by
  classical
  subst hp
  haveI : CharP F 3 := charP_of_injective_algebraMap (algebraMap (ZMod 3) F).injective 3
  haveI : Module.Finite (ZMod 3) F := Module.Finite.of_finite
  -- trace duality: `ℓ = Tr(c ·)` with `c ≠ 0`
  obtain ⟨c, hc⟩ := OddOrder.RelationLattice.exists_trace_repr (K := ZMod 3) ℓ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hℓ (LinearMap.ext fun x => by simp [hc x])
  -- nondegeneracy of the trace form
  have hnd : ∀ a : F, (∀ x : F, Algebra.trace (ZMod 3) F (a * x) = 0) → a = 0 := by
    intro a ha
    refine (traceForm_nondegenerate (ZMod 3) F).1 a fun x => ?_
    rw [Algebra.traceForm_apply]; exact ha x
  -- `ℓ ∘ Frob = Tr(d ·)` where `d³ = c`
  have hpdvd : 3 ∣ Fintype.card F :=
    (CharP.cast_eq_zero_iff F 3 (Fintype.card F)).mp (Nat.cast_card_eq_zero F)
  set d : F := c ^ (Fintype.card F / 3) with hd
  have hdp : d ^ 3 = c := by
    rw [hd, ← pow_mul, Nat.div_mul_cancel hpdvd, FiniteField.pow_card]
  have hfrob : ∀ x : F, ℓ (x ^ 3) = Algebra.trace (ZMod 3) F (d * x) := by
    intro x
    rw [hc, ← trace_pow_char (d * x), mul_pow, hdp]
  -- Frobenius-stability makes `ℓ ∘ Frob` a scalar multiple of `ℓ`
  obtain ⟨v, hv⟩ : ∃ v : F, ℓ v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : F, ℓ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hℓ (LinearMap.ext hcon)
    exact ⟨(ℓ w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  set μ : ZMod 3 := ℓ (v ^ 3) with hμ
  have hscal : ∀ x : F, ℓ (x ^ 3) = μ * ℓ x := by
    intro x
    have hker : ℓ (x - ℓ x • v) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, hv, mul_one, sub_self]
    have hz := hstab _ hker
    have hexp : (x - ℓ x • v) ^ 3 = x ^ 3 - (ℓ x) • v ^ 3 := by
      have h := (frobLin (p := 3) (F := F)).map_sub x ((ℓ x) • v)
      rw [map_smul] at h
      simpa only [frobLin_apply] using h
    rw [hexp, map_sub, map_smul, smul_eq_mul, ← hμ, sub_eq_zero] at hz
    rw [hz, mul_comm]
  -- duality turns that into `d = μ • c`, hence `c = μ • c³`
  have hdc : d = μ • c := by
    refine sub_eq_zero.mp (hnd _ fun x => ?_)
    have h1 : Algebra.trace (ZMod 3) F (d * x) = μ * ℓ x := by rw [← hfrob x, hscal x]
    have h2 : Algebra.trace (ZMod 3) F ((μ • c) * x) = μ * ℓ x := by
      rw [Algebra.smul_def, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, hc]
    rw [sub_mul, map_sub, h1, h2, sub_self]
  have hcmu : c = algebraMap (ZMod 3) F μ * c ^ 3 := by
    have h := congrArg (fun z : F => z ^ 3) hdc
    simp only [hdp, Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card] at h
    exact h
  -- `-1` is not a square, which kills the case `μ = -1`
  have hns : ¬ IsSquare (-1 : F) := by
    refine OddOrder.Paley.not_isSquare_neg_one ?_ h4
    rw [ringChar.eq F 3]
    decide
  have hc1 : c = 1 ∨ c = -1 := by
    rcases zmod3_trichotomy μ with h0 | h1 | h2
    · rw [h0, map_zero, zero_mul] at hcmu
      exact absurd hcmu hc0
    · rw [h1, map_one, one_mul] at hcmu
      have hfac : c * ((c - 1) * (c + 1)) = 0 := by linear_combination -hcmu
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hc0
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · exfalso
      have h2F : algebraMap (ZMod 3) F 2 = -1 := by
        rw [zmod3_two_eq_neg_one, map_neg, map_one]
      rw [h2, h2F] at hcmu
      have hfac : c * (1 + c ^ 2) = 0 := by linear_combination hcmu
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hc0
      · exact hns ⟨c, by linear_combination -h⟩
  ext x
  simp only [LinearMap.mem_ker, hc x]
  rcases hc1 with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, map_neg, neg_eq_zero]

/-- **Subspace form.**  A Frobenius-stable `𝔽₃`-hyperplane (the kernel of a non-zero functional)
of a finite field of characteristic three with `|F| ≡ 3 (mod 4)` equals `ker Tr`. -/
theorem frobeniusStableHyperplane_unique [Fintype F] (hp : p = 3)
    (h4 : Fintype.card F % 4 = 3) {W : Submodule (ZMod p) F}
    (hW : ∃ ℓ : F →ₗ[ZMod p] ZMod p, ℓ ≠ 0 ∧ W = LinearMap.ker ℓ)
    (hstab : ∀ x ∈ W, x ^ p ∈ W) :
    W = LinearMap.ker (Algebra.trace (ZMod p) F) := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hW
  exact ker_eq_ker_trace_of_frobenius_stable hp h4 ℓ hℓ fun x hx => hstab x hx

end Uniqueness

end OddOrder.FrobeniusStable
