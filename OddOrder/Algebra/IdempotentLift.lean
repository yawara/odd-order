/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.LinearCombination

/-!
# Lifting idempotents along a Henselian ideal

Block theory over a `p`-modular system needs the block idempotents of `Z(𝒪G)`, obtained by
lifting those of `Z(FG)` along `𝒪G ↠ FG`.  mathlib lifts idempotents only along a **nilpotent**
kernel (`RingTheory.Idempotents`), and `𝔪·𝒪G` is not nilpotent — for the valuation ring of `ℂ_p`
the value group is divisible, so even `𝔪² = 𝔪`, and no `𝔪`-adic argument can work.

What does work is Hensel's lemma in its root-lifting form, which is exactly what mathlib's
`HenselianRing` provides: an approximate idempotent `c` (that is, `c² - c ∈ I`) is an approximate
root of `X² - X`, and it is a *simple* one, because the derivative `2c - 1` is its own inverse
modulo `I`:

`(2c - 1)² = 4(c² - c) + 1 ≡ 1 (mod I)`.

So no completeness is needed, only that `I` be a Henselian ideal.  The lift is moreover unique:
the difference `d` of two idempotents satisfies `d³ = d`, and `d ∈ I ≤ J(R)` makes `d² - 1` a
unit, forcing `d = 0`.

## Main results

* `OddOrder.exists_isIdempotentElem_sub_mem` — existence of the lift
* `OddOrder.eq_of_isIdempotentElem_of_sub_mem` — uniqueness
* `OddOrder.existsUnique_isIdempotentElem_sub_mem`
-/

namespace OddOrder

open Polynomial

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The derivative of `X² - X` at an approximate idempotent is a unit modulo `I`: it is its own
inverse there, since `(2c - 1)² = 4(c² - c) + 1`. -/
theorem isUnit_two_mul_sub_one_of_sub_mem {c : R} (hc : c * c - c ∈ I) :
    IsUnit (Ideal.Quotient.mk I (2 * c - 1)) := by
  refine ⟨⟨Ideal.Quotient.mk I (2 * c - 1), Ideal.Quotient.mk I (2 * c - 1), ?_, ?_⟩, rfl⟩ <;>
  · rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have hexp : (2 * c - 1) * (2 * c - 1) - 1 = 4 * (c * c - c) := by ring
    rw [hexp]
    exact Ideal.mul_mem_left _ _ hc

variable [HenselianRing R I]

/-- **Idempotents lift along a Henselian ideal.**  If `c² ≡ c (mod I)` then there is an idempotent
`e` with `e ≡ c (mod I)`. -/
theorem exists_isIdempotentElem_sub_mem {c : R} (hc : c * c - c ∈ I) :
    ∃ e : R, IsIdempotentElem e ∧ e - c ∈ I := by
  have hmonic : (X ^ 2 - X : R[X]).Monic := by
    have h : ((X : R[X]) ^ 2 - X) = X ^ (1 + 1) - X := by norm_num
    rw [h]
    exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have heval : (X ^ 2 - X : R[X]).eval c ∈ I := by
    have h : (X ^ 2 - X : R[X]).eval c = c * c - c := by simp [pow_two]
    rw [h]; exact hc
  have hderiv : (X ^ 2 - X : R[X]).derivative.eval c = 2 * c - 1 := by
    simp [derivative_sub]
    try ring
  obtain ⟨e, hroot, hsub⟩ := HenselianRing.is_henselian (X ^ 2 - X : R[X]) hmonic c heval
    (by rw [hderiv]; exact isUnit_two_mul_sub_one_of_sub_mem I hc)
  refine ⟨e, ?_, hsub⟩
  have hz : e ^ 2 - e = 0 := by simpa [pow_two] using hroot
  have h2 : e ^ 2 = e := by rwa [sub_eq_zero] at hz
  change e * e = e
  rw [← pow_two]; exact h2

/-- **The lift is unique.**  Two idempotents congruent modulo an ideal inside the Jacobson radical
are equal: their difference `d` satisfies `d³ = d`, and `d ∈ I ≤ J(R)` makes `d² - 1` a unit.

Only `I ≤ J(R)` is used, not Henselianness — the same uniqueness therefore applies to the
non-complete coefficient rings of `AlgClosedIdempotentLift`. -/
theorem eq_of_isIdempotentElem_of_sub_mem (I) (hjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {e f : R}
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef : e - f ∈ I) : e = f := by
  have h1 : e * e = e := he
  have h2 : f * f = f := hf
  have hcube : (e - f) * ((e - f) * (e - f) - 1) = 0 := by
    linear_combination (e + 1 - 3 * f) * h1 + (3 * e - f - 1) * h2
  have hunit : IsUnit ((e - f) * (e - f) - 1) := by
    have hmem : (e - f) * (e - f) ∈ Ideal.jacobson (⊥ : Ideal R) :=
      Ideal.mul_mem_left _ _ (hjac hef)
    have hu := (Ideal.mem_jacobson_bot.mp hmem) (-1)
    have hrw : ((e - f) * (e - f) * (-1) + 1) = -((e - f) * (e - f) - 1) := by ring
    rw [hrw] at hu
    simpa using hu.neg
  have hzero : e - f = 0 := hunit.mul_right_cancel (by rw [hcube, zero_mul])
  exact sub_eq_zero.mp hzero

/-- **Idempotents lift uniquely along a Henselian ideal.** -/
theorem existsUnique_isIdempotentElem_sub_mem {c : R} (hc : c * c - c ∈ I) :
    ∃! e : R, IsIdempotentElem e ∧ e - c ∈ I := by
  obtain ⟨e, he, hec⟩ := exists_isIdempotentElem_sub_mem I hc
  refine ⟨e, ⟨he, hec⟩, fun f hfx => ?_⟩
  refine eq_of_isIdempotentElem_of_sub_mem I HenselianRing.jac hfx.1 he ?_
  have hrw : f - e = (f - c) - (e - c) := by ring
  rw [hrw]
  exact Ideal.sub_mem _ hfx.2 hec

end OddOrder
