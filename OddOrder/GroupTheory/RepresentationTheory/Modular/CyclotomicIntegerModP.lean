/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerInductionDescent

/-!
# The residue ring `ℤ[ω] / p` and its characteristic

Gorenstein Lemma 7.5 (issue 9508, 段 D) works "modulo `pR`" for `R = ℤ[ω]`, and its last step is
the observation

`ℤ ∩ pR = pℤ`,

which turns a congruence between rational integers in `R` into an honest congruence in `ℤ`.  The
same observation says that the residue ring `R / pR` has characteristic exactly `p`, so it carries
a Frobenius: that is what lets the argument raise a sum to the `p^s`-th power term by term.

Both facts come from the `ℤ`-basis `1, ω, …, ω^{n-1}` of `ℤ[ω]` established in
`BrauerInductionDescent`.

## Main definitions

* `OddOrder.adjoinPrimeIdeal` — the ideal `p · ℤ[ω]`

## Main results

* `OddOrder.intCast_dvd_of_mem_adjoinPrimeIdeal` — `ℤ ∩ pR = pℤ`
* `OddOrder.charP_quotient_adjoinPrimeIdeal` — `R / pR` has characteristic `p`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.5 (`references/gorenstein/pages/`).
-/

namespace OddOrder

open OddOrder.RepresentationTheory

variable {K : Type*} [Field K] [CharZero K] {ω : K} {p : ℕ}

variable (ω p) in
/-- The ideal `p · ℤ[ω]` of the ring of cyclotomic integers attached to `ω`. -/
def adjoinPrimeIdeal : Ideal ↥(Algebra.adjoin ℤ ({ω} : Set K)) :=
  Ideal.span {(p : ↥(Algebra.adjoin ℤ ({ω} : Set K)))}

/-- **`ℤ ∩ pℤ[ω] = pℤ`.**  Expand the cofactor in the power basis `1, ω, …, ω^{n-1}`: the
`ω^0`-coordinate of `p · a` must be the integer, and the others must vanish. -/
theorem intCast_dvd_of_mem_adjoinPrimeIdeal (hω : IsIntegral ℤ ω) {k : ℤ}
    (h : (k : ↥(Algebra.adjoin ℤ ({ω} : Set K))) ∈ adjoinPrimeIdeal ω p) : (p : ℤ) ∣ k := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  -- push the identity `a * p = k` into `K`
  have haK : (a : K) * (p : K) = (k : K) := by
    have := congrArg (Subalgebra.val (Algebra.adjoin ℤ ({ω} : Set K))) ha
    simpa using this
  obtain ⟨c, hc⟩ := exists_intCast_sum_pow hω a.2
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (minpoly ℤ ω).natDegree, (j₀ : ℕ) = 0 :=
    ⟨⟨0, natDegree_minpoly_int_pos hω⟩, rfl⟩
  refine ⟨c j₀, ?_⟩
  have hzero : ∀ j : Fin (minpoly ℤ ω).natDegree,
      (if j = j₀ then (p : ℤ) * c j - k else (p : ℤ) * c j) = 0 := by
    refine fun j => eq_zero_of_sum_intCast_pow_eq_zero
      (c := fun j => if j = j₀ then (p : ℤ) * c j - k else (p : ℤ) * c j) hω ?_ j
    have hexp : ∀ j : Fin (minpoly ℤ ω).natDegree,
        ((if j = j₀ then (p : ℤ) * c j - k else (p : ℤ) * c j : ℤ) : K) * ω ^ (j : ℕ)
          = ((p : ℤ) : K) * ((c j : ℤ) : K) * ω ^ (j : ℕ)
            - (if j = j₀ then ((k : ℤ) : K) else 0) := by
      intro j
      by_cases hjj : j = j₀
      · subst hjj
        rw [if_pos rfl, if_pos rfl, Int.cast_sub, Int.cast_mul, sub_mul, hj₀]
        norm_num
      · rw [if_neg hjj, if_neg hjj, Int.cast_mul, sub_zero]
    have hsum : ∑ j : Fin (minpoly ℤ ω).natDegree,
        ((p : ℤ) : K) * ((c j : ℤ) : K) * ω ^ (j : ℕ) = (k : K) := by
      rw [← haK, hc, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hexp j, Finset.sum_sub_distrib, hsum]
    simp
  have h0 := hzero j₀
  rw [if_pos rfl, sub_eq_zero] at h0
  exact h0.symm

/-- **The residue ring `ℤ[ω] / p` has characteristic `p`.**  Hence (for `p` prime) it carries a
Frobenius endomorphism, which is what Lemma 7.5 raises its sums by.  Primality is not needed for
the characteristic itself — only the `ℤ`-basis of `ℤ[ω]` is. -/
theorem charP_quotient_adjoinPrimeIdeal (hω : IsIntegral ℤ ω) :
    CharP (↥(Algebra.adjoin ℤ ({ω} : Set K)) ⧸ adjoinPrimeIdeal ω p) p := by
  refine ⟨fun k => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk (adjoinPrimeIdeal ω p)) k,
    Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hmem
    have : (p : ℤ) ∣ (k : ℤ) := by
      refine intCast_dvd_of_mem_adjoinPrimeIdeal (ω := ω) (p := p) hω ?_
      simpa using hmem
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    rw [Nat.cast_mul, adjoinPrimeIdeal]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

omit [CharZero K] in
/-- `p` itself is zero in the residue ring. -/
theorem natCast_prime_mem_adjoinPrimeIdeal :
    (p : ↥(Algebra.adjoin ℤ ({ω} : Set K))) ∈ adjoinPrimeIdeal ω p :=
  Ideal.subset_span rfl

end OddOrder
