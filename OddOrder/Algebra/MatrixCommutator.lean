/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import OddOrder.Algebra.CommutatorSpan

/-!
# The commutator span of a matrix algebra is the trace-zero subspace

Brauer's count of the irreducible modular representations compares the `p`-radical
`T' = {x : ∃ m, x ^ (p ^ m) ∈ T}` of `T = [A, A]` with `J(A) + T`, and the comparison is made in
the semisimple quotient, which for a split algebra is a product of matrix algebras.  The two
facts needed about a single matrix factor are collected here:

* `[M_n(R), M_n(R)]` is exactly the kernel of the trace, so `M_n(R) ⧸ [M_n(R), M_n(R)] ≅ R`;
* in characteristic `p`, `tr (M ^ p) = (tr M) ^ p`.

The second is usually proved through the eigenvalues over an algebraic closure.  Here it drops
out of the first: modulo commutators, `M` *is* the scalar `tr M` (in one diagonal slot), and the
`p`-power map on `A ⧸ [A, A]` is semilinear over the Frobenius of the base
(`OddOrder.pow_sub_pow_mem_of_sub_mem`).  No eigenvalues, no base change.

## Main results

* `OddOrder.sub_single_trace_mem_commutatorSpan`
* `OddOrder.mem_commutatorSpan_matrix_iff`
* `OddOrder.trace_pow_prime`
-/

namespace OddOrder

open Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **Off the diagonal a matrix unit is a commutator**: `E_{ij} = [E_{ii}, E_{ij}]`. -/
theorem single_mem_commutatorSpan {i j : n} (h : i ≠ j) (c : R) :
    single i j c ∈ commutatorSpan R (Matrix n n R) := by
  have hc : single i j c
      = single i i (1 : R) * single i j c - single i j c * single i i (1 : R) := by
    rw [single_mul_single_same, single_mul_single_of_ne _ _ _ _ h.symm, one_mul, sub_zero]
  rw [hc]
  exact commutator_mem_commutatorSpan _ _

/-- **A difference of two diagonal matrix units is a commutator**: `E_{ii} - E_{jj} =
[E_{ij}, E_{ji}]`.  (For `i = j` both sides are zero, so no case split is needed.) -/
theorem single_diag_sub_single_diag_mem_commutatorSpan (i j : n) (c : R) :
    single i i c - single j j c ∈ commutatorSpan R (Matrix n n R) := by
  have hc : single i i c - single j j c
      = single i j c * single j i (1 : R) - single j i (1 : R) * single i j c := by
    rw [single_mul_single_same, single_mul_single_same, mul_one, one_mul]
  rw [hc]
  exact commutator_mem_commutatorSpan _ _

/-- **Modulo commutators a matrix is its trace**, placed in a chosen diagonal slot. -/
theorem sub_single_trace_mem_commutatorSpan (i₀ : n) (M : Matrix n n R) :
    M - single i₀ i₀ M.trace ∈ commutatorSpan R (Matrix n n R) := by
  induction M using Matrix.induction_on' with
  | h_zero => simp
  | h_add x y hx hy =>
    have hsplit : x + y - single i₀ i₀ (x + y).trace
        = (x - single i₀ i₀ x.trace) + (y - single i₀ i₀ y.trace) := by
      rw [trace_add, single_add]
      abel
    rw [hsplit]
    exact Submodule.add_mem _ hx hy
  | h_std_basis i j x =>
    rcases eq_or_ne i j with rfl | h
    · rw [trace_single_eq_same]
      exact single_diag_sub_single_diag_mem_commutatorSpan i i₀ x
    · rw [trace_single_eq_of_ne _ _ _ h, single_zero, sub_zero]
      exact single_mem_commutatorSpan h x

/-- **The commutator span of a matrix algebra is exactly the trace-zero subspace.**  Hence
`M_n(R) ⧸ [M_n(R), M_n(R)]` is free of rank one, with the trace as coordinate. -/
theorem mem_commutatorSpan_matrix_iff [Nonempty n] {M : Matrix n n R} :
    M ∈ commutatorSpan R (Matrix n n R) ↔ M.trace = 0 := by
  constructor
  · intro hM
    induction hM using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      rw [trace_sub, trace_mul_comm, sub_self]
    | zero => rw [trace_zero]
    | add x y _ _ hx hy => rw [trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [trace_smul, hx, smul_zero]
  · intro hM
    inhabit n
    have h := sub_single_trace_mem_commutatorSpan (default : n) M
    rwa [hM, single_zero, sub_zero] at h

/-- Powers of a diagonal matrix unit stay diagonal matrix units. -/
theorem single_diag_pow (i : n) (c : R) : ∀ m : ℕ,
    (single i i c) ^ (m + 1) = single i i (c ^ (m + 1))
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, single_diag_pow i c m, single_mul_single_same, ← pow_succ]

/-- **In characteristic `p` the trace of a `p`-th power is the `p`-th power of the trace.**
Modulo commutators `M` is the scalar `tr M`, and the `p`-power map on `A ⧸ [A, A]` is semilinear
over the Frobenius of `R` — so no eigenvalues or base change are needed. -/
theorem trace_pow_prime [Nonempty n] {p : ℕ} (hp : p.Prime) (hchar : (p : R) = 0)
    (M : Matrix n n R) : (M ^ p).trace = M.trace ^ p := by
  inhabit n
  have hcharM : ((p : ℕ) : Matrix n n R) = 0 := by
    rw [← map_natCast (algebraMap R (Matrix n n R)) p, hchar, map_zero]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hpow := pow_sub_pow_mem_of_sub_mem (k := R) hp hcharM
    (sub_single_trace_mem_commutatorSpan (default : n) M)
  rw [single_diag_pow] at hpow
  have htr := mem_commutatorSpan_matrix_iff.mp hpow
  rwa [trace_sub, trace_single_eq_same, sub_eq_zero] at htr

end OddOrder
