/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace

/-!
# The trace of left multiplication

Two computations of `tr(x ↦ a · x)`, on a group algebra and on a product of matrix algebras.
Comparing them across a Wedderburn splitting `K[G] ≃ ∏_i M_{m_i}(K)` reads off the dimension of
the part of `K[G]` cut out by a central idempotent, which is how Navarro (6.13) gets the Cartan
matrix of the principal block.

* on `K[G]` with the group-element basis the matrix of `x ↦ a · x` has `(g,h)` entry `a(g h⁻¹)`,
  so every diagonal entry is `a(1)` and the trace is `|G| · a(1)`;
* on `∏_i M_{m_i}(K)` with the matrix-unit basis the `(i,a,b)` diagonal entry of `x ↦ v · x` is
  `(v_i)_{aa}`, so the trace is `∑_i m_i · tr(v_i)`.

## Main results

* `OddOrder.Algebra.trace_mulLeft_monoidAlgebra` — `tr(L_a) = |G| · a(1)`
* `OddOrder.Algebra.trace_mulLeft_pi_matrix` — `tr(L_v) = ∑_i m_i · tr(v_i)`
-/

namespace OddOrder.Algebra

open MonoidAlgebra

/-- **The trace of left multiplication on a group algebra** is `|G|` times the coefficient at `1`.
-/
theorem trace_mulLeft_monoidAlgebra {K G : Type*} [CommRing K] [Group G] [Fintype G]
    (a : MonoidAlgebra K G) :
    LinearMap.trace K (MonoidAlgebra K G) (LinearMap.mulLeft K a)
      = (Fintype.card G : K) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K), Matrix.trace]
  have hdiag : ∀ g : G, LinearMap.toMatrix (MonoidAlgebra.basis G K) (MonoidAlgebra.basis G K)
      (LinearMap.mulLeft K a) g g = a.coeff 1 := by
    intro g
    rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, LinearMap.mulLeft_apply]
    have hcoeff : (a * single g (1 : K)).coeff g = a.coeff 1 * 1 :=
      coeff_mul_single_eq_coeff_mul 1 fun m' _ => by
        constructor
        · intro h; simpa using h
        · rintro rfl; rw [one_mul]
    simp [MonoidAlgebra.basis, hcoeff]
  simp only [Matrix.diag_apply, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The trace of left multiplication on a product of matrix algebras.**  In the matrix-unit
basis the diagonal entry at `(i, a, c)` is `(v_i)_{aa}`, and `c` ranges over `m i`. -/
theorem trace_mulLeft_pi_matrix {K ι : Type*} [CommRing K] [Fintype ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] (v : ∀ i, Matrix (m i) (m i) K) :
    LinearMap.trace K (∀ i, Matrix (m i) (m i) K) (LinearMap.mulLeft K v)
      = ∑ i, (Fintype.card (m i) : K) * Matrix.trace (v i) := by
  classical
  set b : Module.Basis (Σ i, m i × m i) K (∀ i, Matrix (m i) (m i) K) :=
    Pi.basis fun i => Matrix.stdBasis K (m i) (m i) with hb
  rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
  have hdiag : ∀ x : Σ i, m i × m i,
      LinearMap.toMatrix b b (LinearMap.mulLeft K v) x x = v x.1 x.2.1 x.2.1 := by
    rintro ⟨i, a, c⟩
    rw [LinearMap.toMatrix_apply]
    have hbx : b ⟨i, (a, c)⟩ = Pi.single i (Matrix.single a c (1 : K)) := by
      rw [hb, Pi.basis_apply, Matrix.stdBasis_eq_single]
    rw [hbx, LinearMap.mulLeft_apply, hb, Pi.basis_repr]
    have hmulapp : (v * (Pi.single i (Matrix.single a c (1 : K)) :
        ∀ j, Matrix (m j) (m j) K)) i = v i * Matrix.single a c (1 : K) := by
      rw [Pi.mul_apply, Pi.single_eq_same]
    rw [hmulapp]
    have hrepr : (Matrix.stdBasis K (m i) (m i)).repr (v i * Matrix.single a c (1 : K)) (a, c)
        = (v i * Matrix.single a c (1 : K)) a c := by
      simp [Matrix.stdBasis, Pi.basis_repr]
    rw [hrepr]
    simp [Matrix.mul_apply, Matrix.single_apply]
  simp only [Matrix.diag_apply, hdiag]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ∑ _y : m i, v i a a = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.diag_apply]

end OddOrder.Algebra
