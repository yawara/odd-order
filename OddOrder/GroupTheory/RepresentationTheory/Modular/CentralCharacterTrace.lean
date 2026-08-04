/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Character
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrreducibles

/-!
# The central character of a class sum, read off the character

For a Wedderburn splitting `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)` the class sum `K̂` is central, so it
acts on the `i`-th block by a scalar `ω_i(K̂)`.  Taking traces of `e(K̂)_i = ω_i(K̂) · 1` in the two
obvious ways gives the classical

`ω_i(K̂) · χ_i(1) = ∑_{g ∈ K} χ_i(g)  ( = |K| · χ_i(x_K) )`.

This is the only new ingredient needed to run Burnside's class-multiplication formula in the
`K`-Wedderburn setting: combined with the second orthogonality relation it inverts
`ω_i(K̂) ω_i(L̂) = ∑_M a_{KLM} ω_i(M̂)` into a formula for the structure constants `a_{KLM}`, which
is what Navarro (4.19) — and through it Külshammer's formula (6.14) and the third main theorem —
runs on.

## Main results

* `OddOrder.RepresentationTheory.Modular.trace_apply_single` — `χ_i(g)` is the matrix trace
* `OddOrder.RepresentationTheory.Modular.centralScalar_classSum_mul_character_one`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupTheory.CenterClassSum

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

omit [Fintype G] [DecidableEq (ConjClasses G)] [∀ i, Nonempty (m i)] in
/-- The character value `χ_i(g)` is the trace of the matrix `e(g)_i`. -/
theorem trace_apply_single (g : G) :
    (wedderburnRepresentation e i).character g = Matrix.trace (e (MonoidAlgebra.single g 1) i) := by
  classical
  rw [Representation.character]
  have hmap : (wedderburnRepresentation e i) g
      = Matrix.toLin (Pi.basisFun K (m i)) (Pi.basisFun K (m i)) (e (MonoidAlgebra.single g 1) i) :=
    LinearMap.ext fun v => by
      rw [wedderburnRepresentation_apply, Matrix.toLin_apply]
      funext a
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hmap, Matrix.trace_toLin_eq]

/-- **`ω_i(K̂) · χ_i(1) = ∑_{g ∈ K} χ_i(g)`.**  Both sides are the trace of `e(K̂)_i`: on the left
because `K̂` is central and so acts by a scalar, on the right by linearity. -/
theorem centralScalar_classSum_mul_character_one (C : ConjClasses G) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
        * (wedderburnRepresentation e i).character 1
      = ∑ g : G,
        if ConjClasses.mk g = C then (wedderburnRepresentation e i).character g else 0 := by
  classical
  have hscal : e (classSum (k := K) C) i
      = Matrix.scalar (m i) (MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)) :=
    MatrixModule.scalar_centralScalar e.toAlgHom.toRingHom i e.surjective
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp (classSum_mem_center C)))
  have hleft : Matrix.trace (e (classSum (k := K) C) i)
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
        * (wedderburnRepresentation e i).character 1 := by
    rw [hscal, Representation.char_one, Module.finrank_fintype_fun_eq_card, Matrix.trace,
      Matrix.scalar]
    simp [Matrix.diag_apply, Finset.card_univ, mul_comm]
  have hright : Matrix.trace (e (classSum (k := K) C) i)
      = ∑ g : G,
        if ConjClasses.mk g = C then (wedderburnRepresentation e i).character g else 0 := by
    rw [classSum]
    have hlin : e (∑ g : G, if ConjClasses.mk g = C then MonoidAlgebra.of K G g else 0) i
        = ∑ g : G, if ConjClasses.mk g = C then e (MonoidAlgebra.single g (1 : K)) i else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply, apply_ite (fun a : ∀ j, Matrix (m j) (m j) K => a i),
        apply_ite (fun a : MonoidAlgebra K G => e a), map_zero, Pi.zero_apply,
        MonoidAlgebra.of_apply]
    rw [hlin, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [apply_ite Matrix.trace, Matrix.trace_zero, trace_apply_single]
  rw [← hleft, hright]

end OddOrder.RepresentationTheory.Modular
