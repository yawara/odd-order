/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ComputeDegree
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types

/-!
# Peterfalvi Appendix III, Proposition 1: the field model of `B(n, 1, ε)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Proposition 1, p. 142.

Let `q : F × F → F` be the quadratic map of `B(n, 1, ε)` (that is,
`typeBQuadraticMap 1 ε : (a, b) ↦ a² + εab + b²`).  Anisotropy of `q` makes
`X² + εX + 1` irreducible over `F`; on the quadratic extension
`K = F[X]/(X² + εX + 1)` the conjugation `α ↦ ε + α` is the order-`2`
automorphism, and under the `F`-linear identification `(a, b) ↦ a + bα` the
quadratic map becomes the norm: `q(x) = x·x̄`.

Main declarations:

* `fieldModelPoly_irreducible` — `X² + εX + 1` is irreducible (from anisotropy);
* `FieldModel ε` — the field `F[X]/(X² + εX + 1)` (an `AdjoinRoot`);
* `fieldModelEquiv` — the `F`-linear identification `F × F ≃ₗ[F] FieldModel ε`
  (the compatibility of the field structure with the `F`-vector structure);
* `fieldModelConj` — the conjugation automorphism, of order `2`
  (`fieldModelConj_conj`, `fieldModelConj_ne_refl`);
* `fieldModel_mul_conj` — **Proposition 1**: `x · x̄ = q(x)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open Polynomial

noncomputable section

variable {F : Type*} [Field F] [CharP F 2] (ε : F)

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The defining polynomial `X² + εX + 1` of the field model. -/
def fieldModelPoly : F[X] := X ^ 2 + C ε * X + 1

omit [CharP F 2] in
theorem fieldModelPoly_monic : (fieldModelPoly ε).Monic := by
  unfold fieldModelPoly
  monicity!

omit [CharP F 2] in
theorem fieldModelPoly_natDegree : (fieldModelPoly ε).natDegree = 2 := by
  unfold fieldModelPoly
  compute_degree!

/-- Evaluation of the defining polynomial is the quadratic map at `(t, 1)`. -/
theorem fieldModelPoly_eval (t : F) :
    (fieldModelPoly ε).eval t = typeBQuadraticMap (1 : RingAut F) ε (t, 1) := by
  simp only [fieldModelPoly, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_one, typeBQuadraticMap_apply, RingAut.one_apply]
  ring

/-- **Irreducibility from anisotropy** (the first step of Proposition 1): if
the type-B quadratic map is anisotropic, `X² + εX + 1` has no root, hence is
irreducible (degree `2`). -/
theorem fieldModelPoly_irreducible
    (hq : (typeBQuadraticMap (1 : RingAut F) ε).Anisotropic) :
    Irreducible (fieldModelPoly ε) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [fieldModelPoly_natDegree]
    decide
  · intro t ht
    have h0 : typeBQuadraticMap (1 : RingAut F) ε (t, 1) = 0 := by
      rw [← fieldModelPoly_eval]
      exact ht
    have := hq _ h0
    exact one_ne_zero (congrArg Prod.snd this)

/-- `ε ≠ 0` (evaluate anisotropy at `(1, 1)`; characteristic `2`). -/
theorem epsilon_ne_zero_of_anisotropic
    (hq : (typeBQuadraticMap (1 : RingAut F) ε).Anisotropic) : ε ≠ 0 := by
  intro h0
  have h1 : typeBQuadraticMap (1 : RingAut F) ε (1, 1) = 0 := by
    rw [typeBQuadraticMap_apply, h0]
    simp only [RingAut.one_apply, mul_one, add_zero]
    exact CharTwo.add_self_eq_zero 1
  exact one_ne_zero (congrArg Prod.fst (hq _ h1))

/-- **The field model** `K = F[X]/(X² + εX + 1)` of Proposition 1. -/
abbrev FieldModel := AdjoinRoot (fieldModelPoly ε)

namespace FieldModel

/-- The distinguished root `α` (with `α² + εα + 1 = 0`). -/
def alpha : FieldModel ε := AdjoinRoot.root (fieldModelPoly ε)

/-- Characteristic `2` in the model, without needing nontriviality: `x + x`
is the `F`-scalar `2 = 0` acting on `x`. -/
theorem add_self (x : FieldModel ε) : x + x = 0 := by
  rw [← two_smul F x, show (2 : F) = 0 from CharTwo.two_eq_zero, zero_smul]

/-- The defining relation `α² = εα + 1` (characteristic `2`). -/
theorem alpha_sq :
    alpha ε ^ 2 = algebraMap F (FieldModel ε) ε * alpha ε + 1 := by
  have h : (Polynomial.aeval (alpha ε)) (fieldModelPoly ε) = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root _
  simp only [fieldModelPoly, map_add, map_mul, map_pow, aeval_X, aeval_C,
    map_one] at h
  have h2 : alpha ε ^ 2 +
      (algebraMap F (FieldModel ε) ε * alpha ε + 1) = 0 := by
    rw [← add_assoc]
    exact h
  calc alpha ε ^ 2
      = alpha ε ^ 2 +
          ((algebraMap F (FieldModel ε) ε * alpha ε + 1) +
            (algebraMap F (FieldModel ε) ε * alpha ε + 1)) := by
        rw [add_self, add_zero]
    _ = (alpha ε ^ 2 + (algebraMap F (FieldModel ε) ε * alpha ε + 1)) +
          (algebraMap F (FieldModel ε) ε * alpha ε + 1) := by ring
    _ = algebraMap F (FieldModel ε) ε * alpha ε + 1 := by
        rw [h2, zero_add]

/-- The conjugate root: `ε + α` also satisfies the defining polynomial
(characteristic `2`). -/
theorem aeval_conj_root :
    (Polynomial.aeval (algebraMap F (FieldModel ε) ε + alpha ε))
      (fieldModelPoly ε) = 0 := by
  simp only [fieldModelPoly, map_add, map_mul, map_pow, aeval_X, aeval_C,
    map_one]
  have hsq := alpha_sq ε
  have hchar : ∀ x : FieldModel ε, x + x = 0 := add_self ε
  set e := algebraMap F (FieldModel ε) ε with he
  set a := alpha ε with ha
  -- (e + a)² + e(e + a) + 1 = e² + a² + e² + ea + 1 = a² + ea + 1 = 0
  have hexp : (e + a) ^ 2 = e ^ 2 + a ^ 2 := by
    linear_combination hchar (e * a)
  rw [hexp]
  have hgoal : e ^ 2 + a ^ 2 + e * (e + a) + 1 =
      (a ^ 2 + e * a + 1) + (e ^ 2 + e ^ 2) := by ring
  rw [hgoal, hchar (e ^ 2), add_zero]
  have h2 : a ^ 2 + (e * a + 1) = 0 := by
    rw [hsq]
    exact hchar _
  rw [← add_assoc] at h2
  exact h2

end FieldModel

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
