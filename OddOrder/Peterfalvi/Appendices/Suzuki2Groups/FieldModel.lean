/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Pi
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
* `FieldModel ε` — the ring `F[X]/(X² + εX + 1)` (an `AdjoinRoot`; a field under
  anisotropy, `FieldModel.isField`);
* `FieldModel.equivProd` — the `F`-linear identification
  `F × F ≃ₗ[F] FieldModel ε`, `(a, b) ↦ a + bα`;
* `FieldModel.conj` — the conjugation automorphism `α ↦ ε + α`, an involution
  (`FieldModel.conj_conj`), nontrivial when `ε ≠ 0` (`FieldModel.conj_ne_refl`);
* `FieldModel.mul_conj` — **Proposition 1**: `x · x̄ = q(x)`;
* `FieldModel.exists_mul_conj_eq` / `typeBQuadraticMap_surjective` — over a
  finite `F` the norm (equivalently the square map `q`) is surjective, since
  in characteristic `2` already the scalars `a·ā = a²` exhaust `F`.
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

/-- Under anisotropy the model is a field (the defining polynomial is
irreducible). -/
theorem isField (hq : (typeBQuadraticMap (1 : RingAut F) ε).Anisotropic) :
    IsField (FieldModel ε) := by
  haveI : Fact (Irreducible (fieldModelPoly ε)) :=
    ⟨fieldModelPoly_irreducible ε hq⟩
  exact Field.toIsField (FieldModel ε)

/-! ### The conjugation automorphism `α ↦ ε + α` -/

/-- The conjugation `α ↦ ε + α` as an `F`-algebra endomorphism. -/
def conjAlgHom : FieldModel ε →ₐ[F] FieldModel ε :=
  AdjoinRoot.liftAlgHom (fieldModelPoly ε) (Algebra.ofId F (FieldModel ε))
    (algebraMap F (FieldModel ε) ε + alpha ε)
    (by simpa [Polynomial.aeval_def] using aeval_conj_root ε)

@[simp]
theorem conjAlgHom_alpha :
    conjAlgHom ε (alpha ε) = algebraMap F (FieldModel ε) ε + alpha ε :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Conjugation is an involution on the algebra-endomorphism level. -/
theorem conjAlgHom_comp_conjAlgHom :
    (conjAlgHom ε).comp (conjAlgHom ε) = AlgHom.id F (FieldModel ε) := by
  apply AdjoinRoot.algHom_ext
  change conjAlgHom ε (conjAlgHom ε (alpha ε)) = alpha ε
  rw [conjAlgHom_alpha, map_add, (conjAlgHom ε).commutes, conjAlgHom_alpha,
    ← add_assoc, add_self, zero_add]

/-- **The conjugation automorphism** of the field model (Proposition 1):
`α ↦ ε + α`, an `F`-algebra automorphism. -/
def conj : FieldModel ε ≃ₐ[F] FieldModel ε :=
  AlgEquiv.ofAlgHom (conjAlgHom ε) (conjAlgHom ε)
    (conjAlgHom_comp_conjAlgHom ε) (conjAlgHom_comp_conjAlgHom ε)

@[simp]
theorem conj_alpha :
    conj ε (alpha ε) = algebraMap F (FieldModel ε) ε + alpha ε :=
  conjAlgHom_alpha ε

/-- Conjugation is an involution: `conj` has order dividing `2`. -/
@[simp]
theorem conj_conj (x : FieldModel ε) : conj ε (conj ε x) = x :=
  AlgHom.congr_fun (conjAlgHom_comp_conjAlgHom ε) x

omit [CharP F 2] in
/-- The scalars embed injectively into the model (the defining polynomial has
positive degree). -/
theorem algebraMap_injective :
    Function.Injective (algebraMap F (FieldModel ε)) := by
  have hdeg : (fieldModelPoly ε).degree ≠ 0 := by
    have h2 : 0 < (fieldModelPoly ε).natDegree := by
      rw [fieldModelPoly_natDegree]; norm_num
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp h2)
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.coe_injective hdeg

/-- Conjugation is nontrivial when `ε ≠ 0`: together with `conj_conj` it has
exact order `2`. -/
theorem conj_ne_refl (hε : ε ≠ 0) :
    conj ε ≠ AlgEquiv.refl := by
  intro h
  have h1 : conj ε (alpha ε) = alpha ε := by rw [h]; rfl
  rw [conj_alpha] at h1
  have h2 : algebraMap F (FieldModel ε) ε = 0 := by linear_combination h1
  exact hε (algebraMap_injective ε (h2.trans (map_zero _).symm))

/-! ### The `F`-linear identification `F × F ≃ F[α]` -/

/-- The power basis `(1, α)` of the model, reindexed to `Fin 2`. -/
def powerBasisFin : Module.Basis (Fin 2) F (FieldModel ε) :=
  (AdjoinRoot.powerBasis' (fieldModelPoly_monic ε)).basis.reindex
    (finCongr (fieldModelPoly_natDegree ε))

omit [CharP F 2] in
theorem powerBasisFin_apply (i : Fin 2) :
    powerBasisFin ε i = alpha ε ^ (i : ℕ) := by
  simp only [powerBasisFin, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen, finCongr_symm,
    finCongr_apply, Fin.val_cast]
  rfl

/-- **The `F`-linear identification** of Proposition 1:
`(a, b) ↦ a + bα` is an `F`-linear equivalence `F × F ≃ F[α]`. -/
def equivProd : (F × F) ≃ₗ[F] FieldModel ε :=
  (LinearEquiv.finTwoArrow F F).symm.trans (powerBasisFin ε).equivFun.symm

omit [CharP F 2] in
theorem equivProd_apply (a b : F) :
    equivProd ε (a, b) =
      algebraMap F (FieldModel ε) a +
        algebraMap F (FieldModel ε) b * alpha ε := by
  simp only [equivProd, LinearEquiv.trans_apply,
    Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, powerBasisFin_apply,
    Algebra.smul_def]
  norm_num [LinearEquiv.finTwoArrow]

/-! ### Proposition 1: the quadratic map is the norm -/

/-- **Peterfalvi Appendix III, Proposition 1** (p. 142): under the
identification `(a, b) ↦ a + bα`, the type-B quadratic map of `B(n, 1, ε)`
becomes the norm of the quadratic extension: `q(x) = x·x̄`. -/
theorem mul_conj (a b : F) :
    equivProd ε (a, b) * conj ε (equivProd ε (a, b)) =
      algebraMap F (FieldModel ε)
        (typeBQuadraticMap (1 : RingAut F) ε (a, b)) := by
  rw [equivProd_apply]
  have hconj :
      conj ε (algebraMap F (FieldModel ε) a +
          algebraMap F (FieldModel ε) b * alpha ε) =
        algebraMap F (FieldModel ε) a +
          algebraMap F (FieldModel ε) b *
            (algebraMap F (FieldModel ε) ε + alpha ε) := by
    rw [map_add, map_mul, conj_alpha, (conj ε).commutes, (conj ε).commutes]
  rw [hconj, typeBQuadraticMap_apply]
  simp only [RingAut.one_apply, map_add, map_mul]
  linear_combination
    (algebraMap F (FieldModel ε) b) ^ 2 * alpha_sq ε +
      add_self ε
        (algebraMap F (FieldModel ε) a * algebraMap F (FieldModel ε) b *
            alpha ε +
          (algebraMap F (FieldModel ε) b) ^ 2 *
            algebraMap F (FieldModel ε) ε * alpha ε)

/-! ### Fixed points of the conjugation -/

/-- Conjugation in coordinates: `κ(a + bα) = (a + bε) + bα`. -/
theorem conj_equivProd (a b : F) :
    conj ε (equivProd ε (a, b)) = equivProd ε (a + b * ε, b) := by
  rw [equivProd_apply, equivProd_apply, map_add, map_mul, conj_alpha,
    (conj ε).commutes, (conj ε).commutes, map_add, map_mul]
  ring

/-- **The fixed points of the conjugation are exactly the scalars** (for
`ε ≠ 0`): in coordinates `κ(a + bα) = (a + bε) + bα`, so fixedness forces
`b = 0`. -/
theorem conj_eq_self_iff (hε : ε ≠ 0) (x : FieldModel ε) :
    conj ε x = x ↔ x ∈ (algebraMap F (FieldModel ε)).range := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (equivProd ε).surjective x
  constructor
  · intro h
    rw [conj_equivProd] at h
    have hab := (equivProd ε).injective h
    have hb : b * ε = 0 := by
      have h2 := congrArg Prod.fst hab
      simp only at h2
      linear_combination h2
    have hb0 : b = 0 := by
      rcases mul_eq_zero.mp hb with h' | h'
      · exact h'
      · exact absurd h' hε
    refine ⟨a, ?_⟩
    rw [hb0, equivProd_apply, map_zero, zero_mul, add_zero]
  · rintro ⟨c, hc⟩
    rw [← hc]
    exact (conj ε).commutes c

/-! ### Surjectivity of the norm (step (iv) of Proposition 2)

Over a finite `F` of characteristic `2` no counting is needed: squaring is
surjective on `F` (Frobenius), the conjugation fixes scalars, and so already
the scalar `a` with `a² = c` has norm `a·ā = a² = c`. -/

section NormSurjectivity

variable [Finite F]

/-- **Norm surjectivity** (toward Proposition 2, p. 142): over a finite `F`
of characteristic `2` every scalar of the field model is a norm `x·x̄`. -/
theorem exists_mul_conj_eq (c : F) :
    ∃ x : FieldModel ε, x * conj ε x = algebraMap F (FieldModel ε) c := by
  obtain ⟨a, ha⟩ := (frobeniusEquiv F 2).surjective c
  have ha2 : a ^ 2 = c := ha
  refine ⟨algebraMap F (FieldModel ε) a, ?_⟩
  rw [(conj ε).commutes, ← map_mul, ← pow_two, ha2]

end NormSurjectivity

end FieldModel

section NormSurjectivity

variable [Finite F]

/-- **Surjectivity of the type-B square map** `q(a, b) = a² + εab + b²` of
`B(n, 1, ε)` over a finite field of characteristic `2` (step (iv) of
Proposition 2): already the first axis realizes every value, since
`q(a, 0) = a²` and squaring (Frobenius) is surjective. -/
theorem typeBQuadraticMap_surjective :
    Function.Surjective (typeBQuadraticMap (1 : RingAut F) ε) := by
  intro c
  obtain ⟨a, ha⟩ := (frobeniusEquiv F 2).surjective c
  have ha2 : a ^ 2 = c := ha
  refine ⟨(a, 0), ?_⟩
  rw [typeBQuadraticMap_apply]
  simp only [RingAut.one_apply, mul_zero, add_zero]
  rw [← pow_two, ha2]

/-- The values of the type-B square map additively generate all of `W = F` —
the spanning hypothesis (`hspan`) of the kernel statements of Proposition 2
(`QuadraticExtension.ker_autQuotientHom`). -/
theorem closure_range_typeBQuadraticMap :
    AddSubgroup.closure
      (Set.range fun p : F × F => typeBQuadraticMap (1 : RingAut F) ε p) =
      ⊤ := by
  rw [Set.range_eq_univ.mpr (typeBQuadraticMap_surjective ε),
    AddSubgroup.closure_univ]

end NormSurjectivity

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
