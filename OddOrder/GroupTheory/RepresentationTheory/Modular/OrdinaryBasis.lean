/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality

/-!
# `Irr(G)` is a basis of the class functions

The character table is a square invertible matrix
(`characterMatrix_mul_characterMatrixInv`, `characterMatrixInv_mul_characterMatrix`), so a class
function of `G` is uniquely a `K`-combination of the ordinary irreducible characters.  This is the
characteristic-zero counterpart of `BrauerBasis.existsUnique_coeff_irreducibleBrauerCharacter`,
which does the same for `IBr(G)` on the `p`-regular classes.

It is what makes the **`B`-part** `θ_B = ∑_{χ ∈ Irr(B)} [θ,χ] χ` of Navarro (5.10)–(5.13) well
defined without any inner product: the coefficients are read off from the unique expansion, and
`Irr(B)` is cut out by `blockOfIrr`.

## Main results

* `OddOrder.RepresentationTheory.Modular.existsUnique_coeff_ordinaryCharacter`
* `OddOrder.RepresentationTheory.Modular.ordinaryCoeff` — the coefficients of the expansion
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupTheory

variable {G : Type*} [Group G]
variable {K : Type*} [Field K] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Fintype G] [Fintype (ConjClasses G)] [Fintype ι'] [Invertible (Nat.card G : K)]

omit [Invertible (Nat.card G : K)] in
-- The finiteness instances are what `classRep` is built from.
set_option linter.unusedFintypeInType false in
/-- Every element is conjugate to the representative of its own class. -/
theorem isConj_classRep (g : G) :
    IsConj g (classRep e ((equivConjClasses e).symm (ConjClasses.mk g))) := by
  refine ConjClasses.mk_eq_mk_iff_isConj.mp ?_
  rw [classRep, conjugacyClassRepresentative_mk_eq, Equiv.apply_symm_apply]

-- The finiteness instances are consumed by the character table in the proof.
set_option linter.unusedFintypeInType false in
/-- **`Irr(G)` is a basis of the class functions.**  A conjugacy-invariant `f : G → K` is uniquely
a `K`-combination of the ordinary irreducible characters. -/
theorem existsUnique_coeff_ordinaryCharacter (f : G → K)
    (hf : ∀ g h : G, IsConj g h → f g = f h) :
    ∃! c : ι' → K,
      ∀ g : G, ∑ i, c i * (wedderburnRepresentation e i).character g = f g := by
  classical
  set fv : ι' → K := fun j => f (classRep e j) with hfv
  -- the statement at the class representatives is a `vecMul` equation
  have hkey : ∀ c : ι' → K,
      (∀ g : G, ∑ i, c i * (wedderburnRepresentation e i).character g = f g)
        ↔ c ᵥ* characterMatrix e = fv := by
    intro c
    constructor
    · intro h
      funext j
      exact h (classRep e j)
    · intro h g
      have hc := isConj_classRep e g
      rw [Finset.sum_congr rfl fun i _ =>
          congrArg (c i * ·) (character_eq_of_isConj (wedderburnRepresentation e i) hc),
        hf g _ hc]
      exact congrFun h _
  refine ⟨fv ᵥ* characterMatrixInv e, (hkey _).mpr ?_, fun c hc => ?_⟩
  · rw [Matrix.vecMul_vecMul, characterMatrixInv_mul_characterMatrix, Matrix.vecMul_one]
  · rw [← (hkey c).mp hc, Matrix.vecMul_vecMul, characterMatrix_mul_characterMatrixInv,
      Matrix.vecMul_one]

-- Same finiteness instances as above.
set_option linter.unusedFintypeInType false in
/-- **The coefficients of a class function in the basis `Irr(G)`.**  For `f` the character of a
representation these are the multiplicities `[f, χ_i]`. -/
noncomputable def ordinaryCoeff (f : G → K) (hf : ∀ g h : G, IsConj g h → f g = f h) : ι' → K :=
  (existsUnique_coeff_ordinaryCharacter e f hf).choose

-- Same finiteness instances as above.
set_option linter.unusedFintypeInType false in
/-- **The defining property**: `f = ∑_i [f, χ_i] χ_i`. -/
theorem sum_ordinaryCoeff (f : G → K) (hf : ∀ g h : G, IsConj g h → f g = f h) (g : G) :
    ∑ i, ordinaryCoeff e f hf i * (wedderburnRepresentation e i).character g = f g :=
  (existsUnique_coeff_ordinaryCharacter e f hf).choose_spec.1 g

-- Same finiteness instances as above.
set_option linter.unusedFintypeInType false in
/-- **Uniqueness**: any family with the defining property *is* the family of coefficients. -/
theorem eq_ordinaryCoeff (f : G → K) (hf : ∀ g h : G, IsConj g h → f g = f h) {c : ι' → K}
    (hc : ∀ g : G, ∑ i, c i * (wedderburnRepresentation e i).character g = f g) :
    c = ordinaryCoeff e f hf :=
  (existsUnique_coeff_ordinaryCharacter e f hf).choose_spec.2 c hc

end OddOrder.RepresentationTheory.Modular
