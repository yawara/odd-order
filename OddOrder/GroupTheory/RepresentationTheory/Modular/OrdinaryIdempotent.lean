/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.GroupAlgebraConjugation
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralCharacterTrace
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryOrthogonality

/-!
# The primitive central idempotents of `K[G]`

For a Wedderburn splitting `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)` the idempotent `e⁻¹(Pi.single i 1)`
is the classical

`e_{χ_i} = (χ_i(1)/|G|) ∑_g χ_i(g⁻¹) g`.

Only two facts are needed to see this: the element on the right is central because its
coefficients are class functions, and its central-character value on the `j`-th block is
`δ_{ij}` — which is exactly the **first orthogonality relation**, read through
`ω_j(w) χ_j(1) = ∑_g w(g) χ_j(g)`.

The class-sum coefficients of these idempotents are what Navarro (4.19) regroups block by block,
so this is the entry point to the character side of Külshammer's formula.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.ordinaryIdempotent`

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_ordinaryIdempotent` — `ω_j(e_i) = δ_{ij}`
* `OddOrder.RepresentationTheory.Modular.apply_ordinaryIdempotent` — `e(e_i) = Pi.single i 1`
* `OddOrder.RepresentationTheory.Modular.sum_ordinaryIdempotent` — they sum to `1`
* `OddOrder.RepresentationTheory.Modular.eq_sum_centralScalar_smul_ordinaryIdempotent` — the
  spectral decomposition of `Z(K[G])`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

open scoped OddOrder.Conjugation

variable {K G : Type*} [Field K] [Group G] [Fintype G]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Invertible (Nat.card G : K)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

/-- **The primitive central idempotent** `e_{χ_i} = (χ_i(1)/|G|) ∑_g χ_i(g⁻¹) g`. -/
noncomputable def ordinaryIdempotent : MonoidAlgebra K G :=
  ∑ g : G, MonoidAlgebra.single g
    (⅟(Nat.card G : K) * (wedderburnRepresentation e i).character 1
      * (wedderburnRepresentation e i).character g⁻¹)

theorem coeff_ordinaryIdempotent (g : G) :
    (ordinaryIdempotent e i).coeff g
      = ⅟(Nat.card G : K) * (wedderburnRepresentation e i).character 1
        * (wedderburnRepresentation e i).character g⁻¹ := by
  classical
  rw [ordinaryIdempotent, MonoidAlgebra.coeff_finsetSum]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
    show (MonoidAlgebra.single x (⅟(Nat.card G : K)
          * (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character x⁻¹)).coeff g
        = if x = g then ⅟(Nat.card G : K) * (wedderburnRepresentation e i).character 1
            * (wedderburnRepresentation e i).character x⁻¹ else 0 by
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]]
  rw [Finset.sum_ite_eq' Finset.univ g fun x => ⅟(Nat.card G : K)
    * (wedderburnRepresentation e i).character 1 * (wedderburnRepresentation e i).character x⁻¹]
  simp

/-- The coefficients of `e_{χ_i}` are class functions, so `e_{χ_i}` is central. -/
theorem ordinaryIdempotent_mem_center :
    ordinaryIdempotent e i ∈ Subalgebra.center K (MonoidAlgebra K G) := by
  have hfix : ∀ g : G, g • (ordinaryIdempotent e i) = ordinaryIdempotent e i := by
    intro g
    refine (OddOrder.GroupAlgebra.smul_eq_self_iff_coeff g _).mpr fun n => ?_
    rw [coeff_ordinaryIdempotent, coeff_ordinaryIdempotent]
    have hconj : (wedderburnRepresentation e i).character (g⁻¹ * n * g)⁻¹
        = (wedderburnRepresentation e i).character n⁻¹ :=
      character_eq_of_isConj (wedderburnRepresentation e i) (isConj_iff.mpr ⟨g, by group⟩)
    rw [hconj]
  exact Subalgebra.mem_center_iff.mpr fun y =>
    (OddOrder.GroupAlgebra.forall_smul_eq_iff_mem_center.mp hfix y).symm

section Orthogonality

variable [CharZero K] [∀ i, Nonempty (m i)] [DecidableEq ι']

/-- **`ω_j(e_{χ_i}) = δ_{ij}`.**  This is the first orthogonality relation, read through
`ω_j(w) χ_j(1) = ∑_g w(g) χ_j(g)`. -/
theorem centralScalar_ordinaryIdempotent (j : ι') :
    MatrixModule.centralScalar e.toAlgHom.toRingHom j (ordinaryIdempotent e i)
      = if i = j then 1 else 0 := by
  classical
  have hchar : (wedderburnRepresentation e j).character 1 = (Fintype.card (m j) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  have hne : (wedderburnRepresentation e j).character 1 ≠ 0 := by
    rw [hchar]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine mul_right_cancel₀ hne ?_
  rw [centralScalar_mul_character_one e j _ (ordinaryIdempotent_mem_center e i)]
  have hterm : ∀ g : G, (ordinaryIdempotent e i).coeff g
      * (wedderburnRepresentation e j).character g
      = ⅟(Nat.card G : K) * (wedderburnRepresentation e i).character 1
        * ((wedderburnRepresentation e i).character g⁻¹
          * (wedderburnRepresentation e j).character g) := fun g => by
    rw [coeff_ordinaryIdempotent]; ring
  rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.mul_sum]
  rw [show ∑ g : G, (wedderburnRepresentation e i).character g⁻¹
        * (wedderburnRepresentation e j).character g
      = if i = j then (Nat.card G : K) else 0 from by
    rw [← sum_character_mul_character_inv e i j]
    exact Finset.sum_congr rfl fun g _ => mul_comm _ _]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, one_mul]
    rw [mul_comm (⅟(Nat.card G : K)) _, mul_assoc, invOf_mul_self, mul_one]
  · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]

/-- **`e(e_{χ_i}) = Pi.single i 1`**: the `i`-th block sees `e_{χ_i}` as the identity, the others
as zero. -/
theorem apply_ordinaryIdempotent : e (ordinaryIdempotent e i) = Pi.single i 1 := by
  classical
  funext j
  have hscal : e (ordinaryIdempotent e i) j
      = Matrix.scalar (m j)
        (MatrixModule.centralScalar e.toAlgHom.toRingHom j (ordinaryIdempotent e i)) :=
    MatrixModule.scalar_centralScalar e.toAlgHom.toRingHom j e.surjective
      (Semigroup.mem_center_iff.mpr
        (Subalgebra.mem_center_iff.mp (ordinaryIdempotent_mem_center e i)))
  rw [hscal, centralScalar_ordinaryIdempotent]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Pi.single_eq_same]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.scalar_apply, Matrix.one_apply_eq]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  · rw [if_neg hij, Pi.single_eq_of_ne (Ne.symm hij)]
    simp

/-! ### The `e_{χ_i}` form a complete orthogonal family -/

theorem ordinaryIdempotent_mul (j : ι') :
    ordinaryIdempotent e i * ordinaryIdempotent e j
      = if i = j then ordinaryIdempotent e i else 0 := by
  refine e.injective ?_
  rw [map_mul, apply_ordinaryIdempotent, apply_ordinaryIdempotent, apply_ite e, map_zero]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, apply_ordinaryIdempotent]
    funext a
    by_cases ha : a = i
    · subst ha; simp
    · simp [Pi.single_eq_of_ne ha]
  · rw [if_neg hij]
    funext a
    by_cases ha : a = i
    · subst ha
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne ha]

omit [DecidableEq ι'] in
theorem isIdempotentElem_ordinaryIdempotent :
    IsIdempotentElem (ordinaryIdempotent e i) := by
  classical
  have h := ordinaryIdempotent_mul e i i
  rwa [if_pos rfl] at h

variable [Fintype ι']

omit [DecidableEq ι'] in
/-- **The `e_{χ_i}` sum to `1`.** -/
theorem sum_ordinaryIdempotent : ∑ j : ι', ordinaryIdempotent e j = 1 := by
  classical
  refine e.injective ?_
  rw [map_sum, map_one]
  funext a
  rw [Finset.sum_apply, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
    congrFun (apply_ordinaryIdempotent e j) a]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, Pi.one_apply]
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [DecidableEq ι'] in
/-- **The spectral decomposition of `Z(K[G])`**: a central element is the sum of its
central-character values against the primitive idempotents. -/
theorem eq_sum_centralScalar_smul_ordinaryIdempotent (z : MonoidAlgebra K G)
    (hz : z ∈ Subalgebra.center K (MonoidAlgebra K G)) :
    z = ∑ j : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom j z • ordinaryIdempotent e j := by
  classical
  refine e.injective ?_
  funext a
  rw [map_sum, Finset.sum_apply]
  have hcomp : ∀ j : ι',
      e (MatrixModule.centralScalar e.toAlgHom.toRingHom j z • ordinaryIdempotent e j) a
        = MatrixModule.centralScalar e.toAlgHom.toRingHom j z
          • (Pi.single j (1 : Matrix (m j) (m j) K) : ∀ b, Matrix (m b) (m b) K) a := fun j => by
    rw [map_smul, Pi.smul_apply, apply_ordinaryIdempotent]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hcomp j]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
    exact MatrixModule.scalar_centralScalar e.toAlgHom.toRingHom a e.surjective
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp hz)) |>.trans (by
        ext r c
        by_cases hrc : r = c
        · subst hrc; simp [Matrix.scalar_apply, Matrix.one_apply_eq]
        · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hrc, Matrix.one_apply_ne hrc])
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Orthogonality

end OddOrder.RepresentationTheory.Modular
