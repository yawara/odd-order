/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The nonsplit torus of `SL(2, F)`

For a finite field `F` with `q` elements, `SL(2, F)` contains a cyclic subgroup of
order `q + 1` — the *nonsplit torus*.  It arises from a quadratic extension `E / F`:
multiplication by `u ∈ E` is an `F`-linear endomorphism of the two-dimensional
`F`-vector space `E`, whose determinant is the field norm `N_{E/F}(u)`; so the
norm-one units of `E` embed into `SL(2, F)`.

This file develops the group-theoretic half of that construction: the norm-one units
of a quadratic extension of a finite field form a cyclic group of order `q + 1`.

The nonsplit torus is what makes the Sylow subgroups of `PSL(2, 2ⁿ)` for odd primes
dividing `q + 1` cyclic, which is the input Peterfalvi uses in Part II, Ch. II, (15)
(`L = C_G(st) ∩ ⟨Q₀, K, t⟩` is cyclic of order `9` inside `PSL(2, 8)`).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.ProjectiveSpecialLinear

open Module

open scoped Pointwise

section NormOne

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Finite E]

/-- The **norm-one units** of an extension `E / F`: the kernel of the norm map on
unit groups. -/
noncomputable def normOneUnits : Subgroup Eˣ :=
  (Units.map (Algebra.norm F (S := E))).ker

omit [Finite E] in
theorem mem_normOneUnits_iff {u : Eˣ} :
    u ∈ normOneUnits F E ↔ Algebra.norm F (u : E) = 1 := by
  rw [normOneUnits, MonoidHom.mem_ker, Units.ext_iff]
  simp [Units.map]

/-- The norm-one units form a cyclic group (a subgroup of the cyclic group `Eˣ`). -/
theorem isCyclic_normOneUnits : IsCyclic ↥(normOneUnits F E) := by
  haveI : Fact (Nat.card Eˣ ≠ 0) := ⟨Nat.card_pos.ne'⟩
  infer_instance

/-- **`|E¹| = q + 1` for a quadratic extension of a finite field**: the norm is
surjective on units, so `|E¹| = (q² - 1)/(q - 1) = q + 1`. -/
theorem card_normOneUnits (h2 : Module.finrank F E = 2) :
    Nat.card ↥(normOneUnits F E) = Nat.card F + 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F E).injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite E
  have hq : 1 < Nat.card F := Finite.one_lt_card
  -- `|E| = q²`
  have hE : Nat.card E = Nat.card F ^ 2 := by
    rw [Nat.card_eq_fintype_card (α := E), Nat.card_eq_fintype_card (α := F),
      Module.card_eq_pow_finrank (K := F) (V := E), h2]
  -- the norm is surjective on units, so `|Eˣ| = |Fˣ| · |E¹|`
  have hsurj := FiniteField.unitsMap_norm_surjective F E
  have hker := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Units.map (Algebra.norm F (S := E))).ker
  have hquot : Nat.card (Eˣ ⧸ (Units.map (Algebra.norm F (S := E))).ker)
      = Nat.card Fˣ := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (Units.map (Algebra.norm F (S := E)))).toEquiv,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  rw [hquot, Nat.card_units E, Nat.card_units F, hE] at hker
  -- arithmetic: `q² - 1 = (q - 1)(q + 1)`
  have hpos : 0 < Nat.card F - 1 := by omega
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, hq.le]
    ring
  rw [hfac] at hker
  exact (Nat.eq_of_mul_eq_mul_left hpos hker).symm

end NormOne

section Embedding

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Finite E]

/-- **The nonsplit torus embedding**: multiplication by a norm-one unit of a quadratic
extension `E / F` is an `F`-linear endomorphism of `E` of determinant `1`, i.e. an
element of `SL(2, F)` once a basis is chosen. -/
noncomputable def normOneToSL (b : Basis (Fin 2) F E) :
    ↥(normOneUnits F E) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun u := ⟨Algebra.leftMulMatrix b ((u : Eˣ) : E), by
    rw [← Algebra.norm_eq_matrix_det b]
    exact (mem_normOneUnits_iff F E).mp u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

omit [Finite E] in
theorem normOneToSL_injective (b : Basis (Fin 2) F E) :
    Function.Injective (normOneToSL F E b) := fun _ _ huv =>
  Subtype.ext (Units.ext
    (Algebra.leftMulMatrix_injective b (congrArg Subtype.val huv)))

/-- **The nonsplit torus of `SL(2, F)`**: if the finite field `F` (with `q` elements)
has a quadratic extension `E`, then `SL(2, F)` contains a cyclic subgroup of order
`q + 1`, namely the image of the norm-one units of `E`. -/
theorem exists_isCyclic_card_eq_card_add_one (h2 : Module.finrank F E = 2) :
    ∃ C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      IsCyclic ↥C ∧ Nat.card ↥C = Nat.card F + 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F E).injective
  haveI : Module.Finite F E := Module.Finite.of_finite
  haveI := isCyclic_normOneUnits F E
  set b : Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2 with hb
  refine ⟨(normOneToSL F E b).range, ?_, ?_⟩
  · exact isCyclic_of_surjective _ (normOneToSL F E b).rangeRestrict_surjective
  · rw [← card_normOneUnits F E h2]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (normOneToSL_injective F E b)).toEquiv).symm

end Embedding

end OddOrder.GroupTheory.ProjectiveSpecialLinear
