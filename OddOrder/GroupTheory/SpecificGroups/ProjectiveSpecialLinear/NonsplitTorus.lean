/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.RootGroupSylow
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

section AnyFiniteField

/-- **The nonsplit torus of `SL(2, F)`** for an arbitrary finite field `F` with `q`
elements: `SL(2, F)` contains a cyclic subgroup of order `q + 1`.

The quadratic extension is `FiniteField.Extension F p 2`. -/
theorem exists_isCyclic_card_specialLinearGroup_eq_card_add_one
    (F : Type*) [Field F] [Finite F] :
    ∃ C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      IsCyclic ↥C ∧ Nat.card ↥C = Nat.card F + 1 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  exact exists_isCyclic_card_eq_card_add_one F (FiniteField.Extension F p 2)
    (FiniteField.finrank_extension F p 2)

end AnyFiniteField

section SylowThree

/-- **Every Sylow `3`-subgroup of `SL(2, F)` with `|F| = 8` is cyclic of order `9`.**

`|SL(2,8)| = 8·7·9`, so a Sylow `3`-subgroup has order `9`; the nonsplit torus is a
cyclic subgroup of that order, hence is a Sylow `3`-subgroup, and all Sylow
`3`-subgroups are isomorphic.

This is the input for Peterfalvi Part II, Ch. II, (15): in `⟨Q₀, K, t⟩ ≅ PSL(2, 8)`
the centralizer of the order-`3` element `st` is cyclic of order `9`. -/
theorem isCyclic_and_card_sylow_three_of_card_eq_eight
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 8)
    (S : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F)) :
    IsCyclic ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
      ∧ Nat.card ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 504 := by
    rw [SpecificGroups.ProjectiveSpecialLinear.natCard_specialLinearGroup_fin_two, hF]
  have hcard : ∀ T : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F),
      Nat.card ↥(T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = 9 := by
    intro T
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp T.isPGroup'
    have hmul := (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).card_mul_index
    rw [hk, hSL] at hmul
    have hnd := T.not_dvd_index
    have hcop : Nat.Coprime ((3 : ℕ) ^ 2)
        ((T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).index) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd)
    have h1 : (3 : ℕ) ^ 2 ∣ 3 ^ k := by
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [hmul]
      exact ⟨56, by norm_num⟩
    have h2 : (3 : ℕ) ^ k ∣ 3 ^ 2 := by
      refine (Nat.Coprime.pow_left k (show Nat.Coprime 3 56 by norm_num)).dvd_of_dvd_mul_left ?_
      rw [show (56 : ℕ) * 3 ^ 2 = 504 by norm_num]
      exact ⟨_, hmul.symm⟩
    have hk2 : k = 2 :=
      le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2)
        ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1)
    rw [hk, hk2]
    norm_num
  refine ⟨?_, hcard S⟩
  obtain ⟨C, hCcyc, hCcard⟩ := exists_isCyclic_card_specialLinearGroup_eq_card_add_one F
  rw [hF] at hCcard
  have hCp : IsPGroup 3 ↥C := IsPGroup.of_card (n := 2) (by rw [hCcard]; norm_num)
  obtain ⟨Q, hCQ⟩ := hCp.exists_le_sylow
  have hCQeq : C = (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Subgroup.eq_of_le_of_card_ge hCQ (by rw [hcard Q, hCcard])
  have hQcyc : IsCyclic ↥(Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [← hCQeq]; exact hCcyc
  exact isCyclic_of_surjective (Sylow.equiv Q S) (Sylow.equiv Q S).surjective

end SylowThree

end OddOrder.GroupTheory.ProjectiveSpecialLinear
