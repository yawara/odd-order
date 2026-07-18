/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.RootGroup

/-!
# The standard root group is Sylow in PSL(2,F)

For a finite field `F` of characteristic two, this file computes the order
of `SL(2,F)` and observes that its center is trivial.  Consequently
`PSL(2,F)` has order `q(q-1)(q+1)`, while the upper-unipotent root group has
order `q`.  Since `q` is a power of two and `(q-1)(q+1)` is odd, the root
group is a Sylow `2`-subgroup.

This is the standard-group calculation used in Peterfalvi, Part II,
Chapter I section 3, Proposition 1(c) (pp. 105--106).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear

open Matrix

open scoped CharTwo MatrixGroups

universe u

variable {F : Type u} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem card_specialLinearGroup_mul_units :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * Nat.card Fˣ =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) := by
  let detGL : Matrix.GeneralLinearGroup (Fin 2) F →* Fˣ :=
    Matrix.GeneralLinearGroup.det
  let toGLSL : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL
  have htoGL_range_eq_ker : toGLSL.range = detGL.ker := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      simp [detGL, toGLSL]
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      have hgdet : ((g : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).det = 1 := by
        have h := congrArg Units.val hg
        simpa [detGL, Matrix.GeneralLinearGroup.val_det_apply] using h
      refine ⟨⟨((g : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F), hgdet⟩, ?_⟩
      exact Units.ext rfl
  have htop_map_eq_range :
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map toGLSL =
        toGLSL.range := by
    ext
    simp
  have hcard_SL_range :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
        Nat.card toGLSL.range := by
    calc
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
          Nat.card (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
            rw [Subgroup.card_top]
      _ = Nat.card ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map
            toGLSL) := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective
                (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) toGLSL
                Matrix.SpecialLinearGroup.toGL_injective).toEquiv
      _ = Nat.card toGLSL.range := by rw [htop_map_eq_range]
  have hcard_SL_ker :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
        Nat.card detGL.ker := by
    rw [hcard_SL_range, htoGL_range_eq_ker]
  have hdet_range_top : detGL.range = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      let A : Matrix (Fin 2) (Fin 2) F := !![(x : F), 0; 0, 1]
      have hdetA_ne : A.det ≠ 0 := by
        simp [A, Matrix.det_fin_two, x.ne_zero]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA_ne, ?_⟩
      ext
      simp [detGL, A, Matrix.det_fin_two]
  have hker_mul_range :
      Nat.card detGL.ker * Nat.card detGL.range =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [← Subgroup.index_ker detGL]
    exact Subgroup.card_mul_index detGL.ker
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * Nat.card Fˣ =
        Nat.card detGL.ker * Nat.card detGL.range := by
          rw [hcard_SL_ker, hdet_range_top, Subgroup.card_top]
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) := hker_mul_range

/-- The order of `SL(2,F)` over a finite field is `q(q-1)(q+1)`. -/
theorem natCard_specialLinearGroup_fin_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F - 1) * (Nat.card F + 1) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hunit : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units,
      Fintype.card_eq_nat_card]
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F - 1) * (Nat.card F - 1) *
        (Nat.card F + 1) := by
    rw [Matrix.card_GL_field (n := 2)]
    simp only [Fin.prod_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, pow_zero, Nat.mod_succ, pow_one,
      Fintype.card_eq_nat_card]
    have hsq_sub_one : Nat.card F ^ 2 - 1 =
        (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    have hsq_sub_self : Nat.card F ^ 2 - Nat.card F =
        Nat.card F * (Nat.card F - 1) := by
      calc
        Nat.card F ^ 2 - Nat.card F =
            Nat.card F * Nat.card F - Nat.card F * 1 := by
              rw [pow_two, mul_one]
        _ = Nat.card F * (Nat.card F - 1) :=
          (Nat.mul_sub_left_distrib (Nat.card F) (Nat.card F) 1).symm
    rw [hsq_sub_one, hsq_sub_self]
    ring
  have hpred : 0 < Nat.card F - 1 := Nat.sub_pos_of_lt hq
  apply Nat.mul_right_cancel hpred
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (Nat.card F - 1) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) := by
          rw [← hunit]
          exact card_specialLinearGroup_mul_units
    _ = Nat.card F * (Nat.card F - 1) * (Nat.card F - 1) *
        (Nat.card F + 1) := hGL
    _ = (Nat.card F * (Nat.card F - 1) * (Nat.card F + 1)) *
        (Nat.card F - 1) := by ring

omit [Finite F] in
/-- In characteristic two, `SL(2,F)` has trivial center. -/
theorem center_specialLinearGroup_fin_two_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  ext A
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      rw [sq_eq_one_iff] at hr2
      rcases hr2 with hr2 | hr2
      · exact hr2
      · simpa only [CharTwo.neg_eq] using hr2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1]
    simp
  · intro hA
    rw [Subgroup.mem_bot] at hA
    rw [hA]
    exact Subgroup.one_mem _

/-- In characteristic two, `PSL(2,F)` has order `q(q-1)(q+1)`. -/
theorem natCard_projectiveSpecialLinearGroup_fin_two :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F - 1) * (Nat.card F + 1) := by
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = _
  rw [center_specialLinearGroup_fin_two_eq_bot]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [Subgroup.card_bot, mul_one, natCard_specialLinearGroup_fin_two] at hcard
  exact hcard.symm

/-- The index of the standard root group is `(q-1)(q+1)`. -/
theorem rootSubgroup_index :
    (rootSubgroup (F := F)).index =
      (Nat.card F - 1) * (Nat.card F + 1) := by
  have hcard := (rootSubgroup (F := F)).card_mul_index
  rw [natCard_rootSubgroup, natCard_projectiveSpecialLinearGroup_fin_two] at hcard
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
  simpa [mul_assoc] using hcard

/-- The standard root subgroup has odd index in `PSL(2,F)`. -/
theorem rootSubgroup_index_odd : Odd (rootSubgroup (F := F)).index := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
  have hqeven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact even_two.pow_of_ne_zero hn0
  rw [rootSubgroup_index]
  have hpredOdd : Odd (Nat.card F - 1) := by
    exact Nat.Even.sub_odd (Nat.card_pos (α := F)) hqeven odd_one
  have hsuccOdd : Odd (Nat.card F + 1) := hqeven.add_one
  exact hpredOdd.mul hsuccOdd

/-- The upper-unipotent root group is a Sylow `2`-subgroup of `PSL(2,F)`. -/
noncomputable def rootSylow :
    Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  rootSubgroup_isElementaryAbelian.isPGroup.toSylow
    (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr (rootSubgroup_index_odd (F := F)))

set_option linter.unusedSectionVars false in
@[simp] theorem coe_rootSylow :
    (rootSylow (F := F) :
      Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      rootSubgroup (F := F) := rfl

end OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear
