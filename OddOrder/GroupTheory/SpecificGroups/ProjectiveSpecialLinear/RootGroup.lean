/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# The standard root group and Weyl element of PSL(2,F)

For a field F of characteristic two, this file constructs the upper
unipotent root group of PSL(2,F) from the public special-linear
transvections. It proves that the quotient map remains injective on this
root group, computes its exact order, and shows that it is elementary
abelian. The standard Weyl element is represented by the usual matrix; the
distinguished nonidentity root element multiplied by this Weyl element has
order three.

This is the concrete PSL(2,q) structure cited in Peterfalvi, Part II,
Chapter I section 3, Proposition 1(c) (pp. 105--106).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear

open Matrix

open scoped CharTwo MatrixGroups

universe u

variable {F : Type u} [Field F]

/-- The upper-unipotent transvections, mapped into PSL(2,F). -/
noncomputable def rootHom : Multiplicative F →*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F where
  toFun x := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one x.toAdd)
  map_one' := by
    change QuotientGroup.mk' _
      (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (0 : F)) = 1
    have hz : (Matrix.SpecialLinearGroup.transvection (ι := Fin 2)
        Fin.zero_ne_one (0 : F) : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
      ext i j
      simp [Matrix.SpecialLinearGroup.transvection_coe]
    simpa using congrArg
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) hz
  map_mul' x y := by
    change QuotientGroup.mk' _ (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one
      (x.toAdd + y.toAdd)) = _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact map_mul _ _ _

/-- The quotient map remains injective on the upper-unipotent root group. -/
theorem rootHom_injective : Function.Injective (rootHom (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  change QuotientGroup.mk' _
    (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one x.toAdd) = 1 at hx
  have hx' : Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one x.toAdd ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp hx
  have : x.toAdd = 0 :=
    (Matrix.SpecialLinearGroup.transvection_mem_center_iff Fin.zero_ne_one _).mp hx'
  apply Multiplicative.toAdd.injective
  simpa using this

/-- The standard upper-unipotent root subgroup of PSL(2,F). -/
noncomputable def rootSubgroup : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  (rootHom (F := F)).range

/-- Root coordinates give an explicit equivalence onto the standard root subgroup. -/
noncomputable def rootMulEquiv : Multiplicative F ≃* rootSubgroup (F := F) :=
  MulEquiv.ofBijective (rootHom (F := F)).rangeRestrict
    ⟨fun _ _ h => rootHom_injective (congrArg Subtype.val h),
      (rootHom (F := F)).rangeRestrict_surjective⟩

section CharacteristicTwo

variable [CharP F 2]

/-- The additive field is elementary abelian when written multiplicatively. -/
theorem multiplicativeField_isElementaryAbelian :
    OddOrder.GroupTheory.IsElementaryAbelian 2 (Multiplicative F) := by
  constructor
  · intro x y
    apply Multiplicative.toAdd.injective
    simp [add_comm]
  · intro x
    apply Multiplicative.toAdd.injective
    simp

/-- The standard root subgroup is elementary abelian. -/
theorem rootSubgroup_isElementaryAbelian :
    OddOrder.GroupTheory.IsElementaryAbelian 2 (rootSubgroup (F := F)) :=
  OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv (rootMulEquiv (F := F))
    multiplicativeField_isElementaryAbelian

end CharacteristicTwo

/-- The standard root subgroup has order |F|. -/
theorem natCard_rootSubgroup [Finite F] :
    Nat.card (rootSubgroup (F := F)) = Nat.card F := by
  rw [Nat.card_congr (rootMulEquiv (F := F)).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

/-- The standard Weyl matrix [[0,-1],[1,0]] in SL(2,F). -/
noncomputable def weylSL : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The standard Weyl involution in PSL(2,F). -/
noncomputable def canonicalT : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.mk' _ (weylSL (F := F))

/-- The parameter-one nonidentity element of the standard root subgroup. -/
noncomputable def canonicalS : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  rootHom (F := F) (Multiplicative.ofAdd 1)

/-- The standard distinguished product is nonidentity. -/
theorem canonicalS_mul_T_ne_one :
    canonicalS (F := F) * canonicalT (F := F) ≠ 1 := by
  intro h
  have h' :
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (1 : F) * weylSL (F := F)) = 1 := by
    simpa [canonicalS, rootHom, canonicalT] using h
  have hcenter :
      Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (1 : F) * weylSL (F := F) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp h'
  obtain ⟨r, hr1, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr2
  simp [Matrix.SpecialLinearGroup.transvection_coe, weylSL, Matrix.mul_apply] at hij

section CharacteristicTwoPair

variable [CharP F 2]

/-- The standard Weyl element has square one in characteristic two. -/
theorem canonicalT_sq : canonicalT (F := F) ^ 2 = 1 := by
  have hw : weylSL (F := F) ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylSL, pow_two, CharTwo.neg_eq, Matrix.mul_apply]
  change (QuotientGroup.mk' _ (weylSL (F := F))) ^ 2 = 1
  rw [← map_pow]
  simp [hw]

/-- The canonical root element has square one. -/
theorem canonicalS_sq : canonicalS (F := F) ^ 2 = 1 := by
  simpa [canonicalS] using (rootSubgroup_isElementaryAbelian (F := F)).pow_eq_one
    (⟨canonicalS (F := F), ⟨Multiplicative.ofAdd 1, rfl⟩⟩ : rootSubgroup (F := F))

/-- The standard distinguished product has cube one. -/
theorem canonicalS_mul_T_cubed :
    (canonicalS (F := F) * canonicalT (F := F)) ^ 3 = 1 := by
  let a : Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (1 : F) * weylSL (F := F)
  have ha : a ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, weylSL, pow_succ, CharTwo.neg_eq,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply]
  change ((QuotientGroup.mk' _
    (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (1 : F))) *
    QuotientGroup.mk' _ (weylSL (F := F))) ^ 3 = 1
  rw [← map_mul, ← map_pow]
  simp [a, ha]


/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
For the standard root and Weyl coordinates, st has order exactly three. -/
theorem orderOf_canonicalS_mul_T :
    orderOf (canonicalS (F := F) * canonicalT (F := F)) = 3 :=
  orderOf_eq_prime canonicalS_mul_T_cubed canonicalS_mul_T_ne_one

end CharacteristicTwoPair

end OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear
