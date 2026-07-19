/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
import OddOrder.GroupTheory.RepresentationTheory.BaseChange

/-!
# Higman's degree-three lower-central bracket

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), section 4,
pp. 85--86, Lemma 6.

This file constructs the actual associated-graded commutator

`L₂ × L₁ → L₃`,

where `Lᵢ = Hᵢ / (Hᵢ² Hᵢ₊₁)`.  The construction is by representatives and
two quotient descents.  Bilinearity is proved in the class-three quotient
`H / (H₃² H₄)`: the image of `H₃` is central there, so the correction terms
in the two commutator product identities vanish.  The resulting map has
spanning range in `L₃` and intertwines every automorphism action induced
from `H`.  These are the group-theoretic inputs for Higman's triple-weight
argument in Lemma 6.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open scoped commutatorElement IsMulCommutative TensorProduct

universe uK uH uX uA uB uC

local instance instLowerCentralLayerKernelTwoInAmbientNormal
    (H : Type uH) [Group H] :
    (lowerCentralLayerKernelInAmbient H 2).Normal :=
  lowerCentralLayerKernelInAmbient_normal H 2

/-! ## The class-three ambient quotient -/

/-- Quotienting by `H₃²H₄` kills the fourth lower-central term. -/
theorem lowerCentralSeries_three_map_layerKernel_two_eq_bot
    (H : Type uH) [Group H] :
    (lowerCentralTerm H 3).map
        (QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  simpa using lowerCentralTerm_succ_le_layerKernelInAmbient H 2

/-- The quotient `H / (H₃²H₄)` has nilpotency class at most three. -/
theorem quotient_layerKernel_two_lowerCentralSeries_three_eq_bot
    (H : Type uH) [Group H] :
    (⊤ : Subgroup (H ⧸ lowerCentralLayerKernelInAmbient H 2)).lowerCentralSeries 3 = ⊥ := by
  rw [← Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2))
      (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_lowerCentralSeries]
  exact lowerCentralSeries_three_map_layerKernel_two_eq_bot H

/-- In `H / (H₃²H₄)`, the image of `H₃` is central. -/
theorem quotient_layerKernel_two_lowerCentralSeries_two_le_center
    (H : Type uH) [Group H] :
    (⊤ : Subgroup (H ⧸ lowerCentralLayerKernelInAmbient H 2)).lowerCentralSeries 2 ≤
      Subgroup.center (H ⧸ lowerCentralLayerKernelInAmbient H 2) := by
  have hfour := quotient_layerKernel_two_lowerCentralSeries_three_eq_bot H
  change
    (⊤ : Subgroup (H ⧸ lowerCentralLayerKernelInAmbient H 2)).lowerCentralSeries
        (2 + 1) = ⊥ at hfour
  rw [Subgroup.lowerCentralSeries_succ] at hfour
  have hcentralizer :
      (⊤ : Subgroup (H ⧸ lowerCentralLayerKernelInAmbient H 2)).lowerCentralSeries 2 ≤
        Subgroup.centralizer
          (⊤ : Subgroup (H ⧸ lowerCentralLayerKernelInAmbient H 2)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hfour
  simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hcentralizer

/-- An element of `H₃` maps to the center of the class-three quotient. -/
theorem quotient_layerKernel_two_mk_mem_center
    (H : Type uH) [Group H] {x : H}
    (hx : x ∈ lowerCentralTerm H 2) :
    QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) x ∈
      Subgroup.center (H ⧸ lowerCentralLayerKernelInAmbient H 2) := by
  apply quotient_layerKernel_two_lowerCentralSeries_two_le_center H
  have hxmap :
      QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) x ∈
        (lowerCentralTerm H 2).map
          (QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2)) :=
    Subgroup.mem_map_of_mem _ hx
  simpa only [lowerCentralTerm, Subgroup.map_lowerCentralSeries,
    Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2))
      (QuotientGroup.mk'_surjective _)] using hxmap

/-- The natural embedding of `L₃` into `H / (H₃²H₄)`. -/
noncomputable def lowerCentralLayerTwoToAmbientQuotient
    (H : Type uH) [Group H] :
    lowerCentralLayer H 2 →*
      H ⧸ lowerCentralLayerKernelInAmbient H 2 :=
  QuotientGroup.map
    (lowerCentralLayerKernel H 2)
    (lowerCentralLayerKernelInAmbient H 2)
    (lowerCentralTerm H 2).subtype (by
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_rfl)

/-- The natural map from `L₃` into the ambient quotient is injective. -/
theorem lowerCentralLayerTwoToAmbientQuotient_injective
    (H : Type uH) [Group H] :
    Function.Injective (lowerCentralLayerTwoToAmbientQuotient H) := by
  rw [lowerCentralLayerTwoToAmbientQuotient,
    ← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf H 2]
  exact le_rfl

/-! ## The representative-level degree-three commutator -/

/-- A commutator of an `H₂` representative with an `H₁` representative,
viewed as an element of `H₃`. -/
def lowerCentralDegreeThreeCommutator
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    ↥(lowerCentralTerm H 2) :=
  ⟨⁅(x : H), (y : H)⁆, by
    apply OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le 1 0
    exact Subgroup.commutator_mem_commutator x.2 y.2⟩

/-- The representative-level degree-three commutator, reduced modulo
`H₃²H₄`. -/
def lowerCentralDegreeThreeCommutatorValue
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralLayer H 2 :=
  QuotientGroup.mk' (lowerCentralLayerKernel H 2)
    (lowerCentralDegreeThreeCommutator H x y)

/-- Mapping the degree-three value into the ambient quotient gives the
ambient commutator of the mapped representatives. -/
@[simp]
theorem lowerCentralLayerTwoToAmbientQuotient_commutatorValue
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralLayerTwoToAmbientQuotient H
        (lowerCentralDegreeThreeCommutatorValue H x y) =
      ⁅QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) (x : H),
        QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) (y : H)⁆ := by
  simp [lowerCentralLayerTwoToAmbientQuotient,
    lowerCentralDegreeThreeCommutatorValue,
    lowerCentralDegreeThreeCommutator]
  rfl

/-- Every representative-level degree-three commutator maps to the center
of the ambient class-three quotient. -/
theorem quotient_layerKernel_two_commutator_mem_center
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    ⁅QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) (x : H),
      QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 2) (y : H)⁆ ∈
        Subgroup.center (H ⧸ lowerCentralLayerKernelInAmbient H 2) := by
  rw [← map_commutatorElement]
  exact quotient_layerKernel_two_mk_mem_center H
    (lowerCentralDegreeThreeCommutator H x y).2

/-- A commutator is multiplicative in the right slot when the correction
commutator is central. -/
private theorem commutatorElement_mul_right_of_commutator_mem_center
    {G : Type*} [Group G] (a b c : G)
    (hc : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ =
        ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by simp only [mul_assoc]
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b * b⁻¹) := by
      rw [Subgroup.mem_center_iff.mp hc b]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by simp

/-- A commutator is multiplicative in the left slot when the correction
commutator is central. -/
private theorem commutatorElement_mul_left_of_commutator_mem_center
    {G : Type*} [Group G] (a b c : G)
    (hb : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hconj : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    calc
      a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ * a * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hb a]
      _ = ⁅b, c⁆ := by simp
  rw [hconj]
  exact (Subgroup.mem_center_iff.mp hb ⁅a, c⁆).symm

/-- The raw degree-three commutator is multiplicative in its `H₂` slot. -/
theorem lowerCentralDegreeThreeCommutatorValue_mul_left
    (H : Type uH) [Group H]
    (x x' : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralDegreeThreeCommutatorValue H (x * x') y =
      lowerCentralDegreeThreeCommutatorValue H x y *
        lowerCentralDegreeThreeCommutatorValue H x' y := by
  apply lowerCentralLayerTwoToAmbientQuotient_injective H
  rw [map_mul]
  simp only [lowerCentralLayerTwoToAmbientQuotient_commutatorValue,
    Subgroup.coe_mul, map_mul]
  exact commutatorElement_mul_left_of_commutator_mem_center _ _ _
    (quotient_layerKernel_two_commutator_mem_center H x' y)

/-- The raw degree-three commutator is multiplicative in its `H₁` slot. -/
theorem lowerCentralDegreeThreeCommutatorValue_mul_right
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y y' : ↥(lowerCentralTerm H 0)) :
    lowerCentralDegreeThreeCommutatorValue H x (y * y') =
      lowerCentralDegreeThreeCommutatorValue H x y *
        lowerCentralDegreeThreeCommutatorValue H x y' := by
  apply lowerCentralLayerTwoToAmbientQuotient_injective H
  rw [map_mul]
  simp only [lowerCentralLayerTwoToAmbientQuotient_commutatorValue,
    Subgroup.coe_mul, map_mul]
  exact commutatorElement_mul_right_of_commutator_mem_center _ _ _
    (quotient_layerKernel_two_commutator_mem_center H x y')

local instance instDegreeThreeLowerCentralLayerIsMulCommutative
    (H : Type uH) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  ⟨⟨(lowerCentralLayer_isElementaryAbelian H i).1⟩⟩

noncomputable local instance instDegreeThreeLowerCentralLayerZModTwoModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- Before quotienting either input, the degree-three commutator is a
bihomomorphism `H₂ → H₁ → L₃`. -/
noncomputable def lowerCentralDegreeThreeCommutatorBihomRaw
    (H : Type uH) [Group H] :
    ↥(lowerCentralTerm H 1) →*
      ↥(lowerCentralTerm H 0) →*
        lowerCentralLayer H 2 where
  toFun x :=
    { toFun := lowerCentralDegreeThreeCommutatorValue H x
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [show lowerCentralDegreeThreeCommutator H x 1 = 1 from
          Subtype.ext (commutatorElement_one_right (x : H))]
        exact Subgroup.one_mem _
      map_mul' := lowerCentralDegreeThreeCommutatorValue_mul_right H x }
  map_one' := by
    ext y
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [show lowerCentralDegreeThreeCommutator H 1 y = 1 from
      Subtype.ext (commutatorElement_one_left (y : H))]
    exact Subgroup.one_mem _
  map_mul' x x' := by
    ext y
    exact lowerCentralDegreeThreeCommutatorValue_mul_left H x x' y

/-- The raw bihomomorphism kills `H₂²H₃` in its left slot. -/
theorem lowerCentralDegreeThreeCommutatorBihomRaw_ker_left
    (H : Type uH) [Group H]
    {k : ↥(lowerCentralTerm H 1)}
    (hk : k ∈ lowerCentralLayerKernel H 1)
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralDegreeThreeCommutatorBihomRaw H k y = 1 := by
  apply (show lowerCentralLayerKernel H 1 ≤
      ((MonoidHom.eval y).comp
        (lowerCentralDegreeThreeCommutatorBihomRaw H)).ker by
    rw [lowerCentralLayerKernel]
    apply sup_le
    · rw [Agemo, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      change lowerCentralDegreeThreeCommutatorBihomRaw H (a ^ (2 ^ 1)) y = 1
      rw [map_pow]
      simpa using
        (lowerCentralLayer_isElementaryAbelian H 2).2
          (lowerCentralDegreeThreeCommutatorBihomRaw H a y)
    · intro z hz
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff _).mpr
      change lowerCentralDegreeThreeCommutator H z y ∈
        Agemo (↥(lowerCentralTerm H 2)) 2 1 ⊔
          (lowerCentralTerm H 3).subgroupOf (lowerCentralTerm H 2)
      apply (show (lowerCentralTerm H 3).subgroupOf
          (lowerCentralTerm H 2) ≤ _ from le_sup_right)
      change ⁅(z : H), (y : H)⁆ ∈ lowerCentralTerm H 3
      apply OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le 2 0
      exact Subgroup.commutator_mem_commutator hz y.2)
  exact hk

/-- The raw bihomomorphism kills `H₁²H₂` in its right slot. -/
theorem lowerCentralDegreeThreeCommutatorBihomRaw_ker_right
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    {k : ↥(lowerCentralTerm H 0)}
    (hk : k ∈ lowerCentralLayerKernel H 0) :
    lowerCentralDegreeThreeCommutatorBihomRaw H x k = 1 := by
  apply (show lowerCentralLayerKernel H 0 ≤
      (lowerCentralDegreeThreeCommutatorBihomRaw H x).ker by
    rw [lowerCentralLayerKernel]
    apply sup_le
    · rw [Agemo, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      change lowerCentralDegreeThreeCommutatorBihomRaw H x (a ^ (2 ^ 1)) = 1
      rw [map_pow]
      simpa using
        (lowerCentralLayer_isElementaryAbelian H 2).2
          (lowerCentralDegreeThreeCommutatorBihomRaw H x a)
    · intro z hz
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff _).mpr
      change lowerCentralDegreeThreeCommutator H x z ∈
        Agemo (↥(lowerCentralTerm H 2)) 2 1 ⊔
          (lowerCentralTerm H 3).subgroupOf (lowerCentralTerm H 2)
      apply (show (lowerCentralTerm H 3).subgroupOf
          (lowerCentralTerm H 2) ≤ _ from le_sup_right)
      change ⁅(x : H), (z : H)⁆ ∈ lowerCentralTerm H 3
      apply OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le 1 1
      exact Subgroup.commutator_mem_commutator x.2 hz)
  exact hk

/-- Descend the right input to `L₁`. -/
noncomputable def lowerCentralDegreeThreeCommutatorBihomRight
    (H : Type uH) [Group H] :
    ↥(lowerCentralTerm H 1) →*
      lowerCentralLayer H 0 →*
        lowerCentralLayer H 2 where
  toFun x :=
    QuotientGroup.lift
      (lowerCentralLayerKernel H 0)
      (lowerCentralDegreeThreeCommutatorBihomRaw H x)
      (fun k hk => MonoidHom.mem_ker.mpr
        (lowerCentralDegreeThreeCommutatorBihomRaw_ker_right H x hk))
  map_one' := by
    ext q
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk', MonoidHom.one_apply, map_one]
  map_mul' x x' := by
    ext q
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply,
      QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_mul]

/-- The fully descended multiplicative bracket `L₂ → L₁ → L₃`. -/
noncomputable def lowerCentralDegreeThreeCommutatorBihom
    (H : Type uH) [Group H] :
    lowerCentralLayer H 1 →*
      lowerCentralLayer H 0 →*
        lowerCentralLayer H 2 :=
  QuotientGroup.lift
    (lowerCentralLayerKernel H 1)
    (lowerCentralDegreeThreeCommutatorBihomRight H)
    (fun k hk => MonoidHom.mem_ker.mpr (by
      ext q
      simp only [lowerCentralDegreeThreeCommutatorBihomRight,
        MonoidHom.coe_mk, OneHom.coe_mk]
      exact lowerCentralDegreeThreeCommutatorBihomRaw_ker_left H hk q))

/-- Evaluation of the descended bracket on representatives. -/
@[simp]
theorem lowerCentralDegreeThreeCommutatorBihom_mk
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralDegreeThreeCommutatorBihom H
        (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x)
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0) y) =
      lowerCentralDegreeThreeCommutatorValue H x y := by
  rfl

/-! ## Additive and `F₂`-linear forms -/

/-- A multiplicative bihomomorphism with different input groups, written
additively in both inputs and the output. -/
def mixedBihomToAdditive
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Group A] [Group B] [Group C]
    [IsMulCommutative A] [IsMulCommutative B] [IsMulCommutative C]
    (b : A →* B →* C) :
    Additive A →+ Additive B →+ Additive C :=
  AddMonoidHom.mk'
    (fun x => (b (Additive.toMul x)).toAdditive)
    (fun x x' => by
      ext y
      change Additive.ofMul
          (b (Additive.toMul x * Additive.toMul x') (Additive.toMul y)) = _
      rw [map_mul, MonoidHom.mul_apply]
      rfl)

@[simp]
theorem mixedBihomToAdditive_apply
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Group A] [Group B] [Group C]
    [IsMulCommutative A] [IsMulCommutative B] [IsMulCommutative C]
    (b : A →* B →* C) (x : Additive A) (y : Additive B) :
    mixedBihomToAdditive b x y =
      Additive.ofMul (b (Additive.toMul x) (Additive.toMul y)) := rfl

/-- Every mixed bi-additive map between canonical `ZMod 2` modules is
canonically bilinear. -/
noncomputable def mixedBihomToZModTwoBilinear
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Group A] [Group B] [Group C]
    [IsMulCommutative A] [IsMulCommutative B] [IsMulCommutative C]
    [Module (ZMod 2) (Additive A)]
    [Module (ZMod 2) (Additive B)]
    [Module (ZMod 2) (Additive C)]
    (b : A →* B →* C) :
    Additive A →ₗ[ZMod 2] Additive B →ₗ[ZMod 2] Additive C :=
  (AddMonoidHom.mk'
    (fun x => (mixedBihomToAdditive b x).toZModLinearMap 2)
    (fun x x' => by
      ext y
      simp [map_add])).toZModLinearMap 2

@[simp]
theorem mixedBihomToZModTwoBilinear_apply
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Group A] [Group B] [Group C]
    [IsMulCommutative A] [IsMulCommutative B] [IsMulCommutative C]
    [Module (ZMod 2) (Additive A)]
    [Module (ZMod 2) (Additive B)]
    [Module (ZMod 2) (Additive C)]
    (b : A →* B →* C) (x : Additive A) (y : Additive B) :
    mixedBihomToZModTwoBilinear b x y =
      Additive.ofMul (b (Additive.toMul x) (Additive.toMul y)) := rfl

/-- The actual degree-three commutator as an `F₂`-bilinear map
`L₂ × L₁ → L₃`. -/
noncomputable def lowerCentralDegreeThreeCommutatorBilinear
    (H : Type uH) [Group H] :
    Additive (lowerCentralLayer H 1) →ₗ[ZMod 2]
      Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
        Additive (lowerCentralLayer H 2) :=
  mixedBihomToZModTwoBilinear
    (lowerCentralDegreeThreeCommutatorBihom H)

@[simp]
theorem lowerCentralDegreeThreeCommutatorBilinear_apply
    (H : Type uH) [Group H]
    (x : Additive (lowerCentralLayer H 1))
    (y : Additive (lowerCentralLayer H 0)) :
    lowerCentralDegreeThreeCommutatorBilinear H x y =
      Additive.ofMul
        (lowerCentralDegreeThreeCommutatorBihom H
          (Additive.toMul x) (Additive.toMul y)) := rfl

/-- Evaluation of the bilinear degree-three bracket on representatives. -/
@[simp]
theorem lowerCentralDegreeThreeCommutatorBilinear_mk
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1))
    (y : ↥(lowerCentralTerm H 0)) :
    lowerCentralDegreeThreeCommutatorBilinear H
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 0) y)) =
      Additive.ofMul (lowerCentralDegreeThreeCommutatorValue H x y) := by
  change Additive.ofMul
      (lowerCentralDegreeThreeCommutatorBihom H
        (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x)
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0) y)) = _
  rw [lowerCentralDegreeThreeCommutatorBihom_mk]

/-! ## Spanning range and automorphism equivariance -/

/-- The image in `L₃` of a commutator between an element of `H₂` and an
ambient element of `H`. -/
def lowerCentralDegreeThreeRawBracket
    (H : Type uH) [Group H]
    (x : ↥(lowerCentralTerm H 1)) (y : H) :
    lowerCentralLayer H 2 :=
  QuotientGroup.mk' (lowerCentralLayerKernel H 2)
    ⟨⁅(x : H), y⁆, by
      apply OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le 1 0
      exact Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top y)⟩

/-- The representative commutators `[H₂,H]` span `L₃`. -/
theorem lowerCentralDegreeThreeRawBracket_span_eq_top
    (H : Type uH) [Group H] :
    Submodule.span (ZMod 2)
        (Set.range fun z : ↥(lowerCentralTerm H 1) × H =>
          Additive.ofMul (lowerCentralDegreeThreeRawBracket H z.1 z.2)) = ⊤ := by
  let S : Set H :=
    {c | ∃ x ∈ lowerCentralTerm H 1,
      ∃ y ∈ (⊤ : Subgroup H), ⁅x, y⁆ = c}
  have hterm : lowerCentralTerm H 2 = Subgroup.closure S := by
    rfl
  let P : ∀ z : H, z ∈ Subgroup.closure S → Prop :=
    fun z hz =>
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 2)
            (⟨z, hterm.symm ▸ hz⟩ : lowerCentralTerm H 2)) ∈
        Submodule.span (ZMod 2)
          (Set.range fun w : ↥(lowerCentralTerm H 1) × H =>
            Additive.ofMul (lowerCentralDegreeThreeRawBracket H w.1 w.2))
  have hclosure : ∀ z (hz : z ∈ Subgroup.closure S), P z hz := by
    intro z hz
    refine Subgroup.closure_induction (p := P) ?_ ?_ ?_ ?_ hz
    · intro c hc
      rcases hc with ⟨x, hx, y, _hy, rfl⟩
      exact Submodule.subset_span ⟨(⟨x, hx⟩, y), rfl⟩
    · dsimp only [P]
      change (0 : Additive (lowerCentralLayer H 2)) ∈
        Submodule.span (ZMod 2)
          (Set.range fun w : ↥(lowerCentralTerm H 1) × H =>
            Additive.ofMul (lowerCentralDegreeThreeRawBracket H w.1 w.2))
      exact Submodule.zero_mem _
    · intro a b ha hb iha ihb
      dsimp only [P] at iha ihb ⊢
      have hab :
          (⟨a * b, hterm.symm ▸ Subgroup.mul_mem _ ha hb⟩ :
              lowerCentralTerm H 2) =
            (⟨a, hterm.symm ▸ ha⟩ : lowerCentralTerm H 2) *
              (⟨b, hterm.symm ▸ hb⟩ : lowerCentralTerm H 2) := by
        rfl
      rw [hab, map_mul]
      exact Submodule.add_mem _ iha ihb
    · intro a ha iha
      dsimp only [P] at iha ⊢
      have hainv :
          (⟨a⁻¹, hterm.symm ▸ Subgroup.inv_mem _ ha⟩ :
              lowerCentralTerm H 2) =
            (⟨a, hterm.symm ▸ ha⟩ : lowerCentralTerm H 2)⁻¹ := by
        rfl
      rw [hainv, map_inv]
      exact Submodule.neg_mem _ iha
  refine Submodule.eq_top_iff'.mpr fun q => ?_
  change Additive.ofMul q.toMul ∈
    Submodule.span (ZMod 2)
      (Set.range fun z : ↥(lowerCentralTerm H 1) × H =>
        Additive.ofMul (lowerCentralDegreeThreeRawBracket H z.1 z.2))
  obtain ⟨z, hzq⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 2) q.toMul
  rw [← hzq]
  rcases z with ⟨z, hz⟩
  have hz' : z ∈ Subgroup.closure S := hterm ▸ hz
  simpa [P] using hclosure z hz'

/-- Any descended mixed pairing agreeing with `[x,y]` on representatives
has spanning range in `L₃`. -/
theorem lowerCentralDegreeThreePairing_span_eq_top_of_apply_mk
    (H : Type uH) [Group H]
    (b : lowerCentralLayer H 1 → lowerCentralLayer H 0 →
      Additive (lowerCentralLayer H 2))
    (hb : ∀ (x : ↥(lowerCentralTerm H 1)) (y : H),
      b (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x)
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0)
          (⟨y, Subgroup.mem_top y⟩ : lowerCentralTerm H 0)) =
        Additive.ofMul (lowerCentralDegreeThreeRawBracket H x y)) :
    Submodule.span (ZMod 2)
        (Set.range fun z : lowerCentralLayer H 1 × lowerCentralLayer H 0 =>
          b z.1 z.2) = ⊤ := by
  apply top_unique
  rw [← lowerCentralDegreeThreeRawBracket_span_eq_top H]
  apply Submodule.span_mono
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨(
    QuotientGroup.mk' (lowerCentralLayerKernel H 1) x,
    QuotientGroup.mk' (lowerCentralLayerKernel H 0)
      (⟨y, Subgroup.mem_top y⟩ : lowerCentralTerm H 0)), ?_⟩
  exact hb x y

/-- The actual degree-three bilinear commutator has full spanning range in
`L₃`. -/
theorem lowerCentralDegreeThreeCommutatorBilinear_span_eq_top
    (H : Type uH) [Group H] :
    Submodule.span (ZMod 2)
        (Set.range fun z :
          Additive (lowerCentralLayer H 1) ×
            Additive (lowerCentralLayer H 0) =>
          lowerCentralDegreeThreeCommutatorBilinear H z.1 z.2) = ⊤ := by
  change Submodule.span (ZMod 2)
      (Set.range fun z : lowerCentralLayer H 1 × lowerCentralLayer H 0 =>
        lowerCentralDegreeThreeCommutatorBilinear H
          (Additive.ofMul z.1) (Additive.ofMul z.2)) = ⊤
  exact lowerCentralDegreeThreePairing_span_eq_top_of_apply_mk H
    (fun u v => lowerCentralDegreeThreeCommutatorBilinear H
      (Additive.ofMul u) (Additive.ofMul v))
    (fun x y => by
      rw [lowerCentralDegreeThreeCommutatorBilinear_mk]
      rfl)

/-- The raw degree-three bracket commutes with every automorphism of `H`. -/
theorem lowerCentralLayerAction_degreeThreeRawBracket
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (x : ↥(lowerCentralTerm H 1)) (y : H) :
    lowerCentralLayerAction phi 2 g
        (lowerCentralDegreeThreeRawBracket H x y) =
      lowerCentralDegreeThreeRawBracket H
        (lowerCentralTermAction phi 1 g x) (phi g y) := by
  rw [lowerCentralDegreeThreeRawBracket,
    lowerCentralLayerAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel H 2))
  ext
  exact map_commutatorElement (phi g) (x : H) y

/-- Equivariance of any descended pairing agreeing with the raw bracket. -/
theorem lowerCentralDegreeThreePairing_equivariant_of_apply_mk
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H)
    (b : lowerCentralLayer H 1 → lowerCentralLayer H 0 →
      Additive (lowerCentralLayer H 2))
    (hb : ∀ (x : ↥(lowerCentralTerm H 1)) (y : H),
      b (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x)
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0)
          (⟨y, Subgroup.mem_top y⟩ : lowerCentralTerm H 0)) =
        Additive.ofMul (lowerCentralDegreeThreeRawBracket H x y))
    (g : X) (u : lowerCentralLayer H 1) (v : lowerCentralLayer H 0) :
    lowerCentralLayerRepresentation phi 2 g (b u v) =
      b (lowerCentralLayerAction phi 1 g u)
        (lowerCentralLayerAction phi 0 g v) := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 1) u
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) v
  have hy : lowerCentralTermAction phi 0 g y =
      (⟨phi g y.1, Subgroup.mem_top _⟩ : lowerCentralTerm H 0) := by
    ext
    rfl
  rw [hb x y.1, lowerCentralLayerRepresentation_apply]
  change Additive.ofMul
      (lowerCentralLayerAction phi 2 g
        (lowerCentralDegreeThreeRawBracket H x y.1)) = _
  rw [lowerCentralLayerAction_degreeThreeRawBracket,
    lowerCentralLayerAction_apply_mk,
    lowerCentralLayerAction_apply_mk, hy, hb]

/-- The actual degree-three bilinear commutator intertwines every induced
group action. -/
theorem lowerCentralDegreeThreeCommutatorBilinear_equivariant
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (u : Additive (lowerCentralLayer H 1))
    (v : Additive (lowerCentralLayer H 0)) :
    lowerCentralLayerRepresentation phi 2 g
        (lowerCentralDegreeThreeCommutatorBilinear H u v) =
      lowerCentralDegreeThreeCommutatorBilinear H
        (Additive.ofMul
          (lowerCentralLayerAction phi 1 g (Additive.toMul u)))
        (Additive.ofMul
          (lowerCentralLayerAction phi 0 g (Additive.toMul v))) := by
  let b : lowerCentralLayer H 1 → lowerCentralLayer H 0 →
      Additive (lowerCentralLayer H 2) :=
    fun x y => lowerCentralDegreeThreeCommutatorBilinear H
      (Additive.ofMul x) (Additive.ofMul y)
  have hb : ∀ (x : ↥(lowerCentralTerm H 1)) (y : H),
      b (QuotientGroup.mk' (lowerCentralLayerKernel H 1) x)
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0)
          (⟨y, Subgroup.mem_top y⟩ : lowerCentralTerm H 0)) =
        Additive.ofMul (lowerCentralDegreeThreeRawBracket H x y) := by
    intro x y
    dsimp only [b]
    rw [lowerCentralDegreeThreeCommutatorBilinear_mk]
    rfl
  simpa only [b, ofMul_toMul] using
    (lowerCentralDegreeThreePairing_equivariant_of_apply_mk
      phi b hb g (Additive.toMul u) (Additive.toMul v))

/-- The same equivariance statement written entirely in representation
notation. -/
theorem lowerCentralDegreeThreeCommutatorBilinear_equivariant_representation
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (u : Additive (lowerCentralLayer H 1))
    (v : Additive (lowerCentralLayer H 0)) :
    lowerCentralLayerRepresentation phi 2 g
        (lowerCentralDegreeThreeCommutatorBilinear H u v) =
      lowerCentralDegreeThreeCommutatorBilinear H
        (lowerCentralLayerRepresentation phi 1 g u)
        (lowerCentralLayerRepresentation phi 0 g v) := by
  have hu := lowerCentralLayerRepresentation_apply
    phi 1 g (Additive.toMul u)
  have hv := lowerCentralLayerRepresentation_apply
    phi 0 g (Additive.toMul v)
  have hu' :
      lowerCentralLayerRepresentation phi 1 g u =
        Additive.ofMul
          (lowerCentralLayerAction phi 1 g (Additive.toMul u)) := by
    simpa only [ofMul_toMul] using hu
  have hv' :
      lowerCentralLayerRepresentation phi 0 g v =
        Additive.ofMul
          (lowerCentralLayerAction phi 0 g (Additive.toMul v)) := by
    simpa only [ofMul_toMul] using hv
  rw [hu', hv']
  exact lowerCentralDegreeThreeCommutatorBilinear_equivariant phi g u v

/-! ## Scalar extension of the degree-three bracket -/

/-- The degree-three lower-central commutator after extending scalars from
`F₂` to `K`. The two input layers are different, so this uses
`LinearMap.baseChange₂`. -/
noncomputable def lowerCentralDegreeThreeCommutatorBilinearBaseChange
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H] :
    (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) →ₗ[K]
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) →ₗ[K]
        (K ⊗[ZMod 2] Additive (lowerCentralLayer H 2)) :=
  (lowerCentralDegreeThreeCommutatorBilinear H).baseChange₂ K

/-- Evaluation of the scalar-extended degree-three commutator on pure
tensors. -/
@[simp]
theorem lowerCentralDegreeThreeCommutatorBilinearBaseChange_tmul
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    (a c : K)
    (x : Additive (lowerCentralLayer H 1))
    (y : Additive (lowerCentralLayer H 0)) :
    lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        (a ⊗ₜ[ZMod 2] x) (c ⊗ₜ[ZMod 2] y) =
      (a * c) ⊗ₜ[ZMod 2]
        lowerCentralDegreeThreeCommutatorBilinear H x y := by
  simp [lowerCentralDegreeThreeCommutatorBilinearBaseChange]

/-- The scalar-extended degree-three commutator intertwines the
scalar-extended actor actions on `L₂`, `L₁`, and `L₃`. -/
theorem lowerCentralDegreeThreeCommutatorBilinearBaseChange_equivariant
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (u : K ⊗[ZMod 2] Additive (lowerCentralLayer H 1))
    (v : K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :
    (lowerCentralLayerRepresentation phi 2 g).baseChange K
        (lowerCentralDegreeThreeCommutatorBilinearBaseChange K H u v) =
      lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
        ((lowerCentralLayerRepresentation phi 1 g).baseChange K u)
        ((lowerCentralLayerRepresentation phi 0 g).baseChange K v) := by
  exact LinearMap.baseChange₂_equivariant
    (lowerCentralDegreeThreeCommutatorBilinear H)
    (lowerCentralLayerRepresentation phi 1 g)
    (lowerCentralLayerRepresentation phi 0 g)
    (lowerCentralLayerRepresentation phi 2 g)
    (lowerCentralDegreeThreeCommutatorBilinear_equivariant_representation phi g)
    u v

/-- The full spanning range of the degree-three commutator survives scalar
extension. -/
theorem lowerCentralDegreeThreeCommutatorBilinearBaseChange_span_eq_top
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H] :
    Submodule.span K
      (Set.range fun z :
          (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) ×
            (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) =>
        lowerCentralDegreeThreeCommutatorBilinearBaseChange K H z.1 z.2) =
      ⊤ := by
  exact LinearMap.baseChange₂_span_eq_top
    (lowerCentralDegreeThreeCommutatorBilinear H)
    (lowerCentralDegreeThreeCommutatorBilinear_span_eq_top H)

/-- The degree-three commutator of scalar-extended eigenvectors has the
product eigenvalue. The value may vanish, so this is an eigenvector equation. -/
theorem lowerCentralDegreeThreeCommutatorBilinearBaseChange_eigenweight
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (a c : K)
    (u : K ⊗[ZMod 2] Additive (lowerCentralLayer H 1))
    (v : K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (hu : (lowerCentralLayerRepresentation phi 1 g).baseChange K u = a • u)
    (hv : (lowerCentralLayerRepresentation phi 0 g).baseChange K v = c • v) :
    (lowerCentralLayerRepresentation phi 2 g).baseChange K
        (lowerCentralDegreeThreeCommutatorBilinearBaseChange K H u v) =
      (a * c) •
        lowerCentralDegreeThreeCommutatorBilinearBaseChange K H u v := by
  rw [lowerCentralDegreeThreeCommutatorBilinearBaseChange_equivariant,
    hu, hv]
  simp [smul_smul, mul_comm]

/-! ## The actual triple commutator -/

/-- The trilinear map induced by the actual iterated commutator
`(x,y,z) ↦ [[x,y],z]`. -/
noncomputable def lowerCentralTripleCommutatorTrilinear
    (H : Type uH) [Group H] :
    Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
        Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
          Additive (lowerCentralLayer H 2) where
  toFun x :=
    (lowerCentralDegreeThreeCommutatorBilinear H).comp
      (lowerCentralCommutatorBilinear H x)
  map_add' x y := by
    ext z w
    simp
  map_smul' c x := by
    ext z w
    simp

@[simp]
theorem lowerCentralTripleCommutatorTrilinear_apply
    (H : Type uH) [Group H]
    (x y z : Additive (lowerCentralLayer H 0)) :
    lowerCentralTripleCommutatorTrilinear H x y z =
      lowerCentralDegreeThreeCommutatorBilinear H
        (lowerCentralCommutatorBilinear H x y) z := rfl

/-- Evaluation of the trilinear map on representatives is the class of the
actual triple commutator `[[x,y],z]`. -/
@[simp]
theorem lowerCentralTripleCommutatorTrilinear_mk
    (H : Type uH) [Group H]
    (x y z : ↥(lowerCentralTerm H 0)) :
    lowerCentralTripleCommutatorTrilinear H
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 0) y))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 0) z)) =
      Additive.ofMul
        (lowerCentralDegreeThreeCommutatorValue H
          (lowerCentralCommutator H x y) z) := by
  rw [lowerCentralTripleCommutatorTrilinear_apply,
    lowerCentralCommutatorBilinear_mk]
  change lowerCentralDegreeThreeCommutatorBilinear H
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel H 1)
          (lowerCentralCommutator H x y)))
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0) z)) = _
  rw [lowerCentralDegreeThreeCommutatorBilinear_mk]

/-- Actual triple commutators span `L₃`.  This combines the full range of
`L₁ × L₁ → L₂` with the full range of `L₂ × L₁ → L₃`; no surjectivity is
postulated for either bracket. -/
theorem lowerCentralTripleCommutatorTrilinear_span_eq_top
    (H : Type uH) [Group H] :
    Submodule.span (ZMod 2)
        (Set.range fun w :
          Additive (lowerCentralLayer H 0) ×
            (Additive (lowerCentralLayer H 0) ×
              Additive (lowerCentralLayer H 0)) =>
          lowerCentralTripleCommutatorTrilinear H
            w.1 w.2.1 w.2.2) = ⊤ := by
  apply top_unique
  rw [← lowerCentralDegreeThreeCommutatorBilinear_span_eq_top H]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, z⟩, rfl⟩
  have hu : u ∈
      Submodule.span (ZMod 2)
        (Set.range fun w :
          Additive (lowerCentralLayer H 0) ×
            Additive (lowerCentralLayer H 0) =>
          lowerCentralCommutatorBilinear H w.1 w.2) := by
    rw [lowerCentralCommutatorBilinear_span_eq_top H]
    exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem w hw =>
      rcases hw with ⟨⟨x, y⟩, rfl⟩
      apply Submodule.subset_span
      exact ⟨(x, (y, z)), rfl⟩
  | zero =>
      change lowerCentralDegreeThreeCommutatorBilinear H 0 z ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _hx _hy ihx ihy =>
      change lowerCentralDegreeThreeCommutatorBilinear H (x + y) z ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _hx ihx =>
      change lowerCentralDegreeThreeCommutatorBilinear H (c • x) z ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

end OddOrder.Higman.Suzuki2Groups
