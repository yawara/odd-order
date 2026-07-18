/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.Bruhat

/-!
# The standard root subgroup of the Suzuki permutation group

This file identifies the range of the faithful root action with the concrete
Suzuki root group, records its order and its square-one locus, and chooses the
standard central involution `s = u(0,1)`.  An explicit Bruhat calculation gives
`orderOf (s * w) = 5` for the standard Weyl involution `w`.

These are the concrete root-subgroup facts used in **Peterfalvi, Part II,
Chapter I section 3, Proposition 1(c)** (pp. 105--106), in the Suzuki-group
case of the induction.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

noncomputable section

section /- Proposition 1(c): the standard Suzuki root subgroup (pp. 105--106) -/

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The standard root subgroup is the range of the faithful root-group action. -/
noncomputable def standardRootSubgroup (m : ℕ) :
    Subgroup (standardPermGroup m) :=
  (rootHom m).range

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The coordinate root group is explicitly isomorphic to the standard root
subgroup of the Suzuki permutation group. -/
noncomputable def rootEquivStandardRoot (m : ℕ) :
    RootGroup m ≃* standardRootSubgroup m :=
  MonoidHom.ofInjective (rootHom_injective m)

/-- The coordinate root group has order equal to the square of the defining
field order. -/
theorem natCard_rootGroup_eq_field_sq (m : ℕ) :
    Nat.card (RootGroup m) = Nat.card (Field m) ^ 2 := by
  rw [RootGroup.natCard, natCard_field, pow_two, ← pow_add]
  congr 1
  omega

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The standard root subgroup has order equal to the square of the defining
field order. -/
theorem natCard_standardRootSubgroup_eq_field_sq (m : ℕ) :
    Nat.card (standardRootSubgroup m) = Nat.card (Field m) ^ 2 := by
  rw [← natCard_rootGroup_eq_field_sq]
  exact (Nat.card_congr (rootEquivStandardRoot m).toEquiv).symm

/-- The standard root subgroup has the same exact power-of-two order as the
coordinate root group. -/
theorem natCard_standardRootSubgroup (m : ℕ) :
    Nat.card (standardRootSubgroup m) = 2 ^ (2 * (2 * m + 1)) := by
  rw [← RootGroup.natCard m]
  exact (Nat.card_congr (rootEquivStandardRoot m).toEquiv).symm

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The square-one locus of the coordinate root group is exactly its central
coordinate line. -/
theorem centerLine_eq_sq_one (m : ℕ) :
    (RootGroup.centerLine m : Set (RootGroup m)) = {x | x ^ 2 = 1} := by
  ext x
  exact (RootGroup.sq_eq_one_iff x).symm

/-- The root parameter `(0,1)` chosen for the standard central involution. -/
private def standardRootInvolutionParameter (m : ℕ) : RootGroup m :=
  RootGroup.mk 0 1

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The canonical central involution `s = u(0,1)` in the standard root subgroup. -/
noncomputable def standardRootInvolution (m : ℕ) : standardPermGroup m :=
  rootHom m (standardRootInvolutionParameter m)

/-- The canonical standard root involution belongs to the standard root
subgroup. -/
theorem standardRootInvolution_mem_standardRootSubgroup (m : ℕ) :
    standardRootInvolution m ∈ standardRootSubgroup m :=
  ⟨standardRootInvolutionParameter m, rfl⟩

@[simp] private theorem standardRootInvolutionParameter_ne_one (m : ℕ) :
    standardRootInvolutionParameter m ≠ 1 := by
  intro h
  have h' := congrArg RootGroup.snd h
  simp [standardRootInvolutionParameter] at h'

@[simp] private theorem standardRootInvolutionParameter_sq (m : ℕ) :
    standardRootInvolutionParameter m * standardRootInvolutionParameter m = 1 := by
  ext
  · change (0 : Field m) + 0 = 0
    rfl
  · change (1 : Field m) + 1 + 0 * titsTwist m 0 = 0
    rw [zero_mul, add_zero, CharTwo.add_self_eq_zero]

/-- The canonical standard root element is an involution. -/
@[simp] theorem standardRootInvolution_sq (m : ℕ) :
    standardRootInvolution m ^ 2 = 1 := by
  rw [pow_two, standardRootInvolution, ← map_mul,
    standardRootInvolutionParameter_sq, map_one]

/-- The canonical standard root involution is nontrivial. -/
@[simp] theorem standardRootInvolution_ne_one (m : ℕ) :
    standardRootInvolution m ≠ 1 := by
  intro h
  apply standardRootInvolutionParameter_ne_one m
  apply rootHom_injective m
  simpa [standardRootInvolution] using h

private def orderFiveParameterB (m : ℕ) : RootGroup m :=
  RootGroup.mk 1 0

private def orderFiveParameterC (m : ℕ) : RootGroup m :=
  RootGroup.mk 1 1

@[simp] private theorem orderFiveParameterB_ne_one (m : ℕ) :
    orderFiveParameterB m ≠ 1 := by
  intro h
  have h' := congrArg RootGroup.fst h
  simp [orderFiveParameterB] at h'

@[simp] private theorem orderFiveParameterC_ne_one (m : ℕ) :
    orderFiveParameterC m ≠ 1 := by
  intro h
  have h' := congrArg RootGroup.fst h
  simp [orderFiveParameterC] at h'

@[simp] private theorem involutionParameter_mul_parameterB (m : ℕ) :
    standardRootInvolutionParameter m * orderFiveParameterB m =
      orderFiveParameterC m := by
  ext
  · change (0 : Field m) + 1 = 1
    rw [zero_add]
  · change (1 : Field m) + 0 + 1 * titsTwist m 0 = 1
    rw [map_zero, mul_zero, add_zero, add_zero]

@[simp] private theorem parameterC_mul_involutionParameter (m : ℕ) :
    orderFiveParameterC m * standardRootInvolutionParameter m =
      orderFiveParameterB m := by
  ext
  · change (1 : Field m) + 0 = 1
    rw [add_zero]
  · change (1 : Field m) + 1 + 0 * titsTwist m 1 = 0
    rw [zero_mul, add_zero, CharTwo.add_self_eq_zero]

@[simp] private theorem parameterB_mul_parameterC (m : ℕ) :
    orderFiveParameterB m * orderFiveParameterC m = 1 := by
  ext
  · change (1 : Field m) + 1 = 0
    exact CharTwo.add_self_eq_zero _
  · change (0 : Field m) + 1 + 1 * titsTwist m 1 = 0
    rw [map_one, one_mul, zero_add, CharTwo.add_self_eq_zero]

@[simp] private theorem parameterB_mul_involutionParameter (m : ℕ) :
    orderFiveParameterB m * standardRootInvolutionParameter m =
      orderFiveParameterC m := by
  ext
  · change (1 : Field m) + 0 = 1
    rw [add_zero]
  · change (0 : Field m) + 1 + 0 * titsTwist m 1 = 1
    rw [zero_mul, add_zero, zero_add]

@[simp] private theorem involutionParameter_norm (m : ℕ) :
    (standardRootInvolutionParameter m).suzukiNorm = 1 := by
  change suzukiNorm m 0 1 = 1
  simp [suzukiNorm]

@[simp] private theorem parameterB_norm (m : ℕ) :
    (orderFiveParameterB m).suzukiNorm = 1 := by
  change suzukiNorm m 1 0 = 1
  simp [suzukiNorm]

@[simp] private theorem parameterC_norm (m : ℕ) :
    (orderFiveParameterC m).suzukiNorm = 1 := by
  change 1 ^ 2 * titsTwist m 1 + 1 * 1 + titsTwist m 1 = (1 : Field m)
  rw [map_one]
  simp only [one_pow, one_mul]
  rw [CharTwo.add_self_eq_zero, zero_add]

@[simp] private theorem weylAffine_involutionParameter (m : ℕ) :
    Ovoid.weylAffine (standardRootInvolutionParameter m) =
      orderFiveParameterB m := by
  ext
  · change (1 : Field m) / (standardRootInvolutionParameter m).suzukiNorm = 1
    rw [involutionParameter_norm, div_one]
  · change (0 : Field m) / (standardRootInvolutionParameter m).suzukiNorm = 0
    rw [zero_div]

@[simp] private theorem weylAffine_parameterB (m : ℕ) :
    Ovoid.weylAffine (orderFiveParameterB m) =
      standardRootInvolutionParameter m := by
  ext
  · change (0 : Field m) / (orderFiveParameterB m).suzukiNorm = 0
    rw [zero_div]
  · change (1 : Field m) / (orderFiveParameterB m).suzukiNorm = 1
    rw [parameterB_norm, div_one]

@[simp] private theorem weylAffine_parameterC (m : ℕ) :
    Ovoid.weylAffine (orderFiveParameterC m) = orderFiveParameterC m := by
  ext
  · change (1 : Field m) / (orderFiveParameterC m).suzukiNorm = 1
    rw [parameterC_norm, div_one]
  · change (1 : Field m) / (orderFiveParameterC m).suzukiNorm = 1
    rw [parameterC_norm, div_one]

@[simp] private theorem bruhatRightRoot_involutionParameter (m : ℕ) :
    bruhatRightRoot (standardRootInvolutionParameter m) =
      orderFiveParameterC m := by
  ext
  · change ((1 : Field m) + 0 * titsTwist m 0) /
        (standardRootInvolutionParameter m).suzukiNorm = 1
    rw [zero_mul, add_zero, involutionParameter_norm, div_one]
  · change (1 : Field m) /
        titsTwist m (standardRootInvolutionParameter m).suzukiNorm = 1
    rw [involutionParameter_norm, map_one, div_one]

@[simp] private theorem bruhatRightRoot_parameterB (m : ℕ) :
    bruhatRightRoot (orderFiveParameterB m) = orderFiveParameterB m := by
  ext
  · change ((0 : Field m) + 1 * titsTwist m 1) /
        (orderFiveParameterB m).suzukiNorm = 1
    rw [map_one, mul_one, zero_add, parameterB_norm, div_one]
  · change (0 : Field m) /
        titsTwist m (orderFiveParameterB m).suzukiNorm = 0
    rw [zero_div]

@[simp] private theorem bruhatRightRoot_parameterC (m : ℕ) :
    bruhatRightRoot (orderFiveParameterC m) =
      standardRootInvolutionParameter m := by
  ext
  · change ((1 : Field m) + 1 * titsTwist m 1) /
        (orderFiveParameterC m).suzukiNorm = 0
    rw [map_one, mul_one, CharTwo.add_self_eq_zero, zero_div]
  · change (1 : Field m) /
        titsTwist m (orderFiveParameterC m).suzukiNorm = 1
    rw [parameterC_norm, map_one, div_one]

private theorem bruhatTorus_involutionParameter (m : ℕ) :
    bruhatTorus (standardRootInvolutionParameter m)
        (standardRootInvolutionParameter_ne_one m) = 1 := by
  apply Units.ext
  change (standardRootInvolutionParameter m).suzukiNorm ^ 2 /
      titsTwist m (standardRootInvolutionParameter m).suzukiNorm = 1
  rw [involutionParameter_norm, map_one]
  norm_num

private theorem bruhatTorus_parameterB (m : ℕ) :
    bruhatTorus (orderFiveParameterB m) (orderFiveParameterB_ne_one m) = 1 := by
  apply Units.ext
  change (orderFiveParameterB m).suzukiNorm ^ 2 /
      titsTwist m (orderFiveParameterB m).suzukiNorm = 1
  rw [parameterB_norm, map_one]
  norm_num

private theorem bruhatTorus_parameterC (m : ℕ) :
    bruhatTorus (orderFiveParameterC m) (orderFiveParameterC_ne_one m) = 1 := by
  apply Units.ext
  change (orderFiveParameterC m).suzukiNorm ^ 2 /
      titsTwist m (orderFiveParameterC m).suzukiNorm = 1
  rw [parameterC_norm, map_one]
  norm_num

private theorem weyl_root_involutionParameter_weyl (m : ℕ) :
    weylElement m * rootHom m (standardRootInvolutionParameter m) * weylElement m =
      rootHom m (orderFiveParameterB m) * weylElement m *
        rootHom m (orderFiveParameterC m) := by
  rw [weylElement_mul_rootHom_mul_weylElement
      (standardRootInvolutionParameter m) (standardRootInvolutionParameter_ne_one m),
    weylAffine_involutionParameter, bruhatTorus_involutionParameter, map_one,
    mul_one, bruhatRightRoot_involutionParameter]

private theorem weyl_root_parameterB_weyl (m : ℕ) :
    weylElement m * rootHom m (orderFiveParameterB m) * weylElement m =
      rootHom m (standardRootInvolutionParameter m) * weylElement m *
        rootHom m (orderFiveParameterB m) := by
  rw [weylElement_mul_rootHom_mul_weylElement
      (orderFiveParameterB m) (orderFiveParameterB_ne_one m),
    weylAffine_parameterB, bruhatTorus_parameterB, map_one, mul_one,
    bruhatRightRoot_parameterB]

private theorem weyl_root_parameterC_weyl (m : ℕ) :
    weylElement m * rootHom m (orderFiveParameterC m) * weylElement m =
      rootHom m (orderFiveParameterC m) * weylElement m *
        rootHom m (standardRootInvolutionParameter m) := by
  rw [weylElement_mul_rootHom_mul_weylElement
      (orderFiveParameterC m) (orderFiveParameterC_ne_one m),
    weylAffine_parameterC, bruhatTorus_parameterC, map_one, mul_one,
    bruhatRightRoot_parameterC]

private theorem standardRootInvolution_mul_weyl_sq (m : ℕ) :
    (standardRootInvolution m * weylElement m) ^ 2 =
      rootHom m (orderFiveParameterC m) * weylElement m *
        rootHom m (orderFiveParameterC m) := by
  rw [pow_two, standardRootInvolution]
  calc
    (rootHom m (standardRootInvolutionParameter m) * weylElement m) *
        (rootHom m (standardRootInvolutionParameter m) * weylElement m) =
      rootHom m (standardRootInvolutionParameter m) *
        (weylElement m * rootHom m (standardRootInvolutionParameter m) *
          weylElement m) := by group
    _ = rootHom m (standardRootInvolutionParameter m) *
        (rootHom m (orderFiveParameterB m) * weylElement m *
          rootHom m (orderFiveParameterC m)) := by
      rw [weyl_root_involutionParameter_weyl]
    _ = (rootHom m (standardRootInvolutionParameter m) *
          rootHom m (orderFiveParameterB m)) *
        weylElement m * rootHom m (orderFiveParameterC m) := by group
    _ = rootHom m
          (standardRootInvolutionParameter m * orderFiveParameterB m) *
        weylElement m * rootHom m (orderFiveParameterC m) := by rw [map_mul]
    _ = rootHom m (orderFiveParameterC m) * weylElement m *
        rootHom m (orderFiveParameterC m) := by
      rw [involutionParameter_mul_parameterB]

private theorem standardRootInvolution_mul_weyl_cube (m : ℕ) :
    (standardRootInvolution m * weylElement m) ^ 3 =
      rootHom m (orderFiveParameterB m) * weylElement m *
        rootHom m (orderFiveParameterB m) := by
  rw [show 3 = 2 + 1 by omega, pow_succ,
    standardRootInvolution_mul_weyl_sq, standardRootInvolution]
  calc
    (rootHom m (orderFiveParameterC m) * weylElement m *
          rootHom m (orderFiveParameterC m)) *
        (rootHom m (standardRootInvolutionParameter m) * weylElement m) =
      rootHom m (orderFiveParameterC m) * weylElement m *
        (rootHom m (orderFiveParameterC m) *
          rootHom m (standardRootInvolutionParameter m)) *
          weylElement m := by group
    _ = rootHom m (orderFiveParameterC m) * weylElement m *
        rootHom m
          (orderFiveParameterC m * standardRootInvolutionParameter m) *
          weylElement m := by rw [map_mul]
    _ = rootHom m (orderFiveParameterC m) *
        (weylElement m * rootHom m (orderFiveParameterB m) * weylElement m) := by
      rw [parameterC_mul_involutionParameter]
      group
    _ = rootHom m (orderFiveParameterC m) *
        (rootHom m (standardRootInvolutionParameter m) * weylElement m *
          rootHom m (orderFiveParameterB m)) := by
      rw [weyl_root_parameterB_weyl]
    _ = (rootHom m (orderFiveParameterC m) *
          rootHom m (standardRootInvolutionParameter m)) *
        weylElement m * rootHom m (orderFiveParameterB m) := by group
    _ = rootHom m
          (orderFiveParameterC m * standardRootInvolutionParameter m) *
        weylElement m * rootHom m (orderFiveParameterB m) := by rw [map_mul]
    _ = rootHom m (orderFiveParameterB m) * weylElement m *
        rootHom m (orderFiveParameterB m) := by
      rw [parameterC_mul_involutionParameter]

private theorem standardRootInvolution_mul_weyl_fourth (m : ℕ) :
    (standardRootInvolution m * weylElement m) ^ 4 =
      weylElement m * rootHom m (standardRootInvolutionParameter m) := by
  rw [show 4 = 3 + 1 by omega, pow_succ,
    standardRootInvolution_mul_weyl_cube, standardRootInvolution]
  calc
    (rootHom m (orderFiveParameterB m) * weylElement m *
          rootHom m (orderFiveParameterB m)) *
        (rootHom m (standardRootInvolutionParameter m) * weylElement m) =
      rootHom m (orderFiveParameterB m) * weylElement m *
        (rootHom m (orderFiveParameterB m) *
          rootHom m (standardRootInvolutionParameter m)) *
          weylElement m := by group
    _ = rootHom m (orderFiveParameterB m) * weylElement m *
        rootHom m
          (orderFiveParameterB m * standardRootInvolutionParameter m) *
          weylElement m := by rw [map_mul]
    _ = rootHom m (orderFiveParameterB m) *
        (weylElement m * rootHom m (orderFiveParameterC m) * weylElement m) := by
      rw [parameterB_mul_involutionParameter]
      group
    _ = rootHom m (orderFiveParameterB m) *
        (rootHom m (orderFiveParameterC m) * weylElement m *
          rootHom m (standardRootInvolutionParameter m)) := by
      rw [weyl_root_parameterC_weyl]
    _ = (rootHom m (orderFiveParameterB m) *
          rootHom m (orderFiveParameterC m)) *
        weylElement m * rootHom m (standardRootInvolutionParameter m) := by group
    _ = rootHom m (orderFiveParameterB m * orderFiveParameterC m) *
        weylElement m * rootHom m (standardRootInvolutionParameter m) := by
      rw [map_mul]
    _ = weylElement m * rootHom m (standardRootInvolutionParameter m) := by
      rw [parameterB_mul_parameterC, map_one, one_mul]

private theorem standardRootInvolution_mul_weyl_pow_five (m : ℕ) :
    (standardRootInvolution m * weylElement m) ^ 5 = 1 := by
  rw [show 5 = 4 + 1 by omega, pow_succ,
    standardRootInvolution_mul_weyl_fourth, standardRootInvolution]
  calc
    (weylElement m * rootHom m (standardRootInvolutionParameter m)) *
        (rootHom m (standardRootInvolutionParameter m) * weylElement m) =
      weylElement m *
        (rootHom m (standardRootInvolutionParameter m) *
          rootHom m (standardRootInvolutionParameter m)) *
          weylElement m := by group
    _ = weylElement m *
        rootHom m
          (standardRootInvolutionParameter m * standardRootInvolutionParameter m) *
          weylElement m := by rw [map_mul]
    _ = 1 := by
      rw [standardRootInvolutionParameter_sq, map_one, mul_one, ← pow_two,
        weylElement_sq_eq_one]

private theorem standardRootInvolution_mul_weyl_ne_one (m : ℕ) :
    standardRootInvolution m * weylElement m ≠ 1 := by
  intro h
  have h' := congrArg
    (fun g : standardPermGroup m => g • Ovoid.infinity m) h
  have ha : Ovoid.affine (standardRootInvolutionParameter m) =
      Ovoid.infinity m := by
    simp [standardRootInvolution, mul_smul, Ovoid.origin] at h'
  exact Ovoid.affine_ne_infinity (standardRootInvolutionParameter m) ha

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
For the canonical central root involution `s` and standard Weyl involution `w`,
the product `sw` has exact order five. -/
theorem orderOf_standardRootInvolution_mul_weylElement (m : ℕ) :
    orderOf (standardRootInvolution m * weylElement m) = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (standardRootInvolution_mul_weyl_pow_five m)
    (standardRootInvolution_mul_weyl_ne_one m)

end

end

end OddOrder.GroupTheory.SpecificGroups.Suzuki
