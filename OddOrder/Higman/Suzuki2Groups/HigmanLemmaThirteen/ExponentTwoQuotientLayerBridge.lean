/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SummandIsomorphismBridge

/-!
# Higman's Lemma 13: the ambient zeroth layer in the Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

For a finite `2`-group `P`, the denominator of the zeroth lower-central layer
is exactly `Φ(P)`.  Hence the canonical map from `L₀(P)` to `P ⧸ Φ(P)` is an
injective `ZMod 2`-linear map.  It also intertwines every automorphism action
on the lower-central layer with the induced action on the Frattini quotient.

The linear map in this file is the quotient-side target for the genuine
factor maps `restrictedFactorAmbientInclusion`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP uY

local instance quotientLayerBridgeLayerIsMulCommutative
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance quotientLayerBridgeLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance quotientLayerBridgeLayerZModTwoModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The canonical commutative-group structure on the Frattini quotient of a
finite `2`-group. -/
abbrev frattiniQuotientCommGroup
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P) :
    CommGroup (P ⧸ frattini P) :=
  { (inferInstance : Group (P ⧸ frattini P)) with
    mul_comm := hP.quotient_frattini_isElementaryAbelian.comm }

/-- The canonical `ZMod 2`-module structure on the Frattini quotient of a
finite `2`-group. -/
noncomputable abbrev frattiniQuotientZModTwoModule
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  AddCommGroup.zmodModule
      (G := Additive (P ⧸ frattini P)) (n := 2) (by
    intro x
    have hx : (Additive.toMul x) ^ 2 = 1 :=
      hP.quotient_frattini_isElementaryAbelian.pow_eq_one _
    have h2 :
        Additive.ofMul ((Additive.toMul x) ^ 2) =
          Additive.ofMul (1 : P ⧸ frattini P) := by
      rw [hx]
    rw [ofMul_pow, ofMul_one, ofMul_toMul] at h2
    exact h2)

/-- For a finite `2`-group, the subgroup-form denominator of `L₀(P)` is its
Frattini subgroup. -/
theorem lowerCentralLayerKernel_zero_eq_frattini_subgroupOf
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P) :
    lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0) := by
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0,
    lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP]

/-- The canonical linear map `L₀(P) → P ⧸ Φ(P)` for a finite `2`-group. -/
noncomputable def layerZeroToFrattiniQuotientLinear
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
      Additive (P ⧸ frattini P) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  exact
    { MonoidHom.toAdditive
        (layerZeroToQuotient (frattini P)
          (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)) with
      map_smul' := ZMod.map_smul
        (MonoidHom.toAdditive
          (layerZeroToQuotient (frattini P)
            (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP))) }

@[simp]
theorem layerZeroToFrattiniQuotientLinear_apply
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P)
    (v : Additive (lowerCentralLayer P 0)) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    layerZeroToFrattiniQuotientLinear P hP v =
      Additive.ofMul
        (layerZeroToQuotient (frattini P)
          (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
          v.toMul) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  rfl

/-- The linear layer-to-Frattini-quotient map is injective. -/
theorem layerZeroToFrattiniQuotientLinear_injective
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    Function.Injective (layerZeroToFrattiniQuotientLinear P hP) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro x y hxy
  apply Additive.toMul.injective
  apply layerZeroToQuotient_injective (frattini P)
    (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
  simpa only [layerZeroToFrattiniQuotientLinear_apply, toMul_ofMul] using
    congrArg Additive.toMul hxy

/-- The linear layer-to-Frattini-quotient map intertwines the lower-central
representation with the induced quotient action. -/
theorem layerZeroToFrattiniQuotientLinear_equivariant
    (P : Type uP) [Group P] [Finite P] (hP : IsPGroup 2 P)
    {Y : Type uY} [Group Y] (phi : Y →* MulAut P)
    (a : Y) (v : Additive (lowerCentralLayer P 0)) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    layerZeroToFrattiniQuotientLinear P hP
        (lowerCentralLayerRepresentation phi 0 a v) =
      Additive.ofMul
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic phi :
            IsAInvariant phi (frattini P))
          a (layerZeroToFrattiniQuotientLinear P hP v).toMul) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  rw [show v = Additive.ofMul v.toMul by rfl,
    lowerCentralLayerRepresentation_apply,
    layerZeroToFrattiniQuotientLinear_apply,
    layerZeroToFrattiniQuotientLinear_apply]
  exact congrArg Additive.ofMul
    (layerZeroToQuotient_equivariant
      (frattini P)
      (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
      phi
      (IsAInvariant.of_characteristic phi :
        IsAInvariant phi (frattini P))
      a v.toMul)

end

end OddOrder.Higman.Suzuki2Groups
