/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniGradedCommutators

/-!
# Higman's Lemma 13: equivariance of the middle Frattini commutator

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The natural map from the first lower-central layer to
`Phi(P) / Phi(P)^2` commutes with the Suzuki actor.  Consequently the
middle Frattini commutator intertwines the induced action on both outer
variables with the actual quotient action on the middle layer.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

local instance instFrattiniGradedEquivarianceLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniGradedEquivarianceLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The natural map from `L₁(P)` to `Phi(P) / Phi(P)^2` commutes with
the actor on underlying multiplicative quotients. -/
theorem lowerCentralLayerOneToFrattiniMiddle_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (c : Y) (q : lowerCentralLayer P 1),
      actualAgemoOneQuotientAction hPhiInv.restrict c
          (lowerCentralLayerOneToFrattiniMiddle
            hP hxi hPhiComm hexists q) =
        lowerCentralLayerOneToFrattiniMiddle
          hP hxi hPhiComm hexists
            (lowerCentralLayerAction Y.subtype 1 c q) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro c q
  refine QuotientGroup.induction_on q ?_
  intro x
  change actualAgemoOneQuotientAction hPhiInv.restrict c
      (lowerCentralLayerOneToFrattiniMiddle hP hxi hPhiComm hexists
        (QuotientGroup.mk' (lowerCentralLayerKernel P 1) x)) =
    lowerCentralLayerOneToFrattiniMiddle hP hxi hPhiComm hexists
      (lowerCentralLayerAction Y.subtype 1 c
        (QuotientGroup.mk' (lowerCentralLayerKernel P 1) x))
  rw [lowerCentralLayerOneToFrattiniMiddle_mk,
    lowerCentralLayerAction_apply_mk,
    lowerCentralLayerOneToFrattiniMiddle_mk]
  change QuotientGroup.mk' (Agemo (frattini P) 2 1)
      (hPhiInv.restrict c (lowerCentralTermOneInFrattini hP x)) =
    QuotientGroup.mk' (Agemo (frattini P) 2 1)
      (lowerCentralTermOneInFrattini hP
        (lowerCentralTermAction Y.subtype 1 c x))
  apply congrArg (QuotientGroup.mk' (Agemo (frattini P) 2 1))
  apply Subtype.ext
  exact (IsAInvariant.restrict_apply_val hPhiInv c
      (lowerCentralTermOneInFrattini hP x)).trans
    (IsAInvariant.restrict_apply_val
      (IsAInvariant.lowerCentralSeries Y.subtype 1) c x).symm

/-- Linear form of equivariance for the natural map
`L₁(P) → Phi(P) / Phi(P)^2`. -/
theorem lowerCentralLayerOneToFrattiniMiddleLinear_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (c : Y) (u : Additive (lowerCentralLayer P 1)),
      actualAgemoOneQuotientRepresentation hPhiInv.restrict c
          (lowerCentralLayerOneToFrattiniMiddleLinear
            hP hxi hPhiComm hexists u) =
        lowerCentralLayerOneToFrattiniMiddleLinear
          hP hxi hPhiComm hexists
            (lowerCentralLayerRepresentation Y.subtype 1 c u) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro c u
  change Additive.ofMul
      (actualAgemoOneQuotientAction hPhiInv.restrict c
        (lowerCentralLayerOneToFrattiniMiddle
          hP hxi hPhiComm hexists u.toMul)) =
    Additive.ofMul
      (lowerCentralLayerOneToFrattiniMiddle hP hxi hPhiComm hexists
        (lowerCentralLayerAction Y.subtype 1 c u.toMul))
  exact congrArg Additive.ofMul
    (lowerCentralLayerOneToFrattiniMiddle_equivariant
      hP hxi hPhiComm hexists c u.toMul)

/-- **Higman Lemma 13 (p. 92), equivariance of the middle bracket.**

The actual commutator `P/Phi(P) × P/Phi(P) → Phi(P)/Phi(P)^2`
intertwines the actor on all three layers. -/
theorem frattiniMiddleCommutatorBilinear_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (c : Y) (u v : Additive (lowerCentralLayer P 0)),
      actualAgemoOneQuotientRepresentation hPhiInv.restrict c
          (frattiniMiddleCommutatorBilinear
            hP hxi hPhiComm hexists u v) =
        frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists
          (lowerCentralLayerRepresentation Y.subtype 0 c u)
          (lowerCentralLayerRepresentation Y.subtype 0 c v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro c u v
  change actualAgemoOneQuotientRepresentation hPhiInv.restrict c
      (lowerCentralLayerOneToFrattiniMiddleLinear
        hP hxi hPhiComm hexists
          (lowerCentralCommutatorBilinear P u v)) = _
  rw [lowerCentralLayerOneToFrattiniMiddleLinear_equivariant,
    lowerCentralCommutatorBilinear_equivariant]
  have hu := lowerCentralLayerRepresentation_apply
    Y.subtype 0 c u.toMul
  have hv := lowerCentralLayerRepresentation_apply
    Y.subtype 0 c v.toMul
  have hu' :
      lowerCentralLayerRepresentation Y.subtype 0 c u =
        Additive.ofMul
          (lowerCentralLayerAction Y.subtype 0 c u.toMul) := by
    simpa only [ofMul_toMul] using hu
  have hv' :
      lowerCentralLayerRepresentation Y.subtype 0 c v =
        Additive.ofMul
          (lowerCentralLayerAction Y.subtype 0 c v.toMul) := by
    simpa only [ofMul_toMul] using hv
  rw [hu', hv']
  rfl

end OddOrder.Higman.Suzuki2Groups
