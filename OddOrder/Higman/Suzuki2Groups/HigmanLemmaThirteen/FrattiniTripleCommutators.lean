/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniGradedCommutatorEquivariance
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCommutatorEquivariance

/-!
# Higman's Lemma 13: the Frattini-valued triple commutator

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The middle bracket and the square-valued bracket compose to the actual
trilinear map

`P / Phi(P) × P / Phi(P) × P / Phi(P) -> Phi(P)^2`.

On representatives its value is the literal nested commutator
`[[x,y],z]`, regarded as an element of `Phi(P)^2`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance instFrattiniTripleLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniTripleLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The raw nested commutator `[[x,y],z]`, with its proof of membership
in the common subgroup `Phi(P)^2`. -/
def frattiniTripleCommutatorValue
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y z : lowerCentralTerm P 0) :
    frattiniSquare P :=
  frattiniSquareCommutatorValue hP hxi hPhiComm hexists
    (lowerCentralTermOneInFrattini hP
      (lowerCentralCommutator P x y)) z

@[simp]
theorem frattiniTripleCommutatorValue_apply_val
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y z : lowerCentralTerm P 0) :
    ((frattiniTripleCommutatorValue
      hP hxi hPhiComm hexists x y z : frattiniSquare P) : P) =
      ⁅⁅(x : P), (y : P)⁆, (z : P)⁆ :=
  rfl

/-- **Higman Lemma 13 (p. 92), the actual triple commutator.**

This is the composition of the actual middle and square-valued brackets,
not an opaque trilinear form supplied as data. -/
noncomputable def frattiniTripleCommutatorTrilinear
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
        Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
          Additive (frattiniSquare P) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact {
    toFun := fun x =>
      (frattiniSquareCommutatorBilinear
        hP hxi hPhiComm hfour hexists).comp
          (frattiniMiddleCommutatorBilinear
            hP hxi hPhiComm hexists x)
    map_add' := by
      intro x y
      ext z w
      simp
    map_smul' := by
      intro c x
      ext z w
      simp }

@[simp]
theorem frattiniTripleCommutatorTrilinear_apply
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y z : Additive (lowerCentralLayer P 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniTripleCommutatorTrilinear
        hP hxi hPhiComm hfour hexists x y z =
      frattiniSquareCommutatorBilinear
        hP hxi hPhiComm hfour hexists
          (frattiniMiddleCommutatorBilinear
            hP hxi hPhiComm hexists x y) z :=
  rfl

/-- Evaluation on representatives is the literal nested commutator
`[[x,y],z]` in `Phi(P)^2`. -/
@[simp]
theorem frattiniTripleCommutatorTrilinear_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y z : lowerCentralTerm P 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniTripleCommutatorTrilinear hP hxi hPhiComm hfour hexists
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) z)) =
      Additive.ofMul
        (frattiniTripleCommutatorValue
          hP hxi hPhiComm hexists x y z) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  rw [frattiniTripleCommutatorTrilinear_apply,
    frattiniMiddleCommutatorBilinear_mk]
  change frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists
      (Additive.ofMul
        (QuotientGroup.mk
          (lowerCentralTermOneInFrattini hP
            (lowerCentralCommutator P x y))))
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0) z)) = _
  rw [frattiniSquareCommutatorBilinear_mk]
  rfl

/-- The representative formula after forgetting the `Phi(P)^2` subtype. -/
@[simp]
theorem frattiniTripleCommutatorTrilinear_mk_apply_val
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y z : lowerCentralTerm P 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    (((frattiniTripleCommutatorTrilinear
        hP hxi hPhiComm hfour hexists
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) z))).toMul :
          frattiniSquare P) : P) =
      ⁅⁅(x : P), (y : P)⁆, (z : P)⁆ := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  rw [frattiniTripleCommutatorTrilinear_mk]
  rfl

/-- The composite triple bracket intertwines the actor on all four
layers. -/
theorem frattiniTripleCommutatorTrilinear_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ (c : Y) (x y z : Additive (lowerCentralLayer P 0)),
      elabRepresentation 2 hSquareInv.restrict c
          (frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists x y z) =
        frattiniTripleCommutatorTrilinear
          hP hxi hPhiComm hfour hexists
          (lowerCentralLayerRepresentation Y.subtype 0 c x)
          (lowerCentralLayerRepresentation Y.subtype 0 c y)
          (lowerCentralLayerRepresentation Y.subtype 0 c z) := by
  dsimp only
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro c x y z
  rw [frattiniTripleCommutatorTrilinear_apply,
    frattiniSquareCommutatorBilinear_equivariant,
    frattiniMiddleCommutatorBilinear_equivariant,
    frattiniTripleCommutatorTrilinear_apply]

end OddOrder.Higman.Suzuki2Groups
