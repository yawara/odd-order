/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCommutators

/-!
# Higman's Lemma 13: equivariance of the square-valued commutator

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The bilinear bracket

`Phi(P) / Phi(P)^2 × P / Phi(P) -> Phi(P)^2`

commutes with the Suzuki actor on all three layers.  This is the
equivariance needed to transport the nested commutator into Higman's
simultaneous eigenbasis.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance instFrattiniSquareEquivarianceLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniSquareEquivarianceLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The literal square-valued commutator commutes with the ambient actor
on representatives. -/
theorem frattiniSquareCommutatorValue_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    ∀ (c : Y) (z : frattini P) (x : lowerCentralTerm P 0),
      hSquareInv.restrict c
          (frattiniSquareCommutatorValue
            hP hxi hPhiComm hexists z x) =
        frattiniSquareCommutatorValue hP hxi hPhiComm hexists
          (hPhiInv.restrict c z)
          (lowerCentralTermAction Y.subtype 0 c x) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  intro c z x
  apply Subtype.ext
  change Y.subtype c ⁅(z : P), (x : P)⁆ =
    ⁅((hPhiInv.restrict c z : frattini P) : P),
      ((lowerCentralTermAction Y.subtype 0 c x :
        lowerCentralTerm P 0) : P)⁆
  rw [map_commutatorElement]
  simp only [IsAInvariant.restrict_apply_val]
  congr 1

/-- The descended multiplicative bracket commutes with the actor on all
three quotient layers. -/
theorem frattiniSquareCommutatorBihom_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    ∀ (c : Y) (u : frattiniMiddleLayer P)
        (v : lowerCentralLayer P 0),
      hSquareInv.restrict c
          (frattiniSquareCommutatorBihom
            hP hxi hPhiComm hfour hexists u v) =
        frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
          (actualAgemoOneQuotientAction hPhiInv.restrict c u)
          (lowerCentralLayerAction Y.subtype 0 c v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  intro c u v
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 0) v
  change hSquareInv.restrict c
      (frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
        (QuotientGroup.mk z)
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)) =
    frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
      (QuotientGroup.mk (hPhiInv.restrict c z))
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
        (lowerCentralTermAction Y.subtype 0 c x))
  rw [frattiniSquareCommutatorBihom_mk,
    frattiniSquareCommutatorBihom_mk]
  exact frattiniSquareCommutatorValue_equivariant
    hP hxi hPhiComm hexists c z x

/-- **Higman Lemma 13 (p. 92), equivariance of the square-valued bracket.**

The actual `F₂`-bilinear commutator
`Phi(P)/Phi(P)^2 × P/Phi(P) -> Phi(P)^2` intertwines the actor on all
three layers. -/
theorem frattiniSquareCommutatorBilinear_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
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
    ∀ (c : Y) (u : Additive (frattiniMiddleLayer P))
        (v : Additive (lowerCentralLayer P 0)),
      elabRepresentation 2 hSquareInv.restrict c
          (frattiniSquareCommutatorBilinear
            hP hxi hPhiComm hfour hexists u v) =
        frattiniSquareCommutatorBilinear hP hxi hPhiComm hfour hexists
          (actualAgemoOneQuotientRepresentation
            hPhiInv.restrict c u)
          (lowerCentralLayerRepresentation Y.subtype 0 c v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
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
  intro c u v
  change Additive.ofMul
      (hSquareInv.restrict c
        (frattiniSquareCommutatorBihom
          hP hxi hPhiComm hfour hexists u.toMul v.toMul)) =
    Additive.ofMul
      (frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
        (actualAgemoOneQuotientAction hPhiInv.restrict c u.toMul)
        (lowerCentralLayerAction Y.subtype 0 c v.toMul))
  exact congrArg Additive.ofMul
    (frattiniSquareCommutatorBihom_equivariant
      hP hxi hPhiComm hfour hexists c u.toMul v.toMul)

end OddOrder.Higman.Suzuki2Groups
