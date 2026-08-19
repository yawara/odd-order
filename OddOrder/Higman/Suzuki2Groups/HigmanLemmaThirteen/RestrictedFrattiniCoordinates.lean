/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCoordinates

/-!
# Higman's Lemma 13: restricted Frattini coordinates

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For either restricted length-three factor `S`, its internal Frattini
subgroup maps onto the common ambient subgroup `Φ(P)²`.  This file turns
that equality into an explicit `ZMod 2`-linear equivalence and proves that
the equivalence intertwines the restricted factor action with the ambient
action on `Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- The factor's Frattini subgroup, embedded into the ambient group and
identified with `Φ(P)²`. -/
noncomputable def restrictedFrattiniEquivFrattiniSquare
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (hMap : (frattini S).map S.subtype = frattiniSquare P) :
    frattini S ≃* frattiniSquare P :=
  (Subgroup.equivMapOfInjective
      (frattini S) S.subtype S.subtype_injective).trans
    (MulEquiv.subgroupCongr hMap)

/-- The restricted Frattini equivalence is the ambient subtype embedding
on underlying elements. -/
@[simp]
theorem restrictedFrattiniEquivFrattiniSquare_apply_val
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    (x : frattini S) :
    ((restrictedFrattiniEquivFrattiniSquare hMap x :
        frattiniSquare P) : P) = (x : S) := by
  simp [restrictedFrattiniEquivFrattiniSquare,
    Subgroup.coe_equivMapOfInjective_apply,
    MulEquiv.subgroupCongr_apply]

/-- Linear form of the restricted-Frattini identification.  Both module
structures are the canonical ones attached to the corresponding
elementary-abelian groups. -/
noncomputable def restrictedFrattiniLinearEquivFrattiniSquare
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (hFrattiniEA : IsElementaryAbelian 2 (frattini S))
    (hSquareEA : IsElementaryAbelian 2 (frattiniSquare P))
    (hMap : (frattini S).map S.subtype = frattiniSquare P) :
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hFrattiniEA.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hFrattiniEA.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    Additive (frattini S) ≃ₗ[ZMod 2]
      Additive (frattiniSquare P) := by
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hFrattiniEA.comm
  letI : CommGroup (frattini S) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini S)) :=
    hFrattiniEA.zmodModule
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact (MulEquiv.toAdditive
      (restrictedFrattiniEquivFrattiniSquare hMap)).toLinearEquiv
    (fun c x => ZMod.map_smul
      (MulEquiv.toAdditive
        (restrictedFrattiniEquivFrattiniSquare hMap)).toAddMonoidHom c x)

/-- The restricted-Frattini linear equivalence intertwines the action on
the factor's internal Frattini subgroup with the actual ambient action on
`Φ(P)²`. -/
theorem restrictedFrattiniLinearEquivFrattiniSquare_equivariant
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hFrattiniEA : IsElementaryAbelian 2 (frattini S))
    (hSquareEA : IsElementaryAbelian 2 (frattiniSquare P))
    (hMap : (frattini S).map S.subtype = frattiniSquare P) :
    let hFrattiniInv : IsAInvariant hSinv.restrict (frattini S) :=
      IsAInvariant.of_characteristic hSinv.restrict
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hFrattiniEA.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hFrattiniEA.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ (g : Y) (v : Additive (frattini S)),
      restrictedFrattiniLinearEquivFrattiniSquare
          hFrattiniEA hSquareEA hMap
          (elabRepresentation 2 hFrattiniInv.restrict g v) =
        elabRepresentation 2 hSquareInv.restrict g
          (restrictedFrattiniLinearEquivFrattiniSquare
            hFrattiniEA hSquareEA hMap v) := by
  dsimp only
  let hFrattiniInv : IsAInvariant hSinv.restrict (frattini S) :=
    IsAInvariant.of_characteristic hSinv.restrict
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hFrattiniEA.comm
  let : CommGroup (frattini S) := inferInstance
  let : Module (ZMod 2) (Additive (frattini S)) :=
    hFrattiniEA.zmodModule
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro g v
  change restrictedFrattiniLinearEquivFrattiniSquare
        hFrattiniEA hSquareEA hMap
        (elabRepresentation 2 hFrattiniInv.restrict g
          (Additive.ofMul v.toMul)) =
      elabRepresentation 2 hSquareInv.restrict g
        (restrictedFrattiniLinearEquivFrattiniSquare
          hFrattiniEA hSquareEA hMap (Additive.ofMul v.toMul))
  rw [elabRepresentation_apply]
  change Additive.ofMul
        (restrictedFrattiniEquivFrattiniSquare hMap
          (hFrattiniInv.restrict g v.toMul)) =
      elabRepresentation 2 hSquareInv.restrict g
        (Additive.ofMul
          (restrictedFrattiniEquivFrattiniSquare hMap v.toMul))
  rw [elabRepresentation_apply]
  have hmul :
      restrictedFrattiniEquivFrattiniSquare hMap
          (hFrattiniInv.restrict g v.toMul) =
        hSquareInv.restrict g
          (restrictedFrattiniEquivFrattiniSquare hMap v.toMul) := by
    apply Subtype.ext
    rw [restrictedFrattiniEquivFrattiniSquare_apply_val,
      IsAInvariant.restrict_apply_val hSquareInv,
      restrictedFrattiniEquivFrattiniSquare_apply_val,
      IsAInvariant.restrict_apply_val hFrattiniInv,
      IsAInvariant.restrict_apply_val hSinv]
  exact congrArg Additive.ofMul hmul

end OddOrder.Higman.Suzuki2Groups
