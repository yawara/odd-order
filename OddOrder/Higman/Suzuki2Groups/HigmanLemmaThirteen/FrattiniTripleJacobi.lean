/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniTripleCommutators

/-!
# Higman's Lemma 13: Jacobi in the common Frattini-square layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The actual `Phi(P)^2`-valued triple commutator satisfies Jacobi.  When a
middle commutator vanishes, Jacobi swaps the last two entries.  Applying
the same-factor vanishing theorem gives Higman's swap relation for either
restricted length-three factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance instFrattiniTripleJacobiLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniTripleJacobiLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- In characteristic two, the actual middle Frattini bracket is
symmetric. -/
theorem frattiniMiddleCommutatorBilinear_comm
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (x y : Additive (lowerCentralLayer P 0)),
      frattiniMiddleCommutatorBilinear
          hP hxi hPhiComm hexists x y =
        frattiniMiddleCommutatorBilinear
          hP hxi hPhiComm hexists y x := by
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro x y
  change lowerCentralLayerOneToFrattiniMiddleLinear
      hP hxi hPhiComm hexists
        (lowerCentralCommutatorBilinear P x y) =
    lowerCentralLayerOneToFrattiniMiddleLinear
      hP hxi hPhiComm hexists
        (lowerCentralCommutatorBilinear P y x)
  rw [lowerCentralCommutatorBilinear_comm]

/-- **Higman Lemma 13 (p. 92), Jacobi in `Phi(P)^2`.**

The Jacobi relation is proved on representatives by Hall--Witt and then
descended through the actual trilinear map. -/
theorem frattiniTripleCommutatorTrilinear_jacobi
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
    ∀ (x y z : Additive (lowerCentralLayer P 0)),
      frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists x y z +
          frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists y z x +
          frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists z x y = 0 := by
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
  intro x y z
  obtain ⟨x₀, hx₀⟩ :=
    QuotientGroup.mk'_surjective
      (lowerCentralLayerKernel P 0) x.toMul
  obtain ⟨y₀, hy₀⟩ :=
    QuotientGroup.mk'_surjective
      (lowerCentralLayerKernel P 0) y.toMul
  obtain ⟨z₀, hz₀⟩ :=
    QuotientGroup.mk'_surjective
      (lowerCentralLayerKernel P 0) z.toMul
  have hx : Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x₀) = x := by
    simpa only [ofMul_toMul] using congrArg Additive.ofMul hx₀
  have hy : Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y₀) = y := by
    simpa only [ofMul_toMul] using congrArg Additive.ofMul hy₀
  have hz : Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) z₀) = z := by
    simpa only [ofMul_toMul] using congrArg Additive.ofMul hz₀
  have hconjClass (b c : lowerCentralTerm P 0) :
      QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (b * c * b⁻¹) =
        QuotientGroup.mk' (lowerCentralLayerKernel P 0) c := by
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_comm_assoc]
  have hvalueConj (a b c : lowerCentralTerm P 0) :
      frattiniTripleCommutatorValue hP hxi hPhiComm hexists
          a b (b * c * b⁻¹) =
        frattiniTripleCommutatorValue
          hP hxi hPhiComm hexists a b c := by
    change frattiniSquareCommutatorValue hP hxi hPhiComm hexists
        (lowerCentralTermOneInFrattini hP
          (lowerCentralCommutator P a b)) (b * c * b⁻¹) =
      frattiniSquareCommutatorValue hP hxi hPhiComm hexists
        (lowerCentralTermOneInFrattini hP
          (lowerCentralCommutator P a b)) c
    calc
      _ = frattiniSquareCommutatorBihom
            hP hxi hPhiComm hfour hexists
            (QuotientGroup.mk
              (lowerCentralTermOneInFrattini hP
                (lowerCentralCommutator P a b)))
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
              (b * c * b⁻¹)) :=
          (frattiniSquareCommutatorBihom_mk
            hP hxi hPhiComm hfour hexists
            (lowerCentralTermOneInFrattini hP
              (lowerCentralCommutator P a b)) (b * c * b⁻¹)).symm
      _ = frattiniSquareCommutatorBihom
            hP hxi hPhiComm hfour hexists
            (QuotientGroup.mk
              (lowerCentralTermOneInFrattini hP
                (lowerCentralCommutator P a b)))
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) c) := by
          rw [hconjClass b c]
      _ = _ :=
          frattiniSquareCommutatorBihom_mk
            hP hxi hPhiComm hfour hexists
            (lowerCentralTermOneInFrattini hP
              (lowerCentralCommutator P a b)) c
  have hprodConj :
      frattiniTripleCommutatorValue hP hxi hPhiComm hexists
            x₀ y₀ (y₀ * z₀ * y₀⁻¹) *
          frattiniTripleCommutatorValue hP hxi hPhiComm hexists
            y₀ z₀ (z₀ * x₀ * z₀⁻¹) *
          frattiniTripleCommutatorValue hP hxi hPhiComm hexists
            z₀ x₀ (x₀ * y₀ * x₀⁻¹) = 1 := by
    apply Subtype.ext
    change
      ⁅⁅(x₀ : P), (y₀ : P)⁆,
          (y₀ : P) * (z₀ : P) * (y₀ : P)⁻¹⁆ *
        ⁅⁅(y₀ : P), (z₀ : P)⁆,
          (z₀ : P) * (x₀ : P) * (z₀ : P)⁻¹⁆ *
        ⁅⁅(z₀ : P), (x₀ : P)⁆,
          (x₀ : P) * (y₀ : P) * (x₀ : P)⁻¹⁆ = (1 : P)
    exact commutatorElement_commutatorElement_conj_mul
      (x₀ : P) (y₀ : P) (z₀ : P)
  have hprod :
      frattiniTripleCommutatorValue hP hxi hPhiComm hexists x₀ y₀ z₀ *
          frattiniTripleCommutatorValue hP hxi hPhiComm hexists y₀ z₀ x₀ *
          frattiniTripleCommutatorValue hP hxi hPhiComm hexists z₀ x₀ y₀ = 1 := by
    rw [hvalueConj x₀ y₀ z₀, hvalueConj y₀ z₀ x₀,
      hvalueConj z₀ x₀ y₀] at hprodConj
    exact hprodConj
  rw [← hx, ← hy, ← hz]
  simpa only [frattiniTripleCommutatorTrilinear_mk,
    ofMul_mul, ofMul_one] using congrArg Additive.ofMul hprod

/-- If the middle bracket of `x` and `y` vanishes, then the two triple
commutators with fixed first entry `z` agree. -/
theorem frattiniTripleCommutatorTrilinear_swap_last_of_middle_eq_zero
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
    ∀ (x y z : Additive (lowerCentralLayer P 0)),
      frattiniMiddleCommutatorBilinear
          hP hxi hPhiComm hexists x y = 0 →
        frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists z x y =
          frattiniTripleCommutatorTrilinear
            hP hxi hPhiComm hfour hexists z y x := by
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
  intro x y z hxy
  have hzero :
      frattiniTripleCommutatorTrilinear
          hP hxi hPhiComm hfour hexists x y z = 0 := by
    rw [frattiniTripleCommutatorTrilinear_apply, hxy,
      map_zero, LinearMap.zero_apply]
  have hsym :
      frattiniTripleCommutatorTrilinear
          hP hxi hPhiComm hfour hexists y z x =
        frattiniTripleCommutatorTrilinear
          hP hxi hPhiComm hfour hexists z y x := by
    rw [frattiniTripleCommutatorTrilinear_apply,
      frattiniTripleCommutatorTrilinear_apply,
      frattiniMiddleCommutatorBilinear_comm]
  have hJ := frattiniTripleCommutatorTrilinear_jacobi
    hP hxi hPhiComm hfour hexists z x y
  rw [hzero, add_zero, hsym] at hJ
  exact (eq_neg_of_add_eq_zero_left hJ).trans
    (ZModModule.neg_eq_self _)

/-- **Higman Lemma 13 (p. 92), restricted-factor Jacobi swap.**

For two outer classes represented in one restricted length-three factor,
the `Phi(P)^2`-valued triple commutator is symmetric in those last two
classes. -/
theorem frattiniTripleCommutatorTrilinear_swap_last_of_mem_restricted_factor
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    (y : Additive (lowerCentralLayer P 0))
    (x x' : lowerCentralTerm P 0)
    (hx : (x : P) ∈ S) (hx' : (x' : P) ∈ S) :
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
        hP hxi hPhiComm hfour hexists y
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x')) =
      frattiniTripleCommutatorTrilinear
        hP hxi hPhiComm hfour hexists y
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x'))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)) := by
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
  apply frattiniTripleCommutatorTrilinear_swap_last_of_middle_eq_zero
    hP hxi hPhiComm hfour hexists
  exact frattiniMiddleCommutatorBilinear_eq_zero_of_mem_restricted_factor
    hP hmulti hxi hprime hPhiComm hexists
      hSinv hPhiS hlenS hncommS x x' hx hx'

end OddOrder.Higman.Suzuki2Groups
