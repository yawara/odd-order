/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseSplitBCD
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Higman.Suzuki2Groups.HigmanTypesCD

/-!
# Higman Lemma 12: the B/C/D classification endpoint

G. Higman, *Suzuki 2-groups*, pp. 90--92.  Each of the three cases assembles the
`Q = q_X + q_Y + M` decomposition (`CaseSplitBCD`) into one of the concrete
type-B/C/D classifications, by rewriting the actual square form `Q` into the
corresponding quadratic map once the mixed term `M` is known.

This file provides the per-case endpoint engines, each parametrised by the
case-specific value of the mixed term `M` (the remaining Higman input from the
Frobenius weight equation).  Given that value, the engine discharges the
`ofExtension` square obligation via `ambientProductExtension_hsq_actual` and
produces the honest type data.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

local instance classifLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance classifLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance classifLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P] [Finite P]

/-- **Higman Lemma 12, type-B endpoint (parametrised by the mixed term).**
When both invariant factors carry the automorphism `φ` and the ambient mixed
term is the type-B pairing `M(α, β) = ε · α · φ(β)`, the actual square form `Q`
becomes the type-B quadratic map, so `P` is a genuine `B(n, φ, ε)`. -/
theorem isTypeB_of_mixedTerm
    {Sl Sr : Subgroup P} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (phi : RingAut (GaloisField 2 n))
    (hthetaL : left.theta = phi) (hthetaR : right.theta = phi)
    (phi_odd : Odd (orderOf phi))
    (epsilon : (GaloisField 2 n)ˣ)
    (hEpsilon : IsTypeBEpsilon phi (epsilon : GaloisField 2 n))
    (n_pos : 0 < n)
    (card_field : Nat.card (GaloisField 2 n) = 2 ^ n)
    (hcentral :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      (ambientProductExtension hK0
          (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
          ePhi).inl.range ≤ Subgroup.center P)
    (hM :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralCommutatorBilinear P (left.incl α) (right.incl β)) =
        (epsilon : GaloisField 2 n) * (α * phi β)) :
    IsTypeB.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  refine ⟨TypeBData.ofExtension n n_pos card_field phi phi_odd epsilon hEpsilon
    (ambientProductExtension hK0
      (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR) ePhi)
    hcentral ?_⟩
  intro x
  refine ambientProductExtension_hsq_of_coordinate hEA hK1amb htermamb hSqamb
    hAgemoamb hK0 ePhi
    (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
    (typeBQuadraticMap phi (epsilon : GaloisField 2 n)) ?_ x
  rintro ⟨a, b⟩
  rw [ambientProductSquare_eq left right hRnormal hinf hsup hΦR a b,
    typeBQuadraticMap_apply, hthetaL, hthetaR, hM]
  ring

/-- **Higman Lemma 12, type-B endpoint (parametrised by an arbitrary
coordinate).**  The same engine as `isTypeB_of_mixedTerm`, but for any linear
coordinate `e` of the zeroth layer whose transported square form is the type-B
quadratic map.  The B case with `θ = φ ≠ 1` enters through the sheared
coordinate `(shearRescaleLinearEquiv ρ t ht).trans e`, which removes the
`θ(α)·β` monomial of the mixed term. -/
theorem isTypeB_of_squareCoordinate
    {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (e :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      (GaloisField 2 n × GaloisField 2 n) ≃ₗ[ZMod 2]
        Additive (lowerCentralLayer P 0))
    (phi : RingAut (GaloisField 2 n))
    (phi_odd : Odd (orderOf phi))
    (epsilon : (GaloisField 2 n)ˣ)
    (hEpsilon : IsTypeBEpsilon phi (epsilon : GaloisField 2 n))
    (n_pos : 0 < n)
    (card_field : Nat.card (GaloisField 2 n) = 2 ^ n)
    (hcentral :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      (ambientProductExtension hK0 e ePhi).inl.range ≤ Subgroup.center P)
    (hq :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ w : GaloisField 2 n × GaloisField 2 n,
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralSquareMapAdditive P hSqamb (e w)) =
        typeBQuadraticMap phi (epsilon : GaloisField 2 n) w) :
    IsTypeB.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  exact ⟨TypeBData.ofExtension n n_pos card_field phi phi_odd epsilon hEpsilon
    (ambientProductExtension hK0 e ePhi) hcentral
    (fun x => ambientProductExtension_hsq_of_coordinate hEA hK1amb htermamb
      hSqamb hAgemoamb hK0 ePhi e
      (typeBQuadraticMap phi (epsilon : GaloisField 2 n)) hq x)⟩

/-- **Higman Lemma 12, type-C endpoint (parametrised by the mixed term).**
The left factor carries `θ` (with `2θ² = 1`), the right factor is commutative,
and the mixed term is the type-C pairing `M(α, β) = ε · (α^{1/2} · (2θ)(β))`. -/
theorem isTypeC_of_mixedTerm
    {Sl Sr : Subgroup P} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (theta : RingAut (GaloisField 2 n))
    (hthetaL : left.theta = theta) (hthetaR : right.theta = 1)
    (theta_two_sq : frobeniusEquiv (GaloisField 2 n) 2 * theta ^ 2 = 1)
    (epsilon : (GaloisField 2 n)ˣ)
    (hEpsilon : IsTypeCEpsilon theta (epsilon : GaloisField 2 n))
    (n_pos : 0 < n)
    (card_field : Nat.card (GaloisField 2 n) = 2 ^ n)
    (hcentral :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      (ambientProductExtension hK0
          (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
          ePhi).inl.range ≤ Subgroup.center P)
    (hM :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralCommutatorBilinear P (left.incl α) (right.incl β)) =
        (epsilon : GaloisField 2 n) *
          ((frobeniusEquiv (GaloisField 2 n) 2)⁻¹ α *
            (frobeniusEquiv (GaloisField 2 n) 2 * theta) β)) :
    IsTypeC.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  refine ⟨TypeCData.ofExtension n n_pos card_field theta theta_two_sq epsilon
    hEpsilon
    (ambientProductExtension hK0
      (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR) ePhi)
    hcentral ?_⟩
  intro x
  refine ambientProductExtension_hsq_of_coordinate hEA hK1amb htermamb hSqamb
    hAgemoamb hK0 ePhi
    (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
    (typeCQuadraticMap theta (epsilon : GaloisField 2 n)) ?_ x
  rintro ⟨a, b⟩
  rw [ambientProductSquare_eq left right hRnormal hinf hsup hΦR a b,
    typeCQuadraticMap_apply, hthetaL, hthetaR, hM, RingAut.one_apply]
  ring

/-- **Higman Lemma 12, type-D endpoint (parametrised by the mixed term).**
The left factor carries `θ` (with `θ⁵ = 1 ≠ θ`), the right factor carries `θ²`,
and the mixed term is the type-D pairing `M(α, β) = ε · (θ³(α) · θ(β))`. -/
theorem isTypeD_of_mixedTerm
    {Sl Sr : Subgroup P} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (theta : RingAut (GaloisField 2 n))
    (hthetaL : left.theta = theta) (hthetaR : right.theta = theta ^ 2)
    (theta_pow_five : theta ^ 5 = 1) (theta_ne_one : theta ≠ 1)
    (epsilon : (GaloisField 2 n)ˣ)
    (hEpsilon : IsTypeDEpsilon theta (epsilon : GaloisField 2 n))
    (n_pos : 0 < n)
    (card_field : Nat.card (GaloisField 2 n) = 2 ^ n)
    (hcentral :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      (ambientProductExtension hK0
          (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
          ePhi).inl.range ≤ Subgroup.center P)
    (hM :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralCommutatorBilinear P (left.incl α) (right.incl β)) =
        (epsilon : GaloisField 2 n) * ((theta ^ 3) α * theta β)) :
    IsTypeD.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  refine ⟨TypeDData.ofExtension n n_pos card_field theta theta_pow_five
    theta_ne_one epsilon hEpsilon
    (ambientProductExtension hK0
      (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR) ePhi)
    hcentral ?_⟩
  intro x
  refine ambientProductExtension_hsq_of_coordinate hEA hK1amb htermamb hSqamb
    hAgemoamb hK0 ePhi
    (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
    (typeDQuadraticMap theta (epsilon : GaloisField 2 n)) ?_ x
  rintro ⟨a, b⟩
  rw [ambientProductSquare_eq left right hRnormal hinf hsup hΦR a b,
    typeDQuadraticMap_apply, hthetaL, hthetaR, hM]
  ring

end

end OddOrder.Higman.Suzuki2Groups
