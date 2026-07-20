/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.AmbientProductCoordinate

/-!
# Higman Lemma 12: the B/C/D case split (assembly)

G. Higman, *Suzuki 2-groups*, pp. 90--92.  This file assembles the ambient
coordinate infrastructure (`AmbientProductCoordinate`) into the classification
`higmanLemmaTwelve`.  The transported ambient square map, in the `F × F`
coordinate, is `q_P(α, β) = q_X(α) + q_Y(β) + mixed(α, β)`; here the two factor
squares `q_X`, `q_Y` are identified with the type-A quadratic maps, and each
case determines the mixed term.

This first step identifies the factor square `A(α) = ambientCenterCoordinate
(sq_ambient (fI α))` with the factor's own type-A quadratic form `α · θ(α)`
(noncommutative branch) via the three defeq-clean square-extraction lemmas.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative TensorProduct BigOperators

noncomputable section

universe uP

local instance caseSplitLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance caseSplitLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance caseSplitLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}

/-- The noncommutative-branch factor inclusion `F →ₗ Additive L₀`. -/
def noncommFactorInclusion
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    GaloisField 2 n →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  factorInclusion (S.subtype.comp (lowerCentralTerm (↥S) 0).subtype) hK0
    (by
      intro g hg
      rw [lowerCentralLayerKernel_zero_eq_of_squares_le (↥S) data.hSq,
        Subgroup.mem_subgroupOf, data.hterm, Subgroup.mem_subgroupOf] at hg
      exact hg)
    data.eQuot

/-- **Factor square identity, noncommutative branch.**  The ambient square map
of the factor inclusion equals the factor's type-A quadratic form `α · θ(α)`. -/
theorem noncomm_ambientSquare_eq
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    (data :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (α : GaloisField 2 n) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1amb htermamb ePhi
        (lowerCentralSquareMapAdditive P hSqamb
          (noncommFactorInclusion data hK0 α)) =
      α * data.theta α := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  -- Represent `α` through the factor quotient.
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel (↥S) 0)
      (data.eQuot.symm α).toMul
  have hαrep : α = data.eQuot (Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel (↥S) 0) g)) := by
    rw [hg]; exact (data.eQuot.apply_symm_apply α).symm
  set f := S.subtype.comp (lowerCentralTerm (↥S) 0).subtype with hf
  -- Ambient side: `A(α) = ePhi (⟨(f g)², _⟩)`.
  have hmem : (f g : P) ^ 2 ∈ frattini P := by
    rw [← hAgemoamb]
    simpa using Agemo.mem_of_eq_pow (G := P) (p := 2) (n := 1) (f g)
  have hA : ambientCenterCoordinate hEA hK1amb htermamb ePhi
      (lowerCentralSquareMapAdditive P hSqamb (noncommFactorInclusion data hK0 α)) =
      ePhi (Additive.ofMul ⟨(f g : P) ^ 2, hmem⟩) := by
    rw [noncommFactorInclusion, hαrep, factorInclusion_eQuot_mk]
    exact ambientCenterCoordinate_squareMap hEA hK1amb htermamb hSqamb ePhi
      (ambientTermZeroHom f g) hmem
  -- Factor side: `α · θ(α) = ePhi (⟨(f g)², _⟩)`.
  have hfactor : α * data.theta α = ePhi (Additive.ofMul ⟨(f g : P) ^ 2, hmem⟩) := by
    have hsn := data.square_normal α
    have heq : data.eQuot.symm α =
        Additive.ofMul (QuotientGroup.mk' (lowerCentralLayerKernel (↥S) 0) g) := by
      rw [hg]; rfl
    rw [heq, lowerCentralSquareMapAdditive_mk, data.eKernel_eq,
      show (factorLayerOneEquivAmbientFrattini hPhiS data.hK1 data.hterm).toAdditive
          (Additive.ofMul (lowerCentralSquareValue (↥S) data.hSq g)) =
        Additive.ofMul (factorLayerOneEquivAmbientFrattini hPhiS data.hK1 data.hterm
          (lowerCentralSquareValue (↥S) data.hSq g)) from rfl,
      factorLayerOneEquivAmbientFrattini_squareValue hPhiS data.hK1 data.hterm
        data.hSq g hmem] at hsn
    exact hsn.symm
  rw [hA, hfactor]

end

end OddOrder.Higman.Suzuki2Groups
