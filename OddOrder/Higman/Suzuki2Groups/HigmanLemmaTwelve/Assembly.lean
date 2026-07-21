/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Classification

/-!
# Higman Lemma 12: assembling the B/C/D classification

G. Higman, *Suzuki 2-groups*, pp. 90--92.  This file connects the actual
mixed term of the two complementary factors (`mixedTermBilinear`) to the
case-dispatch normalizations (`CaseDispatch`) and the per-case endpoint
engines (`Classification`), assembling `higmanLemmaTwelve`.

The pre-case-split state (`exists_mixedFrobeniusWeightEquation_of_xiLengthThree`)
supplies the complementary factors, their coordinate data over a common
ambient Singer datum, and the eigenvalue equations `ν = λθ(λ) = μφ(μ)`.  The
remaining steps are: coordinates for the noncommuting witness (so the mixed
term is a nonzero bilinear map), the Frobenius support extraction per case,
the shear normalization (case `θ = φ ≠ 1`), the `ε` conditions from
anisotropy, and the endpoint engines.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

local instance assemblyLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance assemblyLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance assemblyLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}

/-! ## Coordinates for the noncommuting witness -/

/-- **The actual mixed term is a nonzero bilinear map.**  The noncommuting
mixed-factor witness of the complementary factors has coordinates under the
packaged inclusions, and the ambient centre coordinate is injective, so the
bundled mixed term does not vanish identically.  This is the `hM0` input of
the Frobenius support extraction. -/
theorem exists_mixedTermBilinear_ne_zero
    {n : ℕ}
    (factors : XiLengthThreeTypeAFactorData P Y)
    {hEA : IsElementaryAbelian 2 ↑(frattini P)}
    {ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {hK1amb : lowerCentralLayerKernel P 1 = ⊥}
    {htermamb : lowerCentralTerm P 1 = frattini P}
    {hSqamb : LowerCentralSquaresLieInSecond P}
    {hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)}
    (left : FactorInclusionData factors.left hEA ePhi hK1amb htermamb
      hSqamb hK0)
    (right : FactorInclusionData factors.right hEA ePhi hK1amb htermamb
      hSqamb hK0)
    (hxi : IsXiActor Y)
    (hinvPhi : involutions P ⊆ frattini P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ∃ α β : GaloisField 2 n, mixedTermBilinear left right α β ≠ 0 := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  obtain ⟨x, y, hxL, hyR, hne⟩ :=
    factors.exists_mixed_lowerCentralCommutatorBilinear_ne_zero
      hxi hinvPhi hEA hK1amb
  obtain ⟨α, hα⟩ := left.exists_incl_eq x hxL
  obtain ⟨β, hβ⟩ := right.exists_incl_eq y hyR
  refine ⟨α, β, ?_⟩
  rw [mixedTermBilinear_apply, hα, hβ]
  intro hzero
  exact hne ((LinearEquiv.map_eq_zero_iff
    (ambientCenterCoordinate hEA hK1amb htermamb ePhi)).mp hzero)

end

end OddOrder.Higman.Suzuki2Groups
