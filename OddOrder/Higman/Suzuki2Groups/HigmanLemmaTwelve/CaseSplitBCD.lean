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

/-- The commutative-branch factor inclusion `F →ₗ Additive L₀`. -/
def commFactorInclusion
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : CommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    GaloisField 2 n →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  letI : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := data.hcomm.is_comm.comm }
  letI : IsMulCommutative (↥S ⧸ Agemo (↥S) 2 1) := IsMulCommutative.of_comm mul_comm
  letI : Module (ZMod 2) (Additive (↥S ⧸ Agemo (↥S) 2 1)) :=
    AddCommGroup.zmodModule (fun q => by
      apply Additive.toMul.injective
      change (Additive.toMul q) ^ 2 = 1
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
      rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      simpa using Agemo.mem_of_eq_pow (G := ↥S) (p := 2) (n := 1) x)
  factorInclusion S.subtype hK0
    (fun g hg => by rw [data.hN, Subgroup.mem_subgroupOf] at hg; exact hg)
    { data.eQuot with map_smul' := ZMod.map_smul data.eQuot.toAddMonoidHom }

/-- Bridge lemma for the commutative branch: the factor inclusion sends the
coordinate `data.eQuot [g]` (of the quotient class of `g : ↥S`) to the ambient
class `[S.subtype g]`.  Stated purely through the additive equivalence
`data.eQuot`, so no ambient `↥S ⧸ ℧₁`-module instance leaks into the statement;
this lets `comm_ambientSquare_eq` rewrite through `commFactorInclusion` without
tangling the self-contained instances baked into that definition. -/
theorem commFactorInclusion_eQuot_mk
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : CommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (g : ↥S) :
    commFactorInclusion data hK0
        (data.eQuot (Additive.ofMul (QuotientGroup.mk g))) =
      layerZeroClass (ambientTermZeroHom S.subtype g) := by
  letI : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := data.hcomm.is_comm.comm }
  letI : IsMulCommutative (↥S ⧸ Agemo (↥S) 2 1) := IsMulCommutative.of_comm mul_comm
  letI : Module (ZMod 2) (Additive (↥S ⧸ Agemo (↥S) 2 1)) :=
    AddCommGroup.zmodModule (fun q => by
      apply Additive.toMul.injective
      change (Additive.toMul q) ^ 2 = 1
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
      rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      simpa using Agemo.mem_of_eq_pow (G := ↥S) (p := 2) (n := 1) x)
  rw [commFactorInclusion]
  exact factorInclusion_eQuot_mk S.subtype hK0 _ _ g

/-- **Factor square identity, commutative branch.**  The ambient square map of
the factor inclusion equals `α²` (the type-A quadratic form with `θ = 1`). -/
theorem comm_ambientSquare_eq
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
      CommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
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
          (commFactorInclusion data hK0 α)) =
      α * α := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk_surjective (Additive.toMul (data.eQuot.symm α))
  have hαrep : α = data.eQuot (Additive.ofMul (QuotientGroup.mk g)) := by
    rw [hg]; exact (data.eQuot.apply_symm_apply α).symm
  have hmem : (S.subtype g) ^ 2 ∈ frattini P := by
    rw [← hAgemoamb]
    simpa using Agemo.mem_of_eq_pow (G := P) (p := 2) (n := 1) (S.subtype g)
  -- Ambient side: `A(α) = ePhi (⟨(S.subtype g)², _⟩)`.
  have hA : ambientCenterCoordinate hEA hK1amb htermamb ePhi
      (lowerCentralSquareMapAdditive P hSqamb (commFactorInclusion data hK0 α)) =
      ePhi (Additive.ofMul ⟨(S.subtype g) ^ 2, hmem⟩) := by
    rw [hαrep, commFactorInclusion_eQuot_mk data hK0 g]
    exact ambientCenterCoordinate_squareMap hEA hK1amb htermamb hSqamb ePhi
      (ambientTermZeroHom S.subtype g) hmem
  -- Factor side: `α² = ePhi (⟨(S.subtype g)², _⟩)`.
  have hfactor : α * α = ePhi (Additive.ofMul ⟨(S.subtype g) ^ 2, hmem⟩) := by
    haveI := data.fintypeIndex
    have hsn := data.square_normal α
    have heq : data.eQuot.symm α =
        Additive.ofMul (QuotientGroup.mk g) := by
      rw [hg]; simp
    rw [heq, data.eKernel_eq,
      show ((commutativeFactorSquareEquiv data.hcomm data.equivPi).toAdditive
          (Additive.ofMul (QuotientGroup.mk g))).toMul =
        commutativeFactorSquareEquiv data.hcomm data.equivPi (QuotientGroup.mk g) from rfl,
      homocyclicFourSquareSubgroupEquivFrattini_squareEquiv data.hcomm data.equivPi
        hPhiS data.hN g hmem] at hsn
    exact hsn.symm
  rw [hA, hfactor]

/-! ## Uniform factor-inclusion package for the ambient product -/

/-- One side of the ambient `F × F` coordinate for Higman Lemma 12, packaged
uniformly across the commutative and noncommutative branches.

The branch-specific abstract group `H` maps into `P` by `f`, with normal kernel
`N` cutting out the Frattini classes, and `eQuot` is the branch quotient
coordinate.  The exactness data `hf`/`hfexact` and the identification
`range_eq : f.range = S` feed the ambient product isomorphism; `theta` together
with `ambientSquare` records the factor square law `A(α) = α · θ(α)` (with
`θ = 1` in the commutative branch).  Bundling the branch group `H` lets the four
commutative/noncommutative combinations of the two factors collapse to a single
assembly. -/
structure FactorInclusionData
    {P : Type uP} [Group P] [Finite P]
    (S : Subgroup P) {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) where
  /-- The branch abstract group (`↥S` in the commutative branch, `↥L₀(S)` in the
  noncommutative branch). -/
  H : Type uP
  [group : Group H]
  /-- The factor map into the ambient group. -/
  f : H →* P
  /-- The normal kernel cutting out the Frattini classes. -/
  N : Subgroup H
  [normal : N.Normal]
  [quotComm : IsMulCommutative (H ⧸ N)]
  [quotModule : Module (ZMod 2) (Additive (H ⧸ N))]
  /-- The branch quotient coordinate. -/
  eQuot : Additive (H ⧸ N) ≃ₗ[ZMod 2] GaloisField 2 n
  hf : ∀ g ∈ N, f g ∈ frattini P
  hfexact : ∀ g, f g ∈ frattini P → g ∈ N
  range_eq : f.range = S
  /-- The factor square automorphism; the identity in the commutative branch. -/
  theta : RingAut (GaloisField 2 n)
  ambientSquare : ∀ α,
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1amb htermamb ePhi
        (lowerCentralSquareMapAdditive P hSqamb
          (factorInclusion f hK0 hf eQuot α)) =
      α * theta α

/-- The commutative branch packages into a `FactorInclusionData` with
`H = ↥S`, `f = S.subtype`, `N = ℧₁(S)`, `θ = 1`, and the factor square law
`A(α) = α²` from `comm_ambientSquare_eq`. -/
noncomputable def commFactorInclusionData
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
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
      CommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0 :=
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  letI : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := data.hcomm.is_comm.comm }
  letI : IsMulCommutative (↥S ⧸ Agemo (↥S) 2 1) := IsMulCommutative.of_comm mul_comm
  letI : Module (ZMod 2) (Additive (↥S ⧸ Agemo (↥S) 2 1)) :=
    AddCommGroup.zmodModule (fun q => by
      apply Additive.toMul.injective
      change (Additive.toMul q) ^ 2 = 1
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
      rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      simpa using Agemo.mem_of_eq_pow (G := ↥S) (p := 2) (n := 1) x)
  { H := ↥S
    f := S.subtype
    N := Agemo (↥S) 2 1
    eQuot := { data.eQuot with map_smul' := ZMod.map_smul data.eQuot.toAddMonoidHom }
    hf := fun g hg => by
      rw [data.hN, Subgroup.mem_subgroupOf] at hg; exact hg
    hfexact := fun g hg => by
      rw [data.hN, Subgroup.mem_subgroupOf]; exact hg
    range_eq := Subgroup.range_subtype S
    theta := 1
    ambientSquare := fun α => by
      rw [RingAut.one_apply]
      exact comm_ambientSquare_eq (Y := Y) hEA ePhi data hK1amb htermamb hSqamb
        hAgemoamb hK0 α }

/-- The noncommutative branch packages into a `FactorInclusionData` with
`H = ↥L₀(S)`, `f = S.subtype ∘ L₀(S).subtype`, `N = ℧₁L₀(S) L₁(S)`,
`θ = data.theta`, and the factor square law `A(α) = α · θ(α)` from
`noncomm_ambientSquare_eq`. -/
noncomputable def noncommFactorInclusionData
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
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
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0 :=
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  { H := ↥(lowerCentralTerm (↥S) 0)
    f := S.subtype.comp (lowerCentralTerm (↥S) 0).subtype
    N := lowerCentralLayerKernel (↥S) 0
    eQuot := data.eQuot
    hf := fun g hg => by
      rw [lowerCentralLayerKernel_zero_eq_of_squares_le (↥S) data.hSq,
        Subgroup.mem_subgroupOf, data.hterm, Subgroup.mem_subgroupOf] at hg
      exact hg
    hfexact := fun g hg => by
      rw [lowerCentralLayerKernel_zero_eq_of_squares_le (↥S) data.hSq,
        Subgroup.mem_subgroupOf, data.hterm, Subgroup.mem_subgroupOf]
      exact hg
    range_eq := by
      ext p
      simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply]
      constructor
      · rintro ⟨g, rfl⟩
        exact ((lowerCentralTerm (↥S) 0).subtype g).2
      · intro hp
        have hT : lowerCentralTerm (↥S) 0 = ⊤ := Subgroup.lowerCentralSeries_zero ⊤
        refine ⟨⟨⟨p, hp⟩, ?_⟩, rfl⟩
        rw [hT]; exact Subgroup.mem_top _
    theta := data.theta
    ambientSquare := fun α =>
      noncomm_ambientSquare_eq (Y := Y) hEA ePhi data hK1amb htermamb hSqamb
        hAgemoamb hK0 α }

/-- **Branch dispatch.**  Either factor branch packages uniformly into a
`FactorInclusionData`; the resulting `theta` is `1` in the commutative branch and
`data.theta` in the noncommutative branch, matching `FactorCoordinateData.theta`. -/
noncomputable def FactorCoordinateData.toInclusionData
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
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
      FactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0 :=
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  match data with
  | .commutative d =>
      commFactorInclusionData hEA ePhi d hK1amb htermamb hSqamb hAgemoamb hK0
  | .noncommutative _ d =>
      noncommFactorInclusionData hEA ePhi d hK1amb htermamb hSqamb hAgemoamb hK0

/-- The packaged branch automorphism agrees with `FactorCoordinateData.theta`. -/
theorem FactorCoordinateData.toInclusionData_theta
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
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
      FactorCoordinateData hSinv hPhiS c ePhi nu)
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    (data.toInclusionData hEA ePhi hK1amb htermamb hSqamb hAgemoamb hK0).theta =
      data.theta := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  cases data with
  | commutative d => rfl
  | noncommutative _ d => rfl

/-- The factor inclusion linear map of a package: its branch `factorInclusion`
with the bundled instances resolved.  Exposing it as a map with a clean type
lets downstream statements avoid threading the branch quotient instances. -/
noncomputable def FactorInclusionData.incl
    {P : Type uP} [Group P] [Finite P] {S : Subgroup P} {n : ℕ}
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
    (data : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0) :
    GaloisField 2 n →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  @factorInclusion P _ (GaloisField 2 n) _ _
    data.H data.group data.f data.N data.normal data.quotComm data.quotModule
    hK0 data.hf data.eQuot

/-- The package square law, phrased through `incl`. -/
theorem FactorInclusionData.ambientSquare_incl
    {P : Type uP} [Group P] [Finite P] {S : Subgroup P} {n : ℕ}
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
    (data : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0)
    (α : GaloisField 2 n) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1amb htermamb ePhi
        (lowerCentralSquareMapAdditive P hSqamb (data.incl α)) =
      α * data.theta α :=
  data.ambientSquare α

/-! ## Ambient `F × F` coordinate from two factor packages -/

/-- Assemble the ambient `F × F ≃ₗ Additive L₀` isomorphism from the two factor
inclusion packages, translating the complementarity data of the invariant
factors (`Sₗ ⊓ Sᵣ = Φ(P)`, `Sₗ ⊔ Sᵣ = ⊤`, `Sᵣ` normal, `Φ(P) ≤ Sᵣ`) through
each package's `range_eq`. -/
noncomputable def ambientProductEquivOfFactors
    {P : Type uP} [Group P] [Finite P]
    {Sl Sr : Subgroup P} {n : ℕ}
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
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal)
    (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤)
    (hΦR : frattini P ≤ Sr) :
    (GaloisField 2 n × GaloisField 2 n) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0) :=
  @ambientProductEquiv P _ (GaloisField 2 n) _ _
    left.H left.group left.f left.N left.normal left.quotComm left.quotModule
    right.H right.group right.f right.N right.normal right.quotComm right.quotModule
    hK0 left.hf left.eQuot right.hf right.eQuot
    left.hfexact right.hfexact
    (by rw [right.range_eq]; exact hRnormal)
    (by rw [left.range_eq, right.range_eq]; exact hinf)
    (by rw [left.range_eq, right.range_eq]; exact hsup)
    (by rw [right.range_eq]; exact hΦR)

/-- The assembled coordinate sends `(α, β)` to the sum of the two factor
inclusions. -/
@[simp]
theorem ambientProductEquivOfFactors_apply
    {P : Type uP} [Group P] [Finite P]
    {Sl Sr : Subgroup P} {n : ℕ}
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
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (α β : GaloisField 2 n) :
    ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR (α, β) =
      left.incl α + right.incl β :=
  rfl

/-- **Higman Lemma 12 (p. 90), the ambient square in the `F × F` coordinate.**
The ambient centre coordinate of the square of `(α, β)` decomposes as the two
factor squares `q_X(α) = α · θ_L(α)`, `q_Y(β) = β · θ_R(β)` plus the mixed
commutator term.  This is the `Q(α, β) = q_X(α) + q_Y(β) + M(α, β)` state feeding
the B/C/D case split; the mixed term's case-specific value follows from the
Frobenius weight equation. -/
theorem ambientProductSquare_eq
    {P : Type uP} [Group P] [Finite P]
    {Sl Sr : Subgroup P} {n : ℕ}
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
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (α β : GaloisField 2 n) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1amb htermamb ePhi
        (lowerCentralSquareMapAdditive P hSqamb
          (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR (α, β))) =
      α * left.theta α + β * right.theta β +
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralCommutatorBilinear P (left.incl α) (right.incl β)) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  rw [ambientProductEquivOfFactors_apply,
    centerSquareMap_add hSqamb (ambientCenterCoordinate hEA hK1amb htermamb ePhi)
      (left.incl α) (right.incl β),
    left.ambientSquare_incl α, right.ambientSquare_incl β]

/-! ## Coordinates of the ambient central extension -/

section ExtensionCoordinates

variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
variable [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
variable
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (e : (F × F) ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] F)

/-- The `F × F` coordinate of `x` under the ambient central extension: the layer
kernel projection followed by `e⁻¹`. -/
theorem ambientProductExtension_rightHom_toAdd (x : P) :
    ((ambientProductExtension hK0 e ePhi).rightHom x).toAdd =
      e.symm (Additive.ofMul
        (frattiniQuotientEquivLayerZero hK0 (QuotientGroup.mk x))) :=
  rfl

/-- The Singer embedding of a coordinate `f : F` back into `P` under the ambient
central extension. -/
theorem ambientProductExtension_inl_ofAdd (f : F) :
    (ambientProductExtension hK0 e ePhi).inl (Multiplicative.ofAdd f) =
      (frattini P).subtype (Additive.toMul (ePhi.symm f)) :=
  rfl

end ExtensionCoordinates

/-- **Higman Lemma 12, the case-assembly glue.**  If the ambient centre
coordinate of every square agrees with a quadratic map `q` on the `F × F`
coordinate, then the ambient central extension `ambientProductExtension`
satisfies the type-B/C/D `ofExtension` square obligation `hsq`.  The hypothesis
`hQ` is exactly the case conclusion `Q(α, β) = q(α, β)`; combining it with the
`Q = q_X + q_Y + M` decomposition and the case-specific value of `M` closes each
of the B/C/D cases. -/
theorem ambientProductExtension_hsq_of_coordinate
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
    (e : (GaloisField 2 n × GaloisField 2 n) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ w, ambientCenterCoordinate hEA hK1amb htermamb ePhi
        (lowerCentralSquareMapAdditive P hSqamb (e w)) = q w)
    (x : P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    x ^ 2 = (ambientProductExtension hK0 e ePhi).inl
      (Multiplicative.ofAdd
        (q ((ambientProductExtension hK0 e ePhi).rightHom x).toAdd)) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hxrepP : (((lowerCentralTermZeroEquivAmbient P).symm x :
      lowerCentralTerm P 0) : P) = x := rfl
  have hmem : (((lowerCentralTermZeroEquivAmbient P).symm x :
      lowerCentralTerm P 0) : P) ^ 2 ∈ frattini P := by
    rw [hxrepP, ← hAgemoamb]
    simpa using Agemo.mem_of_eq_pow (G := P) (p := 2) (n := 1) x
  have hw : ((ambientProductExtension hK0 e ePhi).rightHom x).toAdd =
      e.symm (layerZeroClass ((lowerCentralTermZeroEquivAmbient P).symm x)) := by
    rw [ambientProductExtension_rightHom_toAdd]
    congr 1
  have hq : q ((ambientProductExtension hK0 e ePhi).rightHom x).toAdd =
      ePhi (Additive.ofMul ⟨(((lowerCentralTermZeroEquivAmbient P).symm x :
        lowerCentralTerm P 0) : P) ^ 2, hmem⟩) := by
    rw [hw, ← hQ, e.apply_symm_apply]
    exact ambientCenterCoordinate_squareMap hEA hK1amb htermamb hSqamb ePhi
      ((lowerCentralTermZeroEquivAmbient P).symm x) hmem
  rw [hq, ambientProductExtension_inl_ofAdd, ePhi.symm_apply_apply]
  rfl

/-- **Higman Lemma 12, the ambient extension square obligation for the actual
form.**  The ambient central extension built from the two factor packages
satisfies `ofExtension`'s `hsq` with the *actual* square form
`Q(α, β) = α · θ_L(α) + β · θ_R(β) + M(α, β)`.  The B/C/D case assembly then only
has to rewrite this `Q` into the case's `typeB/C/D` quadratic map (via the
case-specific value of the mixed term `M`) before invoking the corresponding
`ofExtension`. -/
theorem ambientProductExtension_hsq_actual
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
    (x : P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    x ^ 2 = (ambientProductExtension hK0
        (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR) ePhi).inl
      (Multiplicative.ofAdd
        ((fun w : GaloisField 2 n × GaloisField 2 n =>
            w.1 * left.theta w.1 + w.2 * right.theta w.2 +
              ambientCenterCoordinate hEA hK1amb htermamb ePhi
                (lowerCentralCommutatorBilinear P
                  (left.incl w.1) (right.incl w.2)))
          ((ambientProductExtension hK0
              (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
              ePhi).rightHom x).toAdd)) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  refine ambientProductExtension_hsq_of_coordinate hEA hK1amb htermamb hSqamb
    hAgemoamb hK0 ePhi
    (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR)
    (fun w : GaloisField 2 n × GaloisField 2 n =>
      w.1 * left.theta w.1 + w.2 * right.theta w.2 +
        ambientCenterCoordinate hEA hK1amb htermamb ePhi
          (lowerCentralCommutatorBilinear P (left.incl w.1) (right.incl w.2)))
    ?_ x
  intro w
  exact ambientProductSquare_eq left right hRnormal hinf hsup hΦR w.1 w.2

/-! ## Actor-equivariance of the factor inclusion (mixed-term prerequisite) -/

/-- **Actor-equivariance of the factor inclusion.**  When the factor
representation `fRep` covers the ambient actor `a` (through `sigma`, with
`hf_int` recording that `f ∘ sigma = a ∘ f`), the factor inclusion intertwines
`fRep` with the ambient zeroth-layer representation.  This transports
`quotientToAmbientLayerZeroLinear_equivariant` through the coordinate `eQuot`,
and it is the actor half of Higman's mixed-term analysis: the mixed commutator
`M(α, β)` inherits the eigenvalue `ν = λ · θ(λ)` from the factor eigenvalues. -/
theorem factorInclusion_representation_equivariant
    {G : Type uP} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)] [Module (ZMod 2) (Additive (G ⧸ N))]
    {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (a : Y)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (eQuot : Additive (G ⧸ N) ≃ₗ[ZMod 2] F)
    (fRep : Additive (G ⧸ N) →ₗ[ZMod 2] Additive (G ⧸ N))
    (sigma : G → G)
    (hfRep : ∀ g, fRep (Additive.ofMul (QuotientGroup.mk' N g)) =
      Additive.ofMul (QuotientGroup.mk' N (sigma g)))
    (hf_int : ∀ g, f (sigma g) = (Y.subtype a : MulAut P) (f g))
    (v : Additive (G ⧸ N)) :
    factorInclusion f hK0 hf eQuot (eQuot (fRep v)) =
      lowerCentralLayerRepresentation Y.subtype 0 a
        (factorInclusion f hK0 hf eQuot (eQuot v)) := by
  simp only [factorInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact quotientToAmbientLayerZeroLinear_equivariant f a hK0 hf fRep sigma hfRep
    hf_int v

/-- **Actor-equivariance of the ambient mixed term.**  In the ambient centre
coordinate the mixed commutator pairing scales by the central eigenvalue `ν`
when both arguments are moved by the actor `c`.  This is the composition of the
bilinear equivariance with `ambientCenterCoordinate_compat`; instantiated at
`u = left.incl α`, `v = right.incl β` (with the factor incl-equivariance) it
gives Higman's `M(λα, μβ) = ν · M(α, β)`. -/
theorem mixedTerm_rep_equivariance
    {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P)
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (c : Y) (nu : GaloisField 2 n)
    (hconj :
      let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
        IsAInvariant.of_characteristic Y.subtype
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (u v : Additive (lowerCentralLayer P 0)) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralCommutatorBilinear P
          (Additive.ofMul (lowerCentralLayerAction Y.subtype 0 c (Additive.toMul u)))
          (Additive.ofMul
            (lowerCentralLayerAction Y.subtype 0 c (Additive.toMul v)))) =
      nu * ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralCommutatorBilinear P u v) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  rw [← lowerCentralCommutatorBilinear_equivariant Y.subtype c u v]
  exact ambientCenterCoordinate_compat hEA hK1 hterm ePhi c nu hconj _

/-- **Higman's mixed-term eigenvalue relation `M(λα, μβ) = ν · M(α, β)`.**
For two factor inclusions `fL`, `fR` whose ambient actor images are the scalars
`λ`, `μ` on their coordinate fields (`hL`, `hR`), the ambient mixed term scales
by `ν` under `(α, β) ↦ (λα, μβ)`.  This is the eigenvalue functional equation
that, together with `ν = λ θ(λ) = μ φ(μ)` and the Frobenius weight equation,
pins the mixed term to its type-B/C/D form. -/
theorem mixedTerm_lambda_equivariance
    {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P)
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (c : Y) (nu : GaloisField 2 n)
    (hconj :
      let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
        IsAInvariant.of_characteristic Y.subtype
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (fL fR : GaloisField 2 n →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (lam mu : GaloisField 2 n)
    (hL : ∀ α, lowerCentralLayerRepresentation Y.subtype 0 c (fL α) = fL (lam • α))
    (hR : ∀ β, lowerCentralLayerRepresentation Y.subtype 0 c (fR β) = fR (mu • β))
    (α β : GaloisField 2 n) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralCommutatorBilinear P (fL (lam • α)) (fR (mu • β))) =
      nu * ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralCommutatorBilinear P (fL α) (fR β)) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  rw [← hL α, ← hR β]
  exact mixedTerm_rep_equivariance hEA hK1 hterm ePhi c nu hconj (fL α) (fR β)

end

end OddOrder.Higman.Suzuki2Groups
