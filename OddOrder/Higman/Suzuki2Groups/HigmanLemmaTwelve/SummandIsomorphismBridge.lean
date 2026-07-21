/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SummandIsomorphism
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE

/-!
# Isomorphic central-quotient summands force Frobenius-conjugate eigenvalues

G. Higman, *Suzuki 2-groups*; T. Peterfalvi, Appendix III, Theorem (e),
p. 141.

The two invariant factors of a ξ-length-3 Suzuki 2-group project onto the two
complementary summands of `P ⧸ Z(P)` (with `Z(P) = Φ(P)`).  This file
converts a `K`-equivariant *group* isomorphism between those summands into a
`ZMod 2`-linear semiconjugation between the factors' Singer coordinates, and
concludes `μ = λ^{2^i}` by `exists_frobenius_conjugate_of_semiconj`.

The conversion goes through the ambient zeroth lower-central layer: the map
`layerZeroToQuotient` identifies `L₀ = P ⧸ (P²·P₂)` with `P ⧸ Z` whenever the
layer denominator equals `Z`, each packaged factor inclusion
(`FactorInclusionData.incl`) then lands bijectively on the corresponding
summand, and the equivariant isomorphism transports along these coordinates.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups (KEquivariantMulEquiv)
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

local instance summandBridgeLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance summandBridgeLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance summandBridgeLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P]

/-! ## From the ambient zeroth layer to the central quotient -/

section LayerZeroToQuotient

variable (Z : Subgroup P) [Z.Normal]
variable (hK0Z : lowerCentralLayerKernel P 0 =
    Z.subgroupOf (lowerCentralTerm P 0))

/-- Descend the inclusion of the zeroth lower-central term to the central
quotient.  When the layer denominator `P²·P₂` equals `Z` (as it does for
`Z = Φ(P) = Z(P)` in the ξ-length-3 setting), this maps `L₀` to `P ⧸ Z`. -/
def layerZeroToQuotient : lowerCentralLayer P 0 →* P ⧸ Z :=
  QuotientGroup.lift (lowerCentralLayerKernel P 0)
    ((QuotientGroup.mk' Z).comp (lowerCentralTerm P 0).subtype)
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [hK0Z, Subgroup.mem_subgroupOf] at hx
      exact hx)

@[simp]
theorem layerZeroToQuotient_mk (x : ↥(lowerCentralTerm P 0)) :
    layerZeroToQuotient Z hK0Z
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x) =
      QuotientGroup.mk' Z (x : P) := rfl

/-- The layer-to-quotient map is injective: its kernel is cut out by exactly
the layer denominator. -/
theorem layerZeroToQuotient_injective :
    Function.Injective (layerZeroToQuotient Z hK0Z) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 0) q
  rw [MonoidHom.mem_ker, layerZeroToQuotient_mk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hq
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    hK0Z]
  exact Subgroup.mem_subgroupOf.mpr hq

/-- The layer-to-quotient map intertwines the induced layer action with the
induced quotient action. -/
theorem layerZeroToQuotient_equivariant
    {X : Type*} [Group X] (phi : X →* MulAut P)
    (hZinv : IsAInvariant phi Z) (a : X) (q : lowerCentralLayer P 0) :
    layerZeroToQuotient Z hK0Z (lowerCentralLayerAction phi 0 a q) =
      IsAInvariant.quotientMulAutHom hZinv a
        (layerZeroToQuotient Z hK0Z q) := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 0) q
  rw [lowerCentralLayerAction_apply_mk, layerZeroToQuotient_mk,
    layerZeroToQuotient_mk, IsAInvariant.quotientMulAutHom_apply_mk']
  rfl

end LayerZeroToQuotient

/-! ## The summand coordinate of a packaged factor inclusion -/

section SummandSemiconj

variable [Finite P] {Y : Subgroup (MulAut P)}
variable {n : ℕ}
variable {hEA : IsElementaryAbelian 2 ↑(frattini P)}
variable {ePhi :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
variable {hK1amb : lowerCentralLayerKernel P 1 = ⊥}
variable {htermamb : lowerCentralTerm P 1 = frattini P}
variable {hSqamb : LowerCentralSquaresLieInSecond P}
variable {hK0 : lowerCentralLayerKernel P 0 =
    (frattini P).subgroupOf (lowerCentralTerm P 0)}

/-- **Equivariantly isomorphic central-quotient summands force
Frobenius-conjugate factor eigenvalues** (Peterfalvi Appendix III,
Theorem (e), the arithmetic obstruction).

Each packaged factor inclusion composes with `layerZeroToQuotient` to a
bijective coordinate of the corresponding summand `S.map (mk' Z)` of
`P ⧸ Z`, equivariant for the actor eigenvalue laws `hrepL`/`hrepR`.  A
`K`-equivariant isomorphism `e` between the two summands therefore reads, in
these coordinates, as a nonzero `ZMod 2`-linear map semiconjugating
multiplication by `lamL` to multiplication by `lamR`, and
`exists_frobenius_conjugate_of_semiconj` yields `lamR = lamL^{2^i}`. -/
theorem exists_frobenius_conjugate_of_summandEquiv
    {Sl Sr : Subgroup P} (hn : n ≠ 0)
    (L : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (R : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    {Z : Subgroup P} [Z.Normal] (hZinv : IsAInvariant Y.subtype Z)
    (hZPhi : Z = frattini P)
    (c : Y) (lamL lamR : GaloisField 2 n)
    (hrepL : ∀ α, lowerCentralLayerRepresentation Y.subtype 0 c (L.incl α) =
      L.incl (lamL • α))
    (hrepR : ∀ α, lowerCentralLayerRepresentation Y.subtype 0 c (R.incl α) =
      R.incl (lamR • α))
    (hVL : IsAInvariant (IsAInvariant.quotientMulAutHom hZinv)
      (Sl.map (QuotientGroup.mk' Z)))
    (hVR : IsAInvariant (IsAInvariant.quotientMulAutHom hZinv)
      (Sr.map (QuotientGroup.mk' Z)))
    (e : KEquivariantMulEquiv hVL.restrict hVR.restrict) :
    ∃ i : Fin n, lamR = lamL ^ 2 ^ (i : ℕ) := by
  classical
  letI := L.group
  letI := L.normal
  letI := L.quotComm
  letI := L.quotModule
  letI := R.group
  letI := R.normal
  letI := R.quotComm
  letI := R.quotModule
  have hK0Z : lowerCentralLayerKernel P 0 =
      Z.subgroupOf (lowerCentralTerm P 0) := by rw [hZPhi]; exact hK0
  -- the raw summand coordinates
  set xiL : GaloisField 2 n → P ⧸ Z := fun α =>
    layerZeroToQuotient Z hK0Z (L.incl α).toMul with hxiLdef
  set xiR : GaloisField 2 n → P ⧸ Z := fun α =>
    layerZeroToQuotient Z hK0Z (R.incl α).toMul with hxiRdef
  -- membership in the summands
  have hmem : ∀ {S : Subgroup P}
      (D : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0) (α),
      layerZeroToQuotient Z hK0Z (D.incl α).toMul ∈
        S.map (QuotientGroup.mk' Z) := by
    intro S D α
    letI := D.group
    letI := D.normal
    letI := D.quotComm
    letI := D.quotModule
    have hr : D.incl α ∈
        LinearMap.range (factorInclusion D.f hK0 D.hf D.eQuot) := ⟨α, rfl⟩
    obtain ⟨x, hxrange, hlayer⟩ :=
      (factorInclusion_range_eq D.f hK0 D.hf D.eQuot (D.incl α)).mp hr
    rw [D.range_eq] at hxrange
    have hxi : layerZeroToQuotient Z hK0Z (D.incl α).toMul =
        QuotientGroup.mk' Z (x : P) := by
      rw [← hlayer]
      rfl
    rw [hxi]
    exact ⟨(x : P), hxrange, rfl⟩
  -- injectivity of the summand coordinates
  have hinj : ∀ {S : Subgroup P}
      (D : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0),
      Function.Injective
        (fun α => layerZeroToQuotient Z hK0Z (D.incl α).toMul) := by
    intro S D
    letI := D.group
    letI := D.normal
    letI := D.quotComm
    letI := D.quotModule
    intro a b hab
    have h1 : (D.incl a).toMul = (D.incl b).toMul :=
      layerZeroToQuotient_injective Z hK0Z hab
    have h2 : D.incl a = D.incl b := Additive.toMul.injective h1
    exact factorInclusion_injective D.f hK0 D.hf D.eQuot D.hfexact h2
  -- surjectivity onto the summands
  have hsurj : ∀ {S : Subgroup P}
      (D : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0)
      (v : ↥(S.map (QuotientGroup.mk' Z))),
      ∃ α, layerZeroToQuotient Z hK0Z (D.incl α).toMul = (v : P ⧸ Z) := by
    intro S D v
    letI := D.group
    letI := D.normal
    letI := D.quotComm
    letI := D.quotModule
    obtain ⟨s, hs, hval⟩ := v.property
    have hs' : s ∈ D.f.range := by rw [D.range_eq]; exact hs
    obtain ⟨g, rfl⟩ := hs'
    refine ⟨D.eQuot (Additive.ofMul (QuotientGroup.mk' D.N g)), ?_⟩
    have hincl : D.incl (D.eQuot (Additive.ofMul (QuotientGroup.mk' D.N g))) =
        layerZeroClass (ambientTermZeroHom D.f g) :=
      factorInclusion_eQuot_mk D.f hK0 D.hf D.eQuot g
    rw [hincl]
    exact hval
  -- equivariance of the summand coordinates
  have hact : ∀ {S : Subgroup P}
      (D : FactorInclusionData S hEA ePhi hK1amb htermamb hSqamb hK0)
      (lam : GaloisField 2 n)
      (hrep : ∀ α, lowerCentralLayerRepresentation Y.subtype 0 c (D.incl α) =
        D.incl (lam • α)) (α : GaloisField 2 n),
      layerZeroToQuotient Z hK0Z (D.incl (lam • α)).toMul =
        IsAInvariant.quotientMulAutHom hZinv c
          (layerZeroToQuotient Z hK0Z (D.incl α).toMul) := by
    intro S D lam hrep α
    have h1 : (D.incl (lam • α)).toMul =
        lowerCentralLayerAction Y.subtype 0 c (D.incl α).toMul := by
      have h := (hrep α).symm
      have h2 : lowerCentralLayerRepresentation Y.subtype 0 c (D.incl α) =
          Additive.ofMul
            (lowerCentralLayerAction Y.subtype 0 c (D.incl α).toMul) :=
        lowerCentralLayerRepresentation_apply Y.subtype 0 c (D.incl α).toMul
      rw [h2] at h
      exact congrArg Additive.toMul h
    rw [h1, layerZeroToQuotient_equivariant Z hK0Z Y.subtype hZinv c]
  -- bundle the coordinates as additive isomorphisms onto the summands
  have hmemL := fun α => hmem L α
  have hmemR := fun α => hmem R α
  let XiL : GaloisField 2 n →+ Additive ↥(Sl.map (QuotientGroup.mk' Z)) :=
    { toFun := fun α => Additive.ofMul
        (⟨xiL α, hmemL α⟩ : ↥(Sl.map (QuotientGroup.mk' Z)))
      map_zero' := by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change xiL 0 = 1
        simp only [hxiLdef, map_zero]
        rfl
      map_add' := fun a b => by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change xiL (a + b) = xiL a * xiL b
        simp only [hxiLdef, map_add]
        rw [show (L.incl a + L.incl b).toMul =
          (L.incl a).toMul * (L.incl b).toMul from rfl, map_mul] }
  let XiR : GaloisField 2 n →+ Additive ↥(Sr.map (QuotientGroup.mk' Z)) :=
    { toFun := fun α => Additive.ofMul
        (⟨xiR α, hmemR α⟩ : ↥(Sr.map (QuotientGroup.mk' Z)))
      map_zero' := by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change xiR 0 = 1
        simp only [hxiRdef, map_zero]
        rfl
      map_add' := fun a b => by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change xiR (a + b) = xiR a * xiR b
        simp only [hxiRdef, map_add]
        rw [show (R.incl a + R.incl b).toMul =
          (R.incl a).toMul * (R.incl b).toMul from rfl, map_mul] }
  have hXiLbij : Function.Bijective XiL := by
    constructor
    · intro a b hab
      exact hinj L (congrArg (fun t => ((t.toMul :
        ↥(Sl.map (QuotientGroup.mk' Z))) : P ⧸ Z)) hab)
    · intro w
      obtain ⟨α, hα⟩ := hsurj L w.toMul
      exact ⟨α, congrArg Additive.ofMul (Subtype.ext hα)⟩
  have hXiRbij : Function.Bijective XiR := by
    constructor
    · intro a b hab
      exact hinj R (congrArg (fun t => ((t.toMul :
        ↥(Sr.map (QuotientGroup.mk' Z))) : P ⧸ Z)) hab)
    · intro w
      obtain ⟨α, hα⟩ := hsurj R w.toMul
      exact ⟨α, congrArg Additive.ofMul (Subtype.ext hα)⟩
  let XiLe : GaloisField 2 n ≃+ Additive ↥(Sl.map (QuotientGroup.mk' Z)) :=
    AddEquiv.ofBijective XiL hXiLbij
  let XiRe : GaloisField 2 n ≃+ Additive ↥(Sr.map (QuotientGroup.mk' Z)) :=
    AddEquiv.ofBijective XiR hXiRbij
  let eAdd : Additive ↥(Sl.map (QuotientGroup.mk' Z)) ≃+
      Additive ↥(Sr.map (QuotientGroup.mk' Z)) :=
    e.toMulEquiv.toAdditive
  let F : GaloisField 2 n ≃+ GaloisField 2 n :=
    (XiLe.trans eAdd).trans XiRe.symm
  -- the semiconjugation `F (lamL * x) = lamR * F x`
  have hXiRF : ∀ x, XiR (F x) = eAdd (XiL x) := by
    intro x
    change XiRe (XiRe.symm (eAdd (XiLe x))) = eAdd (XiL x)
    rw [AddEquiv.apply_symm_apply]
    rfl
  have hsemi : ∀ x, F (lamL * x) = lamR * F x := by
    intro x
    apply hXiRbij.injective
    rw [hXiRF]
    -- right-hand side: `XiR (lamR * F x) = act c (XiR (F x))`
    have hR : XiR (lamR * F x) = Additive.ofMul
        (hVR.restrict c (XiR (F x)).toMul) := by
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change xiR (lamR * F x) = ((hVR.restrict c (XiR (F x)).toMul :
        ↥(Sr.map (QuotientGroup.mk' Z))) : P ⧸ Z)
      rw [IsAInvariant.restrict_apply_val]
      change layerZeroToQuotient Z hK0Z (R.incl (lamR • F x)).toMul =
        IsAInvariant.quotientMulAutHom hZinv c (xiR (F x))
      exact hact R lamR hrepR (F x)
    -- left-hand side: `XiL (lamL * x) = act c (XiL x)`
    have hL : XiL (lamL * x) = Additive.ofMul
        (hVL.restrict c (XiL x).toMul) := by
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change xiL (lamL * x) = ((hVL.restrict c (XiL x).toMul :
        ↥(Sl.map (QuotientGroup.mk' Z))) : P ⧸ Z)
      rw [IsAInvariant.restrict_apply_val]
      change layerZeroToQuotient Z hK0Z (L.incl (lamL • x)).toMul =
        IsAInvariant.quotientMulAutHom hZinv c (xiL x)
      exact hact L lamL hrepL x
    rw [hR, hL]
    -- equivariance of `e` transports the action across `eAdd`
    have hEquiv : eAdd (Additive.ofMul (hVL.restrict c (XiL x).toMul)) =
        Additive.ofMul (hVR.restrict c (eAdd (XiL x)).toMul) := by
      apply congrArg Additive.ofMul
      exact e.equivariant c (XiL x).toMul
    rw [hEquiv, hXiRF]
  -- read off the Frobenius conjugation
  let Flin : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
    { F.toAddMonoidHom with
      map_smul' := ZMod.map_smul F.toAddMonoidHom }
  have hF0 : Flin ≠ 0 := by
    intro h0
    have h1 : Flin 1 = 0 := by rw [h0]; rfl
    have h2 : F 1 = 0 := h1
    exact one_ne_zero (F.injective (h2.trans (map_zero F).symm))
  exact exists_frobenius_conjugate_of_semiconj hn lamL lamR Flin hF0 hsemi

end SummandSemiconj

end

end OddOrder.Higman.Suzuki2Groups
