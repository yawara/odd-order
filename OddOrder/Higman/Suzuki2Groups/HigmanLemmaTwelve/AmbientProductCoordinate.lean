/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedEigenweights

/-!
# Higman Lemma 12: the ambient `F × F` coordinate on `P / Φ(P)`

G. Higman, *Suzuki 2-groups*, p. 90.  Once `P = XY` is the product of the two
complementary `ξ`-length-2 factors `X = left`, `Y = right`, with
`X ⊓ Y = Φ(P)` and `X ⊔ Y = ⊤`, the Frattini quotient `P / Φ(P)` (i.e. the
zeroth lower-central layer `L₀`) is the internal direct product of the two
factor quotients.  This file assembles the resulting coordinate
`Additive L₀ ≃ₗ[ZMod 2] F × F` and, downstream, the ambient central extension
of `P` over `Multiplicative (F × F)` that the type-B/C/D constructors consume.

The single reusable ingredient per factor is the **factor inclusion**
`factorInclusion : F →ₗ[ZMod 2] Additive L₀`, the composite of a factor
coordinate `eQuot : Additive (G ⧸ N) ≃ₗ F` with the ambient inclusion
`quotientToAmbientLayerZeroLinear f`.  It is injective exactly when `N` is the
`f`-preimage of `Φ(P)`, and its image is `{[x] : x ∈ range f}` inside `L₀`.
Both Higman branches (commutative `A(n, 1)` and noncommutative `A(n, θ)`) supply
this data.
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

universe uP uF uG

-- Lower-central layers are elementary abelian by construction; expose their
-- canonical `CommGroup`/`F₂`-module structure locally, matching
-- `MixedEigenweights` (whose analogous instances are `local`, not exported).
local instance ambientProductLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance ambientProductLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance ambientProductLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P]

/-! ## The factor inclusion `F →ₗ Additive L₀` -/

section FactorInclusion

variable {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]
variable {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
variable [IsMulCommutative (G ⧸ N)] [Module (ZMod 2) (Additive (G ⧸ N))]
variable (hK0 : lowerCentralLayerKernel P 0 =
    (frattini P).subgroupOf (lowerCentralTerm P 0))
variable (hf : ∀ g ∈ N, f g ∈ frattini P)
variable (eQuot : Additive (G ⧸ N) ≃ₗ[ZMod 2] F)

/-- The inclusion of a factor's coordinate field into the ambient zeroth
lower-central layer: transport a coordinate through `eQuot.symm` and include it
via `quotientToAmbientLayerZeroLinear`. -/
def factorInclusion :
    F →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  (quotientToAmbientLayerZeroLinear f hK0 hf).comp eQuot.symm.toLinearMap

@[simp]
theorem factorInclusion_eQuot_mk (g : G) :
    factorInclusion f hK0 hf eQuot
        (eQuot (Additive.ofMul (QuotientGroup.mk' N g))) =
      layerZeroClass (ambientTermZeroHom f g) := by
  simp only [factorInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [quotientToAmbientLayerZeroLinear_mk]

/-- Every class of the form `[f g]` in `L₀` lies in the image of the factor
inclusion. -/
theorem layerZeroClass_ambientTermZeroHom_mem_range (g : G) :
    layerZeroClass (ambientTermZeroHom f g) ∈
      LinearMap.range (factorInclusion f hK0 hf eQuot) :=
  ⟨eQuot (Additive.ofMul (QuotientGroup.mk' N g)),
    factorInclusion_eQuot_mk _ _ _ _ _⟩

/-- The image of the factor inclusion is exactly `{[x] : x ∈ range f}`. -/
theorem factorInclusion_range_eq (w : Additive (lowerCentralLayer P 0)) :
    w ∈ LinearMap.range (factorInclusion f hK0 hf eQuot) ↔
      ∃ x : ↥(lowerCentralTerm P 0), (x : P) ∈ f.range ∧ layerZeroClass x = w := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (eQuot.symm c).toMul
    refine ⟨ambientTermZeroHom f g, ⟨g, rfl⟩, ?_⟩
    have hc : c = eQuot (Additive.ofMul (QuotientGroup.mk' N g)) := by
      rw [hg]; exact (eQuot.apply_symm_apply c).symm
    rw [hc, factorInclusion_eQuot_mk]
  · rintro ⟨x, ⟨g, hg⟩, rfl⟩
    have hx : x = ambientTermZeroHom f g := Subtype.ext hg.symm
    rw [hx]
    exact layerZeroClass_ambientTermZeroHom_mem_range f hK0 hf eQuot g

/-- If `N` is exactly the `f`-preimage of `Φ(P)`, then the factor inclusion is
injective. -/
theorem factorInclusion_injective
    (hfexact : ∀ g : G, f g ∈ frattini P → g ∈ N) :
    Function.Injective (factorInclusion f hK0 hf eQuot) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (eQuot.symm c).toMul
  have hcval : c = eQuot (Additive.ofMul (QuotientGroup.mk' N g)) := by
    rw [hg]; exact (eQuot.apply_symm_apply c).symm
  rw [hcval, factorInclusion_eQuot_mk] at hc
  have hmem : ambientTermZeroHom f g ∈ lowerCentralLayerKernel P 0 := by
    have h0 : Additive.ofMul (QuotientGroup.mk'
        (lowerCentralLayerKernel P 0) (ambientTermZeroHom f g)) = 0 := hc
    exact (QuotientGroup.eq_one_iff _).mp (ofMul_eq_zero.mp h0)
  rw [hK0, Subgroup.mem_subgroupOf] at hmem
  have hgN : g ∈ N := hfexact g hmem
  have hg1 : QuotientGroup.mk' N g = 1 := (QuotientGroup.eq_one_iff _).mpr hgN
  rw [hcval, hg1]
  simp

/-- `layerZeroClass` is additive: it is `Additive.ofMul` after the quotient
projection, so it turns products into sums. -/
theorem layerZeroClass_mul (x y : ↥(lowerCentralTerm P 0)) :
    layerZeroClass (x * y) = layerZeroClass x + layerZeroClass y := by
  simp only [layerZeroClass, map_mul, ofMul_mul]

/-- A class `[x]` with `(x : P) ∈ Φ(P)` vanishes in `L₀`. -/
theorem layerZeroClass_eq_zero_of_mem_frattini
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (x : ↥(lowerCentralTerm P 0)) (hx : (x : P) ∈ frattini P) :
    layerZeroClass x = 0 := by
  have hmem : x ∈ lowerCentralLayerKernel P 0 := by
    rw [hK0, Subgroup.mem_subgroupOf]; exact hx
  have h1 : QuotientGroup.mk' (lowerCentralLayerKernel P 0) x = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  show Additive.ofMul (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x) = 0
  exact ofMul_eq_zero.mpr h1

end FactorInclusion

/-! ## The ambient `F × F` coordinate -/

section AmbientProduct

variable {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]
variable {HL : Type uG} [Group HL] (fL : HL →* P) {NL : Subgroup HL} [NL.Normal]
variable [IsMulCommutative (HL ⧸ NL)] [Module (ZMod 2) (Additive (HL ⧸ NL))]
variable {HR : Type uG} [Group HR] (fR : HR →* P) {NR : Subgroup HR} [NR.Normal]
variable [IsMulCommutative (HR ⧸ NR)] [Module (ZMod 2) (Additive (HR ⧸ NR))]
variable (hK0 : lowerCentralLayerKernel P 0 =
    (frattini P).subgroupOf (lowerCentralTerm P 0))
variable (hfL : ∀ g ∈ NL, fL g ∈ frattini P)
variable (eQuotL : Additive (HL ⧸ NL) ≃ₗ[ZMod 2] F)
variable (hfR : ∀ g ∈ NR, fR g ∈ frattini P)
variable (eQuotR : Additive (HR ⧸ NR) ≃ₗ[ZMod 2] F)

/-- The candidate ambient coordinate: send `(α, β)` to the sum of the two factor
inclusions. -/
def combinedFactorMap :
    F × F →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  (factorInclusion fL hK0 hfL eQuotL).coprod (factorInclusion fR hK0 hfR eQuotR)

@[simp]
theorem combinedFactorMap_apply (v : F × F) :
    combinedFactorMap fL fR hK0 hfL eQuotL hfR eQuotR v =
      factorInclusion fL hK0 hfL eQuotL v.1 +
        factorInclusion fR hK0 hfR eQuotR v.2 := rfl

/-- Surjectivity of the combined map: `X ⊔ Y = ⊤` lets every class be split
into a left and a right part. -/
theorem combinedFactorMap_surjective
    (hRnormal : (fR.range).Normal)
    (hsup : fL.range ⊔ fR.range = ⊤) :
    Function.Surjective (combinedFactorMap fL fR hK0 hfL eQuotL hfR eQuotR) := by
  haveI := hRnormal
  intro y
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 0) y.toMul
  have hy : y = layerZeroClass x := by
    apply Additive.toMul.injective
    show Additive.toMul y = QuotientGroup.mk' (lowerCentralLayerKernel P 0) x
    exact hx.symm
  have hxmem : (x : P) ∈ fL.range ⊔ fR.range := hsup ▸ Subgroup.mem_top _
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := hxmem
  rw [SetLike.mem_coe, MonoidHom.mem_range] at ha hb
  obtain ⟨gL, hgL⟩ := ha
  obtain ⟨gR, hgR⟩ := hb
  refine ⟨(eQuotL (Additive.ofMul (QuotientGroup.mk' NL gL)),
      eQuotR (Additive.ofMul (QuotientGroup.mk' NR gR))), ?_⟩
  rw [hy, combinedFactorMap_apply, factorInclusion_eQuot_mk,
    factorInclusion_eQuot_mk, ← layerZeroClass_mul]
  congr 1
  apply Subtype.ext
  show fL gL * fR gR = (x : P)
  rw [hgL, hgR]; exact hab

/-- In a `ZMod 2`-module every element is its own negation. -/
private theorem neg_eq_self_zmodTwo {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (z : M) : z + z = 0 := by
  have h2 : (2 : ZMod 2) • z = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rwa [two_smul] at h2

/-- Injectivity of the combined map: `X ⊓ Y = Φ(P)` forces the two factor
components to agree only in the vanishing class. -/
theorem combinedFactorMap_injective
    (hfexactL : ∀ g : HL, fL g ∈ frattini P → g ∈ NL)
    (hfexactR : ∀ g : HR, fR g ∈ frattini P → g ∈ NR)
    (hinf : fL.range ⊓ fR.range = frattini P)
    (hΦR : frattini P ≤ fR.range) :
    Function.Injective (combinedFactorMap fL fR hK0 hfL eQuotL hfR eQuotR) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨cL, cR⟩ hc
  rw [combinedFactorMap_apply] at hc
  -- The two components share a common value `w`.
  have hchar : factorInclusion fL hK0 hfL eQuotL cL =
      factorInclusion fR hK0 hfR eQuotR cR := by
    rw [add_eq_zero_iff_eq_neg.mp hc,
      neg_eq_of_add_eq_zero_right (neg_eq_self_zmodTwo _)]
  set w := factorInclusion fR hK0 hfR eQuotR cR with hw
  have hwL : w ∈ LinearMap.range (factorInclusion fL hK0 hfL eQuotL) :=
    hchar ▸ ⟨cL, rfl⟩
  have hwR : w ∈ LinearMap.range (factorInclusion fR hK0 hfR eQuotR) := ⟨cR, rfl⟩
  rw [factorInclusion_range_eq] at hwL hwR
  obtain ⟨xL, hxLmem, hxL⟩ := hwL
  obtain ⟨xR, hxRmem, hxR⟩ := hwR
  -- `[xL] = [xR]` gives `(xL)⁻¹ (xR) ∈ Φ`.
  have hdiv : (xL : P)⁻¹ * (xR : P) ∈ frattini P := by
    have hmk : QuotientGroup.mk' (lowerCentralLayerKernel P 0) xL =
        QuotientGroup.mk' (lowerCentralLayerKernel P 0) xR :=
      Additive.ofMul.injective (hxL.trans hxR.symm)
    have hker : xL⁻¹ * xR ∈ lowerCentralLayerKernel P 0 := QuotientGroup.eq.mp hmk
    rw [hK0, Subgroup.mem_subgroupOf] at hker
    exact hker
  -- So `(xL : P) ∈ Y = fR.range`, hence in `X ⊓ Y = Φ`.
  have hxLright : (xL : P) ∈ fR.range := by
    have hcalc : (xL : P) = (xR : P) * ((xL : P)⁻¹ * (xR : P))⁻¹ := by group
    rw [hcalc]
    exact mul_mem hxRmem (fR.range.inv_mem (hΦR hdiv))
  have hxLphi : (xL : P) ∈ frattini P := by
    rw [← hinf]; exact ⟨hxLmem, hxLright⟩
  have hw0 : w = 0 :=
    hxL.symm.trans (layerZeroClass_eq_zero_of_mem_frattini hK0 xL hxLphi)
  have hcL : cL = 0 :=
    factorInclusion_injective fL hK0 hfL eQuotL hfexactL
      (by rw [map_zero]; exact hchar.trans hw0)
  have hcR : cR = 0 :=
    factorInclusion_injective fR hK0 hfR eQuotR hfexactR
      (by rw [map_zero]; exact hw0)
  exact Prod.ext hcL hcR

/-- **Higman Lemma 12 (p. 90), the ambient `F × F` coordinate.**

When `P = XY` with `X ⊓ Y = Φ(P)` and `X ⊔ Y = ⊤`, the two factor coordinates
assemble into a linear isomorphism `F × F ≃ₗ Additive (P / Φ(P))`. -/
def ambientProductEquiv
    (hfexactL : ∀ g : HL, fL g ∈ frattini P → g ∈ NL)
    (hfexactR : ∀ g : HR, fR g ∈ frattini P → g ∈ NR)
    (hRnormal : (fR.range).Normal)
    (hinf : fL.range ⊓ fR.range = frattini P)
    (hsup : fL.range ⊔ fR.range = ⊤)
    (hΦR : frattini P ≤ fR.range) :
    (F × F) ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  LinearEquiv.ofBijective (combinedFactorMap fL fR hK0 hfL eQuotL hfR eQuotR)
    ⟨combinedFactorMap_injective fL fR hK0 hfL eQuotL hfR eQuotR
        hfexactL hfexactR hinf hΦR,
      combinedFactorMap_surjective fL fR hK0 hfL eQuotL hfR eQuotR hRnormal hsup⟩

@[simp]
theorem ambientProductEquiv_apply
    (hfexactL : ∀ g : HL, fL g ∈ frattini P → g ∈ NL)
    (hfexactR : ∀ g : HR, fR g ∈ frattini P → g ∈ NR)
    (hRnormal : (fR.range).Normal)
    (hinf : fL.range ⊓ fR.range = frattini P)
    (hsup : fL.range ⊔ fR.range = ⊤)
    (hΦR : frattini P ≤ fR.range) (v : F × F) :
    ambientProductEquiv fL fR hK0 hfL eQuotL hfR eQuotR
        hfexactL hfexactR hRnormal hinf hsup hΦR v =
      factorInclusion fL hK0 hfL eQuotL v.1 +
        factorInclusion fR hK0 hfR eQuotR v.2 := rfl

end AmbientProduct

/-! ## The ambient central extension over `F × F` -/

section AmbientExtension

/-- Bridge `P / Φ(P) ≃* L₀`: the zeroth lower-central layer is the Frattini
quotient once the layer kernel is identified with `Φ(P)`. -/
def frattiniQuotientEquivLayerZero
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)) :
    P ⧸ frattini P ≃* lowerCentralLayer P 0 :=
  QuotientGroup.congr _ _ (lowerCentralTermZeroEquivAmbient P).symm (by
    rw [hK0]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [lowerCentralTermZeroEquivAmbient, Subgroup.mem_subgroupOf] using hy
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine ⟨(x : P), hx, ?_⟩
      apply Subtype.ext
      rfl)

variable {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]

/-- The multiplicative Frattini-quotient coordinate `P / Φ(P) ≃* 𝔽 × 𝔽`, built
from any additive `F × F` layer coordinate. -/
def layerZeroProductMulCoordinate
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (e : (F × F) ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0)) :
    P ⧸ frattini P ≃* Multiplicative (F × F) :=
  (frattiniQuotientEquivLayerZero hK0).trans
    (AddEquiv.toMultiplicativeRight e.symm.toAddEquiv)

variable [IsMulCommutative ↑(frattini P)]
variable [Module (ZMod 2) (Additive ↑(frattini P))]

/-- The multiplicative Singer kernel coordinate `𝔽 ≃* Φ(P)` from the additive
Singer coordinate on the Frattini subgroup. -/
def frattiniSingerKernelCoordinate
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] F) :
    Multiplicative F ≃* ↥(frattini P) :=
  AddEquiv.toMultiplicativeLeft ePhi.symm.toAddEquiv

/-- **Higman Lemma 12 (p. 90), the ambient central extension.**  `P` as a
central extension of `𝔽 × 𝔽` (= `P / Φ(P)`) by `𝔽` (= `Φ(P)`, Singer), the
input consumed by the type-B/C/D `ofExtension` constructors. -/
def ambientProductExtension
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (e : (F × F) ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] F) :
    GroupExtension (Multiplicative F) P (Multiplicative (F × F)) :=
  GroupExtension.ofNormalSubgroupCoordinates (frattini P)
    (frattiniSingerKernelCoordinate ePhi)
    (layerZeroProductMulCoordinate hK0 e)

@[simp]
theorem ambientProductExtension_inl_range
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (e : (F × F) ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] F) :
    (ambientProductExtension hK0 e ePhi).inl.range = frattini P :=
  GroupExtension.ofNormalSubgroupCoordinates_range_inl _ _ _

end AmbientExtension

/-! ## Polarization of the ambient square map -/

section SquareDecomposition

variable {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]

/-- **Higman Lemma 12 (p. 90), polarization of the ambient square map.**  In any
`F`-valued centre coordinate, the square of a sum splits into the two summand
squares plus the mixed commutator bilinear (Higman's `(u + v)^(2) = u^(2) +
v^(2) + [u, v]`).  Instantiating `u = fI_left α`, `v = fI_right β` yields the
`q_P(α, β) = q_X(α) + q_Y(β) + mixed(α, β)` decomposition. -/
theorem centerSquareMap_add
    (hSq : LowerCentralSquaresLieInSecond P)
    (center : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] F)
    (u v : Additive (lowerCentralLayer P 0)) :
    center (lowerCentralSquareMapAdditive P hSq (u + v)) =
      center (lowerCentralSquareMapAdditive P hSq u) +
        center (lowerCentralSquareMapAdditive P hSq v) +
        center (lowerCentralCommutatorBilinear P u v) := by
  rw [lowerCentralSquareMapAdditive_add, map_add, map_add]

/-- **Higman Lemma 12, the ambient square map extracts the underlying square.**
The centre coordinate of `sq_ambient [x]` is the Singer coordinate of the
genuine square `x²` in `Φ(P)`.  This is the identity that turns the type-B/C/D
`hsq` obligation `x² = S.inl (ofAdd (q (S.rightHom x)))` into the transported
square-map equation. -/
theorem ambientCenterCoordinate_squareMap
    {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P)
    (hSq : LowerCentralSquaresLieInSecond P)
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (x : ↥(lowerCentralTerm P 0))
    (hx2 : (x : P) ^ 2 ∈ frattini P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralSquareMapAdditive P hSq (layerZeroClass x)) =
      ePhi (Additive.ofMul ⟨(x : P) ^ 2, hx2⟩) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  rw [show layerZeroClass x =
      Additive.ofMul (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x) from rfl,
    lowerCentralSquareMapAdditive_mk]
  show ePhi (ambientLayerOneLinearEquivFrattini hEA hK1 hterm
      (Additive.ofMul (lowerCentralSquareValue P hSq x))) =
    ePhi (Additive.ofMul ⟨(x : P) ^ 2, hx2⟩)
  rfl

/-- The factor sibling of `ambientCenterCoordinate_squareMap`: the factor-to-
ambient Frattini bridge of a factor square value is the genuine square, pushed
into `Φ(P)`.  Together with `NoncommutativeFactorCoordinateData.square_normal`
(and `eKernel_eq`) this identifies `A(α) = q_X(α)`. -/
theorem factorLayerOneEquivAmbientFrattini_squareValue
    {S : Subgroup P}
    (hPhiS : frattini P ≤ S)
    (hK1 : lowerCentralLayerKernel S 1 = ⊥)
    (hterm : lowerCentralTerm S 1 = (frattini P).subgroupOf S)
    (hSq : LowerCentralSquaresLieInSecond S)
    (g : ↥(lowerCentralTerm S 0))
    (hmem : (S.subtype ((lowerCentralTerm S 0).subtype g)) ^ 2 ∈ frattini P) :
    (factorLayerOneEquivAmbientFrattini hPhiS hK1 hterm
        (lowerCentralSquareValue S hSq g) : ↥(frattini P)) =
      ⟨(S.subtype ((lowerCentralTerm S 0).subtype g)) ^ 2, hmem⟩ := by
  apply Subtype.ext
  rfl

/-- The commutative sibling of the factor square identity: the homocyclic
`C₄`-square bridge of a factor square is the genuine square, pushed into
`Φ(P)`.  Together with `CommutativeFactorCoordinateData.square_normal`
(= `β²`) this identifies `A(α) = q_X(α) = α²`. -/
theorem homocyclicFourSquareSubgroupEquivFrattini_squareEquiv
    {S : Subgroup P} [Finite ↥S]
    (hcomm : IsMulCommutative ↥S)
    {index : Type} [Fintype index]
    (equivPi : ↥S ≃* (index → Multiplicative (ZMod 4)))
    (hPhiS : frattini P ≤ S)
    (hN : Agemo (↥S) 2 1 = (frattini P).subgroupOf S)
    (g : ↥S)
    (hmem : (S.subtype g) ^ 2 ∈ frattini P) :
    (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN
        (commutativeFactorSquareEquiv hcomm equivPi
          (QuotientGroup.mk g)) : ↥(frattini P)) =
      ⟨(S.subtype g) ^ 2, hmem⟩ := by
  apply Subtype.ext
  rfl

end SquareDecomposition

end

end OddOrder.Higman.Suzuki2Groups
