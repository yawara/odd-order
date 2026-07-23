/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.AInvariantSubrep
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoQuotientLayerBridge
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors

/-!
# Higman's Lemma 13: factor ranges in the Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

For a finite `2`-group `P`, a genuine lower-central factor inclusion has,
after passage through `L₀(P) → P ⧸ Φ(P)`, exactly the additive submodule
underlying the image of the corresponding actual subgroup in `P ⧸ Φ(P)`.

The first result is stated for the raw `factorInclusion` API.  The second
specializes it to a factor produced in a restricted pairwise join.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP uG uF

local instance factorQuotientRangeLayerIsMulCommutative
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance factorQuotientRangeLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance factorQuotientRangeLayerZModTwoModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- On a quotient representative, a raw factor inclusion followed by the
canonical map `L₀(P) → P ⧸ Φ(P)` is the ordinary quotient class of the
represented group element. -/
theorem layerZeroToFrattiniQuotientLinear_factorInclusion_eQuot_mk
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {G : Type uG} [Group G]
    (f : G →* P)
    {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    [Module (ZMod 2) (Additive (G ⧸ N))]
    {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]
    (eQuot : Additive (G ⧸ N) ≃ₗ[ZMod 2] F)
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (g : G) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    layerZeroToFrattiniQuotientLinear P hP
        (factorInclusion f
          (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
          hf eQuot
          (eQuot (Additive.ofMul (QuotientGroup.mk' N g)))) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) (f g)) := by
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  rw [factorInclusion_eQuot_mk,
    layerZeroToFrattiniQuotientLinear_apply]
  rfl

/-- The quotient-side linear range of a genuine raw factor inclusion is
exactly the submodule corresponding to the image of its actual group
range in `P ⧸ Φ(P)`. -/
theorem factorInclusion_frattiniQuotient_range_eq
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {G : Type uG} [Group G]
    (f : G →* P)
    {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    [Module (ZMod 2) (Additive (G ⧸ N))]
    {F : Type uF} [AddCommGroup F] [Module (ZMod 2) F]
    (eQuot : Additive (G ⧸ N) ≃ₗ[ZMod 2] F)
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (W : Subgroup P)
    (hrange : f.range = W) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    LinearMap.range
        ((layerZeroToFrattiniQuotientLinear P hP).comp
          (factorInclusion f
            (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
            hf eQuot)) =
      (elabSubmoduleSubgroupEquiv 2).symm
        (W.map (QuotientGroup.mk' (frattini P))) := by
  classical
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  ext v
  rw [mem_symm_elabSubmoduleSubgroupEquiv]
  constructor
  · rintro ⟨alpha, rfl⟩
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective N (eQuot.symm alpha).toMul
    have halpha :
        alpha = eQuot (Additive.ofMul (QuotientGroup.mk' N g)) := by
      rw [hg]
      exact (eQuot.apply_symm_apply alpha).symm
    rw [halpha, LinearMap.comp_apply,
      layerZeroToFrattiniQuotientLinear_factorInclusion_eQuot_mk]
    change QuotientGroup.mk' (frattini P) (f g) ∈
      W.map (QuotientGroup.mk' (frattini P))
    refine ⟨f g, ?_, rfl⟩
    rw [← hrange]
    exact ⟨g, rfl⟩
  · intro hv
    obtain ⟨x, hxW, hx⟩ := hv
    have hxrange : x ∈ f.range := by
      rw [hrange]
      exact hxW
    obtain ⟨g, hfg⟩ := hxrange
    refine
      ⟨eQuot (Additive.ofMul (QuotientGroup.mk' N g)), ?_⟩
    apply Additive.toMul.injective
    rw [LinearMap.comp_apply,
      layerZeroToFrattiniQuotientLinear_factorInclusion_eQuot_mk,
      toMul_ofMul, hfg]
    exact hx

/-- **Higman Lemma 13 (p. 93), one restricted factor in the Frattini
quotient.**

If the prescribed factor inside a restricted pairwise join `S` is the
`subgroupOf` copy of an actual ambient subgroup `W`, its genuine factor
inclusion has, after passage through `L₀(P) → P ⧸ Φ(P)`, exactly the
submodule underlying `WΦ(P) / Φ(P)`. -/
theorem restrictedFactorAmbientInclusion_frattiniQuotient_range_eq
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    {Y : Subgroup (MulAut P)}
    {W S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hWS : W ≤ S)
    {n : ℕ}
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) :=
        hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    {nu : GaloisField 2 n}
    {T : Subgroup S}
    {hTinv : IsAInvariant hSinv.restrict.range.subtype T}
    {hPhiT : frattini S ≤ T}
    (c : Y)
    (data :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) :=
        hEAS.zmodModule
      FactorCoordinateData hTinv hPhiT
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hT : T = W.subgroupOf S)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hEAS.zmodModule
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    LinearMap.range
        ((layerZeroToFrattiniQuotientLinear P hP).comp
          (restrictedFactorAmbientInclusion hSinv hEAS eS c data
            hK1S htermS hSqS hAgemoS hK0S)) =
      (elabSubmoduleSubgroupEquiv 2).symm
        (W.map (QuotientGroup.mk' (frattini P))) := by
  classical
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : CommGroup (frattini S) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini S)) :=
    hEAS.zmodModule
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  let d :=
    data.toInclusionData hEAS eS
      hK1S htermS hSqS hAgemoS hK0S
  letI := d.group
  letI := d.normal
  letI := d.quotComm
  letI := d.quotModule
  let f : d.H →* P := S.subtype.comp d.f
  have hf : ∀ g ∈ d.N, f g ∈ frattini P := by
    intro g hg
    have hgS :
        ambientTermZeroHom d.f g ∈ lowerCentralLayerKernel S 0 := by
      rw [hK0S, Subgroup.mem_subgroupOf]
      exact d.hf g hg
    have hgP :
        subgroupLowerCentralTermZeroHom S (ambientTermZeroHom d.f g) ∈
          lowerCentralLayerKernel P 0 :=
      subgroupLowerCentralLayerKernelZero_le_comap S hgS
    rw [lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP,
      Subgroup.mem_subgroupOf] at hgP
    simpa [f, subgroupLowerCentralTermZeroHom, ambientTermZeroHom] using hgP
  have hrange : f.range = W := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      have hmem : d.f g ∈ T := d.range_eq.le ⟨g, rfl⟩
      have hmemW : d.f g ∈ W.subgroupOf S := hT.le hmem
      exact hmemW
    · intro hxW
      let s : S := ⟨x, hWS hxW⟩
      have hsW : s ∈ W.subgroupOf S := hxW
      have hsT : s ∈ T := hT.ge hsW
      have hsrange : s ∈ d.f.range := d.range_eq.ge hsT
      obtain ⟨g, hg⟩ := hsrange
      refine ⟨g, ?_⟩
      change (d.f g : P) = x
      exact congrArg Subtype.val hg
  have hiota :
      restrictedFactorAmbientInclusion hSinv hEAS eS c data
          hK1S htermS hSqS hAgemoS hK0S =
        factorInclusion f
          (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
          hf d.eQuot := by
    ext alpha
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective d.N (d.eQuot.symm alpha).toMul
    have halpha :
        alpha = d.eQuot
          (Additive.ofMul (QuotientGroup.mk' d.N g)) := by
      rw [hg]
      exact (d.eQuot.apply_symm_apply alpha).symm
    rw [halpha]
    change
      subgroupLowerCentralLayerZeroLinear S
          (d.incl
            (d.eQuot
              (Additive.ofMul (QuotientGroup.mk' d.N g)))) =
        factorInclusion f
          (lowerCentralLayerKernel_zero_eq_frattini_subgroupOf P hP)
          hf d.eQuot
          (d.eQuot
            (Additive.ofMul (QuotientGroup.mk' d.N g)))
    have hd :
        d.incl (d.eQuot
            (Additive.ofMul (QuotientGroup.mk' d.N g))) =
          layerZeroClass (ambientTermZeroHom d.f g) :=
      factorInclusion_eQuot_mk d.f hK0S d.hf d.eQuot g
    rw [hd, factorInclusion_eQuot_mk]
    change
      subgroupLowerCentralLayerZeroLinear S
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel S 0)
              (ambientTermZeroHom d.f g))) =
        Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
            (ambientTermZeroHom f g))
    rw [subgroupLowerCentralLayerZeroLinear_mk]
    rfl
  rw [hiota]
  exact factorInclusion_frattiniQuotient_range_eq
    hP f d.eQuot hf W hrange

end

end OddOrder.Higman.Suzuki2Groups
