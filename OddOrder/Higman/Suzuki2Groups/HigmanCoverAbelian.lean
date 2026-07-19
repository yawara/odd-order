/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanNormalCover
import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
import OddOrder.Isaacs.Ch01_Sylow.Basic
import OddOrder.GroupTheory.RepresentationTheory.AInvariantSubrep

/-!
# Higman Lemma 7: abelian normal covers

This file formalizes G. Higman, *Suzuki 2-groups*, Lemma 7, p. 86.
The first bridge, omitted in the paper, is that a cover in the lattice of
normal actor-invariant subgroups of a finite `p`-group becomes central after
quotienting by its lower endpoint.  Consequently every actor-invariant
subgroup of the cover quotient lifts to an ambient-normal subgroup, which is
the group-theoretic input behind Higman's assertion that `C / Phi(C)` is
irreducible.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

universe u

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

variable {G X : Type*} [Group G] [Group X]

namespace NormalInvariantCover

private theorem normal_of_le_center
    {Q : Type*} [Group Q] {H : Subgroup Q}
    (hH : H ≤ Subgroup.center Q) : H.Normal :=
  ⟨fun n hn g => by
    rw [(Subgroup.mem_center_iff.mp (hH hn) g), mul_assoc,
      mul_inv_cancel, mul_one]
    exact hn⟩

/-- A normal actor-invariant cover in a finite `p`-group is central modulo
its lower endpoint.

Indeed, the nontrivial normal subgroup `C/A` of `G/A` meets the center
nontrivially.  That intersection is actor-invariant, so its full preimage is
an intermediate normal actor-invariant subgroup.  The cover property forces
the preimage to be all of `C`. -/
theorem map_quotient_le_center
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {act : X →* MulAut G} {A C : Subgroup G}
    [A.Normal]
    (h : NormalInvariantCover act A C) :
    C.map (QuotientGroup.mk' A) ≤ Subgroup.center (G ⧸ A) := by
  letI : C.Normal := h.right.1
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let Cbar : Subgroup (G ⧸ A) := C.map q
  haveI : Cbar.Normal :=
    Subgroup.Normal.map h.right.1 q (QuotientGroup.mk'_surjective A)
  have hCbar_ne : Cbar ≠ ⊥ := by
    intro hbot
    have hCA : C ≤ A := by
      have hker : C ≤ q.ker := (Subgroup.map_eq_bot_iff C).mp hbot
      simpa [q] using hker
    exact h.lt.2 hCA
  let Y : Subgroup (G ⧸ A) := Cbar ⊓ Subgroup.center (G ⧸ A)
  have hYne : Y ≠ ⊥ := by
    haveI : Nontrivial Cbar :=
      (Subgroup.nontrivial_iff_ne_bot Cbar).mpr hCbar_ne
    have hnon : Nontrivial ↥(Cbar ⊓ Subgroup.center (G ⧸ A)) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
        (hG.to_quotient A) (N := Cbar) inferInstance
    exact (Subgroup.nontrivial_iff_ne_bot Y).mp (by simpa [Y] using hnon)
  have hCbarInv : IsAInvariant
      (h.left.2.quotientMulAutHom) Cbar := by
    simpa [Cbar, q] using h.left.2.map_quotient h.right.2
  have hYInv : IsAInvariant
      (h.left.2.quotientMulAutHom) Y := by
    exact hCbarInv.inf
      (IsAInvariant.of_characteristic h.left.2.quotientMulAutHom)
  let D : Subgroup G := Y.comap q
  have hDInv : IsAInvariant act D := by
    simpa [D, q] using h.left.2.comap_quotient hYInv
  haveI : D.Normal := Subgroup.Normal.comap inferInstance q
  have hAD : A ≤ D := by
    intro a ha
    change q a ∈ Y
    have hqa : q a = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [hqa]
    exact Y.one_mem
  have hDC : D ≤ C := by
    intro d hd
    have hqd : q d ∈ Cbar := (show q d ∈ Y from hd).1
    obtain ⟨c, hc, hcd⟩ := hqd
    have hdc : d * c⁻¹ ∈ A := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (d * c⁻¹) = 1
      rw [map_mul, map_inv, hcd]
      simp
    have hprod := C.mul_mem (h.le hdc) hc
    simpa using hprod
  have hDcases : D = A ∨ D = C :=
    h.eq_left_or_eq_right ⟨inferInstance, hDInv⟩ hAD hDC
  have hDneA : D ≠ A := by
    intro hDA
    have hYbot : Y = ⊥ := by
      apply le_antisymm
      · intro y hy
        obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective A y
        have hdD : d ∈ D := by
          change q d ∈ Y
          exact hy
        have hdA : d ∈ A := by simpa [hDA] using hdD
        exact (QuotientGroup.eq_one_iff _).mpr hdA
      · exact bot_le
    exact hYne hYbot
  have hDCeq : D = C := hDcases.resolve_left hDneA
  intro y hy
  obtain ⟨c, hc, rfl⟩ := hy
  have hcD : c ∈ D := by simpa [hDCeq] using hc
  exact (show q c ∈ Y from hcD).2

/-- Every actor-invariant subgroup of the central cover quotient is trivial
or the whole quotient.

The centrality theorem makes the image of such a subgroup normal in `G/A`.
Its preimage is therefore an intermediate normal actor-invariant subgroup
between `A` and `C`, so the cover property applies. -/
theorem invariant_subgroup_quotient_eq_bot_or_top
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {act : X →* MulAut G} {A C : Subgroup G}
    [A.Normal]
    (h : NormalInvariantCover act A C)
    (U : Subgroup ↥(C.map (QuotientGroup.mk' A)))
    (hU : IsAInvariant
      (h.left.2.map_quotient h.right.2).restrict U) :
    U = ⊥ ∨ U = ⊤ := by
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let Cbar : Subgroup (G ⧸ A) := C.map q
  have hCbarInv : IsAInvariant
      (h.left.2.quotientMulAutHom) Cbar := by
    simpa [Cbar, q] using h.left.2.map_quotient h.right.2
  let Ubar : Subgroup (G ⧸ A) := U.map Cbar.subtype
  have hUbarInv : IsAInvariant
      (h.left.2.quotientMulAutHom) Ubar := by
    simpa [Ubar, Cbar, q] using
      aInvariant_map_subtype_of_restrict hCbarInv hU
  have hUbarCenter : Ubar ≤ Subgroup.center (G ⧸ A) :=
    (Subgroup.map_subtype_le U).trans (h.map_quotient_le_center hG)
  haveI : Ubar.Normal := normal_of_le_center hUbarCenter
  let D : Subgroup G := Ubar.comap q
  have hDInv : IsAInvariant act D := by
    simpa [D, q] using h.left.2.comap_quotient hUbarInv
  haveI : D.Normal := Subgroup.Normal.comap inferInstance q
  have hAD : A ≤ D := by
    intro a ha
    change q a ∈ Ubar
    have hqa : q a = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [hqa]
    exact Ubar.one_mem
  have hDC : D ≤ C := by
    have hle : D ≤ Cbar.comap q :=
      Subgroup.comap_mono (Subgroup.map_subtype_le U)
    simpa [D, Cbar, q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr h.le] using hle
  have hDU : D.map q = Ubar := by
    simpa [D] using
      Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective A) Ubar
  rcases h.eq_left_or_eq_right ⟨inferInstance, hDInv⟩ hAD hDC with hDA | hDCeq
  · left
    apply Subgroup.map_injective Cbar.subtype_injective
    have hUbarBot : Ubar = ⊥ := by
      calc
        Ubar = D.map q := hDU.symm
        _ = A.map q := congrArg (Subgroup.map q) hDA
        _ = ⊥ := by
          rw [Subgroup.map_eq_bot_iff]
          simp [q]
    simp [Ubar, hUbarBot]
  · right
    apply Subgroup.map_injective Cbar.subtype_injective
    have hUbarTop : Ubar = Cbar := by
      calc
        Ubar = D.map q := hDU.symm
        _ = C.map q := congrArg (Subgroup.map q) hDCeq
        _ = Cbar := rfl
    rw [show U.map Cbar.subtype = Ubar from rfl, hUbarTop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- Restricting a regular involution actor to the upper endpoint of a
normal invariant cover remains faithful.

The upper endpoint is a nontrivial finite `2`-group, hence contains an
involution.  Two actor elements with the same restriction send that
involution to the same target, and regularity makes them equal. -/
theorem restrict_injective_of_regular_on_involutions
    [Finite G] (hG : IsPGroup 2 G)
    (Y : Subgroup (MulAut G))
    (hreg : ActsRegularlyOnInvolutions Y)
    {A C : Subgroup G}
    (h : NormalInvariantCover Y.subtype A C) :
    Function.Injective h.right.2.restrict := by
  have hCne : C ≠ ⊥ := by
    intro hC
    have hlt : A < ⊥ := hC ▸ h.lt
    exact (not_lt_of_ge bot_le) hlt
  letI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
  have hCtwo : IsPGroup 2 C := hG.to_subgroup C
  have hcard_ne : Nat.card C ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo_dvd : 2 ∣ Nat.card C :=
    hCtwo.card_eq_or_dvd.resolve_left hcard_ne
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 htwo_dvd
  have hz := orderOf_eq_prime_iff.mp hzorder
  have hzG : (z : G) ∈ involutions G := by
    refine ⟨congrArg Subtype.val hz.1, ?_⟩
    intro hzone
    exact hz.2 (Subtype.ext hzone)
  intro a b hab
  let y : G := (a : MulAut G) (z : G)
  have hy : y ∈ involutions G := by
    constructor
    · simpa only [y, map_pow, map_one] using
        congrArg (a : MulAut G) hzG.1
    · intro hyone
      apply hzG.2
      apply (a : MulAut G).injective
      simpa only [y, map_one] using hyone
  obtain ⟨d, hd, huniq⟩ := hreg (z : G) hzG y hy
  have ha : (a : MulAut G) (z : G) = y := rfl
  have hb : (b : MulAut G) (z : G) = y := by
    have hzrestr : h.right.2.restrict a z = h.right.2.restrict b z :=
      DFunLike.congr_fun hab z
    exact (congrArg Subtype.val hzrestr).symm.trans ha
  exact (huniq a ha).trans (huniq b hb).symm

end NormalInvariantCover

/-! ## The actual lower-central overlap -/

/-- `A²`, embedded in `C`, in the form used by Higman Lemma 7. -/
def agemoOneMappedSubgroupOf
    {P : Type*} [Group P] (A C : Subgroup P) : Subgroup C :=
  ((Agemo A 2 1).map A.subtype).subgroupOf C

/-- The exact subgroup overlap extracted from `A = Φ(C)` and `C' ≤ A²`.

The first equality identifies the denominator of the actual first
lower-central layer of `C`; the two inclusions are the overlap between the
power series below `A` and the abelianized power series above `C'`. -/
def LemmaSevenPureOverlap
    {P : Type*} [Group P] (A C : Subgroup P) : Prop :=
  lowerCentralLayerKernelInAmbient C 0 = A.subgroupOf C ∧
    lowerCentralTerm C 1 ≤ agemoOneMappedSubgroupOf A C ∧
    agemoOneMappedSubgroupOf A C ≤ A.subgroupOf C

/-- `A = Φ(C)` identifies the actual first-layer denominator with `A`
inside the subtype group `C`. -/
theorem layerKernel_zero_eq_subgroupOf_of_ambientFrattini_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hPhi : NormalInvariantCover.ambientFrattini C = A) :
    lowerCentralLayerKernelInAmbient C 0 = A.subgroupOf C := by
  rw [lowerCentralLayerKernelInAmbient_zero_eq_frattini C
    (hP.to_subgroup C)]
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  exact hPhi

/-- The source hypothesis `C' ≤ A²`, written ambiently, is exactly the
first inclusion in the overlap chain inside `C`. -/
theorem lowerCentralTerm_one_le_agemoOneMappedSubgroupOf
    {P : Type*} [Group P] {A C : Subgroup P}
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    lowerCentralTerm C 1 ≤ agemoOneMappedSubgroupOf A C := by
  intro x hx
  rw [agemoOneMappedSubgroupOf, Subgroup.mem_subgroupOf]
  apply hderived
  refine ⟨x, ?_, rfl⟩
  rw [_root_.commutator_def]
  simpa [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one] using hx

/-- The embedded square subgroup of `A` lies in `A`. -/
theorem agemoOneMappedSubgroupOf_le
    {P : Type*} [Group P] {A C : Subgroup P} :
    agemoOneMappedSubgroupOf A C ≤ A.subgroupOf C := by
  intro x hx
  rw [agemoOneMappedSubgroupOf, Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨a, _, ha⟩ := hx
  rw [← ha]
  exact a.2

/-- The group-theoretic hypotheses of Higman Lemma 7 construct the actual
overlap chain, without adding any representation-theoretic carrier. -/
theorem lemmaSevenPureOverlap_of_hypotheses
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    LemmaSevenPureOverlap A C :=
  ⟨layerKernel_zero_eq_subgroupOf_of_ambientFrattini_eq hP hAC hPhi,
    lowerCentralTerm_one_le_agemoOneMappedSubgroupOf hderived,
    agemoOneMappedSubgroupOf_le⟩

/-! ## The first lower-central layer as the cover quotient -/

namespace NormalInvariantCover

/-- The representative-level map from Higman's degree-zero lower-central
term to the image of `C/A` in the ambient quotient. -/
def lowerCentralTermZeroToMapHom
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (_h : NormalInvariantCover act A C) :
    ↥(lowerCentralTerm C 0) →*
      ↥(C.map (QuotientGroup.mk' A)) where
  toFun x :=
    ⟨QuotientGroup.mk' A ((x : C) : G),
      ⟨((x : C) : G), (x : C).2, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

@[simp]
theorem lowerCentralTermZeroToMapHom_apply
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (x : ↥(lowerCentralTerm C 0)) :
    (lowerCentralTermZeroToMapHom h x : G ⧸ A) =
      QuotientGroup.mk' A ((x : C) : G) :=
  rfl

theorem lowerCentralTermZeroToMapHom_surjective
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C) :
    Function.Surjective (lowerCentralTermZeroToMapHom h) := by
  rintro ⟨y, g, hgC, rfl⟩
  let c : C := ⟨g, hgC⟩
  let x : ↥(lowerCentralTerm C 0) :=
    ⟨c, by simp [lowerCentralTerm]⟩
  exact ⟨x, rfl⟩

theorem lowerCentralTermZeroToMapHom_ker
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    (lowerCentralTermZeroToMapHom h).ker =
      lowerCentralLayerKernel C 0 := by
  have hK : lowerCentralLayerKernelInAmbient C 0 = A.subgroupOf C :=
    layerKernel_zero_eq_subgroupOf_of_ambientFrattini_eq
      hG h.le hPhi
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx0
    have hxq : QuotientGroup.mk' A ((x : C) : G) = 1 :=
      congrArg Subtype.val hx0
    have hx := (QuotientGroup.eq_one_iff _).mp hxq
    have hx' : (x : C) ∈ lowerCentralLayerKernelInAmbient C 0 := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact hx
    have hx'' : x ∈
        (lowerCentralLayerKernelInAmbient C 0).subgroupOf
          (lowerCentralTerm C 0) := hx'
    rwa [lowerCentralLayerKernelInAmbient_subgroupOf] at hx''
  · intro hx
    have hx' : x ∈
        (lowerCentralLayerKernelInAmbient C 0).subgroupOf
          (lowerCentralTerm C 0) := by
      rwa [lowerCentralLayerKernelInAmbient_subgroupOf]
    have hx'' : (x : C) ∈ lowerCentralLayerKernelInAmbient C 0 := hx'
    rw [hK, Subgroup.mem_subgroupOf] at hx''
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hx''

/-- `L₁(C)` is the image of `C/A` in `G/A`, as a multiplicative group. -/
noncomputable def lowerCentralLayerZeroEquivMap
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    lowerCentralLayer C 0 ≃* ↥(C.map (QuotientGroup.mk' A)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (lowerCentralTermZeroToMapHom_ker hG h hPhi).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (lowerCentralTermZeroToMapHom h)
      (lowerCentralTermZeroToMapHom_surjective h))

@[simp]
theorem lowerCentralLayerZeroEquivMap_mk
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A)
    (x : ↥(lowerCentralTerm C 0)) :
    lowerCentralLayerZeroEquivMap hG h hPhi
        (QuotientGroup.mk' (lowerCentralLayerKernel C 0) x) =
      lowerCentralTermZeroToMapHom h x := by
  rfl

/-- The quotient equivalence intertwines the actual degree-zero
lower-central action with the restricted action on `C/A`. -/
theorem lowerCentralLayerZeroEquivMap_equivariant
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A)
    (g : X) (z : lowerCentralLayer C 0) :
    lowerCentralLayerZeroEquivMap hG h hPhi
        (lowerCentralLayerAction h.right.2.restrict 0 g z) =
      (h.left.2.map_quotient h.right.2).restrict g
        (lowerCentralLayerZeroEquivMap hG h hPhi z) := by
  refine QuotientGroup.induction_on z ?_
  intro x
  apply Subtype.ext
  simp only [IsAInvariant.restrict_apply_val]
  rfl

/-- The cover condition makes the actual first lower-central layer
irreducible at the subgroup-with-operators level. -/
theorem lowerCentralLayerZero_invariant_subgroup_eq_bot_or_top
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A)
    (J : Subgroup (lowerCentralLayer C 0))
    (hJ : IsAInvariant
      (lowerCentralLayerAction h.right.2.restrict 0) J) :
    J = ⊥ ∨ J = ⊤ := by
  let e := lowerCentralLayerZeroEquivMap hG h hPhi
  let Jbar : Subgroup ↥(C.map (QuotientGroup.mk' A)) :=
    J.map e.toMonoidHom
  have hJbar : IsAInvariant
      (h.left.2.map_quotient h.right.2).restrict Jbar := by
    rw [isAInvariant_iff_smul_mem]
    rintro g _ ⟨z, hz, rfl⟩
    change (h.left.2.map_quotient h.right.2).restrict g
      (lowerCentralLayerZeroEquivMap hG h hPhi z) ∈ Jbar
    rw [← lowerCentralLayerZeroEquivMap_equivariant hG h hPhi]
    exact ⟨lowerCentralLayerAction h.right.2.restrict 0 g z,
      hJ.smul_mem g hz, rfl⟩
  rcases h.invariant_subgroup_quotient_eq_bot_or_top hG Jbar hJbar with
    hbot | htop
  · left
    exact (J.map_eq_bot_iff_of_injective e.injective).mp hbot
  · right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    calc
      J.map e.toMonoidHom = ⊤ := htop
      _ = (⊤ : Subgroup (lowerCentralLayer C 0)).map
          e.toMonoidHom := by
        rw [← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr e.surjective]

/-- A genuine cover has a nonzero first lower-central layer once
`A = Phi(C)` identifies its kernel. -/
theorem lowerCentralLayerZero_nontrivial
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    Nontrivial (lowerCentralLayer C 0) := by
  have hCbar_ne : C.map (QuotientGroup.mk' A) ≠ ⊥ := by
    intro hbot
    have hCA : C ≤ A := by
      have hker : C ≤ (QuotientGroup.mk' A).ker :=
        (Subgroup.map_eq_bot_iff C).mp hbot
      simpa using hker
    exact h.lt.2 hCA
  letI : Nontrivial ↥(C.map (QuotientGroup.mk' A)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hCbar_ne
  exact (lowerCentralLayerZeroEquivMap hG h hPhi).toEquiv.nontrivial

section LinearTransport

local instance lemmaSevenCoverLayerCommGroup
    (H : Type*) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance lemmaSevenCoverLayerModTwo
    (H : Type*) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The ambient image `C/A` inherits the elementary-abelian structure of
the actual first lower-central layer. -/
theorem coverMap_isElementaryAbelian
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    IsElementaryAbelian 2 ↥(C.map (QuotientGroup.mk' A)) :=
  IsElementaryAbelian.of_mulEquiv
    (lowerCentralLayerZeroEquivMap hG h hPhi)
    (lowerCentralLayer_isElementaryAbelian C 0)

/-- Linear form of the canonical identification `L₁(C) ≃ C/A`. -/
noncomputable def lowerCentralLayerZeroLinearEquivMap
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    let hEA := coverMap_isElementaryAbelian hG h hPhi
    letI : IsMulCommutative ↥(C.map (QuotientGroup.mk' A)) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2)
        (Additive ↥(C.map (QuotientGroup.mk' A))) := hEA.zmodModule
    Additive (lowerCentralLayer C 0) ≃ₗ[ZMod 2]
      Additive ↥(C.map (QuotientGroup.mk' A)) := by
  let hEA := coverMap_isElementaryAbelian hG h hPhi
  letI : IsMulCommutative ↥(C.map (QuotientGroup.mk' A)) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2)
      (Additive ↥(C.map (QuotientGroup.mk' A))) := hEA.zmodModule
  exact (MulEquiv.toAdditive
      (lowerCentralLayerZeroEquivMap hG h hPhi)).toLinearEquiv
    (fun c x => ZMod.map_smul
      (MulEquiv.toAdditive
        (lowerCentralLayerZeroEquivMap hG h hPhi)).toAddMonoidHom c x)

/-- The linear equivalence intertwines the two canonical `F₂`
representations. -/
theorem lowerCentralLayerZeroLinearEquivMap_equivariant
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    let hEA := coverMap_isElementaryAbelian hG h hPhi
    letI : IsMulCommutative ↥(C.map (QuotientGroup.mk' A)) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2)
        (Additive ↥(C.map (QuotientGroup.mk' A))) := hEA.zmodModule
    ∀ (g : X) (v : Additive (lowerCentralLayer C 0)),
      lowerCentralLayerZeroLinearEquivMap hG h hPhi
          (lowerCentralLayerRepresentation h.right.2.restrict 0 g v) =
        elabRepresentation 2
          (h.left.2.map_quotient h.right.2).restrict g
          (lowerCentralLayerZeroLinearEquivMap hG h hPhi v) := by
  dsimp only
  let hEA := coverMap_isElementaryAbelian hG h hPhi
  letI : IsMulCommutative ↥(C.map (QuotientGroup.mk' A)) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2)
      (Additive ↥(C.map (QuotientGroup.mk' A))) := hEA.zmodModule
  intro g v
  apply Additive.toMul.injective
  change lowerCentralLayerZeroEquivMap hG h hPhi
      (lowerCentralLayerAction h.right.2.restrict 0 g v.toMul) =
    (h.left.2.map_quotient h.right.2).restrict g
      (lowerCentralLayerZeroEquivMap hG h hPhi v.toMul)
  exact lowerCentralLayerZeroEquivMap_equivariant
    hG h hPhi g v.toMul

/-- `NormalInvariantCover` and `A = Phi(C)` supply Higman's omitted
irreducibility hypothesis for the actual canonical `L₁` representation. -/
theorem lowerCentralLayerZeroRepresentation_isIrreducible
    [Finite G] (hG : IsPGroup 2 G)
    {act : X →* MulAut G} {A C : Subgroup G} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : ambientFrattini C = A) :
    Representation.IsIrreducible
      (lowerCentralLayerRepresentation h.right.2.restrict 0) := by
  classical
  letI : Nontrivial (lowerCentralLayer C 0) :=
    lowerCentralLayerZero_nontrivial hG h hPhi
  let rho := lowerCentralLayerRepresentation h.right.2.restrict 0
  let Phi : Submodule (ZMod 2) (Additive (lowerCentralLayer C 0)) ≃o
      Subgroup (lowerCentralLayer C 0) :=
    elabSubmoduleSubgroupEquiv 2
  have hmem : ∀
      (W : Submodule (ZMod 2) (Additive (lowerCentralLayer C 0)))
      (x : lowerCentralLayer C 0),
      x ∈ Phi W ↔ Additive.ofMul x ∈ W := by
    intro W x
    exact mem_elabSubmoduleSubgroupEquiv W x
  have hbot_ne_top : (⊥ : Subrepresentation rho) ≠ ⊤ := by
    exact fun hEq => bot_ne_top
      (congrArg Subrepresentation.toSubmodule hEq)
  letI : Nontrivial (Subrepresentation rho) :=
    ⟨⊥, ⊤, hbot_ne_top⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hSne => ?_
  have hJinv : IsAInvariant
      (lowerCentralLayerAction h.right.2.restrict 0)
      (Phi S.toSubmodule) := by
    rw [isAInvariant_iff_smul_mem]
    intro g x hx
    rw [hmem] at hx ⊢
    have hs := S.apply_mem_toSubmodule g hx
    change rho g (Additive.ofMul x) ∈ S.toSubmodule at hs
    simpa [rho, lowerCentralLayerRepresentation_apply] using hs
  rcases lowerCentralLayerZero_invariant_subgroup_eq_bot_or_top
      hG h hPhi (Phi S.toSubmodule) hJinv with hbot | htop
  · exfalso
    apply hSne
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    rw [← Phi.symm_apply_apply S.toSubmodule, hbot]
    exact Phi.symm.map_bot
  · apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    rw [← Phi.symm_apply_apply S.toSubmodule, htop]
    exact Phi.symm.map_top

end LinearTransport

end NormalInvariantCover

/-! ## Higman Lemma 7: the second lower-central layer as an Agemo factor

On p. 86 Higman says that the composition factors of `C` inside the abelian
normal subgroup `A` are power-isomorphic.  For the factor used in Lemma 7 this
means identifying

`L₂(C) = C' / (C'^2 C₃)`

with a successive Agemo factor `AgemoSuccQuotient A s`.  The next declarations
make the omitted identification explicit.  First we transport subgroup
quotients through injective maps into a common ambient group; then we apply
the normal invariant-subgroup classification in `A` to show that the images
of `C'` and `C'^2 C₃` are adjacent Agemo terms. -/

universe uP uS uT uX

/-- Transport two subgroups whose injective images agree in a common ambient
group.  This is the reusable group-level core of Higman's `C' / (C'^2 C₃)`
Agemo-factor identification. -/
private noncomputable def subgroupEquivOfInjectiveAmbientMaps
    {P : Type uP} {S : Type uS} {T : Type uT}
    [Group P] [Group S] [Group T]
    (f : S →* P) (g : T →* P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (B : Subgroup S) (E : Subgroup T)
    (hBE : B.map f = E.map g) : B ≃* E :=
  (B.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hBE).trans
      (E.equivMapOfInjective g hg).symm)

@[simp] private theorem subgroupEquivOfInjectiveAmbientMaps_apply_val
    {P : Type uP} {S : Type uS} {T : Type uT}
    [Group P] [Group S] [Group T]
    (f : S →* P) (g : T →* P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (B : Subgroup S) (E : Subgroup T)
    (hBE : B.map f = E.map g) (x : B) :
    g ((subgroupEquivOfInjectiveAmbientMaps f g hf hg B E hBE x : E) : T) =
      f (x : S) := by
  let y : E.map g :=
    (MulEquiv.subgroupCongr hBE) (B.equivMapOfInjective f hf x)
  have hy := Subgroup.coe_equivMapOfInjective_apply E g hg
    ((E.equivMapOfInjective g hg).symm y)
  rw [(E.equivMapOfInjective g hg).apply_symm_apply] at hy
  calc
    g (((E.equivMapOfInjective g hg).symm y : E) : T) = (y : P) := hy.symm
    _ = f (x : S) := by
      simp [y, MulEquiv.subgroupCongr_apply,
        Subgroup.coe_equivMapOfInjective_apply]

private theorem subgroupEquivOfInjectiveAmbientMaps_map_eq
    {P : Type uP} {S : Type uS} {T : Type uT}
    [Group P] [Group S] [Group T]
    (f : S →* P) (g : T →* P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (B : Subgroup S) (E : Subgroup T)
    (hBE : B.map f = E.map g)
    (K : Subgroup B) (L : Subgroup E)
    (hKL : (K.map B.subtype).map f = (L.map E.subtype).map g) :
    K.map (subgroupEquivOfInjectiveAmbientMaps f g hf hg B E hBE) = L := by
  let e : B ≃* E :=
    subgroupEquivOfInjectiveAmbientMaps f g hf hg B E hBE
  apply Subgroup.map_injective (f := g.comp E.subtype)
    (hg.comp E.subtype_injective)
  have he : (g.comp E.subtype).comp (e : B →* E) =
      f.comp B.subtype := by
    ext x
    exact subgroupEquivOfInjectiveAmbientMaps_apply_val
      f g hf hg B E hBE x
  rw [Subgroup.map_map, he]
  simpa only [Subgroup.map_map] using hKL

/-- Quotient-level transport associated to
`subgroupEquivOfInjectiveAmbientMaps`. -/
private noncomputable def subgroupQuotientEquivOfInjectiveAmbientMaps
    {P : Type uP} {S : Type uS} {T : Type uT}
    [Group P] [Group S] [Group T]
    (f : S →* P) (g : T →* P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (B : Subgroup S) (E : Subgroup T)
    (hBE : B.map f = E.map g)
    (K : Subgroup B) (L : Subgroup E) [K.Normal] [L.Normal]
    (hKL : (K.map B.subtype).map f = (L.map E.subtype).map g) :
    (B ⧸ K) ≃* (E ⧸ L) :=
  QuotientGroup.congr K L
    (subgroupEquivOfInjectiveAmbientMaps f g hf hg B E hBE)
    (subgroupEquivOfInjectiveAmbientMaps_map_eq
      f g hf hg B E hBE K L hKL)

@[simp] private theorem subgroupQuotientEquivOfInjectiveAmbientMaps_mk
    {P : Type uP} {S : Type uS} {T : Type uT}
    [Group P] [Group S] [Group T]
    (f : S →* P) (g : T →* P)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (B : Subgroup S) (E : Subgroup T)
    (hBE : B.map f = E.map g)
    (K : Subgroup B) (L : Subgroup E) [K.Normal] [L.Normal]
    (hKL : (K.map B.subtype).map f = (L.map E.subtype).map g)
    (x : B) :
    subgroupQuotientEquivOfInjectiveAmbientMaps
        f g hf hg B E hBE K L hKL (QuotientGroup.mk' K x) =
      QuotientGroup.mk' L
        (subgroupEquivOfInjectiveAmbientMaps f g hf hg B E hBE x) := by
  exact QuotientGroup.congr_mk _ _ _ _ x

/-! ### Index-parametric lower-central layer transport -/

/-- Internal numerator transport for an arbitrary lower-central index. -/
private noncomputable def lowerCentralTermEquivAgemoAt
    {P : Type uP} [Group P] (A C : Subgroup P)
    (i s : ℕ)
    (hB : (lowerCentralTerm C i).map C.subtype =
      (Agemo A 2 s).map A.subtype) :
    lowerCentralTerm C i ≃* Agemo A 2 s :=
  subgroupEquivOfInjectiveAmbientMaps
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C i) (Agemo A 2 s) hB

private theorem lowerCentralTermEquivAgemoAt_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (i s : ℕ)
      (hB : (lowerCentralTerm C i).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (g : X) (x : lowerCentralTerm C i),
      lowerCentralTermEquivAgemoAt A C i s hB
          (lowerCentralTermAction hCinv.restrict i g x) =
        agemoRestrictAction hAinv.restrict s g
          (lowerCentralTermEquivAgemoAt A C i s hB x) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro i s hB g x
  apply Subtype.ext
  apply Subtype.ext
  calc
    A.subtype
        ((lowerCentralTermEquivAgemoAt A C i s hB
          (lowerCentralTermAction hCinv.restrict i g x) : Agemo A 2 s) : A) =
      C.subtype
        ((lowerCentralTermAction hCinv.restrict i g x :
          lowerCentralTerm C i) : C) :=
      subgroupEquivOfInjectiveAmbientMaps_apply_val
        C.subtype A.subtype C.subtype_injective A.subtype_injective
        (lowerCentralTerm C i) (Agemo A 2 s) hB _
    _ = act g (C.subtype x) := rfl
    _ = act g (A.subtype
        ((lowerCentralTermEquivAgemoAt A C i s hB x : Agemo A 2 s) : A)) :=
      congrArg (act g)
        (subgroupEquivOfInjectiveAmbientMaps_apply_val
          C.subtype A.subtype C.subtype_injective A.subtype_injective
          (lowerCentralTerm C i) (Agemo A 2 s) hB x).symm
    _ = A.subtype
        ((agemoRestrictAction hAinv.restrict s g
          (lowerCentralTermEquivAgemoAt A C i s hB x) : Agemo A 2 s) : A) := rfl

private theorem lowerCentralLayerKernel_agemo_kernel_ambient
    {P : Type uP} [Group P] (A C : Subgroup P)
    (i s : ℕ)
    (hD : (lowerCentralLayerKernelInAmbient C i).map C.subtype =
      (Agemo A 2 (s + 1)).map A.subtype) :
    ((lowerCentralLayerKernel C i).map (lowerCentralTerm C i).subtype).map
        C.subtype =
      (((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)).map
        (Agemo A 2 s).subtype).map A.subtype := by
  change (lowerCentralLayerKernelInAmbient C i).map C.subtype = _
  rw [Subgroup.map_subgroupOf_eq_of_le (Agemo.anti (Nat.le_succ s))]
  exact hD

/-- Internal group equivalence underlying the indexed linear transport. -/
private noncomputable def lowerCentralLayerEquivAgemoSuccAt
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (i s : ℕ)
      (_hB : (lowerCentralTerm C i).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (_hD : (lowerCentralLayerKernelInAmbient C i).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype),
      lowerCentralLayer C i ≃* AgemoSuccQuotient A s := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro i s hB hD
  exact subgroupQuotientEquivOfInjectiveAmbientMaps
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C i) (Agemo A 2 s) hB
    (lowerCentralLayerKernel C i)
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
    (lowerCentralLayerKernel_agemo_kernel_ambient A C i s hD)

private theorem lowerCentralLayerEquivAgemoSuccAt_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (i s : ℕ)
      (hB : (lowerCentralTerm C i).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C i).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype)
      (g : X) (q : lowerCentralLayer C i),
      lowerCentralLayerEquivAgemoSuccAt A C hAcomm i s hB hD
          (lowerCentralLayerAction hCinv.restrict i g q) =
        agemoSuccQuotientAction hAinv.restrict s g
          (lowerCentralLayerEquivAgemoSuccAt A C hAcomm i s hB hD q) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro i s hB hD g q
  refine QuotientGroup.induction_on q ?_
  intro x
  change lowerCentralLayerEquivAgemoSuccAt A C hAcomm i s hB hD
      (lowerCentralLayerAction hCinv.restrict i g
        (QuotientGroup.mk' (lowerCentralLayerKernel C i) x)) =
    agemoSuccQuotientAction hAinv.restrict s g
      (lowerCentralLayerEquivAgemoSuccAt A C hAcomm i s hB hD
        (QuotientGroup.mk' (lowerCentralLayerKernel C i) x))
  rw [lowerCentralLayerAction_apply_mk]
  change QuotientGroup.mk' _
      (lowerCentralTermEquivAgemoAt A C i s hB
        (lowerCentralTermAction hCinv.restrict i g x)) =
    QuotientGroup.mk' _
      (agemoRestrictAction hAinv.restrict s g
        (lowerCentralTermEquivAgemoAt A C i s hB x))
  rw [lowerCentralTermEquivAgemoAt_equivariant
    act A C hAcomm hAinv hCinv i s hB]

/-- Transport the actual `i`-th lower-central layer to a successive Agemo
quotient when numerator and denominator agree in a common ambient group. -/
noncomputable def lowerCentralLayerLinearEquivAgemoSuccAt
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (i s : ℕ)
      (_hB : (lowerCentralTerm C i).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (_hD : (lowerCentralLayerKernelInAmbient C i).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype),
      letI : IsMulCommutative (lowerCentralLayer C i) :=
        lowerCentralLayerIsMulCommutative C i
      letI : Module (ZMod 2) (Additive (lowerCentralLayer C i)) :=
        lowerCentralLayerZmodModule C i
      Additive (lowerCentralLayer C i) ≃ₗ[ZMod 2]
        Additive (AgemoSuccQuotient A s) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro i s hB hD
  letI : IsMulCommutative (lowerCentralLayer C i) :=
    lowerCentralLayerIsMulCommutative C i
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C i)) :=
    lowerCentralLayerZmodModule C i
  let e := lowerCentralLayerEquivAgemoSuccAt A C hAcomm i s hB hD
  exact
    { e.toAdditive with
      map_smul' := ZMod.map_smul e.toAdditive.toAddMonoidHom }

/-- The indexed lower-central/Agemo linear equivalence intertwines the
actions induced from the common ambient actor. -/
theorem lowerCentralLayerLinearEquivAgemoSuccAt_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (i s : ℕ)
      (hB : (lowerCentralTerm C i).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C i).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype),
      letI : IsMulCommutative (lowerCentralLayer C i) :=
        lowerCentralLayerIsMulCommutative C i
      letI : Module (ZMod 2) (Additive (lowerCentralLayer C i)) :=
        lowerCentralLayerZmodModule C i
      ∀ (g : X) (q : Additive (lowerCentralLayer C i)),
      lowerCentralLayerLinearEquivAgemoSuccAt
          A C hAcomm i s hB hD
          (lowerCentralLayerRepresentation hCinv.restrict i g q) =
        agemoSuccQuotientRepresentation hAinv.restrict s g
          (lowerCentralLayerLinearEquivAgemoSuccAt
            A C hAcomm i s hB hD q) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro i s hB hD
  letI : IsMulCommutative (lowerCentralLayer C i) :=
    lowerCentralLayerIsMulCommutative C i
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C i)) :=
    lowerCentralLayerZmodModule C i
  intro g q
  apply Additive.toMul.injective
  exact lowerCentralLayerEquivAgemoSuccAt_equivariant
    act A C hAcomm hAinv hCinv i s hB hD g q.toMul

/-- The numerator identification `C' ≃ Agemo A 2 s`, determined by equality
of their images in the ambient group. -/
noncomputable def lowerCentralTermOneEquivAgemo
    {P : Type uP} [Group P] (A C : Subgroup P)
    (s : ℕ)
    (hB : (lowerCentralTerm C 1).map C.subtype =
      (Agemo A 2 s).map A.subtype) :
    lowerCentralTerm C 1 ≃* Agemo A 2 s :=
  subgroupEquivOfInjectiveAmbientMaps
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C 1) (Agemo A 2 s) hB

@[simp] theorem lowerCentralTermOneEquivAgemo_apply_val
    {P : Type uP} [Group P] (A C : Subgroup P)
    (s : ℕ)
    (hB : (lowerCentralTerm C 1).map C.subtype =
      (Agemo A 2 s).map A.subtype)
    (x : lowerCentralTerm C 1) :
    A.subtype ((lowerCentralTermOneEquivAgemo A C s hB x : Agemo A 2 s) : A) =
      C.subtype (x : C) :=
  subgroupEquivOfInjectiveAmbientMaps_apply_val
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C 1) (Agemo A 2 s) hB x

private theorem lowerCentralLayerOne_agemo_kernel_ambient
    {P : Type uP} [Group P] (A C : Subgroup P)
    (s : ℕ)
    (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
      (Agemo A 2 (s + 1)).map A.subtype) :
    ((lowerCentralLayerKernel C 1).map (lowerCentralTerm C 1).subtype).map
        C.subtype =
      (((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)).map
        (Agemo A 2 s).subtype).map A.subtype := by
  change (lowerCentralLayerKernelInAmbient C 1).map C.subtype = _
  rw [Subgroup.map_subgroupOf_eq_of_le (Agemo.anti (Nat.le_succ s))]
  exact hD

/-- Higman's group isomorphism
`L₂(C) = C' / (C'^2 C₃) ≃ Agemo A 2 s / Agemo A 2 (s+1)`. -/
noncomputable def lowerCentralLayerOneEquivAgemoSucc
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (s : ℕ)
      (_hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (_hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype),
      lowerCentralLayer C 1 ≃* AgemoSuccQuotient A s := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro s hB hD
  exact subgroupQuotientEquivOfInjectiveAmbientMaps
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C 1) (Agemo A 2 s) hB
    (lowerCentralLayerKernel C 1)
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
    (lowerCentralLayerOne_agemo_kernel_ambient A C s hD)

@[simp] theorem lowerCentralLayerOneEquivAgemoSucc_mk
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (s : ℕ)
      (hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype)
      (x : lowerCentralTerm C 1),
      lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD
          (QuotientGroup.mk' (lowerCentralLayerKernel C 1) x) =
        QuotientGroup.mk'
          ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
          (lowerCentralTermOneEquivAgemo A C s hB x) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro s hB hD x
  exact subgroupQuotientEquivOfInjectiveAmbientMaps_mk
    C.subtype A.subtype C.subtype_injective A.subtype_injective
    (lowerCentralTerm C 1) (Agemo A 2 s) hB
    (lowerCentralLayerKernel C 1)
    ((Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s))
    (lowerCentralLayerOne_agemo_kernel_ambient A C s hD) x

theorem lowerCentralTermOneEquivAgemo_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (s : ℕ)
      (hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (g : X) (x : lowerCentralTerm C 1),
      lowerCentralTermOneEquivAgemo A C s hB
          (lowerCentralTermAction hCinv.restrict 1 g x) =
        agemoRestrictAction hAinv.restrict s g
          (lowerCentralTermOneEquivAgemo A C s hB x) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro s hB g x
  apply Subtype.ext
  apply Subtype.ext
  calc
    A.subtype
        ((lowerCentralTermOneEquivAgemo A C s hB
          (lowerCentralTermAction hCinv.restrict 1 g x) : Agemo A 2 s) : A) =
      C.subtype
        ((lowerCentralTermAction hCinv.restrict 1 g x : lowerCentralTerm C 1) : C) :=
      lowerCentralTermOneEquivAgemo_apply_val A C s hB _
    _ = act g (C.subtype x) := rfl
    _ = act g (A.subtype
        ((lowerCentralTermOneEquivAgemo A C s hB x : Agemo A 2 s) : A)) :=
      congrArg (act g)
        (lowerCentralTermOneEquivAgemo_apply_val A C s hB x).symm
    _ = A.subtype
        ((agemoRestrictAction hAinv.restrict s g
          (lowerCentralTermOneEquivAgemo A C s hB x) : Agemo A 2 s) : A) := rfl

theorem lowerCentralLayerOneEquivAgemoSucc_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (s : ℕ)
      (hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype)
      (g : X) (q : lowerCentralLayer C 1),
      lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD
          (lowerCentralLayerAction hCinv.restrict 1 g q) =
        agemoSuccQuotientAction hAinv.restrict s g
          (lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD q) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro s hB hD g q
  refine QuotientGroup.induction_on q ?_
  intro x
  change lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD
      (lowerCentralLayerAction hCinv.restrict 1 g
        (QuotientGroup.mk' (lowerCentralLayerKernel C 1) x)) =
    agemoSuccQuotientAction hAinv.restrict s g
      (lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD
        (QuotientGroup.mk' (lowerCentralLayerKernel C 1) x))
  rw [lowerCentralLayerAction_apply_mk,
    lowerCentralLayerOneEquivAgemoSucc_mk A C hAcomm,
    lowerCentralLayerOneEquivAgemoSucc_mk A C hAcomm]
  change QuotientGroup.mk' _
      (lowerCentralTermOneEquivAgemo A C s hB
        (lowerCentralTermAction hCinv.restrict 1 g x)) =
    QuotientGroup.mk' _
      (agemoRestrictAction hAinv.restrict s g
        (lowerCentralTermOneEquivAgemo A C s hB x))
  rw [lowerCentralTermOneEquivAgemo_equivariant
    act A C hAcomm hAinv hCinv]

/-- The preceding group isomorphism, upgraded to the `ZMod 2`-linear
isomorphism required by Higman's representation-theoretic argument. -/
noncomputable def lowerCentralLayerOneLinearEquivAgemoSucc
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 1) :=
      lowerCentralLayerIsMulCommutative C 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
      lowerCentralLayerZmodModule C 1
    ∀ (s : ℕ)
      (_hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (_hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype),
      Additive (lowerCentralLayer C 1) ≃ₗ[ZMod 2]
        Additive (AgemoSuccQuotient A s) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 1) :=
    lowerCentralLayerIsMulCommutative C 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
    lowerCentralLayerZmodModule C 1
  intro s hB hD
  let e := lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD
  exact
    { e.toAdditive with
      map_smul' := ZMod.map_smul e.toAdditive.toAddMonoidHom }

@[simp] theorem lowerCentralLayerOneLinearEquivAgemoSucc_apply
    {P : Type uP} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 1) :=
      lowerCentralLayerIsMulCommutative C 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
      lowerCentralLayerZmodModule C 1
    ∀ (s : ℕ)
      (hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype)
      (q : Additive (lowerCentralLayer C 1)),
      lowerCentralLayerOneLinearEquivAgemoSucc A C hAcomm s hB hD q =
        Additive.ofMul
          (lowerCentralLayerOneEquivAgemoSucc A C hAcomm s hB hD q.toMul) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 1) :=
    lowerCentralLayerIsMulCommutative C 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
    lowerCentralLayerZmodModule C 1
  intro s hB hD q
  rfl

theorem lowerCentralLayerOneLinearEquivAgemoSucc_equivariant
    {P : Type uP} {X : Type uX} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 1) :=
      lowerCentralLayerIsMulCommutative C 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
      lowerCentralLayerZmodModule C 1
    ∀ (s : ℕ)
      (hB : (lowerCentralTerm C 1).map C.subtype =
        (Agemo A 2 s).map A.subtype)
      (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (Agemo A 2 (s + 1)).map A.subtype)
      (g : X) (q : Additive (lowerCentralLayer C 1)),
      lowerCentralLayerOneLinearEquivAgemoSucc A C hAcomm s hB hD
          (lowerCentralLayerRepresentation hCinv.restrict 1 g q) =
        agemoSuccQuotientRepresentation hAinv.restrict s g
          (lowerCentralLayerOneLinearEquivAgemoSucc A C hAcomm s hB hD q) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 1) :=
    lowerCentralLayerIsMulCommutative C 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
    lowerCentralLayerZmodModule C 1
  intro s hB hD g q
  apply Additive.toMul.injective
  exact lowerCentralLayerOneEquivAgemoSucc_equivariant
    act A C hAcomm hAinv hCinv s hB hD g q.toMul

/-! ### Adjacency of the two Agemo terms

The hypothesis used here is Higman's classification of actor-invariant
subgroups of `A` by its power series.  Since `C'^2 C₃ < C'` and contains the
squares of `C'`, the two classified terms must be consecutive. -/

/-- A strict invariant pair `D < B` in the classified Agemo chain is adjacent
when `D` contains the squares of `B`. -/
theorem exists_eq_agemo_and_eq_succ_of_invariant_strict_of_agemo_one_le
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) {e : ℕ}
    (classify : ∀ U : Subgroup A, IsAInvariant φ U →
      ∃ s ≤ e, U = Agemo A 2 s)
    {D B : Subgroup A}
    (hDinv : IsAInvariant φ D) (hBinv : IsAInvariant φ B)
    (hDB : D < B)
    (hpow : (Agemo B 2 1).map B.subtype ≤ D) :
    ∃ s < e, B = Agemo A 2 s ∧ D = Agemo A 2 (s + 1) := by
  obtain ⟨s, _hse, hBs⟩ := classify B hBinv
  obtain ⟨t, hte, hDt⟩ := classify D hDinv
  have hst : s < t := by
    have hstle : s ≤ t := by
      by_contra hnot
      have hts : t ≤ s := Nat.le_of_not_ge hnot
      apply hDB.ne
      apply le_antisymm hDB.le
      rw [hBs, hDt]
      exact Agemo.anti hts
    exact hstle.lt_of_ne (by
      intro hEq
      apply hDB.ne
      rw [hBs, hDt, hEq])
  have hsuccD : Agemo A 2 (s + 1) ≤ D := by
    rw [agemo_succ_eq_map_agemo_one, ← hBs]
    exact hpow
  have hDsucc : D ≤ Agemo A 2 (s + 1) := by
    rw [hDt]
    exact Agemo.anti (by omega)
  exact ⟨s, lt_of_lt_of_le hst hte, hBs,
    le_antisymm hDsucc hsuccD⟩

/-- Higman's numerator `C'`, viewed as a subgroup of the abelian cover `A`. -/
def lowerCentralTermOneIn
    {P : Type*} [Group P] (A C : Subgroup P) : Subgroup A :=
  ((lowerCentralTerm C 1).map C.subtype).subgroupOf A

/-- Higman's denominator `C'^2 C₃`, viewed as a subgroup of `A`. -/
def lowerCentralLayerKernelOneIn
    {P : Type*} [Group P] (A C : Subgroup P) : Subgroup A :=
  ((lowerCentralLayerKernelInAmbient C 1).map C.subtype).subgroupOf A

theorem lowerCentralTermOneIn_map_subtype
    {P : Type*} [Group P] (A C : Subgroup P)
    (hB : (lowerCentralTerm C 1).map C.subtype ≤ A) :
    (lowerCentralTermOneIn A C).map A.subtype =
      (lowerCentralTerm C 1).map C.subtype := by
  exact Subgroup.map_subgroupOf_eq_of_le hB

theorem lowerCentralLayerKernelOneIn_map_subtype
    {P : Type*} [Group P] (A C : Subgroup P)
    (hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype ≤ A) :
    (lowerCentralLayerKernelOneIn A C).map A.subtype =
      (lowerCentralLayerKernelInAmbient C 1).map C.subtype := by
  exact Subgroup.map_subgroupOf_eq_of_le hD

theorem lowerCentralLayerKernelOneIn_le_termOneIn
    {P : Type*} [Group P] (A C : Subgroup P) :
    lowerCentralLayerKernelOneIn A C ≤ lowerCentralTermOneIn A C := by
  intro x hx
  change (x : P) ∈ (lowerCentralTerm C 1).map C.subtype
  apply Subgroup.map_mono (lowerCentralLayerKernelInAmbient_le C 1)
  exact hx

theorem lowerCentralTermOneIn_isAInvariant
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    IsAInvariant hAinv.restrict (lowerCentralTermOneIn A C) := by
  apply hAinv.subgroupOf
  exact aInvariant_map_subtype_of_restrict hCinv
    (IsAInvariant.lowerCentralSeries hCinv.restrict 1)

theorem lowerCentralLayerKernelOneIn_isAInvariant
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    IsAInvariant hAinv.restrict (lowerCentralLayerKernelOneIn A C) := by
  apply hAinv.subgroupOf
  apply aInvariant_map_subtype_of_restrict hCinv
  change IsAInvariant hCinv.restrict
    ((lowerCentralLayerKernel C 1).map (lowerCentralTerm C 1).subtype)
  exact aInvariant_map_subtype_of_restrict
    (IsAInvariant.lowerCentralSeries hCinv.restrict 1)
    (lowerCentralLayerKernel_isInvariant hCinv.restrict 1)

/-- The squares of the numerator lie in `C'^2 C₃`, the containment that
forces adjacency in the classified Agemo chain. -/
theorem agemo_one_termOneIn_map_le_kernelOneIn
    {P : Type*} [Group P] (A C : Subgroup P)
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    (Agemo (lowerCentralTermOneIn A C) 2 1).map
      (lowerCentralTermOneIn A C).subtype ≤
        lowerCentralLayerKernelOneIn A C := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨z, hz⟩ := mem_agemo_iff_of_comm.mp hb
  rw [hz, pow_one]
  change ((z : A) : P) ^ 2 ∈
    (lowerCentralLayerKernelInAmbient C 1).map C.subtype
  have hzB : ((z : A) : P) ∈ (lowerCentralTerm C 1).map C.subtype := z.2
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzB
  let c' : lowerCentralTerm C 1 := ⟨c, hc⟩
  refine ⟨(lowerCentralTerm C 1).subtype (c' ^ 2), ?_, ?_⟩
  · exact ⟨c' ^ 2, sq_mem_lowerCentralLayerKernel C 1 c', rfl⟩
  · simpa [c'] using congrArg (fun y : P => y ^ 2) hcz

/-- Nontriviality of `L₂(C)` is exactly the strictness
`C'^2 C₃ < C'` needed by the adjacency argument. -/
theorem lowerCentralLayerKernelOneIn_lt_termOneIn_of_nontrivial
    {P : Type*} [Group P] (A C : Subgroup P)
    [Nontrivial (lowerCentralLayer C 1)]
    (hB : (lowerCentralTerm C 1).map C.subtype ≤ A) :
    lowerCentralLayerKernelOneIn A C < lowerCentralTermOneIn A C := by
  refine lt_of_le_of_ne (lowerCentralLayerKernelOneIn_le_termOneIn A C) ?_
  intro hEq
  have hD : (lowerCentralLayerKernelInAmbient C 1).map C.subtype ≤ A :=
    (Subgroup.map_mono (lowerCentralLayerKernelInAmbient_le C 1)).trans hB
  have hMaps :
      (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
        (lowerCentralTerm C 1).map C.subtype := by
    calc
      (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
          (lowerCentralLayerKernelOneIn A C).map A.subtype :=
        (lowerCentralLayerKernelOneIn_map_subtype A C hD).symm
      _ = (lowerCentralTermOneIn A C).map A.subtype :=
        congrArg (Subgroup.map A.subtype) hEq
      _ = (lowerCentralTerm C 1).map C.subtype :=
        lowerCentralTermOneIn_map_subtype A C hB
  have hAmbient : lowerCentralLayerKernelInAmbient C 1 =
      lowerCentralTerm C 1 :=
    Subgroup.map_injective C.subtype_injective hMaps
  have hKtop : lowerCentralLayerKernel C 1 = ⊤ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf C 1, hAmbient]
    exact Subgroup.subgroupOf_self _
  have hall : ∀ q : lowerCentralLayer C 1, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralLayerKernel C 1) q
    apply (QuotientGroup.eq_one_iff x).2
    rw [hKtop]
    exact Subgroup.mem_top x
  obtain ⟨q, hq⟩ := exists_ne (1 : lowerCentralLayer C 1)
  exact hq (hall q)

/-- Higman's assumption `C' ≤ A²` places the first lower-central term inside
the abelian cover `A`. -/
theorem lowerCentralTerm_one_map_le_of_derived_le_agemo_one
    {P : Type*} [Group P] (A C : Subgroup P)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    (lowerCentralTerm C 1).map C.subtype ≤ A := by
  have hterm : lowerCentralTerm C 1 = _root_.commutator C := by
    rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one]
  rw [hterm]
  exact hderived.trans (Subgroup.map_subtype_le _)

/-- **Higman, Lemma 7 (p. 86), second-layer Agemo bridge.**

If every actor-invariant subgroup of the abelian normal cover `A` is an Agemo
term and `C' ≤ A²`, then the actual second lower-central layer of `C` is
equivariantly linearly isomorphic to one successive Agemo factor of `A`.
This packages the source assertion that the relevant composition factors of
`C` in `A` are power-isomorphic. -/
theorem exists_lowerCentralLayerOne_linearEquiv_agemoSucc_of_classification
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) (A C : Subgroup P)
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    {e : ℕ} [Nontrivial (lowerCentralLayer C 1)] :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 1) :=
      lowerCentralLayerIsMulCommutative C 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
      lowerCentralLayerZmodModule C 1
    (∀ U : Subgroup A, IsAInvariant hAinv.restrict U →
      ∃ s ≤ e, U = Agemo A 2 s) →
    ((_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) →
    ∃ s < e,
      ∃ E : Additive (lowerCentralLayer C 1) ≃ₗ[ZMod 2]
          Additive (AgemoSuccQuotient A s),
        ∀ g q,
          E (lowerCentralLayerRepresentation hCinv.restrict 1 g q) =
            agemoSuccQuotientRepresentation hAinv.restrict s g (E q) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 1) :=
    lowerCentralLayerIsMulCommutative C 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 1)) :=
    lowerCentralLayerZmodModule C 1
  intro classify hderived
  let B : Subgroup A := lowerCentralTermOneIn A C
  let D : Subgroup A := lowerCentralLayerKernelOneIn A C
  have hBinP : (lowerCentralTerm C 1).map C.subtype ≤ A :=
    lowerCentralTerm_one_map_le_of_derived_le_agemo_one A C hderived
  have hDinP : (lowerCentralLayerKernelInAmbient C 1).map C.subtype ≤ A :=
    (Subgroup.map_mono (lowerCentralLayerKernelInAmbient_le C 1)).trans hBinP
  have hBinv : IsAInvariant hAinv.restrict B := by
    exact lowerCentralTermOneIn_isAInvariant act A C hAinv hCinv
  have hDinv : IsAInvariant hAinv.restrict D := by
    exact lowerCentralLayerKernelOneIn_isAInvariant act A C hAinv hCinv
  have hDB : D < B := by
    exact lowerCentralLayerKernelOneIn_lt_termOneIn_of_nontrivial A C hBinP
  have hpow : (Agemo B 2 1).map B.subtype ≤ D := by
    exact agemo_one_termOneIn_map_le_kernelOneIn A C hAcomm
  obtain ⟨s, hse, hBs, hDs⟩ :=
    exists_eq_agemo_and_eq_succ_of_invariant_strict_of_agemo_one_le
      hAinv.restrict classify hDinv hBinv hDB hpow
  have hBambient : (lowerCentralTerm C 1).map C.subtype =
      (Agemo A 2 s).map A.subtype := by
    calc
      (lowerCentralTerm C 1).map C.subtype = B.map A.subtype :=
        (lowerCentralTermOneIn_map_subtype A C hBinP).symm
      _ = (Agemo A 2 s).map A.subtype :=
        congrArg (Subgroup.map A.subtype) hBs
  have hDambient : (lowerCentralLayerKernelInAmbient C 1).map C.subtype =
      (Agemo A 2 (s + 1)).map A.subtype := by
    calc
      (lowerCentralLayerKernelInAmbient C 1).map C.subtype = D.map A.subtype :=
        (lowerCentralLayerKernelOneIn_map_subtype A C hDinP).symm
      _ = (Agemo A 2 (s + 1)).map A.subtype :=
        congrArg (Subgroup.map A.subtype) hDs
  let E := lowerCentralLayerOneLinearEquivAgemoSucc
    A C hAcomm s hBambient hDambient
  refine ⟨s, hse, E, ?_⟩
  intro g q
  exact lowerCentralLayerOneLinearEquivAgemoSucc_equivariant
    act A C hAcomm hAinv hCinv s hBambient hDambient g q

/-! ## The lower-central spectral endpoint -/

local instance lemmaSevenLayerIsMulCommutative
    (H : Type*) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance lemmaSevenLayerModTwo
    (H : Type*) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The actor-side data needed to feed the actual first two lower-central
layers to Higman Lemma 4.

The bracket, alternation, full-span property, and equivariance do not occur
as fields: they are already proved for the actual lower-central layers. -/
structure LemmaSevenSpectralCertificate
    {H X : Type*} [Group H] [Group X] [Finite H]
    (phi : X →* MulAut H) where
  finrank_second_ge_two :
    2 ≤ Module.finrank (ZMod 2) (Additive (lowerCentralLayer H 1))
  faithful_first : Function.Injective
    (lowerCentralLayerRepresentation phi 0)
  transitive_second : ∀ v w : Additive (lowerCentralLayer H 1),
    v ≠ 0 → w ≠ 0 →
      ∃ x : X, lowerCentralLayerRepresentation phi 1 x v = w
  layerEquiv : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2]
    Additive (lowerCentralLayer H 1)
  layerEquiv_equivariant : ∀ x v,
    layerEquiv (lowerCentralLayerRepresentation phi 0 x v) =
      lowerCentralLayerRepresentation phi 1 x (layerEquiv v)

/-- A Lemma 7 spectral certificate contradicts the already-proved Higman
Lemma 4.  This is the complete adapter from the source's composition-factor
overlap to the actual lower-central commutator bracket. -/
theorem LemmaSevenSpectralCertificate.false
    {H X : Type u} [Group H] [CommGroup X]
    [Finite H] [Finite X] [IsCyclic X]
    (phi : X →* MulAut H)
    (d : LemmaSevenSpectralCertificate phi) : False := by
  let n := Module.finrank (ZMod 2) (Additive (lowerCentralLayer H 1))
  letI : Nontrivial (Additive (lowerCentralLayer H 1)) :=
    Module.nontrivial_of_finrank_pos
      (lt_of_lt_of_le (by omega : 0 < 2) d.finrank_second_ge_two)
  letI : Nontrivial (Additive (lowerCentralLayer H 0)) :=
    d.layerEquiv.toEquiv.nontrivial
  have htransFirst : ∀ v w : Additive (lowerCentralLayer H 0),
      v ≠ 0 → w ≠ 0 →
        ∃ x : X, lowerCentralLayerRepresentation phi 0 x v = w := by
    intro v w hv hw
    obtain ⟨x, hx⟩ := d.transitive_second
      (d.layerEquiv v) (d.layerEquiv w)
      (d.layerEquiv.map_ne_zero_iff.mpr hv)
      (d.layerEquiv.map_ne_zero_iff.mpr hw)
    refine ⟨x, d.layerEquiv.injective ?_⟩
    rw [d.layerEquiv_equivariant]
    exact hx
  have hirrFirst : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0) :=
    representation_isIrreducible_of_transitive_nonzero
      (lowerCentralLayerRepresentation phi 0) htransFirst
  apply (not_exists_equivariant_linearEquiv_of_higman_bracket
    (lowerCentralLayerRepresentation phi 0)
    (lowerCentralLayerRepresentation phi 1)
    n d.finrank_second_ge_two rfl
    hirrFirst d.faithful_first
    (lowerCentralCommutatorBilinear H))
  · intro x a b
    simpa only [← lowerCentralLayerRepresentation_apply, ofMul_toMul] using
      lowerCentralCommutatorBilinear_equivariant phi x a b
  · exact lowerCentralCommutatorBilinear_self H
  · exact lowerCentralCommutatorBilinear_span_eq_top H
  · exact d.transitive_second
  · exact ⟨d.layerEquiv, d.layerEquiv_equivariant⟩

end OddOrder.Higman.Suzuki2Groups
