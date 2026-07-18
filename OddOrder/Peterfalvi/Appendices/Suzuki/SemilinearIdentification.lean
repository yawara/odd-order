/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Peterfalvi Part II, Chapter I §2, Proposition 3 — Suzuki-side identifications

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §2, pp. 103–104.

This file prepares the group-theoretic input to Proposition 3.  In the faithful
action of `D̄ = D/W` on `Q₀`, it identifies the image `K̄` of the cyclic normal
subgroup `K` with `F(D̄)`, identifies `V̄` with the stabilizer of the distinguished
involution, proves that `F(D̄)` acts irreducibly on `Q₀`, and exhibits
`D̄ = K̄ ⋊ V̄` as an internal and external semidirect product.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)
open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch06 (actionFixedBy mem_actionFixedBy)
open scoped Pointwise

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The images `K̄`, `V̄`, and the distinguished point -/

/-- The image `K̄ = KW/W` of `K` in `D̄ = D/W`. -/
def Kbar : Subgroup hyp.Dbar :=
  (hyp.K.subgroupOf hyp.D).map
    (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D))

/-- The image `V̄ = V/W` of `V` in `D̄ = D/W`. -/
def Vbar : Subgroup hyp.Dbar :=
  (hyp.V.subgroupOf hyp.D).map
    (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D))

/-- The distinguished involution, regarded as a nonidentity point of `Q₀`. -/
noncomputable def sQ0 : ↥hyp.Q0 :=
  ⟨hyp.distinguishedInvolution,
    hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩

theorem sQ0_ne_one : hyp.sQ0 ≠ 1 := by
  intro h
  apply hyp.distinguishedInvolution_ne_one
  simpa [sQ0] using congrArg Subtype.val h

/-! ## `K̄ = F(D̄)` and `V̄ = C_D̄(s)` -/

/-- **Peterfalvi Part II, Ch. I §2, Proposition 2.**  The image `K̄` is the
Fitting subgroup of `D̄`. -/
theorem Kbar_eq_fitting : hyp.Kbar = fitting hyp.Dbar := by
  apply le_antisymm
  · rintro x ⟨k, hkK, rfl⟩
    apply hyp.mem_fittingPreimage_of_mem_KSet
    rw [← hyp.coe_K]
    exact hkK
  · intro x hxF
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    have hdpre : d ∈ hyp.fittingPreimage := by
      rw [hyp.mem_fittingPreimage_iff]
      exact hxF
    have hdG : (d : G) ∈ hyp.fittingPreimageInG := by
      change (d : G) ∈ hyp.fittingPreimage.map hyp.D.subtype
      exact ⟨d, hdpre, rfl⟩
    have hdKW : (d : G) ∈ hyp.KSet * (hyp.W : Set G) := by
      rw [← hyp.fittingPreimageInG_eq_KSet_mul_W]
      exact hdG
    rw [Set.mem_mul] at hdKW
    obtain ⟨k, hkK, w, hwW, hkw⟩ := hdKW
    let kd : ↥hyp.D := ⟨k, hyp.mem_D_of_mem_KSet hkK⟩
    let wd : ↥hyp.D := ⟨w, hyp.V_le_D (hyp.W_le_V hwW)⟩
    have hprod : kd * wd = d := Subtype.ext hkw
    refine ⟨kd, ?_, ?_⟩
    · change k ∈ (hyp.K : Set G)
      rw [hyp.coe_K]
      exact hkK
    · have hwd : wd ∈ hyp.W.subgroupOf hyp.D := hwW
      have hwdq : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) wd = 1 :=
        (QuotientGroup.eq_one_iff wd).mpr hwd
      change QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd =
        QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d
      calc
        _ = QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd * 1 := by rw [mul_one]
        _ = QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd *
              QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) wd := by rw [hwdq]
        _ = QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) (kd * wd) := by rw [map_mul]
        _ = QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) d := congrArg _ hprod

/-- **Peterfalvi Part II, Ch. I §2, Proposition 3 preparation.**  The image
`V̄ = V/W` is exactly the point stabilizer of the distinguished involution. -/
theorem Vbar_eq_pointStabilizer :
    hyp.Vbar =
      OddOrder.Peterfalvi.Appendices.Huppert.pointStabilizer
        hyp.conjQ0bar hyp.sQ0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hvV, hvx⟩ := hx
    rw [← hvx]
    rw [OddOrder.Peterfalvi.Appendices.Huppert.mem_pointStabilizer]
    obtain ⟨_, hvcent⟩ : (v : G) ∈ hyp.D ∧
        (v : G) ∈ Subgroup.centralizer {hyp.distinguishedInvolution} := by
      rw [← Subgroup.mem_inf, ← hyp.V_eq_centralizer_distinguishedInvolution]
      exact hvV
    have hcomm : Commute (v : G) hyp.distinguishedInvolution :=
      Subgroup.mem_centralizer_singleton_iff.mp hvcent
    change hyp.conjQ0bar (QuotientGroup.mk v) hyp.sQ0 = hyp.sQ0
    rw [hyp.conjQ0bar_mk]
    apply Subtype.ext
    rw [hyp.conjQ0_apply_coe]
    change (v : G) * hyp.distinguishedInvolution * (v : G)⁻¹ =
      hyp.distinguishedInvolution
    rw [hcomm.eq]
    group
  · intro hx
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    rw [OddOrder.Peterfalvi.Appendices.Huppert.mem_pointStabilizer] at hx
    have hfix : (d : G) * hyp.distinguishedInvolution * (d : G)⁻¹ =
        hyp.distinguishedInvolution := by
      simpa [sQ0] using congrArg Subtype.val hx
    have hcomm : Commute (d : G) hyp.distinguishedInvolution := by
      change (d : G) * hyp.distinguishedInvolution =
        hyp.distinguishedInvolution * (d : G)
      have h := congrArg (· * (d : G)) hfix
      simpa [mul_assoc] using h
    have hdV : (d : G) ∈ hyp.V := by
      rw [hyp.V_eq_centralizer_distinguishedInvolution]
      exact ⟨d.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    exact ⟨d, hdV, rfl⟩

/-! ## The irreducible Fitting action -/

/-- The restricted action of `F(D̄)` on `Q₀`. -/
def fittingAction : ↥(fitting hyp.Dbar) →* MulAut ↥hyp.Q0 :=
  hyp.conjQ0bar.comp (fitting hyp.Dbar).subtype

/-- `F(D̄)` is transitive on `Q₀^#`. -/
theorem fittingAction_transitive (a b : ↥hyp.Q0) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ g : ↥(fitting hyp.Dbar), hyp.fittingAction g a = b := by
  have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have himg := hyp.image_conj_KSet_eq_involutions_H
    (s := (a : G)) a.2.2 a.2.1 ha'
  have hbmem : (b : G) ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} :=
    ⟨b.2.1, hb', b.2.2⟩
  rw [← himg] at hbmem
  obtain ⟨k, hkK, hk⟩ := hbmem
  have hkiK : k⁻¹ ∈ hyp.KSet := hyp.inv_mem_KSet hkK
  let kd : ↥hyp.D := ⟨k⁻¹, hkiK.1⟩
  have hfit : QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd ∈ fitting hyp.Dbar :=
    hyp.mem_fittingPreimage_of_mem_KSet hkiK
  refine ⟨⟨QuotientGroup.mk' (hyp.W.subgroupOf hyp.D) kd, hfit⟩, ?_⟩
  change hyp.conjQ0bar (QuotientGroup.mk kd) a = b
  rw [hyp.conjQ0bar_mk]
  apply Subtype.ext
  change k⁻¹ * (a : G) * k⁻¹⁻¹ = (b : G)
  rw [inv_inv]
  exact hk

/-- The action of `F(D̄)` on `Q₀` is irreducible. -/
theorem fittingAction_irreducible (U : Subgroup ↥hyp.Q0)
    (hU : IsAInvariant hyp.fittingAction U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  rw [Subgroup.eq_top_iff']
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact U.one_mem
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨g, hg⟩ := hyp.fittingAction_transitive y x
    (fun h => hy (Subtype.ext h)) hx
  rw [← hg]
  exact hU.smul_mem g y.2

/-! ## The internal and external semidirect products -/

/-- `F(D̄)` and `V̄` are complementary subgroups of `D̄`. -/
theorem fitting_isComplement_Vbar :
    (fitting hyp.Dbar).IsComplement' hyp.Vbar := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hfpf := hyp.fitting_Dbar_cyclic_fpf_abelian.2.1 x hx.1 hx1
    have hxfix : hyp.conjQ0bar x hyp.sQ0 = hyp.sQ0 := by
      rw [hyp.Vbar_eq_pointStabilizer,
        OddOrder.Peterfalvi.Appendices.Huppert.mem_pointStabilizer] at hx
      exact hx.2
    have hsfix : hyp.sQ0 ∈ actionFixedBy hyp.conjQ0bar x :=
      mem_actionFixedBy.mpr hxfix
    rw [hfpf, Subgroup.mem_bot] at hsfix
    exact hyp.sQ0_ne_one hsfix
  · rw [Set.eq_univ_iff_forall]
    intro x
    let b : ↥hyp.Q0 := hyp.conjQ0bar x hyp.sQ0
    have hb1 : b ≠ 1 := by
      intro hb
      apply hyp.sQ0_ne_one
      have h := congrArg (hyp.conjQ0bar x).symm hb
      simpa [b] using h
    obtain ⟨a, ha⟩ := hyp.fittingAction_transitive
      hyp.sQ0 b hyp.sQ0_ne_one hb1
    let v : hyp.Dbar := (a : hyp.Dbar)⁻¹ * x
    have hv : v ∈ hyp.Vbar := by
      rw [hyp.Vbar_eq_pointStabilizer,
        OddOrder.Peterfalvi.Appendices.Huppert.mem_pointStabilizer]
      change hyp.conjQ0bar ((a : hyp.Dbar)⁻¹ * x) hyp.sQ0 = hyp.sQ0
      rw [map_mul, map_inv]
      change (hyp.conjQ0bar (a : hyp.Dbar))⁻¹
        (hyp.conjQ0bar x hyp.sQ0) = hyp.sQ0
      change (hyp.conjQ0bar (a : hyp.Dbar))⁻¹ b = hyp.sQ0
      change hyp.conjQ0bar (a : hyp.Dbar) hyp.sQ0 = b at ha
      rw [← ha]
      exact (hyp.conjQ0bar (a : hyp.Dbar)).symm_apply_apply hyp.sQ0
    refine ⟨(a : hyp.Dbar), a.2, v, hv, ?_⟩
    change (a : hyp.Dbar) * ((a : hyp.Dbar)⁻¹ * x) = x
    group

/-- The image `K̄` is normal in `D̄`. -/
instance Kbar_normal : hyp.Kbar.Normal :=
  (inferInstance : (hyp.K.subgroupOf hyp.D).Normal).map
    (QuotientGroup.mk' (hyp.W.subgroupOf hyp.D))
    (QuotientGroup.mk'_surjective (hyp.W.subgroupOf hyp.D))

/-- `K̄` and `V̄` are complementary subgroups of `D̄`. -/
theorem Kbar_isComplement_Vbar : hyp.Kbar.IsComplement' hyp.Vbar := by
  rw [hyp.Kbar_eq_fitting]
  exact hyp.fitting_isComplement_Vbar

/-- The conjugation action of `V̄` on the normal subgroup `K̄`. -/
abbrev KbarConjAction : ↥hyp.Vbar →* MulAut ↥hyp.Kbar :=
  (hyp.Kbar.normalizerMonoidHom).comp
    (Subgroup.inclusion (hyp.Kbar.normalizer_eq_top ▸ le_top))

/-- **Peterfalvi Part II, Ch. I §2, Proposition 3 preparation.**
The external semidirect product `K̄ ⋊ V̄` is isomorphic to `D̄`. -/
noncomputable def KbarSemidirectEquiv :
    ↥hyp.Kbar ⋊[hyp.KbarConjAction] ↥hyp.Vbar ≃* hyp.Dbar :=
  SemidirectProduct.mulEquivSubgroup hyp.Kbar_isComplement_Vbar

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
