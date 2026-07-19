/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppD_CNGroups.MaximalSylowIntersection

/-!
# BG Appendix D, Lemmas D.1 and D.2

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--155.

* **D.1**: in a minimal simple CN-group of odd order the Sylow `p`-subgroups form a
  trivial-intersection family.
* **D.2**: consequently a nontrivial Sylow `p`-subgroup lies in the derived subgroup of its own
  normalizer.

Both are proved by the Focal Subgroup Theorem (BG Thm 1.17, `commutator_inf_eq_focalSubgroup`
in mathlib) together with `G' = G`, which holds because `G` is simple and nonsolvable.  For D.1
the local analysis of `OddOrder.BG.AppD.MaximalSylowIntersection` supplies the key input: with
`N = N_G(Z(L(P)))`, every Sylow `p`-subgroup `R ≠ P` satisfies `P ∩ R ≤ O_p(N)`, and `N` is a
3-step group with respect to `p`.

⚠ Minimal simplicity is essential in both: see the module docstring of
`OddOrder.BG.AppD.Basic` for the two counterexamples among general odd CN-groups.
-/

namespace OddOrder.BG.AppD

open OddOrder.GroupTheory OddOrder.Isaacs

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **BG Lemma D.1** (mmd L5155): in a minimal simple CN-group of odd order, the Sylow
`p`-subgroups form a TI family — two Sylow `p`-subgroups meeting nontrivially are equal.

⚠ Minimal simplicity is essential: for general odd CN-groups this is **false**
(`F_{3⁶} ⋊ (C₇ ⋊ C₃)`; see `OddOrder.BG.AppD.Basic`).

Proof (BG, following **G**).  Suppose not, and put `N = N_G(Z(L(P)))`.  The local analysis shows
`N` is a 3-step group for `p` containing `P` as a Sylow `p`-subgroup, and that `P ∩ R ≤ O_p(N)`
for every Sylow `R ≠ P`.  Writing `K = O_{p,p'}(N)`, the quotient `N/K` is a nontrivial
`p`-group, so `N' K ≠ N` and `P ⊄ N'K`.  On the other hand each focal generator `⁅x, u⁆` of `P`
lies in `N'K`: if `u` normalizes `P` then `u ∈ N` and the commutator lies in `N'`; otherwise both
`x⁻¹` and its conjugate lie in intersections of `P` with *other* Sylow subgroups, hence in
`O_p(N) ≤ K`.  So the Focal Subgroup Theorem and `G' = G` give `P = P ∩ G' ≤ P ∩ N'K ⊊ P`. -/
theorem sylow_eq_of_nontrivial_inter (hyp : MinimalSimpleCNHypothesis G) (P Q : Sylow p G)
    (hinter : ((P : Subgroup G) ⊓ (Q : Subgroup G)) ≠ ⊥) :
    (P : Subgroup G) = (Q : Subgroup G) := by
  classical
  by_contra hPQ
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G,
      N = Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hPN : (P : Subgroup G) ≤ N := hN ▸ sylow_le_normalizer_zCenterLOdd P
  have h3 : IsThreeStepGroup ↥N p := by
    rw [hN]; exact isThreeStepGroup_normalizer_zCenterLOdd hyp (Ne.symm hPQ) hinter
  have hcore : ∀ R : Sylow p G, (R : Subgroup G) ≠ (P : Subgroup G) →
      (P : Subgroup G) ⊓ (R : Subgroup G) ≤ opiCoreInG ({p} : Set ℕ) N := by
    intro R hR
    rw [hN]; exact inf_le_oPiCore_normalizer_zCenterLOdd hyp hR
  have hnormP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ N := by
    rw [hN]; exact Ch2.S08.normalizer_le_normalizer_zCenterLOdd _
  -- `W = N'·O_{p,p'}(N)`, realized in `G`.
  set W : Subgroup G := (commutator ↥N ⊔ opPPrimeCore p ↥N).map N.subtype with hW
  -- `N'K ≠ N`, since `N/K` is a nontrivial `p`-group.
  haveI hntq : Nontrivial (↥N ⧸ opPPrimeCore p ↥N) := h3.nontrivial_quotient
  haveI hnilq : Group.IsNilpotent (↥N ⧸ opPPrimeCore p ↥N) := h3.isPGroup_quotient.isNilpotent
  have hne_top : commutator ↥N ⊔ opPPrimeCore p ↥N ≠ ⊤ := by
    intro heq
    refine (IsSolvable.commutator_lt_top_of_nontrivial (↥N ⧸ opPPrimeCore p ↥N)).ne ?_
    have hmapK : (opPPrimeCore p ↥N).map (QuotientGroup.mk' (opPPrimeCore p ↥N)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hpush := congrArg (Subgroup.map (QuotientGroup.mk' (opPPrimeCore p ↥N))) heq
    rw [Subgroup.map_sup, hmapK, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hpush
    rw [← hpush, commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  -- `P` covers `N/K`, so `P ⊄ N'K`.
  have hsup : ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N) ⊔ opPPrimeCore p ↥N = ⊤ :=
    sylow_sup_eq_top_of_isPGroup_quotient h3.isPGroup_quotient (P.subtype hPN)
  have hPnotle :
      ¬ ((P : Subgroup G).subgroupOf N ≤ commutator ↥N ⊔ opPPrimeCore p ↥N) := by
    intro hle
    refine hne_top (top_le_iff.mp ?_)
    rw [← hsup]
    exact sup_le hle le_sup_right
  -- Every focal generator of `P` lands in `W`.
  have hKcore : opiCoreInG ({p} : Set ℕ) N ≤ W := by
    rw [hW, opiCoreInG]
    exact Subgroup.map_mono
      ((GroupTheory.oPiCore_le_opPPrimeCore (G := ↥N) p).trans le_sup_right)
  have hgenW : Subgroup.focalSubgroup (P : Subgroup G) ≤ W := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    -- `⁅x, u⁆ = (x⁻¹)⁻¹ * (u * x⁻¹ * u⁻¹)`, with both factors' bases in `P`.
    have hz : x⁻¹ ∈ (P : Subgroup G) := inv_mem hxP
    have hsplit : ⁅x, u⁆ = (x⁻¹)⁻¹ * (u * x⁻¹ * u⁻¹) := by
      rw [commutatorElement_def]; group
    have hyP : u * x⁻¹ * u⁻¹ ∈ (P : Subgroup G) := by
      have hrw : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
      rw [hrw]; exact mul_mem hz hgP
    have hconjP : ((u • P : Sylow p G) : Subgroup G)
        = (P : Subgroup G).map (MulAut.conj u).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
    have hyPu : u * x⁻¹ * u⁻¹ ∈ ((u • P : Sylow p G) : Subgroup G) := by
      rw [hconjP]; exact ⟨x⁻¹, hz, rfl⟩
    by_cases hconj : ((u • P : Sylow p G) : Subgroup G) = (P : Subgroup G)
    · -- `u` normalizes `P`, so `u ∈ N` and the commutator lies in `N'`.
      have huN : u ∈ N :=
        hnormP (AppB.map_conj_eq_iff_mem_normalizer.mp (hconjP ▸ hconj))
      have hxN : x ∈ N := hPN hxP
      refine Subgroup.mem_map.mpr ⟨⁅(⟨x, hxN⟩ : ↥N), (⟨u, huN⟩ : ↥N)⁆, ?_, ?_⟩
      · exact (le_sup_left : commutator ↥N ≤ commutator ↥N ⊔ opPPrimeCore p ↥N)
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      · rw [map_commutatorElement]; rfl
    · -- Both `x⁻¹` and its conjugate lie in `O_p(N) ≤ K`.
      have hconjP' : ((u⁻¹ • P : Sylow p G) : Subgroup G)
          = (P : Subgroup G).map (MulAut.conj u⁻¹).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
      have hconj' : ((u⁻¹ • P : Sylow p G) : Subgroup G) ≠ (P : Subgroup G) := by
        intro hcon
        refine hconj ?_
        have heq : (u⁻¹ • P : Sylow p G) = P := Sylow.ext hcon
        calc ((u • P : Sylow p G) : Subgroup G)
            = ((u • (u⁻¹ • P) : Sylow p G) : Subgroup G) := by rw [heq]
          _ = (P : Subgroup G) := by rw [smul_smul, mul_inv_cancel, one_smul]
      have hzPu : x⁻¹ ∈ ((u⁻¹ • P : Sylow p G) : Subgroup G) := by
        rw [hconjP']
        refine ⟨u * x⁻¹ * u⁻¹, hyP, ?_⟩
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
        group
      have hyK : u * x⁻¹ * u⁻¹ ∈ opiCoreInG ({p} : Set ℕ) N :=
        hcore (u • P) hconj ⟨hyP, hyPu⟩
      have hzK : x⁻¹ ∈ opiCoreInG ({p} : Set ℕ) N := hcore (u⁻¹ • P) hconj' ⟨hz, hzPu⟩
      rw [hsplit]
      exact hKcore (mul_mem (inv_mem hzK) hyK)
  -- Focal Subgroup Theorem plus `G' = G`.
  have hfocal : (P : Subgroup G) = Subgroup.focalSubgroup (P : Subgroup G) := by
    have h := Subgroup.commutator_inf_eq_focalSubgroup P
    rwa [hyp.minimalSimpleOdd.commutator_eq_top, top_inf_eq] at h
  refine hPnotle (fun y hy => ?_)
  have hyW : (y : G) ∈ W := hgenW (hfocal ▸ (Subgroup.mem_subgroupOf.mp hy))
  obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp hyW
  exact (Subtype.ext hweq : w = y) ▸ hw

/-- **BG Lemma D.2** (mmd L5180): for a Sylow `p`-subgroup `P` of a minimal simple CN-group of
odd order, the focal subgroup argument places `P` inside the derived subgroup of its normalizer.

⚠ Minimal simplicity is essential: for general odd CN-groups this is **false** (`G = C₃`; see
`OddOrder.BG.AppD.Basic`).

Proof (BG): if `x, y ∈ P` are conjugate in `G`, say `y = x^t`, and both are nontrivial, then
`P ∩ P^t ≠ 1`, so `P = P^t` by Lemma D.1 and `t ∈ N_G(P)`; hence `x⁻¹y = ⁅x, t⁆ ∈ N_G(P)'`.  The
Focal Subgroup Theorem and `G' = G` then give `P = P ∩ G' ≤ N_G(P)'`.

BG assumes `P ≠ 1`; the argument never uses it (for `P = 1` the conclusion is vacuous), so the
hypothesis is dropped here. -/
theorem sylow_le_commutator_normalizer (hyp : MinimalSimpleCNHypothesis G) (P : Sylow p G) :
    (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G,
      N = Subgroup.normalizer ((P : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hPN : (P : Subgroup G) ≤ N := hN ▸ Subgroup.le_normalizer
  have hgen : Subgroup.focalSubgroup (P : Subgroup G) ≤ derivedInG N := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hz : x⁻¹ ∈ (P : Subgroup G) := inv_mem hxP
    have hyP : u * x⁻¹ * u⁻¹ ∈ (P : Subgroup G) := by
      have hrw : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
      rw [hrw]; exact mul_mem hz hgP
    have hconjP : ((u • P : Sylow p G) : Subgroup G)
        = (P : Subgroup G).map (MulAut.conj u).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
    have hyPu : u * x⁻¹ * u⁻¹ ∈ ((u • P : Sylow p G) : Subgroup G) := by
      rw [hconjP]; exact ⟨x⁻¹, hz, rfl⟩
    by_cases hx1 : x = 1
    · simp [hx1]
    -- `x ≠ 1` forces the conjugate to be a nonidentity element of `P ∩ P^u`, so `P^u = P`.
    have hy1 : u * x⁻¹ * u⁻¹ ≠ 1 := by
      intro h
      refine hx1 (inv_eq_one.mp ?_)
      calc x⁻¹ = u⁻¹ * (u * x⁻¹ * u⁻¹) * u := by group
        _ = u⁻¹ * 1 * u := by rw [h]
        _ = 1 := by group
    have hinter : (P : Subgroup G) ⊓ ((u • P : Sylow p G) : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hmem : u * x⁻¹ * u⁻¹ ∈ (P : Subgroup G) ⊓ ((u • P : Sylow p G) : Subgroup G) :=
        ⟨hyP, hyPu⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hy1 hmem
    have hconj : (P : Subgroup G) = ((u • P : Sylow p G) : Subgroup G) :=
      sylow_eq_of_nontrivial_inter hyp P (u • P) hinter
    have huN : u ∈ N :=
      hN ▸ AppB.map_conj_eq_iff_mem_normalizer.mp (hconjP ▸ hconj.symm)
    exact Subgroup.mem_map.mpr ⟨⁅(⟨x, hPN hxP⟩ : ↥N), (⟨u, huN⟩ : ↥N)⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),
      by rw [map_commutatorElement]; rfl⟩
  have hfocal : (P : Subgroup G) = Subgroup.focalSubgroup (P : Subgroup G) := by
    have h := Subgroup.commutator_inf_eq_focalSubgroup P
    rwa [hyp.minimalSimpleOdd.commutator_eq_top, top_inf_eq] at h
  rw [← hN]
  exact hfocal ▸ hgen

end OddOrder.BG.AppD
