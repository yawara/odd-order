/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Order.Atoms.Finite
import OddOrder.Higman.Suzuki2Groups.HigmanNormalAbelian
import OddOrder.GroupTheory.MinimalInvariantNormal
import OddOrder.BG.Ch1_Preliminary.S01_Solvable

/-!
# Higman Lemma 3: normal invariant covers

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

The cover relation in Higman Lemma 3 is taken in the poset of normal actor-invariant
subgroups, not in the lattice of all subgroups. This file models that poset
honestly and proves the cover--Frattini paragraph on p. 83.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch04

variable {G X : Type*} [Group G] [Group X]

/-- A subgroup normal in the ambient group and invariant under the actor. -/
def IsNormalInvariant (act : X →* MulAut G) (N : Subgroup G) : Prop :=
  N.Normal ∧ IsAInvariant act N

/-- The honest poset carrier for normal actor-invariant subgroups. -/
abbrev NormalInvariantSubgroup (act : X →* MulAut G) :=
  {N : Subgroup G // IsNormalInvariant act N}

/-- `C` covers `A` in the poset of normal actor-invariant subgroups. -/
structure NormalInvariantCover (act : X →* MulAut G)
    (A C : Subgroup G) : Prop where
  left : IsNormalInvariant act A
  right : IsNormalInvariant act C
  covBy :
    (⟨A, left⟩ : NormalInvariantSubgroup act) ⋖
      (⟨C, right⟩ : NormalInvariantSubgroup act)

namespace NormalInvariantCover

variable {act : X →* MulAut G} {A B C : Subgroup G}

theorem lt (h : NormalInvariantCover act A C) : A < C :=
  h.covBy.lt

theorem le (h : NormalInvariantCover act A C) : A ≤ C :=
  h.covBy.le

theorem eq_left_or_eq_right
    (h : NormalInvariantCover act A C)
    (hB : IsNormalInvariant act B) (hAB : A ≤ B) (hBC : B ≤ C) :
    B = A ∨ B = C := by
  let B' : NormalInvariantSubgroup act := ⟨B, hB⟩
  rcases h.covBy.eq_or_eq (c := B') hAB hBC with hBA | hBC'
  · exact Or.inl (congrArg Subtype.val hBA)
  · exact Or.inr (congrArg Subtype.val hBC')

/-- The Frattini subgroup of `H`, mapped into the ambient group. -/
def ambientFrattini (H : Subgroup G) : Subgroup G :=
  (frattini H).map H.subtype

/-- Higman's first p.83 cover consequence: `Phi(C)` lies in `A`. -/
theorem ambientFrattini_right_le_left [Finite G]
    (h : NormalInvariantCover act A C) : ambientFrattini C ≤ A := by
  letI : A.Normal := h.left.1
  letI : C.Normal := h.right.1
  obtain ⟨hPhiInv, hPhiNorm, hPhiLeC⟩ :=
    aInvariant_normal_map_of_characteristic h.right.2 (frattini C)
  let PhiC : Subgroup G := ambientFrattini C
  have hPhiEq : PhiC = (frattini C).map C.subtype := rfl
  have hPhiInv' : IsAInvariant act PhiC := by
    simpa [PhiC, ambientFrattini] using hPhiInv
  have hPhiNorm' : PhiC.Normal := by
    simpa [PhiC, ambientFrattini] using hPhiNorm
  have hPhiLeC' : PhiC ≤ C := by
    simpa [PhiC, ambientFrattini] using hPhiLeC
  have hSupNorm : (A ⊔ PhiC).Normal := by
    letI : PhiC.Normal := hPhiNorm'
    infer_instance
  have hcases : A ⊔ PhiC = A ∨ A ⊔ PhiC = C :=
    h.eq_left_or_eq_right ⟨hSupNorm, h.left.2.sup hPhiInv'⟩
      le_sup_left (sup_le h.le hPhiLeC')
  rcases hcases with hsup | hsup
  · intro x hx
    have hx' : x ∈ A ⊔ PhiC :=
      (le_sup_right : PhiC ≤ A ⊔ PhiC) hx
    rwa [hsup] at hx'
  · exfalso
    have hgen : A.subgroupOf C ⊔ frattini C = ⊤ := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr h.le, ← hPhiEq, hsup,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hAtop : A.subgroupOf C = ⊤ := frattini_nongenerating hgen
    exact h.lt.ne (le_antisymm h.le (Subgroup.subgroupOf_eq_top.mp hAtop))

/-- In a finite commutative p-group, `Phi(A)` is its first Agemo layer. -/
theorem frattini_eq_agemo_one
    {P : Type*} [CommGroup P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) : frattini P = Agemo P p 1 := by
  apply le_antisymm
  · apply (frattini_le_iff_isElementaryAbelian_quotient_of_pgroup hP).2
    refine ⟨fun x y => mul_comm x y, ?_⟩
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    have hx : x ^ p ∈ Agemo P p 1 := by
      simpa using (Agemo.mem_of_eq_pow (G := P) (p := p) (n := 1) x)
    have hq : (QuotientGroup.mk' (Agemo P p 1)) (x ^ p) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hx
    change (QuotientGroup.mk' (Agemo P p 1) x) ^ p = 1
    simpa only [map_pow] using hq
  · rw [Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_mem_frattini hP x

/-- If `A ≤ C`, `A` is abelian, and both are subgroups of a finite 2-group,
then the ambient image of `Phi(A)` lies in that of `Phi(C)`. -/
theorem ambientFrattini_left_le_right_of_comm
    [Finite G] (hG : IsPGroup 2 G) (hAcomm : IsMulCommutative A)
    (hAC : A ≤ C) : ambientFrattini A ≤ ambientFrattini C := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  rw [ambientFrattini, frattini_eq_agemo_one (hG.to_subgroup A)]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ := mem_agemo_iff_of_comm.mp ha
  let c : C := ⟨(b : G), hAC b.2⟩
  refine ⟨c ^ 2, IsPGroup.pow_mem_frattini (hG.to_subgroup C) c, ?_⟩
  simpa [c] using congrArg Subtype.val hb.symm

/-- Lemma 1 makes the first Agemo layer a coatom among invariant subgroups. -/
theorem eq_agemo_one_or_top_of_invariant_classification
    {Y P : Type*} [Group Y] [CommGroup P] (actP : Y →* MulAut P)
    (classify : ∀ U : Subgroup P, IsAInvariant actP U →
      ∃ s : ℕ, U = Agemo P 2 s)
    {U : Subgroup P} (hUinv : IsAInvariant actP U)
    (hAgemoU : Agemo P 2 1 ≤ U) :
    U = Agemo P 2 1 ∨ U = ⊤ := by
  obtain ⟨s, rfl⟩ := classify U hUinv
  rcases s with _ | s
  · exact Or.inr agemo_zero_eq_top
  · exact Or.inl
      (le_antisymm (Agemo.anti (Nat.succ_le_succ (Nat.zero_le s))) hAgemoU)

/-- Higman's complete preliminary p.83 dichotomy:
`Phi(C) = A` or `Phi(C) = Phi(A)` (all Frattini subgroups mapped ambiently). -/
theorem ambientFrattini_right_eq_left_or_leftFrattini
    [Finite G] (hG : IsPGroup 2 G)
    (h : NormalInvariantCover act A C) (hAcomm : IsMulCommutative A)
    (classify : ∀ U : Subgroup A,
      IsAInvariant h.left.2.restrict U → ∃ s : ℕ, U = Agemo A 2 s) :
    ambientFrattini C = A ∨ ambientFrattini C = ambientFrattini A := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  have hPhiCLeA : ambientFrattini C ≤ A := h.ambientFrattini_right_le_left
  have hPhiALePhiC : ambientFrattini A ≤ ambientFrattini C :=
    ambientFrattini_left_le_right_of_comm hG hAcomm h.le
  have hPhiCInv : IsAInvariant act (ambientFrattini C) := by
    simpa [ambientFrattini] using
      aInvariant_map_subtype_of_restrict h.right.2
        (IsAInvariant.of_characteristic h.right.2.restrict :
          IsAInvariant h.right.2.restrict (frattini C))
  let U : Subgroup A := (ambientFrattini C).subgroupOf A
  have hUinv : IsAInvariant h.left.2.restrict U := by
    simpa [U] using h.left.2.subgroupOf hPhiCInv
  have hAgemoU : Agemo A 2 1 ≤ U := by
    rw [← frattini_eq_agemo_one (hG.to_subgroup A)]
    intro a ha
    rw [Subgroup.mem_subgroupOf]
    apply hPhiALePhiC
    exact ⟨a, ha, rfl⟩
  rcases eq_agemo_one_or_top_of_invariant_classification
      h.left.2.restrict classify hUinv hAgemoU with hU | hU
  · right
    apply le_antisymm
    · intro x hx
      have hxA : x ∈ A := hPhiCLeA hx
      let a : A := ⟨x, hxA⟩
      have haU : a ∈ U := by
        simpa [U, Subgroup.mem_subgroupOf] using hx
      rw [hU] at haU
      refine ⟨a, ?_, rfl⟩
      rwa [frattini_eq_agemo_one (hG.to_subgroup A)]
    · exact hPhiALePhiC
  · left
    apply le_antisymm hPhiCLeA
    intro x hxA
    let a : A := ⟨x, hxA⟩
    have haU : a ∈ U := by rw [hU]; exact Subgroup.mem_top a
    simpa [U, Subgroup.mem_subgroupOf, a] using haU

end NormalInvariantCover

end OddOrder.Higman.Suzuki2Groups
