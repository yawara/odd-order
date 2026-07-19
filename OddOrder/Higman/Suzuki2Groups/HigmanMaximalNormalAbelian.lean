/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanFinalCase
import OddOrder.Higman.Suzuki2Groups.HigmanCoverPowerOverlap
import OddOrder.Higman.Suzuki2Groups.HigmanCoverDerivedSeries

/-!
# Higman Lemma 9: maximal normal invariant abelian subgroups

This file formalizes the first conclusion of G. Higman, *Suzuki 2-groups*,
Lemma 9, p. 87. A maximal abelian subgroup among the normal
actor-invariant subgroups has exponent at most four.

The proof constructs a normal actor-invariant cover and follows Higman's
exhaustive split: Lemma 3 applies when the Frattini images agree; otherwise
the derived subgroup is either all of the lower endpoint, where Lemma 8
applies, or lies in its square subgroup, where Lemma 7 makes the cover
abelian and contradicts maximality.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

/-- Maximality among the abelian normal actor-invariant subgroups.

This is the exact maximality notion in Higman, *Suzuki 2-groups*, Lemma 9,
rather than maximality among all normal abelian subgroups. -/
structure IsMaximalNormalInvariantAbelian
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) (A : Subgroup P) : Prop where
  /-- The subgroup is normal in the ambient group and actor-invariant. -/
  isNormalInvariant : IsNormalInvariant act A
  /-- The subgroup is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- No larger normal actor-invariant subgroup is abelian. -/
  maximal : ∀ B : Subgroup P, IsNormalInvariant act B →
    IsMulCommutative B → A ≤ B → B = A

namespace IsMaximalNormalInvariantAbelian

variable {P X : Type*} [Group P] [Finite P] [Group X]
  {act : X →* MulAut P} {A : Subgroup P}

/-- A maximal normal actor-invariant abelian subgroup of a finite `2`-group
with at least two involutions is nontrivial. -/
theorem ne_bot (h : IsMaximalNormalInvariantAbelian act A)
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) :
    A ≠ ⊥ := by
  obtain ⟨x, y, _hx, _hy, hxy⟩ := hmulti
  letI : Nontrivial P := ⟨⟨x, y, hxy⟩⟩
  intro hAbot
  have hZA : Subgroup.center P = A := h.maximal (Subgroup.center P)
    ⟨inferInstance, IsAInvariant.of_characteristic act⟩ inferInstance
    (by rw [hAbot]; exact bot_le)
  have hZne : Subgroup.center P ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (Subgroup.center P)).mp
      hP.center_nontrivial
  exact hZne (hZA.trans hAbot)

omit [Finite P] in
/-- A maximal normal actor-invariant abelian subgroup is proper when the
ambient group is nonabelian. -/
theorem lt_top (h : IsMaximalNormalInvariantAbelian act A)
    (hncomm : ¬ IsMulCommutative P) : A < ⊤ := by
  refine lt_top_iff_ne_top.mpr ?_
  intro hAtop
  apply hncomm
  exact IsMulCommutative.of_comm fun x y => by
    have hx : x ∈ A := by rw [hAtop]; exact Subgroup.mem_top x
    have hy : y ∈ A := by rw [hAtop]; exact Subgroup.mem_top y
    exact congrArg Subtype.val
      (h.isMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

/-- In a finite nonabelian group, a maximal normal actor-invariant abelian
subgroup admits a cover in the poset of normal actor-invariant subgroups. -/
theorem exists_cover (h : IsMaximalNormalInvariantAbelian act A)
    (hncomm : ¬ IsMulCommutative P) :
    ∃ C : Subgroup P, NormalInvariantCover act A C := by
  let a : NormalInvariantSubgroup act := ⟨A, h.isNormalInvariant⟩
  let t : NormalInvariantSubgroup act :=
    ⟨⊤, inferInstance, IsAInvariant.top act⟩
  have hat : a < t := by
    change A < ⊤
    exact h.lt_top hncomm
  obtain ⟨c, hac, _hct⟩ := exists_covBy_le_of_lt hat
  exact ⟨c.1, ⟨h.isNormalInvariant, c.2, hac⟩⟩

end IsMaximalNormalInvariantAbelian

namespace NormalInvariantCover

/-- Under Higman Lemma 1's invariant-subgroup classification, if the
Frattini subgroup of a cover is its lower endpoint, then the derived subgroup
of the cover either maps onto that endpoint or lies in its square subgroup. -/
theorem commutator_map_eq_left_or_le_agemo_one
    {P X : Type*} [Group P] [Finite P] [Group X]
    {act : X →* MulAut P} {A C : Subgroup P}
    (hP : IsPGroup 2 P)
    (h : NormalInvariantCover act A C)
    (classify : ∀ U : Subgroup A,
      IsAInvariant h.left.2.restrict U →
        ∃ s : ℕ, U = Agemo A 2 s)
    (hPhi : ambientFrattini C = A) :
    (_root_.commutator C).map C.subtype = A ∨
      (_root_.commutator C).map C.subtype ≤
        (Agemo A 2 1).map A.subtype := by
  letI : A.Normal := h.left.1
  letI : C.Normal := h.right.1
  let D : Subgroup P := (_root_.commutator C).map C.subtype
  have hDle : D ≤ A := by
    rw [← hPhi]
    exact Subgroup.map_mono
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup
        (hP.to_subgroup C))
  have hDinv : IsAInvariant act D := by
    simpa [D] using aInvariant_map_subtype_of_restrict h.right.2
      (IsAInvariant.commutator_self h.right.2.restrict)
  let U : Subgroup A := D.subgroupOf A
  have hUinv : IsAInvariant h.left.2.restrict U := by
    simpa [U] using h.left.2.subgroupOf hDinv
  obtain ⟨s, hs⟩ := classify U hUinv
  rcases s with _ | s
  · left
    have hDA : D = A := by
      apply le_antisymm hDle
      apply Subgroup.subgroupOf_eq_top.mp
      simpa [U, agemo_zero_eq_top] using hs
    exact hDA
  · right
    intro d hd
    have hdA : d ∈ A := hDle hd
    let a : A := ⟨d, hdA⟩
    have haU : a ∈ U := by
      change d ∈ D
      exact hd
    have haPow : a ∈ Agemo A 2 (s + 1) := by
      rwa [← hs]
    exact ⟨a, Agemo.anti (Nat.le_add_left 1 s) haPow, rfl⟩

end NormalInvariantCover

/-- **Higman, Suzuki 2-groups, Lemma 9 (p. 87), exponent conclusion.**

If `A` is maximal among the abelian normal actor-invariant subgroups of a
nonabelian finite `2`-group whose cyclic actor acts regularly on the
involutions, then every element of `A` has fourth power one. -/
theorem higmanLemmaNine_pow_four_eq_one
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (hXcyc : IsCyclic X)
    (hreg : ActsRegularlyOnInvolutions X)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hncomm : ¬ IsMulCommutative P)
    (A : Subgroup P)
    (hAmax : IsMaximalNormalInvariantAbelian X.subtype A) :
    ∀ a : A, a ^ 4 = 1 := by
  letI : A.Normal := hAmax.isNormalInvariant.1
  have htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ g : X, (g : MulAut P) x = y := by
    intro x hx y hy
    obtain ⟨g, hg, _⟩ := hreg x hx y hy
    exact ⟨g, hg⟩
  have htransA : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, hAmax.isNormalInvariant.2.restrict g x = y :=
    restricted_involutions_transitive X.subtype
      hAmax.isNormalInvariant.2 (by simpa using htrans)
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAmax.isMulCommutative.is_comm.comm }
  obtain ⟨ι, hι, e, _he, _hε, classifyFull⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup A) hAmax.isNormalInvariant.2.restrict htransA
  letI : Fintype ι := hι
  have classify : ∀ U : Subgroup A,
      IsAInvariant hAmax.isNormalInvariant.2.restrict U →
        ∃ s : ℕ, U = Agemo A 2 s := by
    intro U hU
    obtain ⟨s, _hs, hsU⟩ := classifyFull U hU
    exact ⟨s, hsU⟩
  obtain ⟨C, hcover⟩ := hAmax.exists_cover hncomm
  rcases hcover.ambientFrattini_right_eq_left_or_leftFrattini
      hP hAmax.isMulCommutative classify with hPhi | hPhi
  · rcases hcover.commutator_map_eq_left_or_le_agemo_one
        hP classify hPhi with hderived | hderived
    · intro a
      have htwo := higmanLemmaEight_pow_two_eq_one
        hP X hXcyc hreg hmulti A C hcover
          hAmax.isMulCommutative hderived a
      calc
        a ^ 4 = (a ^ 2) ^ 2 := by group
        _ = 1 := by rw [htwo]; simp
    · have hCcomm : IsMulCommutative C :=
        higmanLemmaSeven_isMulCommutative
          hP X hXcyc hreg hmulti A C hcover
            hAmax.isMulCommutative hPhi hderived
      have hCA : C = A :=
        hAmax.maximal C hcover.right hCcomm hcover.le
      exact False.elim (hcover.lt.ne hCA.symm)
  · exact hcover.pow_four_eq_one_of_frattini_map_eq
      hP X htrans hmulti hAmax.isMulCommutative (by
        simpa [NormalInvariantCover.ambientFrattini] using hPhi)

end OddOrder.Higman.Suzuki2Groups
