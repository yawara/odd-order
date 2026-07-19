/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanFinalCase
import OddOrder.Higman.Suzuki2Groups.HigmanCoverPowerOverlap
import OddOrder.Higman.Suzuki2Groups.HigmanCoverDerivedSeries
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.Isaacs.Ch04_Commutators.Main.CommutatorIdentities
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# Higman Lemma 9: maximal normal invariant abelian subgroups

This file formalizes both conclusions of G. Higman, *Suzuki 2-groups*,
Lemma 9, p. 87. A maximal abelian subgroup among the normal
actor-invariant subgroups has exponent at most four and contains the
Frattini subgroup of the ambient group.

The proof constructs a normal actor-invariant cover and follows Higman's
exhaustive split: Lemma 3 applies when the Frattini images agree; otherwise
the derived subgroup is either all of the lower endpoint, where Lemma 8
applies, or lies in its square subgroup, where Lemma 7 makes the cover
abelian and contradicts maximality.

For the Frattini conclusion, a cover inside `A ⊔ Φ(P)` supplies a witness
from `Φ(P)` outside `A`. The square-commutator calculation puts
`[Φ(P),A]` in `A⁴`; Lemma 2 and the cover Frattini dichotomy then force
`Φ(C)=A`. Lemmas 7 and 8 reduce to exponent two, after which maximality
identifies `A` with the center and bounds the nilpotency class by two.
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

/-! ## The Frattini-containment argument -/

/-- In a finite `2`-group the Frattini subgroup is the subgroup generated
by squares. The commutator part of the standard Frattini formula is absorbed
by the square subgroup. -/
private theorem frattini_eq_agemo_two_one_of_isPGroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) :
    frattini P = Agemo P 2 1 := by
  have h := OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini hP
  rw [← h]
  have hsquares : Subgroup.closure (Set.range (fun x : P => x ^ 2)) =
      Agemo P 2 1 := by
    rw [Agemo]
    congr 1
    ext x
    simp only [Nat.pow_one]
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩
  rw [hsquares, sup_eq_right.mpr (commutator_le_agemo_two_one P)]

/-- The source step `[Φ(P),A] ≤ A⁴`: first identify `Φ(P)` with the
square-generated subgroup and then apply the generic Agemo commutator
propagation lemma. -/
private theorem commutator_frattini_le_agemo_two_map
    {P : Type*} [Group P] [Finite P] {A : Subgroup P} [A.Normal]
    (hP : IsPGroup 2 P)
    (hAcomm : IsMulCommutative A)
    (hPA : ⁅(⊤ : Subgroup P), A⁆ ≤ (Agemo A 2 1).map A.subtype) :
    ⁅frattini P, A⁆ ≤ (Agemo A 2 2).map A.subtype := by
  rw [frattini_eq_agemo_two_one_of_isPGroup hP]
  exact commutator_agemo_two_one_le_agemo_two_map hAcomm hPA

/-- If `A` does not contain the ambient Frattini subgroup, choose a normal
actor-invariant cover inside `A ⊔ Φ(P)`. Dedekind's identity then supplies
an element of the Frattini factor outside `A`. -/
private theorem exists_frattini_cover_with_witness
    {P X : Type*} [Group P] [Finite P] [Group X]
    {act : X →* MulAut P} {A : Subgroup P}
    (hA : IsNormalInvariant act A)
    (hnot : ¬ frattini P ≤ A) :
    ∃ (C : Subgroup P) (b : P),
      NormalInvariantCover act A C ∧
      C ≤ A ⊔ frattini P ∧
      b ∈ C ∧ b ∈ frattini P ∧ b ∉ A ∧
      C = A ⊔ (C ⊓ frattini P) := by
  letI : A.Normal := hA.1
  let a : NormalInvariantSubgroup act := ⟨A, hA⟩
  let u : NormalInvariantSubgroup act :=
    ⟨A ⊔ frattini P,
      ⟨inferInstance, hA.2.sup (IsAInvariant.frattini act)⟩⟩
  have hau : a < u := by
    change A < A ⊔ frattini P
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply hnot
    intro x hx
    have hx' : x ∈ A ⊔ frattini P :=
      (le_sup_right : frattini P ≤ A ⊔ frattini P) hx
    rwa [← hEq] at hx'
  obtain ⟨c, hac, hcu⟩ := exists_covBy_le_of_lt hau
  let C : Subgroup P := c.1
  have hcover : NormalInvariantCover act A C :=
    ⟨hA, c.2, hac⟩
  have hCle : C ≤ A ⊔ frattini P := hcu
  have hdecomp : C = A ⊔ (C ⊓ frattini P) :=
    Subgroup.eq_sup_inf_of_le_sup_of_normal_of_le hcover.le hCle
  have hfactor_not_le : ¬ C ⊓ frattini P ≤ A := by
    intro hfactor
    have hCA : C ≤ A := by
      rw [hdecomp]
      exact sup_le le_rfl hfactor
    exact hcover.lt.2 hCA
  obtain ⟨b, hbFactor, hbA⟩ := Set.not_subset.mp hfactor_not_le
  exact ⟨C, b, hcover, hCle, hbFactor.1, hbFactor.2, hbA, hdecomp⟩

/-- Lemma 2 applied to a Frattini-factor witness: if
`[Φ(P),A] ≤ A⁴`, then a witness `b ∈ Φ(P) \ A` cannot have its square in
`A²`. -/
private theorem square_not_mem_agemo_one_of_frattini_witness
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ g : X, (g : MulAut P) x = y)
    (A : Subgroup P) [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant X.subtype A)
    (hAne : A ≠ ⊥)
    {b : P} (hbPhi : b ∈ frattini P) (hbA : b ∉ A)
    (hPhiComm :
      ⁅frattini P, A⁆ ≤ (Agemo A 2 2).map A.subtype) :
    b ^ 2 ∉ (Agemo A 2 1).map A.subtype := by
  intro hb2
  apply no_sq_mem_agemo_one_and_commutator_le_agemo_two
    hP X htrans A hAcomm hAinv hAne hbA
  refine ⟨hb2, ?_⟩
  exact
    (Subgroup.commutator_mono
      (Subgroup.zpowers_le.mpr hbPhi) le_rfl).trans hPhiComm

/-- The cover selected from `A ⊔ Φ(P)` has ambient Frattini subgroup equal
to `A`: the other side of the Frattini dichotomy would put `b²` in `A²`,
contrary to Lemma 2. -/
private theorem exists_special_cover_ambientFrattini_eq_left
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ g : X, (g : MulAut P) x = y)
    (A : Subgroup P)
    (hA : IsNormalInvariant X.subtype A)
    (hAcomm : IsMulCommutative A)
    (hAne : A ≠ ⊥)
    (classify : ∀ U : Subgroup A,
      IsAInvariant hA.2.restrict U → ∃ s : ℕ, U = Agemo A 2 s)
    (hnot : ¬ frattini P ≤ A)
    (hPhiComm :
      ⁅frattini P, A⁆ ≤ (Agemo A 2 2).map A.subtype) :
    ∃ (C : Subgroup P) (b : P),
      NormalInvariantCover X.subtype A C ∧
      C ≤ A ⊔ frattini P ∧
      b ∈ C ∧ b ∈ frattini P ∧ b ∉ A ∧
      b ^ 2 ∉ (Agemo A 2 1).map A.subtype ∧
      NormalInvariantCover.ambientFrattini C = A := by
  letI : A.Normal := hA.1
  obtain ⟨C, b, hcover, hCle, hbC, hbPhi, hbA, _hdecomp⟩ :=
    exists_frattini_cover_with_witness hA hnot
  have hb2not : b ^ 2 ∉ (Agemo A 2 1).map A.subtype :=
    square_not_mem_agemo_one_of_frattini_witness
      hP X htrans A hAcomm hA.2 hAne hbPhi hbA hPhiComm
  have hb2PhiC : b ^ 2 ∈ NormalInvariantCover.ambientFrattini C := by
    change b ^ 2 ∈ (frattini C).map C.subtype
    let c : C := ⟨b, hbC⟩
    refine ⟨c ^ 2, IsPGroup.pow_mem_frattini (hP.to_subgroup C) c, ?_⟩
    rfl
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hPhiC : NormalInvariantCover.ambientFrattini C = A := by
    rcases hcover.ambientFrattini_right_eq_left_or_leftFrattini
        hP hAcomm classify with hEq | hEq
    · exact hEq
    · exfalso
      apply hb2not
      have hb2PhiA :
          b ^ 2 ∈ NormalInvariantCover.ambientFrattini A := by
        rw [← hEq]
        exact hb2PhiC
      simpa [NormalInvariantCover.ambientFrattini,
        NormalInvariantCover.frattini_eq_agemo_one
          (hP.to_subgroup A)] using hb2PhiA
  exact ⟨C, b, hcover, hCle, hbC, hbPhi, hbA, hb2not, hPhiC⟩

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

/-- The join of two abelian subgroups is abelian when the left subgroup
centralizes the right one. This local form avoids importing the later BG
copy of the same elementary fact into the Higman development. -/
private theorem isMulCommutative_sup_of_central_left
    {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsMulCommutative A) (hB : IsMulCommutative B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simpa using congrArg Subtype.val
      (isMulCommutative_iff.mp hA ⟨x, hx⟩ ⟨y, hy⟩)
  · exact (Subgroup.mem_centralizer_iff.mp (hAB hx) y hy).symm
  · exact Subgroup.mem_centralizer_iff.mp (hAB hy) x hx
  · simpa using congrArg Subtype.val
      (isMulCommutative_iff.mp hB ⟨x, hx⟩ ⟨y, hy⟩)

/-- Endgame of Higman Lemma 9. If the maximal normal invariant abelian
subgroup has exponent two, every one of its nonidentity elements is a
central involution, so maximality identifies it with the center. A lower
central-series argument then forces class at most two, and the class-two
Frattini theorem gives `Φ(P) ≤ A`. -/
private theorem IsMaximalNormalInvariantAbelian.frattini_le_of_pow_two_eq_one
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (hXcyc : IsCyclic X)
    (hreg : ActsRegularlyOnInvolutions X)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hncomm : ¬ IsMulCommutative P)
    {A : Subgroup P}
    (hAmax : IsMaximalNormalInvariantAbelian X.subtype A)
    (hAexp : ∀ a : A, a ^ 2 = 1) :
    frattini P ≤ A := by
  letI : A.Normal := hAmax.isNormalInvariant.1
  have hSuzuki : IsSuzuki2Group P :=
    ⟨hP, hncomm, hmulti, ⟨X, hXcyc, hreg⟩⟩
  have hAcenter : A ≤ Subgroup.center P := by
    intro a ha
    by_cases ha1 : a = 1
    · subst a
      exact Subgroup.one_mem _
    · apply involutions_subset_center hSuzuki
      refine ⟨?_, ha1⟩
      simpa using congrArg Subtype.val (hAexp ⟨a, ha⟩)
  have hcenterEq : Subgroup.center P = A :=
    hAmax.maximal (Subgroup.center P)
      ⟨inferInstance, IsAInvariant.center X.subtype⟩ inferInstance hAcenter
  letI : Group.IsNilpotent P := hP.isNilpotent
  have hclass : Group.nilpotencyClass P ≤ 2 := by
    by_contra hnot
    have hc : 3 ≤ Group.nilpotencyClass P := by omega
    let L : Subgroup P :=
      (⊤ : Subgroup P).lowerCentralSeries (Group.nilpotencyClass P - 2)
    have hLLbot : ⁅L, L⁆ = (⊥ : Subgroup P) := by
      apply le_bot_iff.mp
      calc
        ⁅L, L⁆ ≤ (⊤ : Subgroup P).lowerCentralSeries
            ((Group.nilpotencyClass P - 2) +
              (Group.nilpotencyClass P - 2) + 1) := by
          simpa [L] using
            (OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le
              (G := P) (Group.nilpotencyClass P - 2)
                (Group.nilpotencyClass P - 2))
        _ ≤ (⊤ : Subgroup P).lowerCentralSeries
            (Group.nilpotencyClass P) := by
          apply (⊤ : Subgroup P).lowerCentralSeries_antitone
          omega
        _ = ⊥ := Subgroup.lowerCentralSeries_nilpotencyClass
    have hLcomm : IsMulCommutative L := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hLLbot
      refine ⟨⟨fun x y => ?_⟩⟩
      have hxcent : (x : P) ∈ Subgroup.centralizer (L : Set P) :=
        hLLbot x.property
      rw [Subgroup.mem_centralizer_iff] at hxcent
      exact Subtype.ext (hxcent y y.property).symm
    have hLinv : IsAInvariant X.subtype L := by
      simpa [L] using
        (IsAInvariant.lowerCentralSeries X.subtype
          (Group.nilpotencyClass P - 2))
    have hLnorm : L.Normal := by
      dsimp [L]
      infer_instance
    letI : L.Normal := hLnorm
    have hsupNI : IsNormalInvariant X.subtype (A ⊔ L) :=
      ⟨inferInstance, hAmax.isNormalInvariant.2.sup hLinv⟩
    have hsupComm : IsMulCommutative ↥(A ⊔ L) :=
      isMulCommutative_sup_of_central_left
        hAmax.isMulCommutative hLcomm
        (hAcenter.trans (Subgroup.center_le_centralizer _))
    have hsupEq : A ⊔ L = A :=
      hAmax.maximal (A ⊔ L) hsupNI hsupComm le_sup_left
    have hLcenter : L ≤ Subgroup.center P := by
      have hLA : L ≤ A := by
        intro x hx
        have : x ∈ A ⊔ L := (le_sup_right : L ≤ A ⊔ L) hx
        rwa [hsupEq] at this
      exact hLA.trans hAcenter
    have hnextBot :
        (⊤ : Subgroup P).lowerCentralSeries
            ((Group.nilpotencyClass P - 2) + 1) = ⊥ :=
      Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup P) hLcenter
    have hclassLePred :
        Group.nilpotencyClass P ≤ (Group.nilpotencyClass P - 2) + 1 :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hnextBot
    omega
  have hlcsTwo :
      (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclass
  have htopCommBot :
      ⁅(⊤ : Subgroup P), _root_.commutator P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, ← Subgroup.top_lowerCentralSeries_one]
    simpa [Subgroup.lowerCentralSeries_succ] using hlcsTwo
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at htopCommBot
  have hcommCenter : _root_.commutator P ≤ Subgroup.center P := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro p
    have hpcent := htopCommBot (Subgroup.mem_top p)
    exact (hpcent c hc).symm
  have hcommExp : ∀ c ∈ _root_.commutator P, c ^ 2 = 1 := by
    intro c hc
    have hcA : c ∈ A := by
      rw [← hcenterEq]
      exact hcommCenter hc
    simpa using congrArg Subtype.val (hAexp ⟨c, hcA⟩)
  have hPhiCenter : frattini P ≤ Subgroup.center P :=
    OddOrder.Isaacs.Ch04.frattini_le_center_of_class_le_two_of_commutator_pow_eq_one
      hP hcommCenter hcommExp
  rwa [hcenterEq] at hPhiCenter

/-- **Higman, Suzuki 2-groups, Lemma 9 (p. 87).**

If `A` is maximal among the abelian normal actor-invariant subgroups of a
nonabelian finite `2`-group whose cyclic actor acts regularly on the
involutions, then `A` has exponent at most four and contains the Frattini
subgroup of the ambient group. -/
theorem higmanLemmaNine
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
    (∀ a : A, a ^ 4 = 1) ∧ frattini P ≤ A := by
  refine ⟨higmanLemmaNine_pow_four_eq_one
    hP X hXcyc hreg hmulti hncomm A hAmax, ?_⟩
  by_contra hnot
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
  have hAne : A ≠ ⊥ := hAmax.ne_bot hP hmulti
  letI : Group.IsNilpotent P := hP.isNilpotent
  let D : Subgroup P := ⁅(⊤ : Subgroup P), A⁆
  have hDlt : D < A := by
    dsimp [D]
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient
      (E := A) (F := (⊤ : Subgroup P)) hAne
  have hDinv : IsAInvariant X.subtype D := by
    dsimp [D]
    exact IsAInvariant.commutator
      (IsAInvariant.top X.subtype) hAmax.isNormalInvariant.2
  let U : Subgroup A := D.subgroupOf A
  have hUinv : IsAInvariant hAmax.isNormalInvariant.2.restrict U := by
    simpa [U] using hAmax.isNormalInvariant.2.subgroupOf hDinv
  obtain ⟨s, hs⟩ := classify U hUinv
  have hDleA2 : D ≤ (Agemo A 2 1).map A.subtype := by
    rcases s with _ | s
    · have hDA : D = A := by
        apply le_antisymm hDlt.le
        apply Subgroup.subgroupOf_eq_top.mp
        simpa [U, agemo_zero_eq_top] using hs
      exact (hDlt.ne hDA).elim
    · intro d hd
      have hdA : d ∈ A := hDlt.le hd
      let a : A := ⟨d, hdA⟩
      have haU : a ∈ U := by
        change d ∈ D
        exact hd
      have haPow : a ∈ Agemo A 2 (s + 1) := by
        rwa [← hs]
      exact ⟨a, Agemo.anti (Nat.le_add_left 1 s) haPow, rfl⟩
  have hPA : ⁅(⊤ : Subgroup P), A⁆ ≤
      (Agemo A 2 1).map A.subtype := by
    simpa [D] using hDleA2
  have hPhiComm :
      ⁅frattini P, A⁆ ≤ (Agemo A 2 2).map A.subtype :=
    commutator_frattini_le_agemo_two_map
      hP hAmax.isMulCommutative hPA
  obtain ⟨C, _b, hcover, _hCle, _hbC, _hbPhi, _hbA, _hb2not, hPhi⟩ :=
    exists_special_cover_ambientFrattini_eq_left
      hP X htrans A hAmax.isNormalInvariant hAmax.isMulCommutative
        hAne classify hnot hPhiComm
  have hderived : (_root_.commutator C).map C.subtype = A := by
    rcases hcover.commutator_map_eq_left_or_le_agemo_one
        hP classify hPhi with hEq | hle
    · exact hEq
    · have hCcomm : IsMulCommutative C :=
        higmanLemmaSeven_isMulCommutative
          hP X hXcyc hreg hmulti A C hcover
            hAmax.isMulCommutative hPhi hle
      have hCA : C = A :=
        hAmax.maximal C hcover.right hCcomm hcover.le
      exact False.elim (hcover.lt.ne hCA.symm)
  have hAexp : ∀ a : A, a ^ 2 = 1 :=
    higmanLemmaEight_pow_two_eq_one
      hP X hXcyc hreg hmulti A C hcover
        hAmax.isMulCommutative hderived
  exact hnot
    (IsMaximalNormalInvariantAbelian.frattini_le_of_pow_two_eq_one
      hP X hXcyc hreg hmulti hncomm hAmax hAexp)

end OddOrder.Higman.Suzuki2Groups
