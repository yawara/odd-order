/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Suzuki 2-groups

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
79--96, p. 79.  See also T. Peterfalvi, *Character Theory for the Odd Order
Theorem*, Appendix III, Definition 1, p. 141.

This source-neutral leaf contains the definition-level API shared by Higman’s
classification, Peterfalvi’s Appendix III restatement, and concrete groups
whose root subgroups are Suzuki 2-groups.  The paper-specific classification
proof lives under `OddOrder.Higman.Suzuki2Groups`.
-/

namespace OddOrder.GroupTheory.Suzuki2Group

variable {P : Type*} [Group P]

/-- The nonidentity involutions of a group. -/
def involutions (P : Type*) [Group P] : Set P :=
  {x | x ^ 2 = 1 ∧ x ≠ 1}

/-- A subgroup of the automorphism group acts transitively on the involutions
when every ordered pair of involutions is connected by an automorphism.

This is the action hypothesis in Higman's original definition of a Suzuki
`2`-group.  Regularity is a later conclusion of the classification. -/
def ActsTransitivelyOnInvolutions (A : Subgroup (MulAut P)) : Prop :=
  ∀ x ∈ involutions P, ∀ y ∈ involutions P,
    ∃ a : ↥A, (a : MulAut P) x = y

/-- A subgroup of the automorphism group acts regularly on the involutions
when every ordered pair of involutions is connected by a unique automorphism. -/
def ActsRegularlyOnInvolutions (A : Subgroup (MulAut P)) : Prop :=
  ∀ x ∈ involutions P, ∀ y ∈ involutions P,
    ∃! a : ↥A, (a : MulAut P) x = y

/-- Every regular action on the involutions is transitive. -/
theorem ActsRegularlyOnInvolutions.transitive
    {A : Subgroup (MulAut P)} (hreg : ActsRegularlyOnInvolutions A) :
    ActsTransitivelyOnInvolutions A := by
  intro x hx y hy
  obtain ⟨a, ha, _⟩ := hreg x hx y hy
  exact ⟨a, ha⟩

/-- A group acting regularly on the involutions of a finite `2`-group has
odd order.

The orbit of one involution identifies the actor with the full involution
set.  Inversion pairs the remaining elements of the ambient `2`-group, so
that set has odd cardinality. -/
theorem actor_card_odd_of_regular_on_involutions
    [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup (MulAut P))
    (hreg : ActsRegularlyOnInvolutions A)
    (hinv : (involutions P).Nonempty) :
    Odd (Nat.card A) := by
  classical
  obtain ⟨x, hx⟩ := hinv
  letI : Nontrivial P := ⟨⟨x, 1, hx.2⟩⟩
  letI : Fintype P := Fintype.ofFinite P
  let f : Function.End P := fun y => y⁻¹
  have hf2 : f ^ 2 = 1 := by
    funext y
    change (y⁻¹)⁻¹ = y
    simp
  have hmod :=
    Equiv.Perm.card_fixedPoints_modEq
      (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hcard_ne : Nat.card P ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo : 2 ∣ Nat.card P :=
    hP.card_eq_or_dvd.resolve_left hcard_ne
  have hPmod : Fintype.card P % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.dvd_iff_mod_eq_zero.mp htwo
  have hfixedMod : Fintype.card ↥(Function.fixedPoints f) % 2 = 0 := by
    rw [Nat.ModEq] at hmod
    omega
  have hfixed :
      Function.fixedPoints f = insert 1 (involutions P) := by
    ext y
    change y⁻¹ = y ↔ y = 1 ∨ (y ^ 2 = 1 ∧ y ≠ 1)
    constructor
    · intro hy
      have hy2 : y ^ 2 = 1 := by
        rw [pow_two, ← inv_eq_iff_mul_eq_one]
        exact hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr ⟨hy2, hy1⟩
    · rintro (rfl | ⟨hy2, _⟩)
      · simp
      · rw [inv_eq_iff_mul_eq_one, ← pow_two]
        exact hy2
  have hfixedCard :
      Fintype.card ↥(Function.fixedPoints f) =
        (involutions P).ncard + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hfixed,
      Set.ncard_insert_of_notMem]
    simp [involutions]
  have hinvOdd : Odd (involutions P).ncard := by
    rw [Nat.odd_iff]
    omega
  let orbit : A → ↥(involutions P) := fun a =>
    ⟨(a : MulAut P) x, by
      constructor
      · simpa only [map_pow, map_one] using
          congrArg (a : MulAut P) hx.1
      · intro hax
        apply hx.2
        apply (a : MulAut P).injective
        simpa only [map_one] using hax⟩
  have horbitInj : Function.Injective orbit := by
    intro a b hab
    let y : P := (a : MulAut P) x
    have hy : y ∈ involutions P := (orbit a).2
    obtain ⟨c, hc, huniq⟩ := hreg x hx y hy
    have ha : (a : MulAut P) x = y := rfl
    have hb : (b : MulAut P) x = y := by
      exact (congrArg Subtype.val hab).symm
    exact (huniq a ha).trans (huniq b hb).symm
  have horbitSurj : Function.Surjective orbit := by
    intro y
    obtain ⟨a, ha, _⟩ := hreg x hx y y.2
    exact ⟨a, Subtype.ext ha⟩
  have hcardActor : Nat.card A = (involutions P).ncard := by
    calc
      Nat.card A = Nat.card ↥(involutions P) :=
        Nat.card_congr (Equiv.ofBijective orbit ⟨horbitInj, horbitSurj⟩)
      _ = (involutions P).ncard := Nat.card_coe_set_eq _
  rwa [hcardActor]

/-- **Higman, Suzuki 2-groups, p. 79; Peterfalvi Appendix III, Definition 1**:
a Suzuki `2`-group is a
nonabelian `2`-group with at least two involutions and a cyclic group of
automorphisms acting faithfully and regularly on its involutions.

The acting group is represented as a subgroup of `MulAut P`, so faithfulness
is built into the representation rather than retained as an opaque field. -/
def IsSuzuki2Group (P : Type*) [Group P] : Prop :=
  IsPGroup 2 P ∧
    ¬ IsMulCommutative P ∧
    (∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) ∧
    ∃ A : Subgroup (MulAut P), IsCyclic ↥A ∧ ActsRegularlyOnInvolutions A

end OddOrder.GroupTheory.Suzuki2Group
