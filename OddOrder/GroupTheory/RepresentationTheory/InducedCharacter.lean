/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Classical induction sums for class functions

For a subgroup `H ≤ G` and a class function `θ : ClassFunction ↥H k`, this file
defines the unscaled classical induction sum

  `Σ x : G, θ (x⁻¹ * g * x)` over those `x` with `x⁻¹ * g * x ∈ H`.

Peterfalvi's induced character `Ind_H^G θ` is this sum divided by `|H|`. The
unscaled form is useful before choosing coefficients where `|H|` is invertible.

## Main definitions

* `ClassFunction.induceTerm H θ x g` — the `x`-summand in the induction formula.
* `ClassFunction.induceSum H θ` — the unscaled induced class function on `G`.
* `ClassFunction.induce H θ` — the normalized induced class function, when
  `|H|` is invertible in the coefficient ring.
* `ClassFunction.conjugatesInto H` — elements of `G` conjugate into `H`.
* `ClassFunction.conjugatesIntoSet H A` — elements of `G` conjugate into `A ⊆ H`.

## References

* Peterfalvi §2 line 21 (`Ind_H^G`) and §3 (1.3).
* Isaacs, *Character Theory of Finite Groups*, Ch. 5-6 induction formula.

-/

noncomputable section

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- Elements of `G` that are conjugate into the subgroup `H`. -/
def conjugatesInto (H : Subgroup G) : Set G :=
  { g | ∃ x : G, x⁻¹ * g * x ∈ H }

/-- Elements of `G` that are conjugate into `A`, where `A` is a set of elements
of the subgroup `H`. -/
def conjugatesIntoSet (H : Subgroup G) (A : Set ↥H) : Set G :=
  { g | ∃ (x : G) (hx : x⁻¹ * g * x ∈ H), (⟨x⁻¹ * g * x, hx⟩ : ↥H) ∈ A }

theorem conjugatesIntoSet_mono {H : Subgroup G} {A B : Set ↥H} (hAB : A ⊆ B) :
    conjugatesIntoSet H A ⊆ conjugatesIntoSet H B := by
  rintro g ⟨x, hx, hA⟩
  exact ⟨x, hx, hAB hA⟩

theorem conjugatesIntoSet_subset_conjugatesInto (H : Subgroup G) (A : Set ↥H) :
    conjugatesIntoSet H A ⊆ conjugatesInto H := by
  rintro g ⟨x, hx, _⟩
  exact ⟨x, hx⟩

@[simp] theorem conjugatesIntoSet_empty (H : Subgroup G) :
    conjugatesIntoSet H (∅ : Set ↥H) = ∅ := by
  ext g
  constructor
  · rintro ⟨_, _, hA⟩
    exact False.elim hA
  · intro hg
    exact False.elim hg

@[simp] theorem conjugatesIntoSet_univ (H : Subgroup G) :
    conjugatesIntoSet H (Set.univ : Set ↥H) = conjugatesInto H := by
  ext g
  constructor
  · intro hg
    exact conjugatesIntoSet_subset_conjugatesInto H Set.univ hg
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, Set.mem_univ _⟩

/-- The `x`-summand in the classical induction formula. It is zero unless
`x⁻¹ * g * x ∈ H`. -/
def induceTerm (H : Subgroup G) (θ : ClassFunction ↥H k) (x g : G) : k :=
  by
    classical
    exact if hx : x⁻¹ * g * x ∈ H then θ ⟨x⁻¹ * g * x, hx⟩ else 0

@[simp] theorem induceTerm_of_mem {H : Subgroup G} (θ : ClassFunction ↥H k) {x g : G}
    (hx : x⁻¹ * g * x ∈ H) :
    induceTerm H θ x g = θ ⟨x⁻¹ * g * x, hx⟩ := by
  simp [induceTerm, hx]

@[simp] theorem induceTerm_of_not_mem {H : Subgroup G} (θ : ClassFunction ↥H k) {x g : G}
    (hx : x⁻¹ * g * x ∉ H) :
    induceTerm H θ x g = 0 := by
  simp [induceTerm, hx]

theorem induceTerm_conj (H : Subgroup G) (θ : ClassFunction ↥H k) (x g h : G) :
    induceTerm H θ x (h * g * h⁻¹) = induceTerm H θ (h⁻¹ * x) g := by
  classical
  unfold induceTerm
  have heq : (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) = x⁻¹ * (h * g * h⁻¹) * x := by
    group
  by_cases hx : x⁻¹ * (h * g * h⁻¹) * x ∈ H
  · have hy : (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) ∈ H := by
      rwa [heq]
    rw [dif_pos hx, dif_pos hy]
    apply congrArg θ
    apply Subtype.ext
    exact heq.symm
  · have hy : (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) ∉ H := by
      intro hy
      exact hx (by rwa [← heq])
    rw [dif_neg hx, dif_neg hy]

@[simp] theorem induceTerm_zero (H : Subgroup G) (x g : G) :
    induceTerm H (0 : ClassFunction ↥H k) x g = 0 := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · simp [induceTerm, hx]
  · simp [induceTerm, hx]

theorem induceTerm_add (H : Subgroup G) (θ ψ : ClassFunction ↥H k) (x g : G) :
    induceTerm H (θ + ψ) x g = induceTerm H θ x g + induceTerm H ψ x g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · simp [induceTerm, hx]
  · simp [induceTerm, hx]

theorem induceTerm_smul (H : Subgroup G) (c : k) (θ : ClassFunction ↥H k) (x g : G) :
    induceTerm H (c • θ) x g = c * induceTerm H θ x g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · simp [induceTerm, hx]
  · simp [induceTerm, hx]

theorem induceTerm_eq_zero_of_not_conjugatesInto {H : Subgroup G} (θ : ClassFunction ↥H k)
    {g : G} (hg : g ∉ conjugatesInto H) (x : G) :
    induceTerm H θ x g = 0 := by
  classical
  have hx : x⁻¹ * g * x ∉ H := by
    intro hx
    exact hg ⟨x, hx⟩
  exact induceTerm_of_not_mem θ hx

theorem induceTerm_eq_zero_of_not_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H}
    {θ : ClassFunction ↥H k} (hθ : θ.support ⊆ A) {g : G}
    (hg : g ∉ conjugatesIntoSet H A) (x : G) :
    induceTerm H θ x g = 0 := by
  classical
  unfold induceTerm
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [dif_pos hx]
    by_contra hne
    exact hg ⟨x, hx, hθ hne⟩
  · rw [dif_neg hx]

variable [Fintype G]

/-- The unscaled classical induction sum.

Peterfalvi's `Ind_H^G θ` is obtained by multiplying this by `(|H| : k)⁻¹` when
that scalar is available. -/
def induceSum (H : Subgroup G) (θ : ClassFunction ↥H k) : ClassFunction G k where
  val g := ∑ x : G, induceTerm H θ x g
  property g h := by
    classical
    change (∑ x : G, induceTerm H θ x (h * g * h⁻¹)) =
      ∑ x : G, induceTerm H θ x g
    exact Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun x => induceTerm_conj H θ x g h)

@[simp] theorem induceSum_apply (H : Subgroup G) (θ : ClassFunction ↥H k) (g : G) :
    induceSum H θ g = ∑ x : G, induceTerm H θ x g := rfl

@[simp] theorem induceSum_zero (H : Subgroup G) :
    induceSum H (0 : ClassFunction ↥H k) = 0 := by
  ext g
  simp [induceSum]

theorem induceSum_add (H : Subgroup G) (θ ψ : ClassFunction ↥H k) :
    induceSum H (θ + ψ) = induceSum H θ + induceSum H ψ := by
  ext g
  simp [induceSum, induceTerm_add, Finset.sum_add_distrib]

theorem induceSum_smul (H : Subgroup G) (c : k) (θ : ClassFunction ↥H k) :
    induceSum H (c • θ) = c • induceSum H θ := by
  ext g
  rw [induceSum_apply, smul_apply, induceSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [induceTerm_smul]

theorem induceSum_eq_zero_of_not_conjugatesInto {H : Subgroup G} (θ : ClassFunction ↥H k)
    {g : G} (hg : g ∉ conjugatesInto H) :
    induceSum H θ g = 0 := by
  simp [induceSum, induceTerm_eq_zero_of_not_conjugatesInto θ hg]

theorem support_induceSum_subset_conjugatesInto (H : Subgroup G) (θ : ClassFunction ↥H k) :
    (induceSum H θ).support ⊆ conjugatesInto H := by
  intro g hg
  by_contra hnot
  exact hg (induceSum_eq_zero_of_not_conjugatesInto θ hnot)

theorem induceSum_eq_zero_of_not_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H}
    {θ : ClassFunction ↥H k} (hθ : θ.support ⊆ A) {g : G}
    (hg : g ∉ conjugatesIntoSet H A) :
    induceSum H θ g = 0 := by
  simp [induceSum, induceTerm_eq_zero_of_not_conjugatesIntoSet hθ hg]

theorem support_induceSum_subset_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H}
    {θ : ClassFunction ↥H k} (hθ : θ.support ⊆ A) :
    (induceSum H θ).support ⊆ conjugatesIntoSet H A := by
  intro g hg
  by_contra hnot
  exact hg (induceSum_eq_zero_of_not_conjugatesIntoSet hθ hnot)

section Normalized

/-- The normalized classical induced class function.

This is Peterfalvi's `Ind_H^G θ`: the unscaled induction sum multiplied by
`|H|⁻¹`.  The invertibility assumption keeps this usable over any coefficient
ring where `|H|` has a specified inverse. -/
def induce (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) : ClassFunction G k :=
  ⅟(Nat.card H : k) • induceSum H θ

@[simp] theorem induce_apply (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) (g : G) :
    induce H θ g = ⅟(Nat.card H : k) * ∑ x : G, induceTerm H θ x g :=
  rfl

@[simp] theorem card_smul_induce (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) :
    (Nat.card H : k) • induce H θ = induceSum H θ := by
  rw [induce, smul_smul, mul_invOf_self, one_smul]

@[simp] theorem induce_zero (H : Subgroup G) [Invertible (Nat.card H : k)] :
    induce H (0 : ClassFunction ↥H k) = 0 := by
  rw [induce, induceSum_zero, smul_zero]

theorem induce_add (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ ψ : ClassFunction ↥H k) :
    induce H (θ + ψ) = induce H θ + induce H ψ := by
  rw [induce, induce, induce, induceSum_add, smul_add]

theorem induce_smul (H : Subgroup G) [Invertible (Nat.card H : k)]
    (c : k) (θ : ClassFunction ↥H k) :
    induce H (c • θ) = c • induce H θ := by
  rw [induce, induce, induceSum_smul, smul_smul, smul_smul, mul_comm]

theorem induce_eq_zero_of_not_conjugatesInto {H : Subgroup G}
    [Invertible (Nat.card H : k)] (θ : ClassFunction ↥H k) {g : G}
    (hg : g ∉ conjugatesInto H) :
    induce H θ g = 0 := by
  rw [induce, smul_apply, induceSum_eq_zero_of_not_conjugatesInto θ hg, mul_zero]

theorem support_induce_subset_conjugatesInto (H : Subgroup G)
    [Invertible (Nat.card H : k)] (θ : ClassFunction ↥H k) :
    (induce H θ).support ⊆ conjugatesInto H := by
  intro g hg
  by_contra hnot
  exact hg (induce_eq_zero_of_not_conjugatesInto θ hnot)

theorem induce_eq_zero_of_not_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H}
    [Invertible (Nat.card H : k)] {θ : ClassFunction ↥H k} (hθ : θ.support ⊆ A)
    {g : G} (hg : g ∉ conjugatesIntoSet H A) :
    induce H θ g = 0 := by
  rw [induce, smul_apply, induceSum_eq_zero_of_not_conjugatesIntoSet hθ hg, mul_zero]

theorem support_induce_subset_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H}
    [Invertible (Nat.card H : k)] {θ : ClassFunction ↥H k} (hθ : θ.support ⊆ A) :
    (induce H θ).support ⊆ conjugatesIntoSet H A := by
  intro g hg
  by_contra hnot
  exact hg (induce_eq_zero_of_not_conjugatesIntoSet hθ hnot)

end Normalized

section FrobeniusReciprocity

variable [StarRing k]

/-- The `x`-slice of the induction sum, paired with `star (χ g)`, does not depend on
`x` when `χ` is a class function: conjugating `g ↦ x * g * x⁻¹` sends the `x`-slice to
the `1`-slice and fixes `χ`. -/
theorem sum_induceTerm_mul_star_eq (H : Subgroup G) (θ : ClassFunction ↥H k)
    (χ : ClassFunction G k) (x : G) :
    (∑ g : G, induceTerm H θ x g * star (χ g)) =
      ∑ g : G, induceTerm H θ 1 g * star (χ g) := by
  refine (Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ ?_).symm
  intro g
  have hconj : (MulAut.conj x).toEquiv g = x * g * x⁻¹ := by simp [MulAut.conj_apply]
  rw [hconj]
  have hterm : induceTerm H θ x (x * g * x⁻¹) = induceTerm H θ 1 g := by
    have := induceTerm_conj H θ x g x
    rwa [inv_mul_cancel] at this
  rw [hterm, χ.conj_eq g x]

/-- The `1`-slice of the induction sum, paired with `star (χ g)`, collected over the
subgroup: only `g ∈ H` contributes, where `induceTerm H θ 1 g = θ g`. -/
theorem sum_induceTerm_one_mul_star_eq (H : Subgroup G) [Fintype H]
    (θ : ClassFunction ↥H k) (χ : ClassFunction G k) :
    (∑ g : G, induceTerm H θ 1 g * star (χ g)) =
      ∑ h : H, θ h * star ((restrict H χ) h) := by
  classical
  set s : Finset G := Finset.univ.filter (fun g : G => g ∈ H) with hs
  have hmem_iff : ∀ x : G, x ∈ s ↔ x ∈ H := fun x => by simp [hs]
  -- Step 1: collapse the universe sum to the filtered sum (off-`H` terms vanish).
  have hstep1 :
      (∑ g : G, induceTerm H θ 1 g * star (χ g)) =
        ∑ g ∈ s, induceTerm H θ 1 g * star (χ g) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro g _ hg
    have hgH : g ∉ H := by rw [hmem_iff] at hg; exact hg
    have hnmem : (1 : G)⁻¹ * g * 1 ∉ H := by simpa using hgH
    rw [induceTerm_of_not_mem θ hnmem, zero_mul]
  -- Step 2: identify the filtered sum with the subtype sum over `H`.
  have hstep2 :
      (∑ g ∈ s, induceTerm H θ 1 g * star (χ g)) =
        ∑ h : H, θ h * star ((restrict H χ) h) := by
    rw [Finset.sum_subtype s hmem_iff (fun g => induceTerm H θ 1 g * star (χ g))]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hmem : (1 : G)⁻¹ * (h : G) * 1 ∈ H := by
      rw [inv_one, one_mul, mul_one]; exact h.2
    rw [induceTerm_of_mem θ hmem]
    have hθeq : (θ : ↥H → k) ⟨(1 : G)⁻¹ * (h : G) * 1, hmem⟩ = (θ : ↥H → k) h :=
      congrArg (θ : ↥H → k) (by apply Subtype.ext; simp)
    rw [hθeq]; rfl
  rw [hstep1, hstep2]

/-- **Frobenius reciprocity** for the classical induced class function, in
unnormalized inner-sum form:

`∑_{g∈G} (Ind θ)^{unscaled}(g) · star (χ g) = |G| · ∑_{h∈H} θ h · star (χ h)`.

The factor `|G|` arises because each of the `|G|` slices indexed by `x ∈ G` contributes
the same subgroup sum. -/
theorem sum_induceSum_mul_star_eq (H : Subgroup G) [Fintype H] (θ : ClassFunction ↥H k)
    (χ : ClassFunction G k) :
    (∑ g : G, induceSum H θ g * star (χ g)) =
      (Nat.card G : k) * ∑ h : H, θ h * star ((restrict H χ) h) := by
  classical
  have hswap :
      (∑ g : G, induceSum H θ g * star (χ g)) =
        ∑ x : G, ∑ g : G, induceTerm H θ x g * star (χ g) := by
    simp only [induceSum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap]
  have hconst : ∀ x : G,
      (∑ g : G, induceTerm H θ x g * star (χ g)) =
        ∑ h : H, θ h * star ((restrict H χ) h) := by
    intro x
    rw [sum_induceTerm_mul_star_eq H θ χ x,
      sum_induceTerm_one_mul_star_eq H θ χ]
  rw [Finset.sum_congr rfl fun x _ => hconst x]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- **Frobenius reciprocity** (numerical / class-function form):
`(Ind_H^G θ, χ)_G = (θ, Res_H^G χ)_H`.

This is [Is] Lemma 5.2, the adjunction between induction and restriction at the level of
class-function inner products. -/
theorem inner_induce_eq_inner_restrict (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) (χ : ClassFunction G k) :
    ClassFunction.inner (induce H θ) χ =
      ClassFunction.inner θ (restrict H χ) := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
    ClassFunction.innerSum]
  have hL : ∀ g : G, (induce H θ) g * star (χ g) =
      ⅟(Nat.card H : k) * (induceSum H θ g * star (χ g)) := by
    intro g
    rw [induce, ClassFunction.smul_apply, mul_assoc]
  rw [Finset.sum_congr rfl fun g _ => hL g, ← Finset.mul_sum,
    sum_induceSum_mul_star_eq H θ χ]
  set S : k := ∑ h : H, θ h * star ((restrict H χ) h) with hS
  -- LHS: ⅟|G| * (⅟|H| * (|G| * S))  =  ⅟|H| * S  :RHS
  calc ⅟(Nat.card G : k) * (⅟(Nat.card H : k) * ((Nat.card G : k) * S))
      = (⅟(Nat.card G : k) * (Nat.card G : k)) * (⅟(Nat.card H : k) * S) := by ring
    _ = ⅟(Nat.card H : k) * S := by rw [invOf_mul_self, one_mul]

end FrobeniusReciprocity

end ClassFunction

end OddOrder.RepresentationTheory
