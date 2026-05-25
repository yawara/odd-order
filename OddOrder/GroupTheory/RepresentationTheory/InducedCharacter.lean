/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Units.Equiv
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

end ClassFunction

end OddOrder.RepresentationTheory
