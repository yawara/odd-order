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
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import OddOrder.GroupTheory.TISubset

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

@[simp] theorem mem_conjugatesInto {H : Subgroup G} {g : G} :
    g ∈ conjugatesInto H ↔ ∃ x : G, x⁻¹ * g * x ∈ H := Iff.rfl

/-- Elements of `G` that are conjugate into `A`, where `A` is a set of elements
of the subgroup `H`. -/
def conjugatesIntoSet (H : Subgroup G) (A : Set ↥H) : Set G :=
  { g | ∃ (x : G) (hx : x⁻¹ * g * x ∈ H), (⟨x⁻¹ * g * x, hx⟩ : ↥H) ∈ A }

theorem mem_conjugatesIntoSet {H : Subgroup G} {A : Set ↥H} {g : G} :
    g ∈ conjugatesIntoSet H A ↔
      ∃ (x : G) (hx : x⁻¹ * g * x ∈ H), (⟨x⁻¹ * g * x, hx⟩ : ↥H) ∈ A := Iff.rfl

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

/-- If H is normal, being conjugate into H is the same as lying in H. -/
theorem conjugatesInto_eq_of_normal (H : Subgroup G) [H.Normal] :
    conjugatesInto H = H := by
  ext g
  constructor
  · rintro ⟨x, hx⟩
    have hg := (‹H.Normal›.conj_mem' (x⁻¹ * g * x) hx x⁻¹)
    have hg' : x * (x⁻¹ * g * x) * x⁻¹ ∈ H := by simpa using hg
    have heq : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
    exact heq ▸ hg'
  · intro hg
    exact ⟨1, by simpa using hg⟩

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

/-- The induction summand commutes with complex conjugation. -/
theorem induceTerm_conjStar (H : Subgroup G) (θ : ClassFunction ↥H ℂ) (x g : G) :
    star (induceTerm H θ x g) = induceTerm H θ.conj x g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem θ hx, induceTerm_of_mem θ.conj hx, conj_apply]
  · rw [induceTerm_of_not_mem θ hx, induceTerm_of_not_mem θ.conj hx, star_zero]

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

/-- The unnormalized induction sum commutes with complex conjugation. -/
theorem induceSum_conj (H : Subgroup G) (θ : ClassFunction ↥H ℂ) :
    (induceSum H θ).conj = induceSum H θ.conj := by
  ext g
  rw [conj_apply, induceSum_apply, induceSum_apply, star_sum]
  exact Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g

open scoped Classical in
/-- **Peterfalvi (2.10.3)** (transversal value, unscaled form).  Only those `x ∈ G`
with `x⁻¹ g x ∈ H` contribute to the induction sum, so the universe sum collapses to a
sum over the `Finset` of such `x`. -/
theorem induceSum_apply_eq_sum_filter (H : Subgroup G) (θ : ClassFunction ↥H k) (g : G) :
    induceSum H θ g =
      ∑ x ∈ Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H), induceTerm H θ x g := by
  rw [induceSum_apply]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro x _ hx
  have hx' : x⁻¹ * g * x ∉ H := by simpa using hx
  exact induceTerm_of_not_mem θ hx'

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

/-- The normalized induced class function commutes with complex conjugation. -/
theorem induce_conj (H : Subgroup G) [Invertible (Nat.card H : ℂ)]
    (θ : ClassFunction ↥H ℂ) :
    (induce H θ).conj = induce H θ.conj := by
  ext g
  rw [conj_apply, induce_apply, induce_apply, star_mul', star_sum]
  have hscale : star (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, star_natCast]
  rw [hscale]
  exact congrArg (fun z => ⅟(Nat.card H : ℂ) * z)
    (Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g)

open scoped Classical in
/-- **Peterfalvi (2.10.3)** (transversal value, normalized form).  The normalized
induced class function `Ind_H^G θ` at `g` is `|H|⁻¹` times the sum of `induceTerm` over
just those `x ∈ G` with `x⁻¹ g x ∈ H`. -/
theorem induce_apply_eq_sum_filter (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) (g : G) :
    induce H θ g =
      ⅟(Nat.card H : k) *
        ∑ x ∈ Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H), induceTerm H θ x g := by
  rw [induce_apply, ← induceSum_apply, induceSum_apply_eq_sum_filter]

/-- **Degree of the induced class function** ([Is] Thm 6.34, degree part).  The induced
class function `Ind_H^G θ` at the identity equals `[G : H] · θ(1)`.

Every conjugate `x⁻¹ · 1 · x = 1` lies in `H`, so all `|G|` summands of the induction sum
equal `θ(1)`; dividing by `|H|` and using `|G| = [G : H] · |H|` (`Subgroup.index_mul_card`)
leaves the index factor `[G : H]`.  This is the final degree computation behind Frobenius'
induced-character degree formula. -/
theorem induce_apply_one (H : Subgroup G) [Invertible (Nat.card H : k)]
    (θ : ClassFunction ↥H k) :
    induce H θ (1 : G) = (H.index : k) * θ (1 : ↥H) := by
  rw [induce_apply]
  have hterm : ∀ x : G, induceTerm H θ x (1 : G) = θ (1 : ↥H) := by
    intro x
    have hx : x⁻¹ * (1 : G) * x ∈ H := by simp [H.one_mem]
    rw [induceTerm_of_mem θ hx]
    exact congrArg θ (Subtype.ext (by simp))
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← H.index_mul_card]
  push_cast
  rw [mul_comm (H.index : k) _, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul]

/-- **Induced class function vanishes outside a normal subgroup.**  For `H ⊴ G` and any
`θ : ClassFunction ↥H k`, the induced `Ind_H^G θ` vanishes off `H`: `Ind_H^G θ (g) = 0` for
`g ∉ H`.  Every induction term `induceTerm H θ x g` vanishes because `x⁻¹ g x ∈ H ⟺ g ∈ H`
(normality: `x H x⁻¹ = H`), so no conjugate of a `g ∉ H` lands in `H`.

This is the support statement behind Peterfalvi (12.5): the off-kernel part of `Res_H ψ`, a
combination of characters induced from `H' ⊴ H`, vanishes on `H − H'`. -/
theorem induce_apply_eq_zero_of_not_mem_normal (H : Subgroup G) [Invertible (Nat.card H : k)]
    [hH : H.Normal] (θ : ClassFunction ↥H k) {g : G} (hg : g ∉ H) :
    induce H θ g = 0 := by
  rw [induce_apply]
  have hz : ∑ x : G, induceTerm H θ x g = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply induceTerm_of_not_mem
    intro hmem
    apply hg
    have h2 : x * (x⁻¹ * g * x) * x⁻¹ ∈ H := hH.conj_mem _ hmem x
    have h3 : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
    rwa [h3] at h2
  rw [hz, mul_zero]

/-- **Sums of characters induced from a normal subgroup vanish off it.**  For `H ⊴ G`, any
`k`-linear combination `∑ i ∈ s, a i • Ind_H^G (θ i)` of induced class functions vanishes at
every `g ∉ H`.  Termwise consequence of `induce_apply_eq_zero_of_not_mem_normal`.

This is Peterfalvi/Coq (12.5) step 6 (`cfun_onP (cfInd_normal)`) and the analogous step of
(12.15): `Res_H(ψ^ρ) = ∑_λ a_λ · Ind_{H'}^H λ + a · 1_H` is constant on `H − H'` because every
induced-from-`H' ⊴ H` summand vanishes there, leaving the constant `a`. -/
theorem sum_smul_induce_apply_eq_zero_of_not_mem_normal {ι : Type*} (H : Subgroup G)
    [Invertible (Nat.card H : k)] [H.Normal] (s : Finset ι) (a : ι → k)
    (θ : ι → ClassFunction ↥H k) {g : G} (hg : g ∉ H) :
    (∑ i ∈ s, a i • induce H (θ i)) g = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, add_apply, smul_apply,
        induce_apply_eq_zero_of_not_mem_normal H (θ i) hg, mul_zero, zero_add, ih]

/-- **An "induced-from-normal + constant" class function is constant off the normal subgroup.**
If `ψ = (∑ i ∈ s, a i • Ind_H^G (θ i)) + c` pointwise, with `H ⊴ G`, then `ψ x = ψ y` for all
`x, y ∉ H`: every induced summand vanishes off `H`
(`sum_smul_induce_apply_eq_zero_of_not_mem_normal`), leaving the common constant `c`.

This is the final "constant on `H − H'`" step shared by Peterfalvi (12.5) (`Res_H(ψ^ρ) =
∑_λ a_λ Ind_{H'}^H λ + a·1_H`) and (12.15) (the analogous `ρ_M`-image decomposition on `K − K'`);
establishing the decomposition itself is the Clifford-theoretic content upstream of this
reduction. -/
theorem apply_eq_of_eq_sum_smul_induce_add_const {ι : Type*} (H : Subgroup G)
    [Invertible (Nat.card H : k)] [H.Normal] (ψ : ClassFunction G k) (s : Finset ι)
    (a : ι → k) (θ : ι → ClassFunction ↥H k) (c : k)
    (hψ : ∀ g : G, ψ g = (∑ i ∈ s, a i • induce H (θ i)) g + c) {x y : G}
    (hx : x ∉ H) (hy : y ∉ H) : ψ x = ψ y := by
  rw [hψ x, hψ y, sum_smul_induce_apply_eq_zero_of_not_mem_normal H s a θ hx,
    sum_smul_induce_apply_eq_zero_of_not_mem_normal H s a θ hy]

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

/-- **Induction commutes with finite sums**: `Ind_H^G (∑ i ∈ s, F i) = ∑ i ∈ s, Ind_H^G (F i)`.
Termwise from `induce_add` / `induce_zero`.  Used to push `Ind_I^H` through the inertia-level
decomposition `∑_β ψ·Inf(β)` in the (1.7.a) Clifford-correspondence lift. -/
theorem induce_sum {ι : Type*} (H : Subgroup G) [Invertible (Nat.card H : k)]
    (s : Finset ι) (F : ι → ClassFunction ↥H k) :
    induce H (∑ i ∈ s, F i) = ∑ i ∈ s, induce H (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, induce_add, ih]

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

/-- If H is normal, Ind_H^G θ vanishes outside H. -/
theorem induce_eq_zero_of_not_mem_normal {H : Subgroup G} [H.Normal]
    [Invertible (Nat.card H : k)] (θ : ClassFunction ↥H k) {g : G} (hg : g ∉ H) :
    induce H θ g = 0 := by
  exact induce_eq_zero_of_not_conjugatesInto θ (by
    simpa [conjugatesInto_eq_of_normal H] using hg)

/-- If H is normal, Ind_H^G θ is supported on H. -/
theorem support_induce_subset_of_normal (H : Subgroup G) [H.Normal]
    [Invertible (Nat.card H : k)] (θ : ClassFunction ↥H k) :
    (induce H θ).support ⊆ H := by
  intro g hg
  have hconj := support_induce_subset_conjugatesInto H θ hg
  simpa [conjugatesInto_eq_of_normal H] using hconj

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

section ConjugacyInvariance

/-! ### Peterfalvi (2.10.1): `L`-conjugacy invariance of the induced class function

If `H` is replaced by its conjugate `H^ℓ = H.map (MulAut.conj ℓ)` and `θ` is transported
accordingly (`transportConj ℓ θ`), the induced class function is unchanged.  This is the
invariance used in Peterfalvi (2.10.1) when re-indexing the inclusion-exclusion sum over a
set of conjugacy-class representatives `ℬ`: each `Ind_{M(B^x)}^G α_{B^x}` equals
`Ind_{M(B)}^G α_B`.
-/

omit [Fintype G] in
/-- The **transport** of a class function `θ` on `H` to a class function on the conjugate
subgroup `H^ℓ = H.map (MulAut.conj ℓ)`: it sends `y ∈ H^ℓ` to `θ (ℓ⁻¹ y ℓ)`.

This is `θ` precomposed with the inverse of the conjugation isomorphism
`MulEquiv.subgroupMap (MulAut.conj ℓ) H : H ≃* H^ℓ`. -/
def transportConj (ℓ : G) {H : Subgroup G} (θ : ClassFunction ↥H k) :
    ClassFunction ↥(H.map (MulAut.conj ℓ : G →* G)) k :=
  compHom (MulEquiv.subgroupMap (MulAut.conj ℓ) H).symm.toMonoidHom θ

omit [Fintype G] in
@[simp] theorem transportConj_apply (ℓ : G) {H : Subgroup G} (θ : ClassFunction ↥H k)
    (y : ↥(H.map (MulAut.conj ℓ : G →* G))) :
    transportConj ℓ θ y = θ ((MulEquiv.subgroupMap (MulAut.conj ℓ) H).symm y) := rfl

omit [Fintype G] in
/-- The summand identity behind Peterfalvi (2.10.1): re-indexing `x ↦ x * ℓ⁻¹` matches the
`x`-summand for `H^ℓ` with the `x`-summand for `H`. -/
theorem induceTerm_transportConj (ℓ : G) {H : Subgroup G} (θ : ClassFunction ↥H k) (x g : G) :
    induceTerm (H.map (MulAut.conj ℓ : G →* G)) (transportConj ℓ θ) (x * ℓ⁻¹) g =
      induceTerm H θ x g := by
  classical
  set e : G ≃* G := MulAut.conj ℓ with he
  -- The reindexed conjugate `e.symm ((x ℓ⁻¹)⁻¹ g (x ℓ⁻¹))` collapses to `x⁻¹ g x`.
  have key : e.symm ((x * ℓ⁻¹)⁻¹ * g * (x * ℓ⁻¹)) = x⁻¹ * g * x := by
    rw [he]; simp only [MulAut.conj_symm_apply]; group
  -- The conjugation condition for `H^ℓ` at `x * ℓ⁻¹` matches the condition for `H` at `x`.
  have hcond : (x * ℓ⁻¹)⁻¹ * g * (x * ℓ⁻¹) ∈ H.map (e : G →* G) ↔ x⁻¹ * g * x ∈ H := by
    rw [← key]; exact Subgroup.mem_map_equiv
  unfold induceTerm
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hy : (x * ℓ⁻¹)⁻¹ * g * (x * ℓ⁻¹) ∈ H.map (e : G →* G) := hcond.mpr hx
    rw [dif_pos hy, dif_pos hx]
    apply congrArg θ
    apply Subtype.ext
    change (e.symm ((x * ℓ⁻¹)⁻¹ * g * (x * ℓ⁻¹)) : G) = x⁻¹ * g * x
    exact key
  · have hy : (x * ℓ⁻¹)⁻¹ * g * (x * ℓ⁻¹) ∉ H.map (e : G →* G) := fun h => hx (hcond.mp h)
    rw [dif_neg hy, dif_neg hx]

/-- **Peterfalvi (2.10.1)** for the unscaled induction sum: the induced class function of a
conjugate subgroup (with the transported class function) agrees with the original. -/
theorem induceSum_map_conj (ℓ : G) {H : Subgroup G} (θ : ClassFunction ↥H k) :
    induceSum (H.map (MulAut.conj ℓ : G →* G)) (transportConj ℓ θ) = induceSum H θ := by
  ext g
  rw [induceSum_apply, induceSum_apply]
  refine Fintype.sum_equiv (Equiv.mulRight ℓ)
    (fun x => induceTerm (H.map (MulAut.conj ℓ : G →* G)) (transportConj ℓ θ) x g)
    (fun x => induceTerm H θ x g) (fun x => ?_)
  have := induceTerm_transportConj ℓ θ (x * ℓ) g
  rwa [mul_inv_cancel_right] at this

/-- **Peterfalvi (2.10.1)** (normalized form): the normalized induced class function
`Ind_{H^ℓ}^G (transportConj ℓ θ) = Ind_H^G θ`.  The `|H^ℓ| = |H|` factors agree because
conjugation is an isomorphism (`Subgroup.card_map_of_injective`). -/
theorem induce_map_conj (ℓ : G) {H : Subgroup G}
    [Invertible (Nat.card H : k)]
    [Invertible (Nat.card (H.map (MulAut.conj ℓ : G →* G)) : k)]
    (θ : ClassFunction ↥H k) :
    induce (H.map (MulAut.conj ℓ : G →* G)) (transportConj ℓ θ) = induce H θ := by
  have hcard : Nat.card (H.map (MulAut.conj ℓ : G →* G)) = Nat.card H :=
    Subgroup.card_map_of_injective (EquivLike.injective (MulAut.conj ℓ))
  have hcast : ((Nat.card (H.map (MulAut.conj ℓ : G →* G)) : k)) = (Nat.card H : k) := by
    rw [hcard]
  rw [induce, induce, induceSum_map_conj]
  congr 1
  -- The two chosen inverses of `(|H| : k)` agree since the cardinalities (hence casts) agree.
  exact invertible_unique _ _ hcast

end ConjugacyInvariance

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

/-- **Frobenius reciprocity against the trivial character.**  `⟨Ind_H^G θ, 1_G⟩ = ⟨θ, 1_H⟩`:
the multiplicity of the principal character of `G` in the induced class function equals the
multiplicity of the principal character of `H` in `θ` (`= ⟨θ, 1_H⟩ = ⟨Ind_H^G θ, 1_G⟩`).  Immediate
from `inner_induce_eq_inner_restrict` and `restrict H 1_G = 1_H`.

This is the source-side computation behind Peterfalvi (7.8): for the induced family
`ζ_i = Ind_H^L θ_i`, a **non-principal** `θ_i ≠ 1_H` gives `⟨ζ_i, 1_L⟩ = ⟨θ_i, 1_H⟩ = 0`, the input
(via the (2.7) adjoint) to the `S^ν ⊥ 1_G` orthogonality (`BetaDecomp.orth_one`). -/
theorem induce_inner_trivial (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    (θ : ClassFunction ↥H ℂ) :
    ClassFunction.inner (induce H θ) (trivialClassFunction G)
      = ClassFunction.inner θ (trivialClassFunction ↥H) := by
  rw [inner_induce_eq_inner_restrict]
  have hres : ClassFunction.restrict H (trivialClassFunction G) = trivialClassFunction ↥H := by
    ext h
    simp [ClassFunction.restrict_apply, trivialClassFunction_apply]
  rw [hres]

end FrobeniusReciprocity

section TIInduction

/-! ### Induction from a TI-subset: value identity and isometry

For a TI-subset `A ⊆ G` with normalizer-bound `H` (`OddOrder.GroupTheory.IsTISubset A H`) and
class functions on `H` vanishing off `A`, induction returns the original values on `A`, hence is
an isometry on `A`-supported class functions (Isaacs, *Character Theory of Finite Groups*,
Lemma 7.7; Coq `PFsection2.normedTI_Ind_id` / `normedTI_isometry`, proved there through the
degenerate Dade context of Peterfalvi (2.3), here directly from the induction formula).  Only
the `|H|` summands with conjugator inside `H` survive in the induction sum — any other
nonvanishing summand would exhibit an overlap of two distinct conjugates of `A` — and each
surviving summand contributes the original value.

This is the `h_isom` input of the prime-TI value identity `prTIirr_id` (Peterfalvi (4.3.c)):
`W ∖ W₂` is a TI-subset in the type-P₂ context, so induction from `CF(W, W ∖ W₂)` is an
isometry onto its image. -/

open OddOrder.GroupTheory (IsTISubset)

/-- **TI value identity** (Isaacs CTFG Lemma 7.7, identity part; Coq `normedTI_Ind_id`): for a
TI-subset `A` with normalizer-bound `H` and a class function `θ` on `H` vanishing off `A`, the
induced class function restricts back to the original values on `A`: `Ind_H^G θ (a) = θ a` for
`a ∈ H` with `↑a ∈ A`.

In the induction sum at `a`, a summand with conjugator `x ∉ H` and `x⁻¹ a x ∈ H` can be nonzero
only if `x⁻¹ a x ∈ A` (support of `θ`), which by the TI condition forces `x⁻¹ ∈ H` — a
contradiction; so the sum collapses to the `|H|` conjugators in `H`, each contributing `θ a` by
conjugation invariance. -/
theorem induce_apply_coe_of_isTISubset (H : Subgroup G)
    [Invertible (Nat.card H : k)]
    {A : Set G} (hTI : IsTISubset A H)
    {θ : ClassFunction ↥H k} (hθ : ∀ x : ↥H, (x : G) ∉ A → θ x = 0)
    {a : ↥H} (ha : (a : G) ∈ A) :
    induce H θ (a : G) = θ a := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite ↥H
  rw [induce_apply]
  set s : Finset G := Finset.univ.filter (fun x : G => x ∈ H) with hs
  have hmem_iff : ∀ x : G, x ∈ s ↔ x ∈ H := fun x => by simp [hs]
  -- Off-`H` conjugators contribute nothing: a nonzero term would place `x⁻¹ a x` in the
  -- support `A`, and the TI condition would force `x ∈ H`.
  have hcollapse : (∑ x : G, induceTerm H θ x (a : G))
      = ∑ x ∈ s, induceTerm H θ x (a : G) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x _ hx
    have hxH : x ∉ H := fun hc => hx ((hmem_iff x).mpr hc)
    by_cases hmem : x⁻¹ * (a : G) * x ∈ H
    · rw [induceTerm_of_mem θ hmem]
      by_contra hne
      have hAin : x⁻¹ * (a : G) * x ∈ A := by
        by_contra hnot
        exact hne (hθ ⟨x⁻¹ * (a : G) * x, hmem⟩ hnot)
      have hinv : x⁻¹ ∈ H := hTI x⁻¹ ⟨(a : G), ha, by rw [inv_inv]; exact hAin⟩
      exact hxH (by simpa using H.inv_mem hinv)
    · exact induceTerm_of_not_mem θ hmem
  -- Conjugators in `H` each contribute `θ a`, by conjugation invariance of `θ`.
  have hconst : (∑ x ∈ s, induceTerm H θ x (a : G)) = ∑ _x : ↥H, θ a := by
    rw [Finset.sum_subtype s hmem_iff (fun x => induceTerm H θ x (a : G))]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hmem : (h : G)⁻¹ * (a : G) * (h : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem h.2) a.2) h.2
    rw [induceTerm_of_mem θ hmem]
    have hcast : (⟨(h : G)⁻¹ * (a : G) * (h : G), hmem⟩ : ↥H) = h⁻¹ * a * h⁻¹⁻¹ :=
      Subtype.ext (by simp)
    rw [hcast]
    exact θ.conj_eq a h⁻¹
  rw [hcollapse, hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, invOf_mul_self, one_mul]

variable [StarRing k]

/-- **TI induction isometry** (Isaacs CTFG Lemma 7.7, isometry part; Coq `normedTI_isometry`):
for a TI-subset `A` with normalizer-bound `H` and class functions `θ, ψ` on `H` vanishing off
`A`, induction preserves inner products: `⟨Ind_H^G θ, Ind_H^G ψ⟩_G = ⟨θ, ψ⟩_H`.

Frobenius reciprocity gives `⟨Ind θ, Ind ψ⟩_G = ⟨θ, Res(Ind ψ)⟩_H`, and by the TI value
identity `Res(Ind ψ)` agrees with `ψ` on `A`, which carries the support of `θ`. -/
theorem inner_induce_eq_of_isTISubset (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]
    {A : Set G} (hTI : IsTISubset A H)
    {θ ψ : ClassFunction ↥H k}
    (hθ : ∀ x : ↥H, (x : G) ∉ A → θ x = 0) (hψ : ∀ x : ↥H, (x : G) ∉ A → ψ x = 0) :
    ClassFunction.inner (induce H θ) (induce H ψ) = ClassFunction.inner θ ψ := by
  rw [inner_induce_eq_inner_restrict]
  have hdiff : ClassFunction.inner θ (restrict H (induce H ψ) - ψ) = 0 := by
    refine inner_eq_zero_of_disjoint_support ?_
    rw [Set.disjoint_left]
    intro x hxθ hxd
    rw [mem_support] at hxθ hxd
    have hxA : (x : G) ∈ A := by
      by_contra h
      exact hxθ (hθ x h)
    refine hxd ?_
    rw [sub_apply, restrict_apply, induce_apply_coe_of_isTISubset H hTI hψ hxA, sub_self]
  rw [inner_sub_right] at hdiff
  exact sub_eq_zero.mp hdiff

end TIInduction

section NormalSubgroupValue

/-! ### Value of the induced character on a normal subgroup contained in `H`

For `A ⊴ G` with `A ≤ H`, every conjugate `x⁻¹ a x` of `a ∈ A` stays in `A ≤ H`, so the
induction sum at `a` has **no** vanishing terms: it runs over all of `G`, each summand being
`θ` evaluated at the conjugate.  This is the computational core behind Peterfalvi (1.6.a):
if `θ` is constant (equal to its degree) on `A`, then so is `Ind_H^G θ`. -/

omit [Fintype G] in
/-- For a normal subgroup `A ⊴ G` with `A ≤ H` and `a ∈ A`, the `x`-summand of the
induction sum at `a` is `θ` evaluated at the conjugate `x⁻¹ a x ∈ A ≤ H` (no term vanishes,
since `A` is closed under `G`-conjugation). -/
theorem induceTerm_of_mem_normal {A H : Subgroup G} (hAH : A ≤ H) [hA : A.Normal]
    (θ : ClassFunction ↥H k) {a : G} (ha : a ∈ A) (x : G) :
    induceTerm H θ x a =
      θ ⟨x⁻¹ * a * x, hAH (hA.conj_mem' a ha x)⟩ := by
  have hxa : x⁻¹ * a * x ∈ H := hAH (hA.conj_mem' a ha x)
  rw [induceTerm_of_mem θ hxa]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Value of `Ind_H^G θ` on a normal subgroup, constant case.**  Let `A ⊴ G` with `A ≤ H`,
and suppose `θ` takes a single value `c` on all of `A` (as a subset of `H`).  Then `Ind_H^G θ`
takes the value `|G|·c·|H|⁻¹` at every `a ∈ A`.

This is the heart of the forward direction of Peterfalvi (1.6.a): since every conjugate of
`a ∈ A` lands back in `A` (normality) and `θ` is constant on `A`, all `|G|` summands of the
induction sum coincide. -/
theorem induce_apply_of_mem_normal_of_const {A H : Subgroup G} (hAH : A ≤ H) [A.Normal]
    [Invertible (Nat.card H : k)] (θ : ClassFunction ↥H k) {c : k}
    (hc : ∀ a' : G, ∀ ha' : a' ∈ A, θ ⟨a', hAH ha'⟩ = c) {a : G} (ha : a ∈ A) :
    induce H θ a = ⅟(Nat.card H : k) * ((Nat.card G : k) * c) := by
  rw [induce_apply]
  congr 1
  have hterm : ∀ x : G, induceTerm H θ x a = c := by
    intro x
    have hconj : x⁻¹ * a * x ∈ A := (‹A.Normal›.conj_mem' a ha x)
    rw [induceTerm_of_mem_normal hAH θ ha x]
    exact hc _ hconj
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]

end NormalSubgroupValue

section InducedTrivialNorm

variable [Invertible (Nat.card G : ℂ)]

omit [Invertible (Nat.card G : ℂ)] in
/-- **Restriction of the induced trivial character to a normal `H`**:
`Res_H Ind_H^G 1_H = [G:H]•1_H`.
Every `G`-conjugate of `h ∈ H` stays in `H` (normality), so `Ind_H^G 1_H` is the constant `[G:H]` on
`H` (`induce_apply_of_mem_normal_of_const`). -/
theorem restrict_induce_trivial (H : Subgroup G) [Finite ↥H] [H.Normal]
    [Invertible (Nat.card ↥H : ℂ)] :
    ClassFunction.restrict H (induce H (trivialClassFunction ↥H))
      = (H.index : ℂ) • trivialClassFunction ↥H := by
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  ext h
  rw [ClassFunction.restrict_apply, ClassFunction.smul_apply, trivialClassFunction_apply, mul_one,
    induce_apply_of_mem_normal_of_const (le_refl H) (trivialClassFunction ↥H)
      (fun a' ha' => trivialClassFunction_apply (⟨a', ha'⟩ : ↥H)) h.2, mul_one]
  have hcard : (Nat.card G : ℂ) = (H.index : ℂ) * (Nat.card ↥H : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  rw [hcard, mul_comm (H.index : ℂ), ← mul_assoc, invOf_mul_self, one_mul]

/-- **Norm of the induced trivial character** `⟨Ind_H^G 1_H, Ind_H^G 1_H⟩ = [G : H]` for a normal
`H ⊴ G` (`restrict_induce_trivial` + `⟨1_H, 1_H⟩ = 1`).  For `H ⊴ L` Frobenius this is Peterfalvi's
`⟨Ind 1_H, Ind 1_H⟩ = e`, the source-side norm behind the (7.8.b) computation `‖β‖² = e + 1`. -/
theorem induce_trivial_inner_self (H : Subgroup G) [Finite ↥H] [H.Normal]
    [Invertible (Nat.card ↥H : ℂ)] :
    ClassFunction.inner (induce H (trivialClassFunction ↥H))
        (induce H (trivialClassFunction ↥H)) = (H.index : ℂ) := by
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  rw [inner_induce_eq_inner_restrict, restrict_induce_trivial, inner_smul_right, star_natCast,
    OddOrder.RepresentationTheory.irr_cf_inner trivialClassFunction_isIrreducible
      trivialClassFunction_isIrreducible, if_pos rfl, mul_one]

/-- **Inner product of an induced character with the induced trivial character** for a normal `H`:
`⟨Ind_H^G φ, Ind_H^G 1_H⟩ = [G:H]·⟨φ, 1_H⟩`.  Frobenius reciprocity + `restrict_induce_trivial`. -/
theorem induce_inner_induce_trivial (H : Subgroup G) [Fintype ↥H] [H.Normal]
    [Invertible (Nat.card ↥H : ℂ)] (φ : ClassFunction ↥H ℂ) :
    ClassFunction.inner (induce H φ) (induce H (trivialClassFunction ↥H))
      = (H.index : ℂ) * ClassFunction.inner φ (trivialClassFunction ↥H) := by
  rw [inner_induce_eq_inner_restrict, restrict_induce_trivial, inner_smul_right, star_natCast]

/-- **Peterfalvi's `⟨ζ, Ind1H⟩ = 0`** (the source-side orthogonality of the (7.8.b) `‖β‖² = e+1`
computation): for a normal `H` and an irreducible `φ ≠ 1_H`, the induced character `Ind_H^G φ` is
orthogonal to the induced principal character `Ind_H^G 1_H`.  Immediate from
`induce_inner_induce_trivial` and `⟨φ, 1_H⟩ = 0`. -/
theorem induce_inner_induce_trivial_eq_zero_of_irreducible (H : Subgroup G) [Finite ↥H] [H.Normal]
    [Invertible (Nat.card ↥H : ℂ)] {φ : ClassFunction ↥H ℂ} (hφ : IsIrreducibleCharacter φ)
    (hφ1 : φ ≠ trivialClassFunction ↥H) :
    ClassFunction.inner (induce H φ) (induce H (trivialClassFunction ↥H)) = 0 := by
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  rw [induce_inner_induce_trivial,
    OddOrder.RepresentationTheory.irr_cf_inner hφ trivialClassFunction_isIrreducible, if_neg hφ1,
    mul_zero]

end InducedTrivialNorm

section VirtualCharacters

/-! ### Restriction and induction preserve virtual characters (Peterfalvi (2.6.b))

The Dade isometry sends virtual characters to virtual characters.  The two facts that
underlie this are:

* `restrict_mem_ZIrr` — restriction `Res^G_H` maps `ℤ[Irr G]` into `ℤ[Irr H]`.  The base
  case (an irreducible character `χ_ρ`) reduces to: the restriction of `ρ` to `H` is a
  *finite-dimensional* (not necessarily irreducible) representation of `H`, whose character
  lies in `ℤ[Irr H]` by `character_mem_ZIrr` (the completeness keystone).
* `induce_mem_ZIrr` — induction `Ind_H^G` maps `ℤ[Irr H]` into `ℤ[Irr G]`.  By completeness
  every class function is determined by its inner products against `Irr G`; numerical
  Frobenius reciprocity (`inner_induce_eq_inner_restrict`) turns each such pairing into a
  pairing over `H` of two virtual characters, which is an integer, so `Ind_H^G θ` is a
  finite integer combination of irreducibles.

These are the single biggest prerequisites of Peterfalvi (2.6.b).
-/

omit [Fintype G] in
/-- The character of `ρ` restricted to a subgroup `H` is the restriction of the character of
`ρ`: `Res^G_H (χ_ρ) = χ_{ρ ∘ H.subtype}`.  Here both sides are taken as class functions on
`H`, the right-hand side being the character of the restricted representation
`ρ.comp H.subtype : Representation ℂ H V`. -/
theorem restrict_repCharacterClassFunction {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (H : Subgroup G) (ρ : Representation ℂ G V) :
    restrict H (repCharacterClassFunction ρ)
      = repCharacterClassFunction (ρ.comp H.subtype) := by
  ext h
  rw [restrict_apply, repCharacterClassFunction_apply, repCharacterClassFunction_apply]
  rfl

variable [Finite G]

omit [Fintype G] in
/-- **Restriction preserves virtual characters.** For a subgroup `H ≤ G` and a virtual
character `φ ∈ ℤ[Irr G]`, the restriction `Res^G_H φ` is a virtual character of `H`.

This is one direction of Peterfalvi (2.6.b).  The proof is `Submodule.span_induction`: the
linear cases are immediate from linearity of `restrict`, and the base case `φ ∈ Irr(G)` —
the character of a finite-dimensional irreducible representation `ρ` — uses that
`Res^G_H (χ_ρ)` is the character of the *finite-dimensional* (a priori reducible)
representation `ρ.comp H.subtype` of `H`, which lies in `ℤ[Irr H]` by `character_mem_ZIrr`. -/
theorem restrict_mem_ZIrr (H : Subgroup G) {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    restrict H φ ∈ ZIrr H := by
  haveI : Finite H := Subtype.finite
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, _, hρeq⟩ := hx
      have hx_eq : x = repCharacterClassFunction ρ := by
        apply ClassFunction.ext
        intro g
        rw [repCharacterClassFunction_apply, congrFun hρeq g]
      rw [hx_eq, restrict_repCharacterClassFunction H ρ]
      exact character_mem_ZIrr (ρ.comp H.subtype)
  | zero => rw [restrict_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [restrict_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, restrict_smul, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ a ih

omit [Fintype G] [Finite G] in
/-- The pullback of the character of `ρ` along a group hom `f : H →* G` is the character of
the pulled-back representation: `(χ_ρ) ∘ f = χ_{ρ ∘ f}`.  Here the right-hand side is the
character of `ρ.comp f : Representation ℂ H V`. -/
theorem compHom_repCharacterClassFunction {H : Type*} [Group H]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : H →* G) (ρ : Representation ℂ G V) :
    compHom f (repCharacterClassFunction ρ)
      = repCharacterClassFunction (ρ.comp f) := by
  ext h
  rfl

omit [Fintype G] [Finite G] in
/-- **Pullback along a group hom preserves virtual characters.** For a group hom
`f : H →* G` with `H` finite and a virtual character `φ ∈ ℤ[Irr G]`, the pullback
`φ ∘ f` is a virtual character of `H`.

This is the general "Res along a homomorphism" form needed for Peterfalvi (2.9): the class
function `α_B = α ∘ f_B` is a virtual character of `M(B)` whenever `α ∈ ℤ[Irr L]`, where
`f_B : M(B) →* L`.  As with `restrict_mem_ZIrr`, the proof is `Submodule.span_induction`;
the base case uses that `(χ_ρ) ∘ f` is the character of the finite-dimensional
representation `ρ.comp f`, which lies in `ℤ[Irr H]` by `character_mem_ZIrr` (irreducibility
of `ρ.comp f` is *not* needed). -/
theorem compHom_mem_ZIrr {H : Type*} [Group H] [Finite H] (f : H →* G)
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    compHom f φ ∈ ZIrr H := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, _, hρeq⟩ := hx
      have hx_eq : x = repCharacterClassFunction ρ := by
        apply ClassFunction.ext
        intro g
        rw [repCharacterClassFunction_apply, congrFun hρeq g]
      rw [hx_eq, compHom_repCharacterClassFunction f ρ]
      exact character_mem_ZIrr (ρ.comp f)
  | zero => rw [compHom_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [compHom_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, compHom_smul, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ a ih

end VirtualCharacters

section InduceVirtualCharacters

/-! ### Induction preserves virtual characters -/

variable [Invertible (Nat.card G : ℂ)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- The inner product of two virtual characters is an integer.  Writing `ψ ∈ ℤ[Irr H]` as a
`ℤ`-combination of irreducibles and using that `⟨φ, χ⟩` is an integer for each irreducible
`χ` (`mem_ZIrr_inner_int`) and conjugate-linearity in the right argument. -/
theorem inner_mem_ZIrr_int {φ ψ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hψ : ψ ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ ψ = (m : ℂ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, hm⟩ := mem_ZIrr_inner_int (⟨x, hx⟩ : IrreducibleCharacter G) hφ
      exact ⟨m, hm⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_right, hmx, hmy]; push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, inner_smul_right, hm]
      simp only [star_intCast]; push_cast; ring

open scoped Classical in
set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Integral orthogonal projection onto a finite ZIrr-orthonormal family.**
For a virtual character `φ ∈ ZIrr G` and a finite family `R : Finset (CF G)` of virtual
characters (`hZ : ∀ α ∈ R, α ∈ ZIrr G`) that is orthonormal (`horth : ⟨α, β⟩ = δ_{α,β}`),
there are *integer* coefficients `c α = ⟨φ, α⟩ ∈ ℤ` (an integer because both `φ` and `α` are
virtual characters, `inner_mem_ZIrr_int`) and an orthogonal residual `Y` with

`φ = (∑_{α ∈ R} c α • α) + Y`     and     `⟨Y, α⟩ = 0` for all `α ∈ R`.

The integral span part `X := ∑_{α ∈ R} c α • α` is the orthogonal projection of `φ` onto
`ℤ[R]`; `Y := φ − X` is automatically orthogonal to `R` because, by orthonormality,
`⟨X, α⟩ = c α = ⟨φ, α⟩` so `⟨Y, α⟩ = ⟨φ, α⟩ − ⟨X, α⟩ = 0`.

This is the genuine *projection primitive* of Peterfalvi §7 (5.4)/(5.5)/(5.6.1): it supplies the
integral `X`-side, the orthogonal `Y`-side, and the integer coefficient function of a
`CharacterPsiDecomposition` from the single number-theoretic input `(χ − ψ)^{τ₁} ∈ ZIrr G`.  The
coefficient integrality (over the signed-irreducible family `R(χ) ⊆ ZIrr G`) is the load-bearing
content; the orthogonality of `Y` is then pure linear algebra. -/
theorem exists_intProjection_of_orthonormal_ZIrr
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {R : Finset (ClassFunction G ℂ)} (hZ : ∀ α ∈ R, α ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) :
    ∃ (c : ClassFunction G ℂ → ℤ) (Y : ClassFunction G ℂ),
      (∀ α ∈ R, (ClassFunction.inner φ α : ℂ) = (c α : ℂ)) ∧
      φ = (∑ α ∈ R, (c α : ℂ) • α) + Y ∧
      ∀ α ∈ R, ClassFunction.inner Y α = 0 := by
  classical
  -- Integer coefficients `c α := the integer value of ⟨φ, α⟩`.
  set c : ClassFunction G ℂ → ℤ :=
    fun α => if hα : α ∈ R then (inner_mem_ZIrr_int hφ (hZ α hα)).choose else 0 with hc
  -- Key: on `R`, `⟨φ, α⟩ = c α`.
  have hcoeff : ∀ α ∈ R, ClassFunction.inner φ α = (c α : ℂ) := by
    intro α hα
    rw [hc]; simp only [dif_pos hα]
    exact (inner_mem_ZIrr_int hφ (hZ α hα)).choose_spec
  refine ⟨c, φ - ∑ α ∈ R, (c α : ℂ) • α, hcoeff, by abel, ?_⟩
  -- `⟨Y, α⟩ = ⟨φ, α⟩ − ⟨X, α⟩ = c α − c α = 0`.
  intro α hα
  rw [ClassFunction.inner_sub_left, inner_orthonormalSum_eq_coeff horth hα, hcoeff α hα, sub_self]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Induction preserves virtual characters.** For a subgroup `H ≤ G` and a virtual
character `θ ∈ ℤ[Irr H]`, the induced class function `Ind_H^G θ` is a virtual character of `G`.

This is the other direction of Peterfalvi (2.6.b), the single biggest prerequisite of the
construction of the Dade map.  The proof is `Submodule.span_induction` on `θ`; the linear
cases follow from `induce_add` / `induce_smul`.  The base case `θ ∈ Irr(H)`:

* For every irreducible `χ ∈ Irr(G)`, numerical Frobenius reciprocity
  (`inner_induce_eq_inner_restrict`) gives `⟨Ind_H^G θ, χ⟩_G = ⟨θ, Res^G_H χ⟩_H`.
  Since `Res^G_H χ ∈ ℤ[Irr H]` (`restrict_mem_ZIrr`) and `θ ∈ ℤ[Irr H]`, this is an integer
  `f χ` (`inner_mem_ZIrr_int`).
* Set `Φ = ∑_{χ ∈ Irr G} (f χ : ℂ) • χ ∈ ℤ[Irr G]`.  Then `Ind_H^G θ - Φ` is orthogonal to
  every irreducible character (the diagonal Fourier coefficients agree by orthonormality), so
  it is `0` by completeness (`classFunction_eq_zero_of_orthogonal`).  Hence `Ind_H^G θ = Φ`. -/
theorem induce_mem_ZIrr (H : Subgroup G) [Fintype H] [Invertible (Nat.card H : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : θ ∈ ZIrr H) :
    induce H θ ∈ ZIrr G := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Finite H := Subtype.finite
  haveI := finite_irreducibleCharacter (G := G)
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  classical
  induction hθ using Submodule.span_induction with
  | mem x hx =>
      set θ₀ : ClassFunction ↥H ℂ := x with hθ₀
      have hθ₀mem : θ₀ ∈ ZIrr H := Submodule.subset_span hx
      -- For each irreducible `χ` of `G`, the Fourier coefficient `⟨Ind θ₀, χ⟩` is an integer.
      have hcoeff : ∀ χ : IrreducibleCharacter G,
          ∃ m : ℤ, ClassFunction.inner (induce H θ₀) (χ : ClassFunction G ℂ) = (m : ℂ) := by
        intro χ
        rw [inner_induce_eq_inner_restrict]
        exact inner_mem_ZIrr_int hθ₀mem (restrict_mem_ZIrr H χ.mem_ZIrr)
      choose f hf using hcoeff
      -- The candidate virtual character `Φ = ∑_χ (f χ) • χ`.
      set Φ : ClassFunction G ℂ :=
        ∑ χ : IrreducibleCharacter G, (f χ : ℂ) • (χ : ClassFunction G ℂ) with hΦ
      have hΦmem : Φ ∈ ZIrr G := by
        rw [hΦ]
        refine Submodule.sum_mem _ fun χ _ => ?_
        rw [Int.cast_smul_eq_zsmul ℂ (f χ) (χ : ClassFunction G ℂ)]
        exact Submodule.smul_mem _ _ χ.mem_ZIrr
      -- `Ind θ₀ - Φ` is orthogonal to every irreducible character, hence zero.
      have hortho : ∀ ψ : IrreducibleCharacter G,
          ClassFunction.inner (induce H θ₀ - Φ) (ψ : ClassFunction G ℂ) = 0 := by
        intro ψ
        rw [ClassFunction.inner_sub_left, hf ψ, hΦ, inner_sum_left]
        have hsum : (∑ χ : IrreducibleCharacter G,
            ClassFunction.inner ((f χ : ℂ) • (χ : ClassFunction G ℂ)) (ψ : ClassFunction G ℂ))
            = (f ψ : ℂ) := by
          rw [Finset.sum_eq_single ψ]
          · rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, if_pos rfl,
              mul_one]
          · intro χ _ hχψ
            rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, if_neg hχψ,
              mul_zero]
          · intro hψ; exact absurd (Finset.mem_univ ψ) hψ
        rw [hsum, sub_self]
      have hzero : induce H θ₀ - Φ = 0 := classFunction_eq_zero_of_orthogonal _ hortho
      have : induce H θ₀ = Φ := by rw [← sub_eq_zero]; exact hzero
      rw [this]; exact hΦmem
  | zero => rw [induce_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [induce_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, induce_smul]
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ a ih

end InduceVirtualCharacters

end ClassFunction

/-- **`Ind` is invariant under transporting the source subgroup along an equality** (the cd-grid /
§9↔§6 transport primitive).  For `A = B` (subgroups of a finite group `K`), inducing the
`MulEquiv.subgroupCongr`-pullback of `ψ : ClassFunction ↥B` from `A` equals inducing `ψ` from `B`.
`subst` collapses `subgroupCongr rfl` to the identity (`compHom id ψ = ψ`). -/
theorem induce_compHom_subgroupCongr {K : Type*} [Group K] [Fintype K]
    {A B : Subgroup K} (hAB : A = B)
    [Invertible (Nat.card ↥A : ℂ)] [Invertible (Nat.card ↥B : ℂ)]
    (ψ : ClassFunction ↥B ℂ) :
    ClassFunction.induce A (ClassFunction.compHom (MulEquiv.subgroupCongr hAB).toMonoidHom ψ)
      = ClassFunction.induce B ψ := by
  subst hAB
  congr 1
  exact Subsingleton.elim _ _

end OddOrder.RepresentationTheory
