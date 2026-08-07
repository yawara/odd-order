/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SupportedSpanOrthogonality

/-!
# Peterfalvi Section 3, result (1.3)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 1 "Preliminary Results from Character Theory", p. 5
(book page `references/peterfalvi/pages/peterfalvi-p005.png`).

⚠ The repository module number is the book **result** chapter number **plus two**
(`S03` ↔ results `(1.x)`).

## Main results

* `restrict_eq_on_iff_forall_inner_eq` -- **Peterfalvi (1.3)(a)**: for `A` a union of conjugacy
  classes of `H` and `(ψⱼ)` spanning `CF(H, A)`,
  `μ|_A = (∑ᵢ dᵢχᵢ)|_A ↔ ∀ j, ∑ᵢ (ψⱼ, χᵢ)_H d̄ᵢ = (Ind_H^G ψⱼ, μ)_G`.
* `restrict_eq_on_of_induce_eq_sum` -- **Peterfalvi (1.3)(b)**, first conclusion: `μᵢ|_A = χᵢ|_A`.
* `restrict_eq_zero_on_of_induce_eq_sum_of_inner_eq_zero` -- **Peterfalvi (1.3)(b)**, second
  conclusion: a `μ` orthogonal to every `μᵢ` has `μ|_A = 0`.
* `restrict_eq_on_and_eq_zero_of_induce_eq_sum` -- (1.3)(b) as the book states it, both
  conclusions bundled.

## Relation to the engine

The combinatorial core -- `CF(H, A)^⊥ = CF(H, H − A)`, i.e. *`D` vanishes on `A` iff `D ⊥ ψⱼ`
for every `j`* -- is `RepresentationTheory.eq_zero_on_iff_forall_inner_eq_zero_of_span`, and the
value-identification half of (1.3)(b) is `restrict_apply_eq_on_of_induce_eq_sum`.  What this file
adds is the textbook bookkeeping those two deliberately left "to the consumers": instantiating
the core at `D = Res_H μ − ∑ᵢ dᵢχᵢ`, converting `(ψⱼ, Res_H μ)_H` into `(Ind_H^G ψⱼ, μ)_G` by
Frobenius reciprocity, and supplying the orthogonality conclusion of (1.3)(b), which the engine
file does not state at all.

## Generality

The book takes `(ψⱼ)_{j∈J}` to be a *basis* of `CF(H, A)` and `(χᵢ)_{i∈I}` to be `Irr(H)`.
Neither is needed: the proof of (1.3)(a) uses only that the `ψⱼ` are `A`-supported and span
`CF(H, A)`, and it never uses irreducibility of the `χᵢ`.  Both are stated here at that weaker
hypothesis, so a caller holding a spanning family (rather than a basis) can apply them directly.
Orthonormality of `(μᵢ)` is genuinely used in (1.3)(b) and is kept.
-/

namespace OddOrder.Peterfalvi.S03

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {H : Subgroup G} [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **Peterfalvi (1.3)(a)** (book p. 5).  Let `H ≤ G`, let `A` be a union of conjugacy classes of
`H`, let `(ψⱼ)_{j∈J}` span `CF(H, A)`, and let `(χᵢ)_{i∈I}` be a finite family of class functions
on `H`.  For `μ ∈ CF(G)` and `dᵢ ∈ ℂ`,

`μ|_A = (∑ᵢ dᵢχᵢ)|_A` **iff** for all `j ∈ J`, `∑ᵢ (ψⱼ, χᵢ)_H · d̄ᵢ = (Ind_H^G ψⱼ, μ)_G`.

*Proof* (the book's, verbatim).  `Res_H μ − ∑ᵢ dᵢχᵢ` lies in `CF(H, H − A)` -- equivalently
vanishes on `A` -- exactly when it is orthogonal to every `ψⱼ`, because the orthogonal complement
of `CF(H, A)` in `CF(H)` is `CF(H, H − A)`
(`eq_zero_on_iff_forall_inner_eq_zero_of_span`).  Expanding that orthogonality by
conjugate-linearity in the second argument turns it into
`∑ᵢ (ψⱼ, χᵢ) d̄ᵢ = (ψⱼ, Res_H μ)`, and Frobenius reciprocity
(`inner_induce_eq_inner_restrict`) rewrites the right-hand side as `(Ind_H^G ψⱼ, μ)_G`. -/
theorem restrict_eq_on_iff_forall_inner_eq
    {A : Set ↥H} (hAconj : ∀ (h : ↥H) ⦃a : ↥H⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {J I : Type*} [Fintype I] (Ψ : J → ClassFunction ↥H ℂ)
    (hΨA : ∀ j, Ψ j ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Ψ))
    (χ : I → ClassFunction ↥H ℂ) (μ : ClassFunction G ℂ) (d : I → ℂ) :
    (∀ a ∈ A, ClassFunction.restrict H μ a = (∑ i, d i • χ i) a) ↔
      ∀ j, ∑ i, ClassFunction.inner (Ψ j) (χ i) * star (d i)
        = ClassFunction.inner (ClassFunction.induce H (Ψ j)) μ := by
  classical
  -- The book's difference `Res_H μ − ∑ᵢ dᵢχᵢ`, fed to the (1.3)(a) core.
  set D : ClassFunction ↥H ℂ := ClassFunction.restrict H μ - ∑ i, d i • χ i with hD
  have hcore := eq_zero_on_iff_forall_inner_eq_zero_of_span hAconj Ψ hΨA hspan D
  -- Left-hand sides agree: `D a = 0` is the value match at `a`.
  have hleft : (∀ a ∈ A, D a = 0) ↔
      ∀ a ∈ A, ClassFunction.restrict H μ a = (∑ i, d i • χ i) a := by
    refine forall_congr' fun a => forall_congr' fun _ => ?_
    exact sub_eq_zero (a := ClassFunction.restrict H μ a) (b := (∑ i, d i • χ i) a)
  -- Right-hand sides agree: expand `⟨Ψ j, D⟩` and apply Frobenius reciprocity.
  have hright : ∀ j, ClassFunction.inner (Ψ j) D = 0 ↔
      ∑ i, ClassFunction.inner (Ψ j) (χ i) * star (d i)
        = ClassFunction.inner (ClassFunction.induce H (Ψ j)) μ := by
    intro j
    have hsum : ClassFunction.inner (Ψ j) (∑ i, d i • χ i)
        = ∑ i, ClassFunction.inner (Ψ j) (χ i) * star (d i) := by
      rw [inner_sum_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ClassFunction.inner_smul_right, mul_comm]
    have hfrob : ClassFunction.inner (Ψ j) (ClassFunction.restrict H μ)
        = ClassFunction.inner (ClassFunction.induce H (Ψ j)) μ :=
      (ClassFunction.inner_induce_eq_inner_restrict H (Ψ j) μ).symm
    rw [hD, ClassFunction.inner_sub_right, hsum, hfrob, sub_eq_zero, eq_comm]
  exact hleft.symm.trans (hcore.trans (forall_congr' hright))

open scoped Classical in
/-- **Peterfalvi (1.3)(b)**, first conclusion (book p. 5): under the induction expansions
`Ind_H^G ψⱼ = ∑ᵢ (ψⱼ, χᵢ) μᵢ` with `(μᵢ)` orthonormal, each `μᵢ` agrees with `χᵢ` on `A`.

This is `restrict_apply_eq_on_of_induce_eq_sum` under the (1.3) naming; it is restated here so
that the two conclusions of (1.3)(b) sit next to each other. -/
theorem restrict_eq_on_of_induce_eq_sum
    {A : Set ↥H} (hAconj : ∀ (h : ↥H) ⦃a : ↥H⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {J I : Type*} [Fintype I] (Ψ : J → ClassFunction ↥H ℂ)
    (hΨA : ∀ j, Ψ j ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Ψ))
    (χ : I → ClassFunction ↥H ℂ) (mu : I → ClassFunction G ℂ)
    (hmu_orth : ∀ i k, ClassFunction.inner (mu i) (mu k) = if i = k then 1 else 0)
    (hInd : ∀ j, ClassFunction.induce H (Ψ j)
      = ∑ i, ClassFunction.inner (Ψ j) (χ i) • mu i)
    (i : I) :
    ∀ a ∈ A, ClassFunction.restrict H (mu i) a = χ i a :=
  restrict_apply_eq_on_of_induce_eq_sum hAconj Ψ hΨA hspan χ mu hmu_orth hInd i

open scoped Classical in
/-- **Peterfalvi (1.3)(b)**, second conclusion (book p. 5): *if `μ` is orthogonal to `μᵢ` for all
`i ∈ I`, then `μ|_A = 0`.*

*Proof.*  By Frobenius reciprocity and the expansion hypothesis,
`(ψⱼ, Res_H μ)_H = (Ind_H^G ψⱼ, μ)_G = ∑ᵢ (ψⱼ, χᵢ)·(μᵢ, μ)_G = 0`,
so `Res_H μ` is orthogonal to every `ψⱼ` and the (1.3)(a) core makes it vanish on `A`.

Note that orthonormality of `(μᵢ)` is *not* needed for this half -- only the expansion and the
orthogonality of `μ` to each `μᵢ`. -/
theorem restrict_eq_zero_on_of_induce_eq_sum_of_inner_eq_zero
    {A : Set ↥H} (hAconj : ∀ (h : ↥H) ⦃a : ↥H⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {J I : Type*} [Fintype I] (Ψ : J → ClassFunction ↥H ℂ)
    (hΨA : ∀ j, Ψ j ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Ψ))
    (χ : I → ClassFunction ↥H ℂ) (mu : I → ClassFunction G ℂ)
    (hInd : ∀ j, ClassFunction.induce H (Ψ j)
      = ∑ i, ClassFunction.inner (Ψ j) (χ i) • mu i)
    (μ : ClassFunction G ℂ) (horth : ∀ i, ClassFunction.inner μ (mu i) = 0) :
    ∀ a ∈ A, ClassFunction.restrict H μ a = 0 := by
  classical
  refine (eq_zero_on_iff_forall_inner_eq_zero_of_span hAconj Ψ hΨA hspan
    (ClassFunction.restrict H μ)).mpr fun j => ?_
  -- `⟨ψⱼ, Res_H μ⟩ = ⟨Ind_H^G ψⱼ, μ⟩` and the expansion collapses against `μ`.
  rw [← ClassFunction.inner_induce_eq_inner_restrict H (Ψ j) μ, hInd j, inner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  -- `⟨μᵢ, μ⟩ = conj ⟨μ, μᵢ⟩ = 0`.
  have hflip : ClassFunction.inner (mu i) μ = 0 := by
    rw [RepresentationTheory.inner_conj_symm, horth i, star_zero]
  rw [ClassFunction.inner_smul_left, hflip, mul_zero]

open scoped Classical in
/-- **Peterfalvi (1.3)(b)** as the book states it (p. 5), both conclusions bundled:

> Suppose that there is an orthonormal family `(μᵢ)_{i∈I}` of elements of `CF(G)` such that, for
> all `j ∈ J`, `Ind_H^G ψⱼ = ∑_{i∈I} (ψⱼ, χᵢ) μᵢ`.  Then `μᵢ|_A = χᵢ|_A` for all `i ∈ I`, and,
> if `μ` is orthogonal to `μᵢ` for all `i ∈ I`, `μ|_A = 0`. -/
theorem restrict_eq_on_and_eq_zero_of_induce_eq_sum
    {A : Set ↥H} (hAconj : ∀ (h : ↥H) ⦃a : ↥H⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {J I : Type*} [Fintype I] (Ψ : J → ClassFunction ↥H ℂ)
    (hΨA : ∀ j, Ψ j ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Ψ))
    (χ : I → ClassFunction ↥H ℂ) (mu : I → ClassFunction G ℂ)
    (hmu_orth : ∀ i k, ClassFunction.inner (mu i) (mu k) = if i = k then 1 else 0)
    (hInd : ∀ j, ClassFunction.induce H (Ψ j)
      = ∑ i, ClassFunction.inner (Ψ j) (χ i) • mu i) :
    (∀ i, ∀ a ∈ A, ClassFunction.restrict H (mu i) a = χ i a) ∧
      ∀ μ : ClassFunction G ℂ, (∀ i, ClassFunction.inner μ (mu i) = 0) →
        ∀ a ∈ A, ClassFunction.restrict H μ a = 0 :=
  ⟨fun i => restrict_eq_on_of_induce_eq_sum hAconj Ψ hΨA hspan χ mu hmu_orth hInd i,
    fun μ horth =>
      restrict_eq_zero_on_of_induce_eq_sum_of_inner_eq_zero hAconj Ψ hΨA hspan χ mu hInd μ horth⟩

end OddOrder.Peterfalvi.S03
