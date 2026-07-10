/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Peterfalvi (1.3.a), the restriction–complement equivalence core

For a conjugation-invariant subset `A ⊆ Γ` and a family `Φ` of `A`-supported class functions
spanning the `A`-supported submodule, a class function vanishes on `A` **iff** it is orthogonal
to every `Φ i` (the core of Coq `PFsection1.equiv_restrict_compl` (1.3.a); the `Res μ − Σ dᵢχᵢ`
bookkeeping of the textbook statement is left to the consumers).  This is the engine of the
prime-TI value identity (4.3.c) (`prTIirr_id`, via (1.3.b)) and of the Peterfalvi (13.18)/(13.19)
grid facts.

The nontrivial direction splits `D = D_A + (D − D_A)` along the indicator of `A` (a class
function by conjugation-invariance of `A`), places `D_A` in the span of `Φ`, and forces
`⟨D_A, D_A⟩ = 0`.
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

open scoped Classical in
/-- **Peterfalvi (1.3.a), core equivalence**: for a conjugation-invariant `A` and an
`A`-supported family `Φ` spanning the `A`-supported class functions, `D` vanishes on `A` iff
`D ⊥ Φ i` for every `i`.  (Coq `equiv_restrict_compl` with the `Res`/coefficient bookkeeping
stripped; instantiate `D := Res_H μ − Σ dᵢ·χᵢ` to recover the textbook (1.3.a).) -/
theorem eq_zero_on_iff_forall_inner_eq_zero_of_span
    {A : Set Γ} (hAconj : ∀ (h : Γ) ⦃a : Γ⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {ι : Type*} (Φ : ι → ClassFunction Γ ℂ)
    (hΦA : ∀ i, Φ i ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Φ))
    (D : ClassFunction Γ ℂ) :
    (∀ a ∈ A, D a = 0) ↔ ∀ i, ClassFunction.inner (Φ i) D = 0 := by
  classical
  constructor
  · -- Easy direction: disjoint supports.
    intro hDA i
    refine ClassFunction.inner_eq_zero_of_disjoint_support ?_
    rw [Set.disjoint_left]
    intro x hxΦ hxD
    rw [ClassFunction.mem_support] at hxΦ hxD
    exact hxD (hDA x (ClassFunction.mem_supportedSubmodule.mp (hΦA i) hxΦ))
  · intro hinner
    -- Split `D` along the indicator of `A` (a class function since `A` is conj-invariant).
    set DA : ClassFunction Γ ℂ :=
      ⟨fun g => if g ∈ A then D g else 0, by
        intro g h
        change (if h * g * h⁻¹ ∈ A then D (h * g * h⁻¹) else 0)
          = (if g ∈ A then D g else 0)
        by_cases hg : g ∈ A
        · rw [if_pos hg, if_pos (hAconj h hg)]
          exact D.conj_eq g h
        · rw [if_neg hg, if_neg (fun hc : h * g * h⁻¹ ∈ A => hg (by
            have hback := hAconj h⁻¹ hc
            have hgid : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
            rwa [hgid] at hback))]⟩ with hDA_def
    have hDA_apply : ∀ g : Γ, DA g = if g ∈ A then D g else 0 := fun _ => rfl
    have hDA_mem : DA ∈ ClassFunction.supportedSubmodule A := by
      rw [ClassFunction.mem_supportedSubmodule]
      intro x hx
      rw [ClassFunction.mem_support] at hx
      by_contra hxA
      exact hx (by rw [hDA_apply, if_neg hxA])
    -- `⟨Φ i, D − DA⟩ = 0`: the difference is supported off `A`.
    have hDc : ∀ i, ClassFunction.inner (Φ i) (D - DA) = 0 := by
      intro i
      refine ClassFunction.inner_eq_zero_of_disjoint_support ?_
      rw [Set.disjoint_left]
      intro x hxΦ hxDc
      rw [ClassFunction.mem_support] at hxΦ hxDc
      have hxA : x ∈ A := ClassFunction.mem_supportedSubmodule.mp (hΦA i) hxΦ
      refine hxDc ?_
      show D x - DA x = 0
      rw [hDA_apply, if_pos hxA, sub_self]
    -- Hence `⟨Φ i, DA⟩ = ⟨Φ i, D⟩ = 0` for every `i`.
    have hΦDA : ∀ i, ClassFunction.inner (Φ i) DA = 0 := by
      intro i
      have h1 := hDc i
      rw [ClassFunction.inner_sub_right] at h1
      have h2 := hinner i
      linear_combination h2 - h1
    -- Orthogonality extends over the span, in particular to `DA` itself.
    have hspan_orth : ∀ f ∈ Submodule.span ℂ (Set.range Φ),
        ClassFunction.inner f DA = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact hΦDA i
      | zero =>
          show ClassFunction.inner (0 : ClassFunction Γ ℂ) DA = 0
          rw [show (0 : ClassFunction Γ ℂ) = (0 : ℂ) • (0 : ClassFunction Γ ℂ) by simp,
            ClassFunction.inner_smul_left, zero_mul]
      | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_left, ihx, ihy, add_zero]
      | smul a x _ ih => rw [ClassFunction.inner_smul_left, ih, mul_zero]
    -- `⟨DA, DA⟩ = 0` forces `DA = 0`, so `D` vanishes on `A`.
    have hDA0 : DA = 0 := by
      refine eq_zero_of_inner_self_re_eq_zero ?_
      rw [hspan_orth DA (hspan hDA_mem)]
      simp
    intro a ha
    have h0 : DA a = 0 := by rw [hDA0]; rfl
    rwa [hDA_apply, if_pos ha] at h0

open scoped Classical in
/-- **Peterfalvi (1.3.b), value-identification half**: if `η` is an orthonormal-image family
matching an orthonormal family `χ` against the `A`-supported spanning family `Φ` — i.e.
`⟨Φ j, η i⟩ = ⟨Φ j, χ i⟩` for all `j` (the Coq hypothesis `Ind Φ_j = Σ_i ⟨Φ_j, χ_i⟩·η_i`
after pairing with `η i`, by orthonormality) — then `η i` agrees with `χ i` on `A`.
Stated in the paired form to keep the ambient/quotient bookkeeping with the consumer. -/
theorem apply_eq_on_of_forall_inner_eq
    {A : Set Γ} (hAconj : ∀ (h : Γ) ⦃a : Γ⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {ι : Type*} (Φ : ι → ClassFunction Γ ℂ)
    (hΦA : ∀ i, Φ i ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Φ))
    (f g : ClassFunction Γ ℂ)
    (hmatch : ∀ j, ClassFunction.inner (Φ j) f = ClassFunction.inner (Φ j) g) :
    ∀ a ∈ A, f a = g a := by
  have h := (eq_zero_on_iff_forall_inner_eq_zero_of_span hAconj Φ hΦA hspan (f - g)).mpr
    (fun j => by
      rw [ClassFunction.inner_sub_right]
      linear_combination hmatch j)
  intro a ha
  have h0 := h a ha
  change f a - g a = 0 at h0
  exact sub_eq_zero.mp h0

open scoped Classical in
/-- **Peterfalvi (1.3.b), cross-level value identification**: for `H ≤ G`, a conjugation-invariant
`A ⊆ H` with an `A`-supported spanning family `Φ`, and an orthonormal family `mu` in `CF(G)`
matched to a family `χ` in `CF(H)` by the induction expansions
`Ind Φ_j = Σ_k ⟨Φ_j, χ_k⟩ • mu_k`, each `mu i` restricts to `χ i` on `A`.

Frobenius reciprocity turns the expansion into `⟨Φ_j, Res (mu i)⟩ = ⟨Φ_j, χ i⟩` (orthonormal
collapse of the sum), and the same-group identification `apply_eq_on_of_forall_inner_eq`
finishes.  This is the Coq `equiv_restrict_compl_ortho` shape that extracts the prime-TI value
identity `prTIirr_id` (4.3.c). -/
theorem restrict_apply_eq_on_of_induce_eq_sum
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [Fintype H] [Invertible (Nat.card ↥H : ℂ)]
    {A : Set ↥H} (hAconj : ∀ (h : ↥H) ⦃a : ↥H⦄, a ∈ A → h * a * h⁻¹ ∈ A)
    {ι κ : Type*} [Fintype κ] (Φ : ι → ClassFunction ↥H ℂ)
    (hΦA : ∀ j, Φ j ∈ ClassFunction.supportedSubmodule A)
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ (Set.range Φ))
    (χ : κ → ClassFunction ↥H ℂ) (mu : κ → ClassFunction G ℂ)
    (hmu_orth : ∀ i k, ClassFunction.inner (mu i) (mu k) = if i = k then 1 else 0)
    (hInd : ∀ j, ClassFunction.induce H (Φ j)
      = ∑ k, ClassFunction.inner (Φ j) (χ k) • mu k)
    (i : κ) :
    ∀ a ∈ A, ClassFunction.restrict H (mu i) a = χ i a := by
  classical
  refine apply_eq_on_of_forall_inner_eq hAconj Φ hΦA hspan
    (ClassFunction.restrict H (mu i)) (χ i) ?_
  intro j
  have hrecip : ClassFunction.inner (Φ j) (ClassFunction.restrict H (mu i))
      = ClassFunction.inner (ClassFunction.induce H (Φ j)) (mu i) :=
    (ClassFunction.inner_induce_eq_inner_restrict H (Φ j) (mu i)).symm
  rw [hrecip, hInd j, inner_sum_left]
  rw [Finset.sum_eq_single i]
  · rw [ClassFunction.inner_smul_left, hmu_orth, if_pos rfl, mul_one]
  · intro k _ hki
    rw [ClassFunction.inner_smul_left, hmu_orth, if_neg hki, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

open scoped Classical in
/-- **Fourier expansion over an orthonormal spanning family**: if `Φ` is orthonormal and spans
all class functions, every `f` is `Σ_i ⟨f, Φ i⟩ • Φ i`.  (The `A = univ` instance of the (1.3.a)
core; for `Φ = Irr Γ` this is the classical Fourier expansion, but the family form also serves
the `ω`-grid of a cyclic `W` directly.) -/
theorem eq_sum_inner_smul_of_orthonormal_of_span_top
    {ι : Type*} [Fintype ι] (Φ : ι → ClassFunction Γ ℂ)
    (horth : ∀ i j, ClassFunction.inner (Φ i) (Φ j) = if i = j then 1 else 0)
    (hspan : (⊤ : Submodule ℂ (ClassFunction Γ ℂ)) ≤ Submodule.span ℂ (Set.range Φ))
    (f : ClassFunction Γ ℂ) :
    f = ∑ i, ClassFunction.inner f (Φ i) • Φ i := by
  classical
  have hAconj : ∀ (h : Γ) ⦃a : Γ⦄, a ∈ (Set.univ : Set Γ) → h * a * h⁻¹ ∈ Set.univ :=
    fun _ _ _ => Set.mem_univ _
  have hΦA : ∀ i, Φ i ∈ ClassFunction.supportedSubmodule (Set.univ : Set Γ) := fun i =>
    ClassFunction.mem_supportedSubmodule.mpr fun x _ => Set.mem_univ x
  have hspan' : ClassFunction.supportedSubmodule (Set.univ : Set Γ)
      ≤ Submodule.span ℂ (Set.range Φ) := fun x _ => hspan (Submodule.mem_top)
  set D : ClassFunction Γ ℂ := f - ∑ i, ClassFunction.inner f (Φ i) • Φ i with hD_def
  have hDzero : ∀ a ∈ (Set.univ : Set Γ), D a = 0 := by
    refine (eq_zero_on_iff_forall_inner_eq_zero_of_span hAconj Φ hΦA hspan' D).mpr ?_
    intro j
    rw [hD_def, ClassFunction.inner_sub_right, inner_sum_right]
    have hsum : ∑ i, ClassFunction.inner (Φ j) (ClassFunction.inner f (Φ i) • Φ i)
        = star (ClassFunction.inner f (Φ j)) := by
      rw [Finset.sum_eq_single j]
      · rw [inner_smul_right, horth, if_pos rfl, mul_one]
      · intro i _ hij
        rw [inner_smul_right, horth, if_neg (Ne.symm hij), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum, ← inner_conj_symm, sub_self]
  ext a
  have h0 := hDzero a (Set.mem_univ a)
  change f a - (∑ i, ClassFunction.inner f (Φ i) • Φ i) a = 0 at h0
  exact sub_eq_zero.mp h0

end OddOrder.RepresentationTheory
