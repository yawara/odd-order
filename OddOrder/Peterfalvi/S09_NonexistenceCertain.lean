/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceTheorems
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.GroupTheory.TISubset

/-!
# Peterfalvi §9: Non-existence of a Certain Type of Group of Odd Order

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§9, pp. 38-43.

This section is **purely character-theoretic**.  Building on the Dade isometry
(§4), TI-subsets (§5-§6), and coherence (§7-§8), it proves a non-existence
result for a configuration of Frobenius subgroups — Peterfalvi's packaging of
the Feit-Thompson final contradiction.

The results, with Peterfalvi's numbering:

* **(7.1)-(7.3)** — the auxiliary map `ρ : CF(G) → CF(L,A)`, `χ^ρ(a) = |H(a)|⁻¹ Σ χ(ax)`,
  its relation to the Dade isometry `τ` (`τρ = id` on `CF(L,A)`, `‖χ^ρ‖² ≤ ‖χ‖²`),
  and the integral inequality `|G|⁻¹ Σ_{A^τ} |χ|² ≥ ‖χ^ρ‖²`.
* **(7.4)-(7.5)** — a family `(L_i)_{i∈I}` each satisfying (7.1), with pairwise
  disjoint `A_iᵗ`, and the master inequality on `Σ_{G₀} |χ|²`.
* **(7.6)-(7.8)** — the normal-subgroup case `A = H^#`, with `T = {Ind_H^L θ}`
  coherent; explicit formula for `χ^ρ` and the norm estimates
  `‖ζ^{νρ}‖² ≥ 1 - e/h`, `‖Γ‖² ≤ e - 1`.
* **(7.9)** — for `I = {1,2}` and `G` of **odd order**, two coherent families
  cannot both be orthogonal: `(β₁, ζ₂^{ν₂}) ≠ 0` or `(β₂, ζ₁^{ν₁}) ≠ 0`.
* **(7.10)** — `k ≥ 2` Frobenius subgroups `L_i` (kernel `H_i`, `H_i^#` a TI-subset
  with normalizer `L_i`, pairwise coprime `|H_i|`) force, for some `i`,
  `(|G₀| - 1)/|G| ≥ (e-1)((h-2e-1)/(eh) + 2/(h(h+2)))`.
* **(7.11)** — the **main theorem**: no such configuration has `G₀ = {1}`.

## Scope of this file (statement preparation)

The headline results **(7.10)** and **(7.11)** have purely group-theoretic
*statements* (Frobenius group + TI-subset + cardinalities); in particular they do
**not** reference the Dade isometry, so they are statable independently of the
character-theory layer.  Their *proofs* require (7.1)-(7.9) and hence the
`OddOrder.RepresentationTheory` Dade/coherence machinery (§4-§8), which is why
they are left `sorry` here.  Results (7.1)-(7.9) — the `ℂ`-valued proof apparatus
— are documented but not yet stated, to avoid coupling to the in-progress
coherence numerical layer.

## Relation to BG Appendix C  ⚠️

BG App.C (= Peterfalvi's 1984 paper, as edited by Carlip-Wheeler) proves the
*same* final contradiction by a **different route**: a finite-field
generator-relation argument over `F_{p^q}` with the Frobenius group `H = P ⋊ U`
(additive `P`, norm-1 `U`), culminating in **Theorem C: `p ≤ q`**.  That is a
*different statement* from (7.11) — they are two formulations that both close the
Feit-Thompson proof, **not** literally equivalent theorems.  (The earlier draft of
`notes/peterfalvi/s09_nonexistence_certain.md`, written 2026-05-22 before the
Phase-2b §3-§8 audit, conflated the two and described §9 in terms of the
finite-field `H = PU` / `p ≤ q` content; that content belongs to BG App.C, not
here.)  A Phase-3 bridge lemma relating the two formulations is deferred.

Reference note: `notes/peterfalvi/s09_nonexistence_certain.md` (⚠️ pre-audit draft
conflates §9 with BG App.C; this header is the corrected account).
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/- (7.1)-(7.9): the character-theoretic proof apparatus.

These are the *proof* ingredients of (7.10): the map `ρ`, the family inequality
(7.5), and the coherence/norm estimates (7.6)-(7.9).  Their statements live over
`ℂ`-valued class functions and depend on the Dade isometry / coherence layer
(`OddOrder.RepresentationTheory`, §4-§8).  The §9 headline results (7.10)-(7.11)
below do not reference them — those are pure group-theoretic statements.

This file installs (7.1)-(7.8), all sorry-free:
* (7.1)-(7.3): the hypothesis bundle (`Hypothesis71`), the `ρ` map
  (`chiRho` / `chiRhoCF` / `chiRhoSupp`), (7.2.a) `chiRho_dadeImage_eq`,
  (7.2.b) `chiRho_norm_sq_le`, (7.3) `chiRho_integral_inequality`;
* (7.4)-(7.5): `FamilyHypothesis71` and `family_inequality`;
* (7.6)-(7.7): the normal-subgroup case `A = H^#` (`Hypothesis76`), with
  (7.7.a) `chiRho_explicit_formula` and (7.7.b) `chiRho_norm_sq_double_sum`;
* (7.8): the coherence-based formula (`Hypothesis78`), with (7.8.c.i)
  `chiRho_eq_inner_beta_on_A` and (7.8.c.ii) `chiRho_norm_sq_eq_card_ratio_mul`.

The (7.7.a) and (7.8.c.i) pointwise identities are carried as structural
certificates (`Hypothesis76.chiRho_decomp`, `Hypothesis78.chiRho_eq_inner_beta`):
they encode Peterfalvi's `CF(L,A)`-basis / coherence reductions, whose proofs
need the induced/restricted-character decomposition theory not yet in this file.
The norm-square corollaries (7.7.b)/(7.8.c.ii) are then proved here outright.
(7.9) remains as follow-on. -/

section Section_7_1_to_7_3

/-- **Peterfalvi (7.1) data.** Hypothesis (2.2) together with a chosen Dade map
`τ : CF(L,A) → CF(G)` (Peterfalvi (2.5)/(2.6)) and the `H(-)`-conjugation-invariance
condition that promotes `chiRho` to a class function on `L`. -/
structure Hypothesis71 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) where
  /-- The underlying Peterfalvi (2.2) hypothesis. -/
  hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L
  /-- The Dade map `τ : CF(L,A) → CF(G)`. -/
  τ : OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L
  /-- `τ` satisfies the Peterfalvi (2.5) Dade-map equations for `hyp`. -/
  isDadeMap : OddOrder.Peterfalvi.S04.IsDadeMap hyp τ
  /-- `H(-)` is `L`-conjugation equivariant: `H(l·a·l⁻¹) = l·H(a)·l⁻¹`.  This makes
  the `ρ`-image of a class function on `G` itself a class function on `L`. -/
  hConjInvariant : hyp.HConjInvariant

namespace Hypothesis71

variable {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}

open scoped Classical in
/-- The **ρ map** of Peterfalvi (7.1).  For `a ∈ A`,
`χ^ρ(a) = |H(a)|⁻¹ Σ_{x ∈ H(a)} χ(a·x)`; for `a ∉ A`, `χ^ρ(a) = 0`.

Returned as a raw function `L → ℂ`; promoting it to a class function (i.e. to
`SupportedClassFunctions ℂ A L`) requires `Hypothesis.HConjInvariant`, which is
not yet folded into the `Hypothesis71` structure. -/
noncomputable def chiRho (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ) :
    L → ℂ := fun a =>
  if ha : (a : G) ∈ A then
    (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ)⁻¹ *
      ∑ x : H71.hyp.H ⟨(a : G), ha⟩, χ ((a : G) * (x : G))
  else 0

open scoped Classical in
@[simp] theorem chiRho_of_not_mem
    (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ)
    {a : L} (ha : (a : G) ∉ A) : H71.chiRho χ a = 0 := by
  simp [chiRho, ha]

open scoped Classical in
theorem chiRho_of_mem (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ)
    {a : L} (ha : (a : G) ∈ A) :
    H71.chiRho χ a =
      (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ)⁻¹ *
        ∑ x : H71.hyp.H ⟨(a : G), ha⟩, χ ((a : G) * (x : G)) := by
  simp [chiRho, ha]

open scoped Classical in
/-- **Peterfalvi (7.2.a).** The Dade map `τ` has the `ρ` map as a left inverse on
`CF(L,A)`: for every `α ∈ CF(L,A)` and `a ∈ A`, `α^{τρ}(a) = α(a)`. -/
theorem chiRho_dadeImage_eq (H71 : Hypothesis71 G A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    {a : L} (ha : (a : G) ∈ A) :
    H71.chiRho (H71.τ α) a = (α : ClassFunction L ℂ) a := by
  rw [H71.chiRho_of_mem _ ha]
  -- Each summand equals `α a`, via `IsDadeMap.map_eq_of_mem_hCoset` on `a · x ∈ aH(a)`.
  have hpt : ∀ x : H71.hyp.H ⟨(a : G), ha⟩,
      H71.τ α ((a : G) * (x : G)) = (α : ClassFunction L ℂ) a := by
    intro x
    have hmem : (a : G) * (x : G) ∈ H71.hyp.hCoset ⟨(a : G), ha⟩ := ⟨x, x.2, rfl⟩
    have hmap := H71.isDadeMap.map_eq_of_mem_hCoset α ⟨(a : G), ha⟩ hmem
    rw [hmap]
  simp_rw [hpt]
  have hne : (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := H71.hyp.H ⟨(a : G), ha⟩)).ne'
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **L-conjugation invariance of `chiRho`.** Under `HConjInvariant` (carried by
`Hypothesis71`), the `ρ`-image of any `χ ∈ CF(G)` is `L`-class-function valued. -/
theorem chiRho_conj_invariant (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ)
    (g h : L) : H71.chiRho χ (h * g * h⁻¹) = H71.chiRho χ g := by
  classical
  have hcoe_conj : ((h * g * h⁻¹ : L) : G) = (h : G) * (g : G) * (h : G)⁻¹ := by
    push_cast; group
  by_cases hg : (g : G) ∈ A
  · -- (g : G) ∈ A and hence the conjugate is too
    have hhgh : ((h * g * h⁻¹ : L) : G) ∈ A := by
      rw [hcoe_conj]; exact H71.hyp.L_normalizes_A h hg
    rw [H71.chiRho_of_mem _ hhgh, H71.chiRho_of_mem _ hg]
    -- Normalize the subtype index on the LHS so it matches `HConjInvariant`.
    have hsubeq : (⟨((h * g * h⁻¹ : L) : G), hhgh⟩ : {x : G // x ∈ A}) =
        ⟨(h : G) * (g : G) * (h : G)⁻¹, H71.hyp.L_normalizes_A h hg⟩ :=
      Subtype.ext hcoe_conj
    rw [hsubeq]
    have hConj := H71.hConjInvariant ⟨(g : G), hg⟩ h
    -- `hConj : H ⟨(h:G)*(g:G)*(h:G)⁻¹, _⟩ = MulAut.conj (h:G) • H ⟨(g:G), hg⟩`
    rw [hConj]
    -- Reduce the cardinality coefficient via conjugacy.
    rw [show Nat.card (MulAut.conj (h : G) • H71.hyp.H ⟨(g : G), hg⟩ : Subgroup G) =
        Nat.card (H71.hyp.H ⟨(g : G), hg⟩) from
        (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (h : G))
          (H71.hyp.H ⟨(g : G), hg⟩)).toEquiv).symm]
    -- Reindex the sum via the same `equivSMul`.
    congr 1
    refine (Fintype.sum_equiv
        (Subgroup.equivSMul (MulAut.conj (h : G)) (H71.hyp.H ⟨(g : G), hg⟩)).toEquiv
        (fun y => χ ((g : G) * (y : G)))
        (fun x => χ ((h : G) * (g : G) * (h : G)⁻¹ * (x : G)))
        ?_).symm
    intro y
    -- After beta + unfolding the equiv apply, both sides reduce to a `χ` equation.
    change χ ((g : G) * (y : G)) =
      χ ((h : G) * (g : G) * (h : G)⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹))
    have hcalc : (h : G) * (g : G) * (h : G)⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) =
        (h : G) * ((g : G) * (y : G)) * (h : G)⁻¹ := by group
    rw [hcalc, χ.conj_eq]
  · -- (g : G) ∉ A: both sides are zero
    have hhgh : ((h * g * h⁻¹ : L) : G) ∉ A := by
      intro hin
      apply hg
      have hcoe_inv : ((h⁻¹ : L) : G) = (h : G)⁻¹ := by push_cast; rfl
      have key := H71.hyp.L_normalizes_A h⁻¹ hin
      rw [hcoe_conj] at key
      have hsimp : ((h⁻¹ : L) : G) * ((h : G) * (g : G) * (h : G)⁻¹) *
          ((h⁻¹ : L) : G)⁻¹ = (g : G) := by rw [hcoe_inv]; group
      rwa [hsimp] at key
    rw [H71.chiRho_of_not_mem _ hhgh, H71.chiRho_of_not_mem _ hg]

/-- The `ρ` image of `χ : CF(G)` as a class function on `L`.  This is `chiRho`
endowed with its `L`-conjugation invariance (proved in `chiRho_conj_invariant`). -/
noncomputable def chiRhoCF (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ) :
    ClassFunction L ℂ :=
  ⟨H71.chiRho χ, fun g h => H71.chiRho_conj_invariant χ g h⟩

@[simp] theorem chiRhoCF_apply (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ)
    (a : L) : H71.chiRhoCF χ a = H71.chiRho χ a := rfl

/-- The support of `chiRhoCF χ` is contained in `A ∩ L` (viewed as a subset of `L`):
`chiRho` vanishes off `A` by definition. -/
theorem chiRhoCF_support_subset (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ) :
    (H71.chiRhoCF χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
  intro a ha
  rw [ClassFunction.mem_support, chiRhoCF_apply] at ha
  by_contra hnotA
  exact ha (H71.chiRho_of_not_mem χ hnotA)

/-- The `ρ` map as a `SupportedClassFunctions ℂ A L`: the class-function form of
`chiRho` together with its support in `A` (Peterfalvi `CF(L,A)`). -/
noncomputable def chiRhoSupp (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H71.chiRhoCF χ, H71.chiRhoCF_support_subset χ⟩

@[simp] theorem chiRhoSupp_coe (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ) :
    ((H71.chiRhoSupp χ : OddOrder.Peterfalvi.S04.SupportedClassFunctions
        (G := G) ℂ A L) : ClassFunction L ℂ) = H71.chiRhoCF χ := rfl

/-- **Class-function form of (7.2.a).**  `chiRhoCF (τ α) = α` as class functions on `L`.
The pointwise (7.2.a) gives the equality on `A`; off `A`, both sides vanish since `α`
is supported on `A` and `chiRho` is supported on `A` by definition. -/
theorem chiRhoCF_dadeImage_eq {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G}
    (H71 : Hypothesis71 G A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) :
    H71.chiRhoCF (H71.τ α) = (α : ClassFunction L ℂ) := by
  ext a
  by_cases ha : (a : G) ∈ A
  · simp only [chiRhoCF_apply]
    exact H71.chiRho_dadeImage_eq α ha
  · simp only [chiRhoCF_apply]
    rw [H71.chiRho_of_not_mem _ ha]
    -- (α : CF L) vanishes outside A
    have hsupp_subset :
        (α : ClassFunction L ℂ).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup A L := α.property
    by_contra hne
    exact ha (hsupp_subset (Ne.symm hne))

/-- Helper: the normalized class-function inner product `⟨φ, φ⟩` is the cast of a real
number (sum of `Complex.normSq` over `G`, divided by `|G|`). -/
theorem ClassFunction.inner_self_eq_ofReal {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ =
      (((Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  have hsum : (∑ g : G, φ g * star (φ g)) =
      ((∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun g _ => ?_)
    exact Complex.mul_conj (φ g)
  rw [hsum, invOf_eq_inv]
  push_cast
  ring

/-- Helper: `(⟨φ, φ⟩).re ≥ 0`. -/
theorem ClassFunction.inner_self_re_nonneg {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    0 ≤ (ClassFunction.inner φ φ).re := by
  rw [ClassFunction.inner_self_eq_ofReal, Complex.ofReal_re]
  have hG_pos : 0 < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos
  have hsum_nonneg : 0 ≤ (∑ g : G, Complex.normSq (φ g) : ℝ) :=
    Finset.sum_nonneg (fun g _ => Complex.normSq_nonneg _)
  exact mul_nonneg (inv_nonneg.mpr hG_pos.le) hsum_nonneg

/-- Helper: `⟨φ, φ⟩` is fixed by `star` (since it is the cast of a real number). -/
theorem ClassFunction.star_inner_self {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    star (ClassFunction.inner φ φ) = ClassFunction.inner φ φ := by
  rw [ClassFunction.inner_self_eq_ofReal, Complex.star_def, Complex.conj_ofReal]

/-- Hermitian symmetry of `ClassFunction.inner`: `⟨ψ, φ⟩ = star ⟨φ, ψ⟩`. -/
theorem ClassFunction.inner_symm {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner ψ φ = star (ClassFunction.inner φ ψ) := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
      ClassFunction.inner_eq_inv_card_mul_innerSum]
  rw [star_mul']
  have h_card_real : star (⅟(Nat.card G : ℂ) : ℂ) = ⅟(Nat.card G : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, Complex.star_def, Complex.conj_natCast]
  rw [h_card_real]
  congr 1
  rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [star_mul', star_star, mul_comm]

/-- Helper: `chiRho` matches the (2.7) `adjointAverageFun` on points of `L`. -/
theorem chiRhoCF_eq_adjointAverageFun {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} (H71 : Hypothesis71 G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) :
    (H71.chiRhoCF χ) ⟨a.1, H71.hyp.subset_L a.2⟩ =
      OddOrder.Peterfalvi.S04.adjointAverageFun H71.hyp χ
        ⟨a.1, H71.hyp.subset_L a.2⟩ := by
  simp only [chiRhoCF_apply, OddOrder.Peterfalvi.S04.adjointAverageFun]
  rw [H71.chiRho_of_mem _ a.2, dif_pos a.2]

/-- **Adjoint formula for `chiRho`** (Peterfalvi (2.7) packaged for `chiRhoCF`).
For `α ∈ CF(L, A)` and `χ ∈ CF(G)`, `⟨τ α, χ⟩_G = ⟨α, χ^ρ⟩_L`. -/
theorem chiRho_adjoint {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    (χ : ClassFunction G ℂ) :
    ClassFunction.inner (H71.τ α) χ =
      ClassFunction.inner (α : ClassFunction L ℂ) (H71.chiRhoCF χ) :=
  OddOrder.Peterfalvi.S04.adjoint_formula H71.hyp H71.τ H71.isDadeMap
    H71.hConjInvariant α χ (H71.chiRhoCF χ) (H71.chiRhoCF_eq_adjointAverageFun χ)

/-- **Peterfalvi (7.2.b).** `‖χ^ρ‖² ≤ ‖χ‖²` for any `χ ∈ CF(G)`.

Proof outline (Peterfalvi p.39): let `φ := τ (χ^ρ)` (the projection of `χ` onto `im τ`).
By the adjoint formula (`chiRho_adjoint`) and isometry (`hiso`), `⟨φ, χ⟩_G = ⟨φ, φ⟩_G`,
and by Hermitian symmetry `⟨χ, φ⟩_G = ⟨φ, φ⟩_G` as well.  Hence `χ - φ` is orthogonal
to `φ`, giving `⟨χ, χ⟩ = ⟨φ, φ⟩ + ⟨χ - φ, χ - φ⟩ ≥ ⟨φ, φ⟩`.  The conclusion follows
from `⟨φ, φ⟩ = ⟨χ^ρ, χ^ρ⟩_L` (isometry). -/
theorem chiRho_norm_sq_le {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hiso : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (χ : ClassFunction G ℂ) :
    (ClassFunction.inner (H71.chiRhoCF χ) (H71.chiRhoCF χ)).re ≤
      (ClassFunction.inner χ χ).re := by
  set α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
    H71.chiRhoSupp χ with hα_def
  set φ : ClassFunction G ℂ := H71.τ α with hφ_def
  -- `(α : CF L) = chiRhoCF χ` is `rfl`.
  have hα_coe : (α : ClassFunction L ℂ) = H71.chiRhoCF χ := rfl
  -- Step 1: `⟨φ, χ⟩ = ⟨φ, φ⟩` via adjoint + isometry.
  have h_phi_chi : ClassFunction.inner φ χ = ClassFunction.inner φ φ := by
    have h_adj : ClassFunction.inner φ χ =
        ClassFunction.inner (α : ClassFunction L ℂ) (H71.chiRhoCF χ) :=
      H71.chiRho_adjoint α χ
    have h_isom : ClassFunction.inner φ φ =
        ClassFunction.inner (α : ClassFunction L ℂ) (α : ClassFunction L ℂ) :=
      hiso.inner_eq α α
    rw [h_adj, h_isom, hα_coe]
  -- Step 2: `⟨χ, φ⟩ = ⟨φ, φ⟩` via Hermitian symmetry + inner_self real.
  have h_chi_phi : ClassFunction.inner χ φ = ClassFunction.inner φ φ := by
    rw [ClassFunction.inner_symm, h_phi_chi, ClassFunction.star_inner_self]
  -- Step 3: Orthogonal decomposition `⟨χ, χ⟩ = ⟨φ, φ⟩ + ⟨χ - φ, χ - φ⟩`.
  have h_decomp : ClassFunction.inner χ χ =
      ClassFunction.inner φ φ + ClassFunction.inner (χ - φ) (χ - φ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_chi_phi, h_phi_chi]
    ring
  -- Step 4: Real-part inequality.
  have h_tail_nonneg : 0 ≤ (ClassFunction.inner (χ - φ) (χ - φ)).re :=
    ClassFunction.inner_self_re_nonneg _
  -- Step 5: `⟨φ, φ⟩ = ⟨χ^ρ, χ^ρ⟩_L`.
  have h_phi_eq : ClassFunction.inner φ φ =
      ClassFunction.inner (H71.chiRhoCF χ) (H71.chiRhoCF χ) := by
    rw [hφ_def]
    exact (hiso.inner_eq α α).trans (by rw [hα_coe])
  rw [h_decomp, Complex.add_re, h_phi_eq]
  linarith

open scoped Classical in
/-- **Peterfalvi (7.3).**  The integral inequality:
`|G|⁻¹ Σ_{g ∈ A^τ} |χ(g)|² ≥ ‖χ^ρ‖²`, with equality iff `χ` is constant on each
`aH(a)`.  Consequence of (7.2.b): define `χ₁ ∈ CF(G)` to be `χ` restricted to
`A^τ = dadeSupport` (zero elsewhere); then `χ₁^ρ = χ^ρ` (since `aH(a) ⊆ A^τ`),
and `‖χ₁‖² = |G|⁻¹ Σ_{g ∈ A^τ} |χ(g)|²`, so (7.2.b) applied to `χ₁` gives the result. -/
theorem chiRho_integral_inequality {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hiso : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (χ : ClassFunction G ℂ) :
    (ClassFunction.inner (H71.chiRhoCF χ) (H71.chiRhoCF χ)).re ≤
      (((Nat.card G : ℂ)⁻¹ *
        ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ H71.hyp.dadeSupport),
          ‖(χ : G → ℂ) g‖^2 : ℂ)).re := by
  -- Define `χ₁`: `χ` restricted to `A^τ = dadeSupport` (zero off `A^τ`).
  set χ₁ : ClassFunction G ℂ :=
    ⟨fun g => if g ∈ H71.hyp.dadeSupport then χ g else 0,
      fun g h => by
        change (if h * g * h⁻¹ ∈ H71.hyp.dadeSupport then χ (h * g * h⁻¹) else 0) =
             (if g ∈ H71.hyp.dadeSupport then χ g else 0)
        by_cases hg : g ∈ H71.hyp.dadeSupport
        · have hconj : h * g * h⁻¹ ∈ H71.hyp.dadeSupport :=
            H71.hyp.conj_mem_dadeSupport hg
          rw [if_pos hg, if_pos hconj]
          exact χ.conj_eq g h
        · have hconj : h * g * h⁻¹ ∉ H71.hyp.dadeSupport := fun hin =>
            hg (H71.hyp.mem_dadeSupport_conj_iff.mp hin)
          rw [if_neg hg, if_neg hconj]⟩ with hχ₁_def
  have hχ₁_apply : ∀ g, (χ₁ : G → ℂ) g =
      if g ∈ H71.hyp.dadeSupport then (χ : G → ℂ) g else 0 := fun _ => rfl
  -- Step 1: `chiRhoCF χ₁ = chiRhoCF χ` (the `ρ` sum sees only `aH(a) ⊆ A^τ`).
  have h_chiRhoCF_eq : H71.chiRhoCF χ₁ = H71.chiRhoCF χ := by
    ext a
    by_cases ha : (a : G) ∈ A
    · rw [chiRhoCF_apply, chiRhoCF_apply,
          H71.chiRho_of_mem _ ha, H71.chiRho_of_mem _ ha]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      have hmem : (a : G) * (x : G) ∈ H71.hyp.dadeSupport :=
        H71.hyp.mem_dadeSupport_of_mem_hCoset (a := ⟨(a : G), ha⟩) x.2
      rw [hχ₁_apply, if_pos hmem]
    · rw [chiRhoCF_apply, chiRhoCF_apply,
          H71.chiRho_of_not_mem _ ha, H71.chiRho_of_not_mem _ ha]
  -- Step 2: apply (7.2.b) to `χ₁`.
  have h72b := H71.chiRho_norm_sq_le hiso χ₁
  rw [h_chiRhoCF_eq] at h72b
  -- Step 3: `⟨χ₁, χ₁⟩_G = (Nat.card G)⁻¹ * ↑(Σ_{g ∈ A^τ} ‖χ g‖²)` (cast outside sum).
  have h_inner_χ₁ :
      ClassFunction.inner χ₁ χ₁ =
        (Nat.card G : ℂ)⁻¹ *
          (((∑ g ∈ Finset.univ.filter (fun x : G => x ∈ H71.hyp.dadeSupport),
              ‖(χ : G → ℂ) g‖^2 : ℝ) : ℂ)) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
        invOf_eq_inv]
    congr 1
    rw [Complex.ofReal_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hχ₁_apply]
    by_cases hg : g ∈ H71.hyp.dadeSupport
    · rw [if_pos hg, if_pos hg]
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [if_neg hg, if_neg hg, star_zero, mul_zero]
  rw [h_inner_χ₁] at h72b
  exact h72b

end Hypothesis71

end Section_7_1_to_7_3

section Section_7_3_constants

/-! ### The cardinality identity `|A^τ|·|L| = |A|·|G|`

Specializing (7.3) to the constant `1_G` gives, in the equality case (the constant
function is constant on every coset `aH(a)`), the cardinality identity used in
(7.5).  This is *not* a generic consequence of (2.6.a) but of (2.5): the Dade map
sends the indicator `1_A ∈ CF(L,A)` to `1_{A^τ} ∈ CF(G)` *exactly* (not just up to
an `im τ` correction), and then isometry equates their norms.
-/

namespace Hypothesis71

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G}

/-- The constant class function with value `1`. -/
def constOne (G : Type*) [Group G] : ClassFunction G ℂ :=
  ⟨fun _ => 1, fun _ _ => rfl⟩

@[simp] theorem constOne_apply {G : Type*} [Group G] (g : G) :
    (constOne G : G → ℂ) g = 1 := rfl

open scoped Classical in
/-- `chiRho` applied to the constant `1_G` is the indicator of `A` on `L`. -/
theorem chiRho_constOne (H71 : Hypothesis71 G A L) (a : L) :
    H71.chiRho (constOne G) a = if (a : G) ∈ A then 1 else 0 := by
  by_cases ha : (a : G) ∈ A
  · rw [if_pos ha, H71.chiRho_of_mem _ ha]
    simp only [constOne_apply, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀]
    exact_mod_cast (Nat.card_pos (α := H71.hyp.H ⟨(a : G), ha⟩)).ne'
  · rw [if_neg ha, H71.chiRho_of_not_mem _ ha]

open scoped Classical in
/-- The Dade image of `chiRhoSupp 1_G` is the indicator of `dadeSupport` on `G`.

Uses both `IsDadeMap.map_eq_of_isConj_hCoset` (positive case) and
`map_eq_zero_of_not_mem_dadeSupport` (negative case). -/
theorem tau_chiRhoSupp_constOne
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (g : G) :
    H71.τ (H71.chiRhoSupp (constOne G)) g =
      if g ∈ H71.hyp.dadeSupport then 1 else 0 := by
  by_cases hg : g ∈ H71.hyp.dadeSupport
  · rw [if_pos hg]
    rcases H71.hyp.mem_dadeSupport_iff.mp hg with ⟨a, h, hh, hconj⟩
    rw [H71.isDadeMap.map_eq_of_isConj_hCoset _ g a h hh hconj]
    change H71.chiRhoCF (constOne G) ⟨a.1, H71.hyp.subset_L a.2⟩ = 1
    rw [chiRhoCF_apply, chiRho_constOne, if_pos a.2]
  · rw [if_neg hg]
    exact H71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport _ g hg

omit [Fintype G] in
/-- `Nat.card` of the `L`-subtype `{l : L | (l : G) ∈ A}` equals `Nat.card A`
when `A ⊆ L`. -/
theorem card_supportInSubgroup_eq_card_A (hAL : A ⊆ L) :
    Nat.card (OddOrder.Peterfalvi.S04.supportInSubgroup A L) = Nat.card A := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨(x.1 : G), x.2⟩
      invFun := fun x => ⟨⟨x.1, hAL x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open scoped Classical in
/-- The cardinality identity `|A^τ| · |L| = |A| · |G|`, in `ℝ`.

Proof: by isometry, `⟨τ α, τ α⟩_G = ⟨α, α⟩_L` where `α = chiRhoSupp 1_G`.  Each
inner product is, by the indicator computations, a normalized cardinality, and
the equation becomes the stated identity. -/
theorem card_dadeSupport_div_card_G_eq_card_A_div_card_L [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hiso : OddOrder.Peterfalvi.S04.IsDadeIsometry
      (G := G) (k := ℂ) (L := L) H71.τ) :
    (Nat.card H71.hyp.dadeSupport : ℝ) / (Nat.card G : ℝ) =
      (Nat.card A : ℝ) / (Nat.card L : ℝ) := by
  set α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
    H71.chiRhoSupp (constOne G) with hα_def
  -- Isometry: ⟨τ α, τ α⟩_G = ⟨α, α⟩_L.
  have hiso_eq : ClassFunction.inner (H71.τ α) (H71.τ α) =
      ClassFunction.inner (α : ClassFunction L ℂ) (α : ClassFunction L ℂ) :=
    hiso.inner_eq α α
  -- Compute ⟨τ α, τ α⟩_G = (Nat.card G)⁻¹ · |dadeSupport|.
  have hRHS : ClassFunction.inner (H71.τ α) (H71.τ α) =
      (Nat.card G : ℂ)⁻¹ * (Nat.card H71.hyp.dadeSupport : ℂ) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv,
        ClassFunction.innerSum]
    congr 1
    -- Rewrite each summand as the indicator.
    have hpt : ∀ g : G, H71.τ α g * star (H71.τ α g) =
        if g ∈ H71.hyp.dadeSupport then (1 : ℂ) else 0 := by
      intro g
      rw [H71.tau_chiRhoSupp_constOne g]
      by_cases hg : g ∈ H71.hyp.dadeSupport
      · simp [hg]
      · simp [hg]
    calc ∑ g : G, H71.τ α g * star (H71.τ α g)
        = ∑ g : G, if g ∈ H71.hyp.dadeSupport then (1 : ℂ) else 0 :=
          Finset.sum_congr rfl (fun g _ => hpt g)
      _ = (Nat.card H71.hyp.dadeSupport : ℂ) := by
          rw [Finset.sum_boole]
          rw [show {x ∈ (Finset.univ : Finset G) | x ∈ H71.hyp.dadeSupport} =
              H71.hyp.dadeSupport.toFinset from by
            ext g; simp]
          rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  -- Compute ⟨α, α⟩_L = (Nat.card L)⁻¹ · |A|.
  have hLHS : ClassFunction.inner (α : ClassFunction L ℂ) (α : ClassFunction L ℂ) =
      (Nat.card L : ℂ)⁻¹ * (Nat.card A : ℂ) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv,
        ClassFunction.innerSum]
    congr 1
    have hpt : ∀ l : L, (α : ClassFunction L ℂ) l * star ((α : ClassFunction L ℂ) l) =
        if (l : G) ∈ A then (1 : ℂ) else 0 := by
      intro l
      change H71.chiRhoCF (constOne G) l * star (H71.chiRhoCF (constOne G) l) = _
      rw [chiRhoCF_apply, chiRho_constOne]
      by_cases hl : (l : G) ∈ A
      · simp [hl]
      · simp [hl]
    calc ∑ l : L, (α : ClassFunction L ℂ) l * star ((α : ClassFunction L ℂ) l)
        = ∑ l : L, if (l : G) ∈ A then (1 : ℂ) else 0 :=
          Finset.sum_congr rfl (fun l _ => hpt l)
      _ = (Nat.card A : ℂ) := by
          rw [Finset.sum_boole]
          norm_cast
          rw [← card_supportInSubgroup_eq_card_A H71.hyp.subset_L,
              Nat.card_eq_fintype_card, Fintype.card_subtype]
          rfl
  -- Combine via isometry.
  rw [hLHS, hRHS] at hiso_eq
  -- Take real parts.
  have hG_pos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hL_pos : (0 : ℝ) < Nat.card L := by exact_mod_cast Nat.card_pos (α := L)
  have hreal : (Nat.card G : ℝ)⁻¹ * (Nat.card H71.hyp.dadeSupport : ℝ) =
      (Nat.card L : ℝ)⁻¹ * (Nat.card A : ℝ) := by
    have := congrArg Complex.re hiso_eq
    push_cast at this
    simpa using this
  field_simp at hreal ⊢
  linarith [hreal]

end Hypothesis71

end Section_7_3_constants

section Section_7_4_to_7_5

/-- **Peterfalvi (7.4) Hypothesis.**  A family `(L_i, A_i, τ_i)_{i ∈ Fin k}`,
each satisfying Hypothesis (7.1) (i.e., Hypothesis (2.2) together with a Dade
isometry `τ_i`), with pairwise-disjoint `A_i^{τ_i}`.

The `Fintype (L i)` and `Invertible (Nat.card (L i) : ℂ)` instances are carried
as plain fields so that per-index `chiRhoCF.inner` is well-defined inside the
structure namespace (accessed via `haveI`). -/
structure FamilyHypothesis71 (G : Type*) [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (k : ℕ) where
  /-- The host subgroups `L_i ≤ G`. -/
  L : Fin k → Subgroup G
  /-- The subsets `A_i ⊆ G`. -/
  A : Fin k → Set G
  /-- `Fintype` instance for each `L_i`. -/
  fintypeL : ∀ i, Fintype (L i)
  /-- `|L_i|`-invertibility in `ℂ`. -/
  invertibleL : ∀ i, Invertible (Nat.card (L i) : ℂ)
  /-- Each `(A_i, L_i)` carries a (7.1) hypothesis (with a chosen Dade map `τ_i`). -/
  hyp71 : ∀ i, Hypothesis71 G (A i) (L i)
  /-- Each `τ_i` is a Dade isometry. -/
  isDadeIsometry : ∀ i,
    haveI := fintypeL i
    haveI := invertibleL i
    OddOrder.Peterfalvi.S04.IsDadeIsometry
      (G := G) (k := ℂ) (L := L i) (hyp71 i).τ
  /-- (7.4): the sets `A_i^{τ_i}` are pairwise disjoint. -/
  pairwise_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint ((hyp71 i).hyp.dadeSupport) ((hyp71 j).hyp.dadeSupport)

namespace FamilyHypothesis71

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ}

/-- **(7.4)(d).**  `G_0 = G - ⋃_i A_i^{τ_i}`: elements not lying in any
`A_i^{τ_i} = (F.hyp71 i).hyp.dadeSupport`. -/
def G0 (F : FamilyHypothesis71 G k) : Set G :=
  {g | ∀ i, g ∉ (F.hyp71 i).hyp.dadeSupport}

theorem mem_G0_iff (F : FamilyHypothesis71 G k) {g : G} :
    g ∈ F.G0 ↔ ∀ i, g ∉ (F.hyp71 i).hyp.dadeSupport := Iff.rfl

/-- `‖χ^{ρ_i}‖²_{L_i}` as a real number, using the per-index `Fintype` and
`Invertible` instances carried by `F`. -/
noncomputable def chiRhoNormSq (F : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (i : Fin k) : ℝ :=
  letI := F.fintypeL i
  letI := F.invertibleL i
  (ClassFunction.inner ((F.hyp71 i).chiRhoCF χ) ((F.hyp71 i).chiRhoCF χ)).re

end FamilyHypothesis71

open scoped Classical in
/-- **Peterfalvi (7.5).**  Under Hypothesis (7.4), for any `χ ∈ CF(G)` of norm one
(in particular, any `χ ∈ Irr G`),
`(1/|G|)(Σ_{g ∈ G_0} |χ(g)|² - |G_0|) + Σ_i (‖χ^{ρ_i}‖² - |A_i|/|L_i|) ≤ 0`.

Proof outline (Peterfalvi p.39).  Apply (7.3) for `χ` at each `i` and partition
`Σ_G |χ|² = Σ_{G_0} |χ|² + Σ_i Σ_{A_i^{τ_i}} |χ|²` (disjointness, `G = G_0 ⊔ ⋃ A_i^{τ_i}`)
to bound the LHS by `‖χ‖² = 1`.  Apply (7.3) for `1_G` (equality case: `1_G` is
trivially constant on each coset `aH(a)`) to identify
`|A_i^{τ_i}|/|G| = ‖1_G^{ρ_i}‖²_{L_i} = |A_i|/|L_i|`, hence
`|G_0|/|G| + Σ_i |A_i|/|L_i| = 1`. -/
theorem family_inequality {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1) :
    ((Nat.card G : ℝ)⁻¹ *
        ((∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
            ‖(χ : G → ℂ) g‖^2) - (Nat.card F.G0 : ℝ))) +
      ∑ i : Fin k, (F.chiRhoNormSq χ i -
        (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ)) ≤ 0 := by
  classical
  -- Shorthand notation.
  let AT : Fin k → Set G := fun i => (F.hyp71 i).hyp.dadeSupport
  -- Cast helper: `((|G|⁻¹ * (Σ ‖χ g‖² : ℝ) : ℂ)).re = |G|⁻¹ * Σ ‖χ g‖²` (real).
  have h_cast_sum_re : ∀ (S : Finset G),
      (((Nat.card G : ℂ)⁻¹ *
          ∑ g ∈ S, ‖(χ : G → ℂ) g‖^2 : ℂ)).re =
        (Nat.card G : ℝ)⁻¹ * ∑ g ∈ S, ‖(χ : G → ℂ) g‖^2 := by
    intro S
    -- Rewrite (Nat.card G : ℂ)⁻¹ as a real cast.
    have h_inv_cast : ((Nat.card G : ℂ)⁻¹ : ℂ) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [show (Nat.card G : ℂ) = ((Nat.card G : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_inv]
    rw [h_inv_cast, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- (I) Per-index (7.3) in real form.
  have h_per_index : ∀ i : Fin k,
      F.chiRhoNormSq χ i ≤ (Nat.card G : ℝ)⁻¹ *
        ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ AT i),
          ‖(χ : G → ℂ) g‖^2 := by
    intro i
    letI : Fintype (F.L i) := F.fintypeL i
    letI : Invertible (Nat.card (F.L i) : ℂ) := F.invertibleL i
    have h73 := (F.hyp71 i).chiRho_integral_inequality (F.isDadeIsometry i) χ
    have h_re : (((Nat.card G : ℂ)⁻¹ *
        ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ (F.hyp71 i).hyp.dadeSupport),
            ‖(χ : G → ℂ) g‖^2 : ℂ)).re =
      (Nat.card G : ℝ)⁻¹ *
        ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ AT i),
          ‖(χ : G → ℂ) g‖^2 :=
      h_cast_sum_re _
    exact h_re ▸ h73
  -- (II) Sum the per-index bounds.
  have h_sum_bound :
      (∑ i : Fin k, F.chiRhoNormSq χ i) ≤
        (Nat.card G : ℝ)⁻¹ *
          ∑ i : Fin k,
            ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ AT i),
              ‖(χ : G → ℂ) g‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => h_per_index i)
  -- (III) Pairwise disjointness on Fin k for the filter Finsets.
  have h_disj :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => Finset.univ.filter (fun x : G => x ∈ AT i)) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    intro x _ hxi
    exact (Set.disjoint_left.mp (F.pairwise_disjoint hij)) hxi
  -- (IV) biUnion sum equals the iterated sum.
  have h_biUnion_sum :
      ∑ i : Fin k,
          ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ AT i),
            ‖(χ : G → ℂ) g‖^2 =
        ∑ g ∈ (Finset.univ : Finset (Fin k)).biUnion
            (fun i => Finset.univ.filter (fun x : G => x ∈ AT i)),
          ‖(χ : G → ℂ) g‖^2 :=
    (Finset.sum_biUnion h_disj).symm
  -- (V) biUnion of the per-index filters = `{g | g ∉ G0}` (as Finsets).
  have h_biUnion_eq :
      (Finset.univ : Finset (Fin k)).biUnion
          (fun i => Finset.univ.filter (fun x : G => x ∈ AT i)) =
        Finset.univ.filter (fun g : G => g ∉ F.G0) := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      F.mem_G0_iff, not_forall, not_not]
    refine ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩
  -- (VI) Σ_G ‖χ‖² = |G| (from `⟨χ, χ⟩ = 1`).
  have h_chi_total : ∑ g : G, ‖(χ : G → ℂ) g‖^2 = (Nat.card G : ℝ) := by
    have h_inner_ℂ : (Nat.card G : ℂ) * ClassFunction.inner χ χ =
        ((∑ g : G, ‖(χ : G → ℂ) g‖^2 : ℝ) : ℂ) := by
      rw [ClassFunction.card_mul_inner, ClassFunction.innerSum]
      push_cast
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.ofReal_pow]
    rw [hχ, mul_one] at h_inner_ℂ
    have := congrArg Complex.re h_inner_ℂ
    rw [Complex.ofReal_re] at this
    rw [← this, Complex.natCast_re]
  -- (VII) Σ_{filter ∉ G0} ‖χ‖² = |G| - Σ_{filter ∈ G0} ‖χ‖².
  have h_chi_split :
      ∑ g ∈ Finset.univ.filter (fun g => g ∉ F.G0), ‖(χ : G → ℂ) g‖^2 =
        (Nat.card G : ℝ) -
          ∑ g ∈ Finset.univ.filter (fun g => g ∈ F.G0), ‖(χ : G → ℂ) g‖^2 := by
    have h_split :
        ∑ g ∈ Finset.univ.filter (fun g => g ∈ F.G0), ‖(χ : G → ℂ) g‖^2 +
          ∑ g ∈ Finset.univ.filter (fun g => g ∉ F.G0), ‖(χ : G → ℂ) g‖^2 =
          ∑ g : G, ‖(χ : G → ℂ) g‖^2 :=
      Finset.sum_filter_add_sum_filter_not Finset.univ _ _
    linarith [h_split, h_chi_total]
  -- (VIII) Per-index cardinality identity: `|A_i|/|L_i| = |AT i|/|G|`.
  have h_card_id : ∀ i : Fin k,
      (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) =
        (Nat.card (AT i) : ℝ) / (Nat.card G : ℝ) := by
    intro i
    letI : Fintype (F.L i) := F.fintypeL i
    letI : Invertible (Nat.card (F.L i) : ℂ) := F.invertibleL i
    exact ((F.hyp71 i).card_dadeSupport_div_card_G_eq_card_A_div_card_L
      (F.isDadeIsometry i)).symm
  -- (IX) `|G| = |G0| + Σ_i |AT i|` (G partition cardinality, in ℝ).
  have h_G_partition : (Nat.card G : ℝ) =
      (Nat.card F.G0 : ℝ) + ∑ i : Fin k, (Nat.card (AT i) : ℝ) := by
    -- Convert to Finset cards.
    have h_disjFin :
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
          (fun i => (AT i).toFinset) := by
      intro i _ j _ hij
      rw [Function.onFun, Set.disjoint_toFinset]
      exact F.pairwise_disjoint hij
    have h_biUnion_card :
        ((Finset.univ : Finset (Fin k)).biUnion (fun i => (AT i).toFinset)).card =
          ∑ i : Fin k, (AT i).toFinset.card :=
      Finset.card_biUnion h_disjFin
    -- biUnion (toFinset of AT i) = G0.toFinsetᶜ.
    have h_biUnion_set :
        (Finset.univ : Finset (Fin k)).biUnion (fun i => (AT i).toFinset) =
          F.G0.toFinsetᶜ := by
      ext g
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_compl,
        Set.mem_toFinset, F.mem_G0_iff, not_forall, not_not]
      refine ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩
    have hG0_le : F.G0.toFinset.card ≤ Fintype.card G := by
      rw [← Finset.card_univ (α := G)]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hG0_card_eq : (F.G0.toFinset.card : ℝ) = Nat.card F.G0 := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    have h_AT_card_eq : ∀ i : Fin k,
        ((AT i).toFinset.card : ℝ) = Nat.card (AT i) := by
      intro i; rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    -- Compute Σ Nat.card (AT i) = |G| - |G0| (cast to ℝ).
    have h_compl_card :
        (F.G0.toFinsetᶜ.card : ℝ) = (Nat.card G : ℝ) - (Nat.card F.G0 : ℝ) := by
      rw [Finset.card_compl]
      push_cast [Nat.cast_sub hG0_le]
      rw [show (Fintype.card G : ℝ) = Nat.card G from by
        rw [Nat.card_eq_fintype_card]]
      linarith [hG0_card_eq]
    have h_AT_sum_card :
        ∑ i : Fin k, ((AT i).toFinset.card : ℝ) =
          ∑ i : Fin k, (Nat.card (AT i) : ℝ) :=
      Finset.sum_congr rfl (fun i _ => h_AT_card_eq i)
    -- Putting it together.
    have h_biUnion_card_real :
        (((Finset.univ : Finset (Fin k)).biUnion
              (fun i => (AT i).toFinset)).card : ℝ) =
          ∑ i : Fin k, (Nat.card (AT i) : ℝ) := by
      rw [h_biUnion_card]; push_cast; exact h_AT_sum_card
    rw [h_biUnion_set] at h_biUnion_card_real
    linarith [h_compl_card, h_biUnion_card_real]
  -- (X) `|G0|/|G| + Σ_i |A_i|/|L_i| = 1`.
  have hG_pos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have h_balance :
      (Nat.card F.G0 : ℝ) / (Nat.card G : ℝ) +
        ∑ i : Fin k, (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) = 1 := by
    have h_eq : ∑ i : Fin k, (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) =
        ∑ i : Fin k, (Nat.card (AT i) : ℝ) / (Nat.card G : ℝ) :=
      Finset.sum_congr rfl (fun i _ => h_card_id i)
    rw [h_eq, ← Finset.sum_div, ← add_div, ← h_G_partition, div_self hG_pos.ne']
  -- (XI) Main bound: Σ_i chiRhoNormSq χ i ≤ 1 - (1/|G|) Σ_{G0} ‖χ‖².
  have h_main :
      (∑ i : Fin k, F.chiRhoNormSq χ i) +
        (Nat.card G : ℝ)⁻¹ *
          (∑ g ∈ Finset.univ.filter (fun g => g ∈ F.G0), ‖(χ : G → ℂ) g‖^2) ≤ 1 := by
    have h1 := h_sum_bound
    rw [h_biUnion_sum, h_biUnion_eq, h_chi_split] at h1
    -- h1 : Σ chiRhoNormSq ≤ |G|⁻¹ * (|G| - Σ_{G0} ‖χ‖²) = 1 - |G|⁻¹ * Σ_{G0} ‖χ‖²
    have h2 : (Nat.card G : ℝ)⁻¹ *
        ((Nat.card G : ℝ) -
          ∑ g ∈ Finset.univ.filter (fun g => g ∈ F.G0), ‖(χ : G → ℂ) g‖^2) =
        1 - (Nat.card G : ℝ)⁻¹ *
          ∑ g ∈ Finset.univ.filter (fun g => g ∈ F.G0), ‖(χ : G → ℂ) g‖^2 := by
      field_simp
    linarith [h1, h2]
  -- (XII) Rearrange to the (7.5) form.
  have h_sum_diff_expand :
      ∑ i : Fin k, (F.chiRhoNormSq χ i -
          (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ)) =
        (∑ i : Fin k, F.chiRhoNormSq χ i) -
          ∑ i : Fin k, (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) :=
    Finset.sum_sub_distrib _ _
  rw [h_sum_diff_expand]
  -- Use `h_balance` to express `Σ |A_i|/|L_i| = 1 - |G0|/|G|`.
  have h_sumA_eq : ∑ i : Fin k, (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) =
      1 - (Nat.card F.G0 : ℝ) / (Nat.card G : ℝ) := by linarith [h_balance]
  rw [h_sumA_eq]
  -- Cancel `(1/|G|) * |G0|` against `|G0|/|G|`.
  have hGne : (Nat.card G : ℝ) ≠ 0 := hG_pos.ne'
  have h_cancel : (Nat.card G : ℝ)⁻¹ * (Nat.card F.G0 : ℝ) =
      (Nat.card F.G0 : ℝ) / (Nat.card G : ℝ) := by
    field_simp
  linarith [h_main, h_cancel]

end Section_7_4_to_7_5

section Section_7_6_to_7_7

/-! ### (7.6)-(7.7): normal-subgroup case `A = H^#`

Specializes Hypothesis (7.1) to the situation where `A = H \ {1}` for a normal
subgroup `H ⊴ L`, with the family `T = {ζ_0, ..., ζ_n}` of induced characters
`Ind_H^L θ`.  The headline outputs are:

* `Hypothesis76` — the (7.6) data bundle, carrying `H ⊴ L`, `A = H^#`, the
  family `(ζ_i, d_i)` of induced characters and degree ratios, the support
  proofs that `ψ_i = ζ_i - d_i ζ_0 ∈ CF(L,A)`, and the **(7.7.a) certificate**
  expressing `χ^ρ` linearly through `(ζ_i)_{i≥1}` with coefficients
  `c̄_i / ‖ζ_i‖²` (where `c_i = (ψ_i^τ, χ)`).

* `Hypothesis76.chiRho_explicit_formula` — Peterfalvi (7.7.a): for `x ∈ A`,
  `χ^ρ(x) = Σ_{i≥1} c̄_i / ‖ζ_i‖² · ζ_i(x)`.

* `Hypothesis76.chiRho_norm_sq_double_sum` — Peterfalvi (7.7.b): the
  double-sum form
  `‖χ^ρ‖² = Σ_{i,j≥1} c̄_i c_j / ‖ζ_i‖² ‖ζ_j‖² · ((ζ_i, ζ_j) - ζ_i(1)·conj(ζ_j(1))/|L|)`,
  obtained by inner-product expansion of (7.7.a) using `ζ_i` supported on `H`.

The (7.7.a) statement is carried as a structural certificate (`chiRho_decomp`)
rather than proved here: it encodes Peterfalvi's basis argument
("ψ_i span CF(L,A)") which depends on the induced/restricted character
decomposition theory not yet formalized in this file.  Once that decomposition
is available the field can be discharged by a constructor.  (7.7.b) is then
proved here as a direct corollary by inner-product expansion. -/

/-- **Peterfalvi (7.6) Hypothesis.**

Carries (in addition to Hypothesis (7.1) + the Dade-isometry property):
* a normal subgroup `H ⊴ L` (with `H ≤ L` and `L`-conjugation closure);
* the assumption `A = H \ {1}`;
* the family `(ζ_i)_{i ≤ n}` of distinct induced characters `Ind_H^L θ` and
  the degree ratios `d_i` (so `ζ_i(1) = d_i · ζ_0(1)`);
* the support fact that `ζ_i` vanishes outside `H` (induced characters from a
  normal subgroup are supported on `H`);
* the (7.7.a) decomposition certificate
  (`chiRho_decomp` — Peterfalvi's basis argument applied to `CF(L,A)`).

Note: `ζ_i` are stored as raw class functions on `L` (without identifying them
with specific induced characters); the support and degree-ratio fields are the
properties needed to derive (7.7.a)-(7.7.b). -/
structure Hypothesis76 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The underlying Hypothesis (7.1) with chosen Dade map `τ`. -/
  hyp71 : Hypothesis71 G A L
  /-- `τ` is a Dade isometry. -/
  isDadeIsometry : OddOrder.Peterfalvi.S04.IsDadeIsometry
    (G := G) (k := ℂ) (L := L) hyp71.τ
  /-- The normal subgroup `H` of `L`. -/
  H : Subgroup G
  /-- `H ≤ L`. -/
  H_le_L : H ≤ L
  /-- `H ⊴ L`: `L` normalizes `H` (so `H.subgroupOf L` is normal in `L`). -/
  H_normal_in_L : ∀ (l : L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H
  /-- `A = H \ {1}` (the "sharp"). -/
  A_eq_H_sharp : A = (H : Set G) \ {1}
  /-- Cardinality of the family `T = {ζ_0, ..., ζ_n}` minus one. -/
  n : ℕ
  /-- The family `T = {ζ_0, ..., ζ_n}` of induced characters (distinct). -/
  zeta : Fin (n + 1) → ClassFunction L ℂ
  /-- Degree ratios `d_i = ζ_i(1) / ζ_0(1)`. -/
  d : Fin (n + 1) → ℂ
  /-- `ζ_i` vanishes outside `H` (a normal subgroup): `Ind_H^L θ` is supported
  on `H` since `H = ⋃_g g H g⁻¹`. -/
  zeta_eq_zero_of_not_mem_H : ∀ (i : Fin (n + 1)) (x : L),
    (x : G) ∉ H → zeta i x = 0
  /-- The degree-ratio relation `ζ_i(1) = d_i · ζ_0(1)`. -/
  zeta_one_eq_d_mul : ∀ i : Fin (n + 1), zeta i (1 : L) = d i * zeta 0 (1 : L)
  /-- `ψ_i = ζ_i - d_i ζ_0` is supported on `A` (= `H \ {1}`).  Follows from
  `zeta_eq_zero_of_not_mem_H` + `zeta_one_eq_d_mul` + `A_eq_H_sharp`; carried
  as a field so the (7.7.a) certificate can name the `SupportedClassFunctions`
  value inline. -/
  psi_support : ∀ i : Fin (n + 1),
    (zeta i - d i • zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  /-- **Peterfalvi (7.7.a) certificate.**  For every `χ ∈ CF(G)` and `x ∈ A`,
  `χ^ρ(x) = Σ_{i≥1} c̄_i / ‖ζ_i‖² · ζ_i(x)`, where
  `c_i = (ψ_i^τ, χ)_G` and `ψ_i = ζ_i - d_i ζ_0`.

  Encodes Peterfalvi's CF(L,A)-basis argument (see proof of (7.7.a), p.39):
  the ψ_i (for i ≥ 1) span CF(L,A) modulo `ψ_0 = 0`, allowing the
  inner-product equations
  `c_j = (ψ_j, χ^ρ)` to determine `χ^ρ` on `A` linearly through the `ζ_i`. -/
  chiRho_decomp : ∀ (χ : ClassFunction G ℂ) (x : L), (x : G) ∈ A →
    hyp71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner
          (hyp71.τ ⟨zeta i - d i • zeta 0, psi_support i⟩) χ) /
          ClassFunction.inner (zeta i) (zeta i)) * zeta i x

namespace Hypothesis76

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `ψ_i = ζ_i - d_i · ζ_0` as a member of `CF(L,A)`. -/
noncomputable def psiSupp (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H76.zeta i - H76.d i • H76.zeta 0, H76.psi_support i⟩

@[simp] theorem psiSupp_coe (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) :
    ((H76.psiSupp i : OddOrder.Peterfalvi.S04.SupportedClassFunctions
        (G := G) ℂ A L) : ClassFunction L ℂ) =
      H76.zeta i - H76.d i • H76.zeta 0 := rfl

/-- Peterfalvi's coefficient `c_i = (ψ_i^τ, χ)_G` for `1 ≤ i ≤ n`.  Also defined
for `i = 0`, where it equals zero (since `ψ_0 = ζ_0 - d_0 ζ_0 = 0` after the
degree-ratio identity, but we do not enforce `d_0 = 1` here). -/
noncomputable def cCoeff (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (i : Fin (H76.n + 1)) : ℂ :=
  ClassFunction.inner (H76.hyp71.τ (H76.psiSupp i)) χ

/-- The squared norm `‖ζ_i‖² = (ζ_i, ζ_i)_L` as a complex number. -/
noncomputable def zetaNormSq (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) : ℂ :=
  ClassFunction.inner (H76.zeta i) (H76.zeta i)

/-- **Peterfalvi (7.7.a).**  For `χ ∈ CF(G)` and `x ∈ A`,
`χ^ρ(x) = Σ_{i ≥ 1} c̄_i / ‖ζ_i‖² · ζ_i(x)`. -/
theorem chiRho_explicit_formula (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H76.hyp71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x :=
  H76.chiRho_decomp χ x hx

/-- The class function `S_χ = Σ_{i ≥ 1} c̄_i / ‖ζ_i‖² · ζ_i ∈ CF(L)`.  By
(7.7.a), `S_χ` agrees with `χ^ρ` on `A`.  Off `H`, `S_χ` vanishes (each `ζ_i`
does), and on `H \ A = {1}`, `S_χ(1) = Σ_{i≥1} c̄_i d_i ζ_0(1) / ‖ζ_i‖²` is in
general nonzero.  Used to package (7.7.b) via inner-product expansion. -/
noncomputable def chiRhoLinearCombo (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) : ClassFunction L ℂ :=
  ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
    (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i

omit [Fintype G] [Fintype L] [Invertible (Nat.card L : ℂ)]
  [Invertible (Nat.card G : ℂ)] in
/-- Pointwise evaluation of a finite sum of class functions.  Provable by
straightforward induction; collected here as a local helper. -/
private theorem classFunction_finsum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ClassFunction L ℂ) (x : L) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
          ClassFunction.add_apply, ih]

@[simp] theorem chiRhoLinearCombo_apply (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (x : L) :
    H76.chiRhoLinearCombo χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x := by
  classical
  unfold chiRhoLinearCombo
  rw [classFunction_finsum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ClassFunction.smul_apply]

/-- `S_χ` vanishes outside `H` (as a subset of `L`). -/
theorem chiRhoLinearCombo_eq_zero_of_not_mem_H (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∉ H76.H) :
    H76.chiRhoLinearCombo χ x = 0 := by
  classical
  rw [chiRhoLinearCombo_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

/-- `1 ∉ A` (since `A = H \ {1}`). -/
theorem one_not_mem_A (H76 : Hypothesis76 G A L) : (1 : G) ∉ A := by
  rw [H76.A_eq_H_sharp]
  rintro ⟨_, h⟩
  exact h rfl

/-- For `x ∈ L` with `(x : G) ∈ H` and `(x : G) ≠ 1`, we have `(x : G) ∈ A`. -/
theorem mem_A_of_mem_H_and_ne_one (H76 : Hypothesis76 G A L) {x : L}
    (hxH : (x : G) ∈ H76.H) (hx1 : (x : G) ≠ 1) : (x : G) ∈ A := by
  rw [H76.A_eq_H_sharp]
  exact ⟨hxH, hx1⟩

/-- The (7.7.a) substitution: `χ^ρ(x) = S_χ(x)` for `x ∈ A`. -/
theorem chiRho_eq_chiRhoLinearCombo_of_mem_A (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H76.hyp71.chiRho χ x = H76.chiRhoLinearCombo χ x := by
  rw [chiRhoLinearCombo_apply]
  exact H76.chiRho_explicit_formula χ hx

/-- `χ^ρ` vanishes outside `H` (since `A ⊆ H`). -/
theorem chiRho_eq_zero_of_not_mem_H (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∉ H76.H) :
    H76.hyp71.chiRho χ x = 0 := by
  have hxA : (x : G) ∉ A := by
    intro h
    rw [H76.A_eq_H_sharp] at h
    exact hx h.1
  exact H76.hyp71.chiRho_of_not_mem χ hxA

open scoped Classical in
/-- **Pointwise key lemma** for (7.7.b): the difference `χ^ρ - S_χ` is
supported at `(1 : L)`, where its value is `-S_χ(1)`. -/
theorem chiRho_sub_chiRhoLinearCombo_apply (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (x : L) :
    H76.hyp71.chiRho χ x - H76.chiRhoLinearCombo χ x =
      if x = 1 then -H76.chiRhoLinearCombo χ 1 else 0 := by
  by_cases hx1 : x = 1
  · subst hx1
    have h_chiRho_one : H76.hyp71.chiRho χ 1 = 0 :=
      H76.hyp71.chiRho_of_not_mem χ (by
        rw [show ((1 : L) : G) = (1 : G) from rfl]
        exact H76.one_not_mem_A)
    rw [h_chiRho_one, if_pos rfl, zero_sub]
  · rw [if_neg hx1]
    by_cases hxH : (x : G) ∈ H76.H
    · -- (x : G) ∈ H and x ≠ 1, so we need (x : G) ≠ 1
      have hx_coe_ne_one : (x : G) ≠ 1 := by
        intro h
        apply hx1
        ext
        rw [h]
        rfl
      have hxA : (x : G) ∈ A := H76.mem_A_of_mem_H_and_ne_one hxH hx_coe_ne_one
      rw [H76.chiRho_eq_chiRhoLinearCombo_of_mem_A χ hxA, sub_self]
    · -- (x : G) ∉ H: both terms zero
      rw [H76.chiRho_eq_zero_of_not_mem_H χ hxH,
          H76.chiRhoLinearCombo_eq_zero_of_not_mem_H χ hxH, sub_self]

/-- The inner sum `Σ_{x ∈ L} χ^ρ(x) · conj(χ^ρ(x))` equals
`Σ_{x} S_χ(x) · conj(S_χ(x)) - S_χ(1) · conj(S_χ(1))`, since they differ only
at `x = 1`. -/
theorem innerSum_chiRho_eq (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ) :
    ClassFunction.innerSum (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      ClassFunction.innerSum (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) -
        H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1) := by
  classical
  -- Both sides are Σ_{x ∈ L} f(x); compare pointwise.
  have hpt : ∀ x : L,
      (H76.hyp71.chiRhoCF χ) x * star ((H76.hyp71.chiRhoCF χ) x) =
        H76.chiRhoLinearCombo χ x * star (H76.chiRhoLinearCombo χ x) -
          (if x = 1 then
            H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1)
           else 0) := by
    intro x
    -- chiRhoCF x = chiRho x; chiRhoCF_apply lets us rewrite the LHS.
    rw [Hypothesis71.chiRhoCF_apply]
    by_cases hx1 : x = 1
    · subst hx1
      have h_chi : H76.hyp71.chiRho χ 1 = 0 :=
        H76.hyp71.chiRho_of_not_mem χ (by
          rw [show ((1 : L) : G) = (1 : G) from rfl]
          exact H76.one_not_mem_A)
      rw [h_chi, star_zero, mul_zero, if_pos rfl, sub_self]
    · rw [if_neg hx1]
      by_cases hxH : (x : G) ∈ H76.H
      · have hx_coe_ne_one : (x : G) ≠ 1 := by
          intro h
          apply hx1
          ext
          rw [h]
          rfl
        have hxA : (x : G) ∈ A := H76.mem_A_of_mem_H_and_ne_one hxH hx_coe_ne_one
        rw [H76.chiRho_eq_chiRhoLinearCombo_of_mem_A χ hxA, sub_zero]
      · rw [H76.chiRho_eq_zero_of_not_mem_H χ hxH,
            H76.chiRhoLinearCombo_eq_zero_of_not_mem_H χ hxH,
            star_zero, mul_zero, sub_zero]
  -- Apply hpt and sum
  unfold ClassFunction.innerSum
  rw [show (∑ g : L, (H76.hyp71.chiRhoCF χ) g * star ((H76.hyp71.chiRhoCF χ) g)) =
      ∑ g : L, (H76.chiRhoLinearCombo χ g * star (H76.chiRhoLinearCombo χ g) -
        (if g = 1 then
          H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1)
         else 0)) from
    Finset.sum_congr rfl (fun g _ => hpt g)]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ (1 : L) (fun _ =>
    H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1))]
  rw [if_pos (Finset.mem_univ _)]

/-- **Inner-product of `S_χ` with itself** as a double sum over `i, j ≥ 1`:
`(S_χ, S_χ) = Σ_{i, j ≥ 1} (c̄_i c_j / (‖ζ_i‖² ‖ζ_j‖²)) · (ζ_i, ζ_j)`.

(`star_div` cancels the conjugate in the smul-right, using that `‖ζ_i‖²` is
fixed by `star` — true here because `inner_self_eq_ofReal`.) -/
theorem inner_chiRhoLinearCombo_self
    (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ) :
    ClassFunction.inner (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j) := by
  classical
  unfold chiRhoLinearCombo
  -- Expand inner of two sums as a double sum, via `inner_sum_left` then
  -- `inner_sum_right` on each summand.
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
  -- Goal: (star c_i / ‖ζ_i‖²) * (star (star c_j / ‖ζ_j‖²) * (ζ_i, ζ_j))
  --       = (star c_i * c_j / (‖ζ_i‖² * ‖ζ_j‖²)) * (ζ_i, ζ_j)
  rw [show star ((star (H76.cCoeff χ j) / H76.zetaNormSq j) : ℂ) =
        H76.cCoeff χ j / star (H76.zetaNormSq j) from by
    rw [star_div₀, star_star]]
  -- Now reduce: ‖ζ_j‖² is fixed by star (since inner_self is real).
  have h_star_norm : star (H76.zetaNormSq j) = H76.zetaNormSq j :=
    Hypothesis71.ClassFunction.star_inner_self _
  rw [h_star_norm]
  ring

/-- The value `S_χ(1) · conj(S_χ(1))` as a double sum.  Uses
`ζ_i(1) = d_i ζ_0(1)` and `star (‖ζ_i‖²) = ‖ζ_i‖²`. -/
theorem chiRhoLinearCombo_one_mul_star (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) :
    H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1)) := by
  classical
  rw [chiRhoLinearCombo_apply]
  rw [star_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  -- LHS term: (star c_i / ‖ζ_i‖²) * ζ_i(1) * star ((star c_j / ‖ζ_j‖²) * ζ_j(1))
  rw [show star (((star (H76.cCoeff χ j) / H76.zetaNormSq j) * H76.zeta j 1) : ℂ) =
        (H76.cCoeff χ j / star (H76.zetaNormSq j)) * star (H76.zeta j 1) from by
    rw [star_mul', star_div₀, star_star]]
  have h_star_norm : star (H76.zetaNormSq j) = H76.zetaNormSq j :=
    Hypothesis71.ClassFunction.star_inner_self _
  rw [h_star_norm]
  ring

/-- **Peterfalvi (7.7.b).**  `‖χ^ρ‖²` has the double-sum form:
`‖χ^ρ‖² = Σ_{i,j ≥ 1} c̄_i c_j / ‖ζ_i‖² ‖ζ_j‖² · ((ζ_i, ζ_j) - ζ_i(1) · conj(ζ_j(1)) / |L|)`.

Proof: by (7.7.a), `χ^ρ` agrees with the linear combination `S_χ` on `A` and
vanishes off `A`; `S_χ` also vanishes off `H` (since each `ζ_i` does).  Thus
`χ^ρ - S_χ` is supported at `x = 1` only, where its value is `-S_χ(1)`.
Subtracting `S_χ(1) · conj(S_χ(1))` from `Σ_L S_χ(x) · conj(S_χ(x))` yields
`Σ_L χ^ρ(x) · conj(χ^ρ(x))`, and dividing by `|L|` and rearranging gives
the displayed double-sum. -/
theorem chiRho_norm_sq_double_sum (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) :
    ClassFunction.inner (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
          (ClassFunction.inner (H76.zeta i) (H76.zeta j) -
            H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) := by
  classical
  -- Step 1: inner χ^ρ χ^ρ = (1/|L|) innerSum χ^ρ χ^ρ.
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv]
  -- Step 2: apply innerSum_chiRho_eq.
  rw [H76.innerSum_chiRho_eq χ]
  -- Step 3: rewrite innerSum S S = |L| · inner S S, then expand inner S S.
  rw [show ClassFunction.innerSum (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) =
      (Nat.card L : ℂ) *
        ClassFunction.inner (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) from
    (ClassFunction.card_mul_inner _ _).symm]
  rw [H76.inner_chiRhoLinearCombo_self χ, H76.chiRhoLinearCombo_one_mul_star χ]
  -- Step 4: distribute (1/|L|) over the difference and unify the two double sums.
  rw [mul_sub]
  have hL_ne : (Nat.card L : ℂ) ≠ 0 := Invertible.ne_zero _
  rw [show (Nat.card L : ℂ)⁻¹ *
      ((Nat.card L : ℂ) *
        ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
            (star (H76.cCoeff χ i) * H76.cCoeff χ j /
              (H76.zetaNormSq i * H76.zetaNormSq j)) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j)) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
          ClassFunction.inner (H76.zeta i) (H76.zeta j) from by
    rw [← mul_assoc, inv_mul_cancel₀ hL_ne, one_mul]]
  rw [show (Nat.card L : ℂ)⁻¹ *
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1)) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring]
  -- Combine into one sum with the inner difference.
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Hypothesis76

end Section_7_6_to_7_7

section Section_7_8

/-! ### (7.8): the coherence-based formula for `χ^ρ`

Bundles Hypothesis (7.6) with the §7 coherence input:

* The family `T = {ζ_0, ..., ζ_n}` contains the **induced principal character**
  `Ind 1_H = Ind_H^L 1_H` at some index `ind1H`.
* The remaining set `S = T \ {Ind 1_H}` is **coherent**, with isometric extension
  `ν : ℤ[S] → ℤ[Irr G]` (represented as an integral linear map on the ambient
  `ClassFunction L ℂ` space).
* There is a **distinguished** `ζ ∈ S` with `ζ(1) = (Ind 1_H)(1)` (= `e = [L:H]`);
  equivalently `(Ind 1_H − ζ)(1) = 0`, so `Ind 1_H − ζ ∈ CF(L,A)`.
* `β := τ (Ind 1_H − ζ) ∈ CF(G)` (Dade image of the supported difference).

The headline output (Peterfalvi (7.8.c), p. 40) is:

* (i)  For χ ∈ Irr(G) with `χ ⊥ S^ν`, `χ^ρ(x) = star (β, χ)_G` for every `x ∈ A`.
* (ii) `‖χ^ρ‖² = (|A|/|L|) · (β, χ)_G · star (β, χ)_G`.

(i) — `chiRho_eq_inner_beta_on_A` — is carried as the structural certificate
`chiRho_eq_inner_beta` inside `Hypothesis78` (the coherence-based derivation
from (7.7.a) is the subject of Peterfalvi (7.8.c) and is not yet formalized).
(ii) — `chiRho_norm_sq_eq_card_ratio_mul` — is then a direct corollary of (i):
the inner product is `(1/|L|) Σ_{l : L} χ^ρ(l) · star (χ^ρ(l))`; off `A` the
summands vanish, on `A` each equals `star (β,χ) · (β,χ)`, and the number of
`l ∈ L` with `(l : G) ∈ A` equals `|A|` (since `A ⊆ L`). -/

/-- **Peterfalvi (7.8) Hypothesis.**  Hypothesis (7.6) together with the
coherence input for `S = T \ {Ind 1_H}` and a distinguished `ζ ∈ S` of degree
`e = [L:H] = (Ind 1_H)(1)`.

The (7.8.c) conclusion (the pointwise identity on `A`) is carried as the
structural certificate `chiRho_eq_inner_beta`. -/
structure Hypothesis78 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The underlying Hypothesis (7.6). -/
  hyp76 : Hypothesis76 G A L
  /-- Index of the induced principal character `Ind 1_H` in `T = {ζ_0, ..., ζ_n}`. -/
  ind1H : Fin (hyp76.n + 1)
  /-- Index of the distinguished `ζ ∈ S = T \ {Ind 1_H}`. -/
  zetaDistinct : Fin (hyp76.n + 1)
  /-- `ζ ≠ Ind 1_H`, so the distinguished `ζ` lies in `S`. -/
  zetaDistinct_ne_ind1H : zetaDistinct ≠ ind1H
  /-- `ζ(1) = (Ind 1_H)(1)` (= `e = [L:H]`).  Makes the difference
  `Ind 1_H − ζ` vanish at `1`, hence supported on `A = H \ {1}`. -/
  zeta_one_eq_ind1H_one :
    hyp76.zeta zetaDistinct (1 : L) = hyp76.zeta ind1H (1 : L)
  /-- `Ind 1_H − ζ` is supported on `A`.  Carried so the supported-class-function
  `β` can be formed cleanly. -/
  diff_support : (hyp76.zeta ind1H - hyp76.zeta zetaDistinct).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  /-- The coherent isometric extension `ν : ℤ[S] → ℤ[Irr G]`, presented as an
  `ℤ`-linear map on the ambient class-function space. -/
  nu : ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ
  /-- `ν` is an isometry: `(ν φ, ν ψ)_G = (φ, ψ)_L`. -/
  nu_isometry : ∀ φ ψ : ClassFunction L ℂ,
    ClassFunction.inner (nu φ) (nu ψ) = ClassFunction.inner φ ψ
  /-- **Peterfalvi (7.8.c.i) certificate.**  For χ ∈ Irr G orthogonal to `S^ν`
  (i.e. `(χ, ν ζ_i)_G = 0` for every `i ≠ ind1H`), and `x ∈ A`,
  `χ^ρ(x) = star (β, χ)_G`, where `β = τ (Ind 1_H − ζ) ∈ CF(G)`.

  Encodes the coherence-based reduction of the (7.7.a) decomposition: under
  `χ ⊥ S^ν`, the inner products `(ψ_i^τ, χ) = (ν(ψ_i), χ)` collapse to a
  single contribution proportional to `β`. -/
  chiRho_eq_inner_beta : ∀ (χ : ClassFunction G ℂ),
    IsIrreducibleCharacter χ →
    (∀ i : Fin (hyp76.n + 1), i ≠ ind1H →
      ClassFunction.inner χ (nu (hyp76.zeta i)) = 0) →
    ∀ {x : L}, (x : G) ∈ A →
    hyp76.hyp71.chiRho χ x =
      star (ClassFunction.inner
        (hyp76.hyp71.τ
          ⟨hyp76.zeta ind1H - hyp76.zeta zetaDistinct, diff_support⟩) χ)

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `Ind 1_H − ζ ∈ CF(L,A)`, the supported difference defining `β`. -/
noncomputable def indMinusZetaSupp (H78 : Hypothesis78 G A L) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct, H78.diff_support⟩

/-- **`β = (Ind 1_H − ζ)^τ ∈ CF(G)`.** -/
noncomputable def beta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.hyp76.hyp71.τ H78.indMinusZetaSupp

theorem beta_def (H78 : Hypothesis78 G A L) :
    H78.beta =
      H78.hyp76.hyp71.τ
        ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct,
          H78.diff_support⟩ :=
  rfl

/-- **Peterfalvi (7.8.c.i).**  For χ ∈ Irr G orthogonal to `S^ν` and `x ∈ A`,
`χ^ρ(x) = star (β, χ)_G`. -/
theorem chiRho_eq_inner_beta_on_A (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0)
    {x : L} (hx : (x : G) ∈ A) :
    H78.hyp76.hyp71.chiRho χ x = star (ClassFunction.inner H78.beta χ) := by
  rw [beta_def]
  exact H78.chiRho_eq_inner_beta χ hχ_irr hχ_orth hx

/-- **Peterfalvi (7.8.c.ii).**  For χ ∈ Irr G orthogonal to `S^ν`,
`‖χ^ρ‖² = (|A|/|L|) · (β, χ)_G · star (β, χ)_G`.

Proof: the inner-product `(χ^ρ, χ^ρ)_L = (1/|L|) Σ_{l : L} χ^ρ(l) · star (χ^ρ(l))`.
By (7.8.c.i), on `{l ∈ L | (l:G) ∈ A}` each summand equals
`star (β,χ) · (β,χ)`; off it the summand vanishes since `chiRho` is supported
on `A`.  The count of `l : L` with `(l : G) ∈ A` equals `|A|` since `A ⊆ L`
(by `Hypothesis71.card_supportInSubgroup_eq_card_A`). -/
theorem chiRho_norm_sq_eq_card_ratio_mul (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0) :
    ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ) =
      ((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta χ *
          star (ClassFunction.inner H78.beta χ)) := by
  classical
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv,
      ClassFunction.innerSum]
  -- Pointwise: each summand is a constant on `{l | (l:G) ∈ A}` and zero off it.
  have hpt : ∀ l : L,
      H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 := by
    intro l
    rw [Hypothesis71.chiRhoCF_apply]
    by_cases hl : (l : G) ∈ A
    · rw [if_pos hl,
          H78.chiRho_eq_inner_beta_on_A χ hχ_irr hχ_orth hl, star_star]
    · rw [if_neg hl, H78.hyp76.hyp71.chiRho_of_not_mem χ hl, star_zero,
          mul_zero]
  -- Aggregate the pointwise rewrite, then convert the indicator sum to a count.
  rw [show ∑ l : L,
        H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
      ∑ l : L,
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 from
    Finset.sum_congr rfl (fun l _ => hpt l)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- The filter count equals `Nat.card A` via `card_supportInSubgroup_eq_card_A`.
  have hcard :
      ((Finset.univ.filter (fun l : L => (l : G) ∈ A)).card : ℂ) =
        (Nat.card A : ℂ) := by
    have hset_eq :
        Finset.univ.filter (fun l : L => (l : G) ∈ A) =
          (OddOrder.Peterfalvi.S04.supportInSubgroup A L).toFinset := by
      ext l
      simp
    rw [hset_eq, Set.toFinset_card, ← Nat.card_eq_fintype_card,
        Hypothesis71.card_supportInSubgroup_eq_card_A
          H78.hyp76.hyp71.hyp.subset_L]
  rw [hcard]
  ring

end Hypothesis78

end Section_7_8

/- 7.10-7.11: the Frobenius-family non-existence theorem (pp. 42-43) -/

/-- **Peterfalvi (7.10) hypothesis.** A family of `k` Frobenius subgroups of `G`
whose kernels are pairwise-coprime TI-subsets.

This bundles conditions (a)-(c) of (7.10):
* `(a)` each `L i` is a Frobenius group with kernel `H i` (`isFrobenius`);
* `(b)` `H i` is `L i`-normal with `L i = N_G(H i)`, and `(H i)^#` is a TI-subset
  of `G` with normalizer `L i` (`normalizer_eq`, `isTI`);
* `(c)` the kernel orders `|H i|` are pairwise coprime (`coprime_kernel`),
together with `k ≥ 2` (`two_le`).  Condition (d) — the definition of `G₀` — is
recorded separately as `FrobeniusFamily.G0`. -/
structure FrobeniusFamily (G : Type*) [Group G] (k : ℕ) where
  /-- The Frobenius subgroups `L_i ≤ G`. -/
  L : Fin k → Subgroup G
  /-- The Frobenius kernels `H_i ⊴ L_i`. -/
  H : Fin k → Subgroup G
  /-- (7.10): the family has at least two members. -/
  two_le : 2 ≤ k
  /-- Each kernel sits inside its host. -/
  kernel_le : ∀ i, H i ≤ L i
  /-- (7.10)(a): each `L_i` is a Frobenius group with kernel `H_i`, for some
  Frobenius complement `C`. -/
  isFrobenius : ∀ i, ∃ C : Subgroup ↥(L i),
    IsFrobeniusGroup ↥(L i) ((H i).subgroupOf (L i)) C
  /-- (7.10)(b), host part: `L_i` is the normalizer of `H_i` in `G`. -/
  normalizer_eq : ∀ i, L i = Subgroup.normalizer (H i : Set G)
  /-- (7.10)(b), TI part: `H_i^#` is a TI-subset of `G` with normalizer `L_i`. -/
  isTI : ∀ i, IsTISubset ((H i : Set G) \ {1}) (L i)
  /-- (7.10)(c): the kernel orders are pairwise coprime. -/
  coprime_kernel : ∀ ⦃i j⦄, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j))

namespace FrobeniusFamily

variable {k : ℕ}

/-- `(H_i^#)^G`: the set of `G`-conjugates of nonidentity elements of the `i`-th
kernel `H_i`. -/
def kernelSpread (F : FrobeniusFamily G k) (i : Fin k) : Set G :=
  {x : G | ∃ g : G, g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}}

/-- **(7.10)(d).** `G₀ = G - ⋃_i (H_i^#)^G`: the elements not conjugate into any
kernel. -/
def G0 (F : FrobeniusFamily G k) : Set G :=
  {x : G | ∀ i, x ∉ F.kernelSpread i}

theorem mem_G0_iff (F : FrobeniusFamily G k) {x : G} :
    x ∈ F.G0 ↔ ∀ i, x ∉ F.kernelSpread i := Iff.rfl

/-- The implementation of kernelSpread is the usual conjugacy closure of H_i^#. -/
lemma mem_kernelSpread_iff_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k)
    {x : G} :
    x ∈ F.kernelSpread i ↔ x ∈ Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  constructor
  · rintro ⟨g, hg⟩
    rw [Group.mem_conjugatesOfSet_iff]
    refine ⟨g * x * g⁻¹, hg, ?_⟩
    rw [isConj_iff]
    refine ⟨g⁻¹, ?_⟩
    group
  · intro hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨y, hy, hconj⟩
    rcases isConj_iff.mp hconj with ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg]
    have hback : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [hback] using hy

lemma kernelSpread_eq_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k) :
    F.kernelSpread i = Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  ext x
  exact F.mem_kernelSpread_iff_conjugatesOfSet i

lemma one_not_mem_kernelSpread (F : FrobeniusFamily G k) (i : Fin k) :
    (1 : G) ∉ F.kernelSpread i := by
  rintro ⟨g, hg⟩
  exact hg.2 (by simp)

lemma one_mem_G0 (F : FrobeniusFamily G k) : (1 : G) ∈ F.G0 := by
  intro i
  exact F.one_not_mem_kernelSpread i

/-- Elements of L_i = N_G(H_i) conjugate H_i to itself. -/
lemma mem_kernel_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ F.H i ↔ x ∈ F.H i := by
  have hnorm : g ∈ Subgroup.normalizer (F.H i : Set G) := by
    rw [← F.normalizer_eq i]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hnorm x).symm

/-- Elements of L_i conjugate the sharp kernel H_i^# to itself. -/
lemma mem_kernel_sharp_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ (F.H i : Set G) \ {1} ↔ x ∈ (F.H i : Set G) \ {1} := by
  constructor
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mp hx.1, by
      intro hx1
      exact hx.2 (by simpa using hx1)⟩
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mpr hx.1, by
      intro hconj
      exact hx.2 (conj_eq_one_iff.mp hconj)⟩

/-- TI for H_i^# says that any element carrying one sharp-kernel element back
into H_i^# already lies in L_i. -/
lemma mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp
    (F : FrobeniusFamily G k) (i : Fin k) {g x : G}
    (hx : x ∈ (F.H i : Set G) \ {1})
    (hconj : g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}) :
    g ∈ F.L i :=
  F.isTI i g ⟨x, hx, hconj⟩

/-- A centralizer of a nonidentity kernel element is contained in the corresponding
normalizer L_i. -/
lemma centralizer_le_L_of_mem_kernel_sharp (F : FrobeniusFamily G k) (i : Fin k)
    {x : G} (hx : x ∈ (F.H i : Set G) \ {1}) :
    Subgroup.centralizer ({x} : Set G) ≤ F.L i := by
  intro g hg
  refine F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i hx ?_
  have hcomm : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hconj : g * x * g⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hcomm
  simpa [hconj] using hx

/-- Inside H_i^#, ambient conjugacy is already L_i-conjugacy. -/
lemma exists_L_conj_of_isConj_kernel_sharp (F : FrobeniusFamily G k) (i : Fin k)
    {x y : G} (hx : x ∈ (F.H i : Set G) \ {1})
    (hy : y ∈ (F.H i : Set G) \ {1}) (hxy : IsConj x y) :
    ∃ l : F.L i, (l : G) * x * (l : G)⁻¹ = y := by
  rcases isConj_iff.mp hxy with ⟨g, hg⟩
  exact ⟨⟨g, F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i hx (by
    simpa [hg] using hy)⟩, hg⟩

/-- The sharp kernel H_i^# has cardinality |H_i| - 1. -/
lemma ncard_kernel_sharp [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    ((F.H i : Set G) \ ({1} : Set G)).ncard = Nat.card (F.H i) - 1 := by
  have hHcard : (F.H i : Set G).ncard = Nat.card (F.H i) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1_mem : (1 : G) ∈ (F.H i : Set G) := (F.H i).one_mem
  rw [Set.ncard_diff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

lemma ne_one_of_mem_kernelSpread (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : x ≠ 1 := by
  rintro rfl
  exact F.one_not_mem_kernelSpread i hx

lemma orderOf_dvd_card_kernel_of_mem_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : orderOf x ∣ Nat.card (F.H i) := by
  rcases hx with ⟨g, hg⟩
  have hsub : orderOf (⟨g * x * g⁻¹, hg.1⟩ : F.H i) ∣ Nat.card (F.H i) :=
    orderOf_dvd_natCard _
  have hy_dvd : orderOf (g * x * g⁻¹) ∣ Nat.card (F.H i) := by
    simpa [Subgroup.orderOf_mk] using hsub
  have hsc : SemiconjBy g x (g * x * g⁻¹) := by
    rw [SemiconjBy]
    group
  have horder : orderOf x = orderOf (g * x * g⁻¹) := SemiconjBy.orderOf_eq g hsc
  simpa [horder] using hy_dvd

/-- `(H_i^#)^G` is closed under ambient conjugation. -/
lemma kernelSpread_conj_mem (F : FrobeniusFamily G k) (i : Fin k)
    (g : G) {x : G} (hx : x ∈ F.kernelSpread i) :
    g * x * g⁻¹ ∈ F.kernelSpread i := by
  rcases hx with ⟨a, ha⟩
  refine ⟨a * g⁻¹, ?_⟩
  have hconj : (a * g⁻¹) * (g * x * g⁻¹) * (a * g⁻¹)⁻¹ = a * x * a⁻¹ := by
    group
  rwa [hconj]

lemma mem_kernelSpread_conj_iff (F : FrobeniusFamily G k) (i : Fin k)
    (g x : G) :
    g * x * g⁻¹ ∈ F.kernelSpread i ↔ x ∈ F.kernelSpread i := by
  constructor
  · intro hx
    have hback := F.kernelSpread_conj_mem i g⁻¹ hx
    simpa [mul_assoc] using hback
  · intro hx
    exact F.kernelSpread_conj_mem i g hx

/-- `G₀`, the complement of the conjugate spreads, is conjugation-invariant. -/
lemma G0_conj_mem (F : FrobeniusFamily G k) (g : G) {x : G}
    (hx : x ∈ F.G0) : g * x * g⁻¹ ∈ F.G0 := by
  intro i hsp
  have hxsp : x ∈ F.kernelSpread i := by
    have hback := F.kernelSpread_conj_mem i g⁻¹ hsp
    simpa [mul_assoc] using hback
  exact hx i hxsp

lemma mem_G0_conj_iff (F : FrobeniusFamily G k) (g x : G) :
    g * x * g⁻¹ ∈ F.G0 ↔ x ∈ F.G0 := by
  constructor
  · intro hx
    have hback := F.G0_conj_mem g⁻¹ hx
    simpa [mul_assoc] using hback
  · intro hx
    exact F.G0_conj_mem g hx

/-- Distinct kernel spreads in Peterfalvi (7.10) are disjoint.  Any element in
their intersection has order dividing both coprime kernel orders, hence is the
identity, contradicting membership in a sharp conjugate spread. -/
lemma kernelSpread_disjoint [Finite G] (F : FrobeniusFamily G k)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (F.kernelSpread i) (F.kernelSpread j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hcop : Nat.Coprime (orderOf x) (Nat.card (F.H j)) :=
    Nat.Coprime.coprime_dvd_left
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxi) (F.coprime_kernel hij)
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxj)
  exact F.ne_one_of_mem_kernelSpread hxi (orderOf_eq_one_iff.mp horder_one)

lemma kernelSpread_pairwiseDisjoint [Finite G] (F : FrobeniusFamily G k) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint F.kernelSpread := by
  intro i _hi j _hj hij
  exact F.kernelSpread_disjoint hij

lemma G0_disjoint_kernelSpread (F : FrobeniusFamily G k) (i : Fin k) :
    Disjoint F.G0 (F.kernelSpread i) := by
  rw [Set.disjoint_left]
  intro x hx hxi
  exact hx i hxi

lemma kernelSpread_disjoint_G0 (F : FrobeniusFamily G k) (i : Fin k) :
    Disjoint (F.kernelSpread i) F.G0 :=
  (F.G0_disjoint_kernelSpread i).symm

lemma not_mem_G0_iff (F : FrobeniusFamily G k) {x : G} :
    x ∉ F.G0 ↔ ∃ i, x ∈ F.kernelSpread i := by
  simp [G0]

lemma mem_G0_or_exists_mem_kernelSpread (F : FrobeniusFamily G k) (x : G) :
    x ∈ F.G0 ∨ ∃ i, x ∈ F.kernelSpread i := by
  by_cases hx : x ∈ F.G0
  · exact Or.inl hx
  · exact Or.inr ((F.not_mem_G0_iff).mp hx)

/-- The sets `G₀` and the pairwise-disjoint kernel spreads partition the ambient
group.  This is the cardinality form of Peterfalvi (7.10)(d). -/
lemma card_eq_card_G0_add_sum_card_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card G = Nat.card F.G0 + ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
  classical
  letI := Fintype.ofFinite G
  have h_disjFin :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => (F.kernelSpread i).toFinset) := by
    intro i _hi j _hj hij
    rw [Function.onFun, Set.disjoint_toFinset]
    exact F.kernelSpread_disjoint hij
  have h_biUnion_card :
      ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset)).card =
        ∑ i : Fin k, (F.kernelSpread i).toFinset.card :=
    Finset.card_biUnion h_disjFin
  have h_biUnion_set :
      (Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset) = F.G0.toFinsetᶜ := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_compl,
      Set.mem_toFinset, F.mem_G0_iff, not_forall, not_not]
  have hG0_le : F.G0.toFinset.card ≤ Fintype.card G := by
    rw [← Finset.card_univ (α := G)]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hG0_card_eq : F.G0.toFinset.card = Nat.card F.G0 := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
  have hspread_card_eq : ∀ i : Fin k,
      (F.kernelSpread i).toFinset.card = Nat.card (F.kernelSpread i) := by
    intro i
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
  have h_compl_card :
      F.G0.toFinsetᶜ.card = Nat.card G - Nat.card F.G0 := by
    rw [Finset.card_compl]
    rw [show Fintype.card G = Nat.card G from by rw [Nat.card_eq_fintype_card],
      hG0_card_eq]
  have h_biUnion_card_nat :
      ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset)).card =
        ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
    rw [h_biUnion_card]
    exact Finset.sum_congr rfl (fun i _ => hspread_card_eq i)
  rw [h_biUnion_set] at h_biUnion_card_nat
  have hsum :
      (∑ i : Fin k, Nat.card (F.kernelSpread i)) =
        Nat.card G - Nat.card F.G0 :=
    h_biUnion_card_nat.symm.trans h_compl_card
  have hG0_le_nat : Nat.card F.G0 ≤ Nat.card G := by
    rw [← hG0_card_eq, Nat.card_eq_fintype_card]
    exact hG0_le
  omega

/-- The partition (7.10)(d) implies `|G₀| ≤ |G|`. -/
lemma card_G0_le_card_G [Finite G] (F : FrobeniusFamily G k) :
    Nat.card F.G0 ≤ Nat.card G := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- Difference form of the (7.10)(d) partition: the spread sizes sum to
`|G| - |G₀|`. -/
lemma sum_card_kernelSpread_eq_card_G_sub_card_G0 [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, Nat.card (F.kernelSpread i)) = Nat.card G - Nat.card F.G0 := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- Difference form of the (7.10)(d) partition: `|G₀|` is the complement
of the spreads. -/
lemma card_G0_eq_card_G_sub_sum_card_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card F.G0 = Nat.card G - ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- Kernel order `h_i = |H_i|`. -/
noncomputable def h (F : FrobeniusFamily G k) (i : Fin k) : ℕ := Nat.card (F.H i)

/-- Complement index `e_i = |L_i : H_i|` (exact, since `H_i ≤ L_i`). -/
noncomputable def e (F : FrobeniusFamily G k) (i : Fin k) : ℕ :=
  Nat.card (F.L i) / Nat.card (F.H i)

/-- `G₀` is nonempty: it contains the identity. -/
lemma one_le_card_G0 [Finite G] (F : FrobeniusFamily G k) :
    1 ≤ Nat.card F.G0 := by
  have : Nonempty F.G0 := ⟨⟨1, F.one_mem_G0⟩⟩
  exact Nat.card_pos

/-- `e_i = |L_i : H_i|` equals the order of the Frobenius complement `C`. -/
lemma e_eq_card_complement [Finite G] (F : FrobeniusFamily G k) (i : Fin k)
    {C : Subgroup ↥(F.L i)} (hC : IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    F.e i = Nat.card C := by
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]; exact hC.isComplement.card_mul
  have h := Nat.mul_div_cancel_left (Nat.card C) (Nat.card_pos (α := F.H i))
  rw [hprod] at h
  exact h

/-- The Frobenius product formula `|H_i| * e_i = |L_i|`. -/
lemma h_mul_e_eq_card_L [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.h i * F.e i = Nat.card (F.L i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  rw [F.e_eq_card_complement i hC]
  exact hprod

/-- The Frobenius congruence gives `e_i ∣ h_i - 1`. -/
lemma e_dvd_h_sub_one [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.e i ∣ F.h i - 1 := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hmod : Nat.card (F.H i) ≡ 1 [MOD Nat.card C] := by
    have := hC.card_kernel_modEq_one
    rwa [hN_card] at this
  have hdvd : Nat.card C ∣ Nat.card (F.H i) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.card_pos (α := F.H i))).mp hmod.symm
  rw [F.e_eq_card_complement i hC]
  exact hdvd

/-- A Frobenius kernel in the family is nontrivial, so `2 ≤ h_i`. -/
lemma two_le_h [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.h i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hh_eq : F.h i = Nat.card (F.H i) := rfl
  rw [hh_eq, ← hN_card]
  have hnt : Nontrivial ((F.H i).subgroupOf (F.L i)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hC.ne_bot_kernel
  have h1 : 1 < Nat.card ((F.H i).subgroupOf (F.L i)) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- In an odd-order ambient group, each Frobenius kernel order `h_i` is odd. -/
lemma odd_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.h i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  exact (Nat.odd_mul.mp (hprod ▸ hLodd)).1

/-- In an odd-order ambient group, each complement index `e_i` is odd. -/
lemma odd_e [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.e i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hCodd : Odd (Nat.card C) := (Nat.odd_mul.mp (hprod ▸ hLodd)).2
  rw [F.e_eq_card_complement i hC]
  exact hCodd

/-- The Frobenius complement of `L_i` is nontrivial, so `e_i = |L_i : H_i| ≥ 2`. -/
lemma two_le_e [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.e i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  rw [F.e_eq_card_complement i hC]
  have hnt : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.ne_bot_complement
  have h1 : 1 < Nat.card C := Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- `2 e_i + 1 ≤ h_i`.  From `e_i ∣ h_i - 1` (Frobenius: `|H_i| ≡ 1 mod e_i`)
together with `|L_i|` odd (whence `e_i` is odd and `h_i - 1` is even), the
quotient `(h_i - 1)/e_i` is even and positive, so `h_i - 1 ≥ 2 e_i`. -/
lemma two_mul_e_add_one_le_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : 2 * F.e i + 1 ≤ F.h i := by
  obtain ⟨m, hm⟩ := F.e_dvd_h_sub_one i
  have hh_odd : Odd (F.h i) := F.odd_h hodd i
  have he_odd : Odd (F.e i) := F.odd_e hodd i
  have hh_ge2 : 2 ≤ F.h i := F.two_le_h i
  have hh_sub_even : Even (F.h i - 1) := by
    obtain ⟨j, hj⟩ := hh_odd
    exact ⟨j, by omega⟩
  have hm_even : Even m := by
    rw [hm] at hh_sub_even
    rcases Nat.even_mul.mp hh_sub_even with he_even | hm_even
    · exact absurd he_even (Nat.not_even_iff_odd.mpr he_odd)
    · exact hm_even
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hm
      omega
    · exact h0
  have hm_ge2 : 2 ≤ m := by
    rcases hm_even with ⟨t, ht⟩
    omega
  have hmul : F.e i * 2 ≤ F.e i * m := Nat.mul_le_mul_left _ hm_ge2
  omega

/-- The explicit right-hand side in Peterfalvi (7.10) is positive for every member
of an odd-order Frobenius family.  This is the arithmetic input used in the final
(7.11) contradiction once `(7.10)` gives the lower bound. -/
lemma lowerBoundTerm_pos [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) :
    0 < ((F.e i : ℚ) - 1) *
      (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
          ((F.e i : ℚ) * (F.h i : ℚ)) +
        2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he2 : (2 : ℚ) ≤ (F.e i : ℚ) := by
    exact_mod_cast F.two_le_e i
  have hh2 : 2 * (F.e i : ℚ) + 1 ≤ (F.h i : ℚ) := by
    exact_mod_cast F.two_mul_e_add_one_le_h hodd i
  have hepos : (0 : ℚ) < (F.e i : ℚ) := by linarith
  have hhpos : (0 : ℚ) < (F.h i : ℚ) := by linarith
  have heh : (0 : ℚ) < (F.e i : ℚ) * (F.h i : ℚ) := mul_pos hepos hhpos
  have hh2pos : (0 : ℚ) < (F.h i : ℚ) * ((F.h i : ℚ) + 2) :=
    mul_pos hhpos (by linarith)
  refine mul_pos (by linarith) ?_
  have h1 : 0 ≤
      ((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
        ((F.e i : ℚ) * (F.h i : ℚ)) :=
    div_nonneg (by linarith) (le_of_lt heh)
  have h2 : 0 < (2 : ℚ) / ((F.h i : ℚ) * ((F.h i : ℚ) + 2)) :=
    div_pos (by norm_num) hh2pos
  linarith

end FrobeniusFamily

/-- **Peterfalvi (7.10).** Under `FrobeniusFamily` with `G` of odd order, there is
an index `i` for which, writing `e = e_i` and `h = h_i`,

`(|G₀| - 1)/|G| ≥ (e - 1) · ((h - 2e - 1)/(e·h) + 2/(h·(h+2)))`.

This is the quantitative heart of §9; its proof uses the Dade isometry and the
coherence estimates (7.5)-(7.9). -/
theorem card_G0_lower_bound [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  sorry

/-- **Peterfalvi (7.11)** — the §9 main theorem.

There is no odd-order group `G` admitting a family of `k ≥ 2` Frobenius subgroups
(as in `FrobeniusFamily`) whose kernels' conjugate-spreads cover everything except
the identity, i.e. with `G₀ = {1}`.

Proof (in the text): if `G₀ = {1}` then `|G₀| = 1`, so the left side of (7.10)
vanishes; but `e ≥ 2` (the Frobenius complement is nontrivial and `|G|` is odd)
and `e ∣ h - 1` with `h` odd give `(h - 2e - 1)/(eh) ≥ 0`, whence the right side
of (7.10) is strictly positive — a contradiction. -/
theorem not_trivial_G0 [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (hG0 : F.G0 = {(1 : G)}) : False := by
  obtain ⟨i, hi⟩ := card_G0_lower_bound F hodd
  -- `G₀ = {1}` forces `|G₀| = 1`, so the left-hand side of (7.10) is `0`.
  have hcard : Nat.card F.G0 = 1 := by rw [hG0]; simp
  -- The right-hand side of (7.10) is strictly positive.
  have hRHS := F.lowerBoundTerm_pos hodd i
  -- But (7.10) says it is `≤ 0` — contradiction.
  rw [hcard] at hi
  have hlhs : ((1 : ℕ) : ℚ) - 1 = 0 := by norm_num
  rw [hlhs, zero_div] at hi
  linarith [hi, hRHS]

end OddOrder.Peterfalvi.S09
