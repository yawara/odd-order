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

This first scaffold installs the (7.1) hypothesis bundle (`Hypothesis71`), the
`ρ` map (`chiRho`), and the (7.2.a) lemma; (7.2.b) and (7.3) are stated with
`sorry` and reserved for follow-on issues (see `issues/0042-*`). -/

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
/-- **Peterfalvi (7.3)** (stated; proof deferred).  The integral inequality:
`|G|⁻¹ Σ_{g ∈ A^τ} |χ(g)|² ≥ ‖χ^ρ‖²`, with equality iff `χ` is constant on each
`aH(a)`.  Consequence of (7.2.b); see `issues/0042-*` follow-on. -/
theorem chiRho_integral_inequality {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (χ : ClassFunction G ℂ) :
    (ClassFunction.inner (H71.chiRhoCF χ) (H71.chiRhoCF χ)).re ≤
      (((Nat.card G : ℂ)⁻¹ *
        ∑ g ∈ Finset.univ.filter (fun x : G => x ∈ H71.hyp.dadeSupport),
          ‖(χ : G → ℂ) g‖^2 : ℂ)).re := by
  sorry

/- (7.2.b) `‖χ^ρ‖² ≤ ‖χ‖²` and (7.3) the integral inequality are deferred to
the follow-on infrastructure issue (promotion of `chiRho` to a class function on
`L` supported on `A`, plus the normalized inner product layer over `CF(L,A)` and
`CF(G)`).  See `issues/0042-peterfalvi-s09-rho-and-7-1-7-3.md`. -/

end Hypothesis71

end Section_7_1_to_7_3

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

/-- Kernel order `h_i = |H_i|`. -/
noncomputable def h (F : FrobeniusFamily G k) (i : Fin k) : ℕ := Nat.card (F.H i)

/-- Complement index `e_i = |L_i : H_i|` (exact, since `H_i ≤ L_i`). -/
noncomputable def e (F : FrobeniusFamily G k) (i : Fin k) : ℕ :=
  Nat.card (F.L i) / Nat.card (F.H i)

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
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]; exact hC.isComplement.card_mul
  have he_eq : F.e i = Nat.card C := F.e_eq_card_complement i hC
  have hh_eq : F.h i = Nat.card (F.H i) := rfl
  -- `|L_i|` is odd (a subgroup of the odd-order group `G`), so `|H_i|` and `|C|` are odd.
  have hLodd : Odd (Nat.card ↥(F.L i)) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  obtain ⟨hHodd, hCodd⟩ := Nat.odd_mul.mp (hprod ▸ hLodd)
  -- `|C| ∣ |H_i| - 1`.
  have hmod : Nat.card (F.H i) ≡ 1 [MOD Nat.card C] := by
    have := hC.card_kernel_modEq_one; rwa [hN_card] at this
  have hdvd : Nat.card C ∣ Nat.card (F.H i) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.card_pos (α := F.H i))).mp hmod.symm
  -- `|H_i| ≥ 2` (nontrivial kernel).
  have hHge2 : 2 ≤ Nat.card (F.H i) := by
    rw [← hN_card]
    have hnt : Nontrivial ((F.H i).subgroupOf (F.L i)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hC.ne_bot_kernel
    have h1 : 1 < Nat.card ((F.H i).subgroupOf (F.L i)) :=
      Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega
  -- The cofactor `m = (|H_i|-1)/|C|` is even and positive, hence `≥ 2`.
  obtain ⟨m, hm⟩ := hdvd
  have hHsub_even : Even (Nat.card (F.H i) - 1) := by
    obtain ⟨j, hj⟩ := hHodd; exact ⟨j, by omega⟩
  have hm_even : Even m := by
    rw [hm] at hHsub_even
    rcases Nat.even_mul.mp hHsub_even with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hCodd)
    · exact h
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact h0
  have hm_ge2 : 2 ≤ m := by
    rcases hm_even with ⟨t, ht⟩; omega
  have hmul : Nat.card C * 2 ≤ Nat.card C * m := Nat.mul_le_mul_left _ hm_ge2
  rw [he_eq, hh_eq]
  omega

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
  -- The two arithmetic facts coming from the Frobenius structure.
  have he2 : (2 : ℚ) ≤ (F.e i : ℚ) := by exact_mod_cast F.two_le_e i
  have hh2 : 2 * (F.e i : ℚ) + 1 ≤ (F.h i : ℚ) := by
    exact_mod_cast F.two_mul_e_add_one_le_h hodd i
  have hepos : (0 : ℚ) < (F.e i : ℚ) := by linarith
  have hhpos : (0 : ℚ) < (F.h i : ℚ) := by linarith
  have heh : (0 : ℚ) < (F.e i : ℚ) * (F.h i : ℚ) := mul_pos hepos hhpos
  have hh2pos : (0 : ℚ) < (F.h i : ℚ) * ((F.h i : ℚ) + 2) := mul_pos hhpos (by linarith)
  -- The right-hand side of (7.10) is then strictly positive.
  have hRHS : 0 < ((F.e i : ℚ) - 1) *
      (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ)) +
        2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
    refine mul_pos (by linarith) ?_
    have h1 : 0 ≤ ((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ)) :=
      div_nonneg (by linarith) (le_of_lt heh)
    have h2 : 0 < (2 : ℚ) / ((F.h i : ℚ) * ((F.h i : ℚ) + 2)) := div_pos (by norm_num) hh2pos
    linarith
  -- But (7.10) says it is `≤ 0` — contradiction.
  rw [hcard] at hi
  have hlhs : ((1 : ℕ) : ℚ) - 1 = 0 := by norm_num
  rw [hlhs, zero_div] at hi
  linarith [hi, hRHS]

end OddOrder.Peterfalvi.S09
