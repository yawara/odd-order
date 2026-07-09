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

This file installs (7.1)-(7.8), all sorry-free, and names the faithful
(7.9) two-family non-orthogonality target as a predicate:
* (7.1)-(7.3): the hypothesis bundle (`Hypothesis71`), the `ρ` map
  (`chiRho` / `chiRhoCF` / `chiRhoSupp`), (7.2.a) `chiRho_dadeImage_eq`,
  (7.2.b) `chiRho_norm_sq_le`, (7.3) `chiRho_integral_inequality`;
* (7.4)-(7.5): `FamilyHypothesis71` and `family_inequality`;
* (7.6)-(7.7): the normal-subgroup case `A = H^#` (`Hypothesis76`), with
  (7.7.a) `chiRho_explicit_formula` and (7.7.b) `chiRho_norm_sq_double_sum`;
* (7.8): the coherence-based formula (`Hypothesis78`), with the (7.8.a)
  target `Hypothesis78.BetaDecomp`, the (7.8.b) target
  `Hypothesis78.NormEstimates`, (7.8.c.i) `chiRho_eq_inner_beta_on_A`,
  and (7.8.c.ii) `chiRho_norm_sq_eq_card_ratio_mul`;
* (7.9): the statement interface `Hypothesis79` and its conclusion predicate
  `Hypothesis79.conclusion`.

The (7.7.a) and (7.8.c.i) pointwise identities are carried as structural
certificates (`Hypothesis76.chiRho_decomp`, `Hypothesis78.chiRho_eq_inner_beta`):
they encode Peterfalvi's `CF(L,A)`-basis / coherence reductions, whose proofs
need the induced/restricted-character decomposition theory not yet in this file.
The norm-square corollaries (7.7.b)/(7.8.c.ii) are then proved here outright.
The proof of (7.9) remains as follow-on. -/

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

/-- **Construct the Peterfalvi (7.1) data from a TI-subset.**  When `A ⊆ G` is a TI-subset with
`L`-normalizer (`IsTISubset A L`), every `H(a)` is trivial (`S04.of_isTISubset`, Peterfalvi (2.3)),
the Dade map is the canonical one (`Hypothesis.dadeMap`, an honest (2.5)/(2.6) Dade isometry by
`isDadeMap_dadeMap`), and the `H(-)`-conjugation-invariance is automatic
(`HConjInvariant.of_forall_H_eq_bot`).  This is the (7.1) `Hypothesis71` for a TI-set — in particular
for `A = H^#`, `L = N_G(H)` of a Frobenius group with kernel `H` (the source of the
`FrobeniusFamily` (7.4) hypotheses of Peterfalvi (7.10)). -/
noncomputable def of_isTISubset
    (hA_sharp : A ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G)) (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) :
    Hypothesis71 G A L where
  hyp := OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset hA_sharp hA_L hL_norm hTI
  τ := (OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset hA_sharp hA_L hL_norm hTI).dadeMap
  isDadeMap := (OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset hA_sharp hA_L hL_norm hTI).isDadeMap_dadeMap
  hConjInvariant :=
    OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

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

/-- The constant-one class function has norm one. -/
theorem constOne_inner_self_eq_one {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] :
    ClassFunction.inner (constOne G) (constOne G) = 1 := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  simp only [constOne_apply, star_one, mul_one, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, invOf_eq_inv]
  field_simp [show (Nat.card G : ℂ) ≠ 0 by exact_mod_cast (Nat.card_pos (α := G)).ne']

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

open scoped Classical in
/-- Reduced form of the family inequality used in Peterfalvi (7.10).

Starting from (7.5), it inserts:
* the identity contribution on `G₀`, expressed as
  `1 ≤ Σ_{g∈G₀} |χ(g)|²`;
* a lower bound `c ≤ ‖χ^{ρ_i}‖²` for the distinguished index;
* nonnegative contributions for the indices outside the chosen `𝓑`-set.

The output is exactly the real-valued reduced inequality later converted into
the `CharacterEstimateData.base_estimate` field. -/
theorem reduced_inequality_of_estimates {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    (i : Fin k) (B : Finset (Fin k)) (c : ℝ)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0 :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi : c ≤ F.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ) ≤
        F.chiRhoNormSq χ j) :
    ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (c - (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) -
          ∑ j ∈ B, (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ)) ≤ 0 := by
  classical
  let ratio : Fin k → ℝ := fun j =>
    (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ)
  let term : Fin k → ℝ := fun j => F.chiRhoNormSq χ j - ratio j
  let g0sum : ℝ :=
    ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0), ‖(χ : G → ℂ) g‖ ^ 2
  let g0term : ℝ := (Nat.card G : ℝ)⁻¹ * (g0sum - (Nat.card F.G0 : ℝ))
  have h75 : g0term + ∑ j : Fin k, term j ≤ 0 := by
    simpa [g0term, g0sum, term, ratio] using family_inequality F χ hχ
  have hG_pos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hG0_lower :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) ≤ g0term := by
    have hsub :
        1 - (Nat.card F.G0 : ℝ) ≤ g0sum - (Nat.card F.G0 : ℝ) := by
      dsimp [g0sum]
      linarith [hG0]
    have hmul := mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hG_pos.le)
    calc
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ))
          = (Nat.card G : ℝ)⁻¹ * (1 - (Nat.card F.G0 : ℝ)) := by
              rw [div_eq_inv_mul, mul_comm]
      _ ≤ (Nat.card G : ℝ)⁻¹ * (g0sum - (Nat.card F.G0 : ℝ)) := hmul
      _ = g0term := rfl
  have hnorm_nonneg : ∀ j : Fin k, 0 ≤ F.chiRhoNormSq χ j := by
    intro j
    letI : Fintype (F.L j) := F.fintypeL j
    letI : Invertible (Nat.card (F.L j) : ℂ) := F.invertibleL j
    simpa [FamilyHypothesis71.chiRhoNormSq] using
      Hypothesis71.ClassFunction.inner_self_re_nonneg ((F.hyp71 j).chiRhoCF χ)
  have hterm_i : c - ratio i ≤ term i := by
    dsimp [term]
    linarith [hi]
  have hB_bound : -(∑ j ∈ B, ratio j) ≤ ∑ j ∈ B, term j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hnonneg := hnorm_nonneg j
    dsimp [term]
    linarith
  have hB_subset : B ⊆ (Finset.univ : Finset (Fin k)).erase i := by
    intro j hj
    rw [Finset.mem_erase]
    exact ⟨(hB_ne j hj).symm, by simp⟩
  have hB_to_erase :
      (∑ j ∈ B, term j) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, term j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hB_subset ?_
    intro j hj_erase hjB
    rw [Finset.mem_erase] at hj_erase
    have hij : i ≠ j := hj_erase.1.symm
    have hj_good := hgood j hij hjB
    dsimp [term]
    linarith
  have hsum_terms :
      c - ratio i - ∑ j ∈ B, ratio j ≤ ∑ j : Fin k, term j := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin k)) term
      (Finset.mem_univ i)
    linarith
  have htarget :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (c - ratio i - ∑ j ∈ B, ratio j) ≤ 0 := by
    have hle :
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
            (c - ratio i - ∑ j ∈ B, ratio j) ≤
          g0term + ∑ j : Fin k, term j := by
      linarith
    exact le_trans hle h75
  simpa [ratio] using htarget

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
  /-- **Induced-ness of the family** (Peterfalvi (7.6): `T = {Ind_H^L θ}`): each `ζ_i` is the
  induction of an irreducible character of `H`.  Stated with the canonical `Fintype`/`Invertible`
  instances (both classes are subsingletons, so consumers can bridge to their own instances by
  `Subsingleton.elim`).  This is what the Peterfalvi (13.5.a) integrality reads: `Res_H ζ_i` is
  `‖ζ_i‖²` times the sum of the `L`-conjugates of `θ_i` (Mackey), a genuine character of `H`. -/
  zeta_induced : ∀ i : Fin (n + 1),
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    ∃ θ : IrreducibleCharacter ↥(H.subgroupOf L),
      zeta i = ClassFunction.induce (H.subgroupOf L) (θ : ClassFunction _ ℂ)
  /-- **Distinctness of the family** (Peterfalvi (7.6): the `ζ_i` are *distinct* induced
  characters): the enumeration is injective.  What pins "`i ≠ i₁ ⟹ ζ_i ≠ λ`" in the (13.5)
  middle-coefficient computation (`lambda_tau1_cCoeff`). -/
  zeta_injective : Function.Injective zeta
  /-- **Exhaustiveness of the family** (Peterfalvi (7.6): `T = {Ind_H^L θ | θ ∈ Irr H}` ranges
  over *all* `θ`): every induced irreducible appears at some family index — the converse
  direction to `zeta_induced`, same canonical-instance convention.  This is what places the
  (13.5)/(13.6) distinguished `λ = Ind_H^S θ` at a family index (`exists_lambda_index`). -/
  zeta_family_cover :
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ∃ i : Fin (n + 1),
        zeta i = ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ)
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
  /-- `ν` is a *family* isometry: it preserves the Gram matrix of the coherent
  family `{ζ_i : i ≠ ind1H}`.  This is the genuine content of coherence (Dade);
  a *global* isometry `CF(L) → CF(G)` need not exist (it would be an isometric
  embedding, but `dim CF(L)` can exceed `dim CF(G)`). -/
  nu_isometry : ∀ i j : Fin (hyp76.n + 1), i ≠ ind1H → j ≠ ind1H →
    ClassFunction.inner (nu (hyp76.zeta i)) (nu (hyp76.zeta j)) =
      ClassFunction.inner (hyp76.zeta i) (hyp76.zeta j)
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

/-- The Dade image defining `β` is a virtual character whenever the source
difference `Ind 1_H - ζ` is a virtual character on `L`. -/
theorem beta_mem_ZIrr_of_sourceDiff_mem_ZIrr (H78 : Hypothesis78 G A L)
    (hdiffZ :
      H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L) :
    H78.beta ∈ ZIrr G := by
  have hτ : H78.hyp76.hyp71.τ = H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) :=
    OddOrder.Peterfalvi.S04.IsDadeMap.unique H78.hyp76.hyp71.isDadeMap
      (H78.hyp76.hyp71.hyp.isDadeMap_dadeMap (k := ℂ))
  have hvirt :=
    (H78.hyp76.hyp71.hyp.fullDadeIsometryData
      H78.hyp76.hyp71.hConjInvariant).maps_virtualCharacter H78.indMinusZetaSupp hdiffZ
  rw [beta, hτ]
  rwa [show (H78.hyp76.hyp71.hyp.fullDadeIsometryData
        H78.hyp76.hyp71.hConjInvariant).toDadeMap =
        H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) from
      H78.hyp76.hyp71.hyp.dadeIsometryData_toDadeMap H78.hyp76.hyp71.hConjInvariant] at hvirt

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- The source difference `Ind 1_H - ζ` is virtual when both source terms are
irreducible characters of `L`. -/
theorem sourceDiff_mem_ZIrr_of_irreducible (H78 : Hypothesis78 G A L)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    hind_irr.mem_ZIrr hzeta_irr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- Irreducibility of the two source terms supplies the virtual-character input
needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_irreducible_sourceDiff (H78 : Hypothesis78 G A L)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    hind_irr.mem_ZIrr hzeta_irr

/-- The coherent source set `S = T \ {Ind 1_H}` from Peterfalvi (7.8),
presented as a set of class functions on `L`. -/
def sourceSet (H78 : Hypothesis78 G A L) : Set (ClassFunction L ℂ) :=
  {φ | ∃ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H ∧ H78.hyp76.zeta i = φ}

/-- Each non-`Ind 1_H` source character belongs to the coherent source set `S`. -/
theorem zeta_mem_sourceSet (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.hyp76.zeta i ∈ H78.sourceSet :=
  ⟨i, hi, rfl⟩

/-- The distinguished `ζ` belongs to the coherent source set `S`. -/
theorem zetaDistinct_mem_sourceSet (H78 : Hypothesis78 G A L) :
    H78.hyp76.zeta H78.zetaDistinct ∈ H78.sourceSet :=
  H78.zeta_mem_sourceSet H78.zetaDistinct_ne_ind1H

/-- S09-facing constructor for the generic S08 weighted Ind-chain package.

A concrete S07 coherent witness over the source set `S = T \ {Ind 1_H}` gives
Peterfalvi's Ind-chain data with output family `χ_t = ν ζ_t`, provided the chosen
source family lies in `S` and the scaled differences lie in the supported
lattice where the coherent extension agrees with the original map `τ`. -/
noncomputable def indChainDecomposition_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := H78.nu (ζ t)
  norm_one t := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hcoh.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul, ← hnu]

open scoped Classical in
/-- S09-facing `IndChainDecomposition` constructor from an arbitrary coherent
source family.

This is the set-parametric form of
`indChainDecomposition_of_isCoherent`: the coherent set need not be
`H78.sourceSet`.  It is the bridge used when §8 has already identified the
source family as a Sibley set `hyp.S`, while the §9 notation still wants the
output family to be exactly `χ_t = H78.nu (ζ_t)`. -/
noncomputable def indChainDecomposition_of_coherenceOn
    (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A_prime) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := H78.nu (ζ t)
  norm_one t := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hcoh.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul, ← hnu]

set_option linter.style.longLine false
open scoped Classical in
/-- **Peterfalvi (6.8.1) → (7.10), Frobenius/base-anchor form.**

The S08 Frobenius branch constructs the full Sibley coherence target from the
base-anchor common-index `X`-chain data and generator-level mixed-inner glue.
This constructor feeds that coherence witness directly into the S09
`Hypothesis78` Ind-chain package, fixing the output family as
`χ_t = H78.nu (ζ_t)` rather than leaving it as an anonymous coherence extension.

The remaining inputs are the genuine (6.6)/(6.8) payload: the `X`-chain step
data, the `ν` agreement/mixed-inner facts for the final glue, and the chosen
orthonormal source chain in the Xset/H-prime union with supported scaled differences. -/
noncomputable def
    indChainDecomposition_of_sibley_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData
    (H78 : Hypothesis78 G A L)
    {H : Subgroup L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : OddOrder.Peterfalvi.S08.SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → OddOrder.RepresentationTheory.IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      H78.nu x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, H78.nu y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (H78.nu x) (H78.nu y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L)))
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction ↥L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L)) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := ↥L) (G := G) hyp.tau ζ d := by
  let hX :=
    hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData
  let hcoh : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) :=
    OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq
      hX hyp.coherentYset H78.nu hagreeX hagreeY
      (hyp.inner_span_Xset_Yset_eq_zero_of_frobenius hF) hmixed hgen
  exact H78.indChainDecomposition_of_coherenceOn hcoh (by rfl)
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp

set_option linter.style.longLine true

/-- H78-facing per-term Ind equation in the constructed Ind-chain package. -/
theorem indChain_image_eq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ (ζ t - (d t) • ζ 0) = data.χ t - (d t) • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ (ζ t - (d t) • ζ 0) = data.χ t - (d t) • data.χ 0
  exact data.image_eq t

/-- H78-facing reference-index vanishing for the per-term Ind equation. -/
theorem indChain_image_eq_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ (ζ 0 - (d 0) • ζ 0) = 0
  exact data.image_eq_zero

/-- H78-facing orthonormality formula for the Ind-chain output family. -/
theorem indChain_inner_chi_eq_ite_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t u : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0
  exact data.inner_chi_eq_ite t u

/-- H78-facing coefficient recovery for the weighted output sum. -/
theorem indChain_inner_chi_weightedOutput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ) := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ)
  exact data.inner_chi_weightedOutput t

set_option linter.style.longLine false in
/-- H78-facing raw weighted Ind equation before collecting the reference term. -/
theorem indChain_image_weightedDifferenceInput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0) := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0)
  exact data.image_weightedDifferenceInput

set_option linter.style.longLine false in
/-- H78-facing normalized weighted Ind equation, with the integer-square coefficient.

This consumes the same concrete S07 coherence witness as
`indChainDecomposition_of_isCoherent`, then applies the S08 weighted source-difference
image identity to the resulting Ind-chain package. -/
theorem indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      data.weightedOutput - (∑ t : Fin n, (d t : ℂ) ^ 2) • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    data.weightedOutput - (∑ t : Fin n, (d t : ℂ) ^ 2) • data.χ 0
  exact data.image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero

set_option linter.style.longLine false in
/-- H78-facing normalized weighted Ind equation, with the Parseval norm coefficient. -/
theorem indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      data.weightedOutput -
        ClassFunction.inner data.weightedOutput data.weightedOutput • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    data.weightedOutput -
      ClassFunction.inner data.weightedOutput data.weightedOutput • data.χ 0
  exact data.image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero

/-- H78-facing complex scalar-coefficient form for the weighted Ind-chain source
difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ClassFunction.inner data.weightedOutput data.weightedOutput := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
    1 - ClassFunction.inner data.weightedOutput data.weightedOutput
  exact data.inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm

set_option linter.style.longLine false in
/-- H78-facing reference coefficient of the raw weighted Ind image. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
    1 - ∑ t : Fin n, (d t : ℂ) ^ 2
  exact data.inner_chi_zero_image_weightedDifferenceInput

/-- H78-facing complex Parseval form for the weighted output. -/
theorem indChain_weightedOutput_inner_self_eq_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner data.weightedOutput data.weightedOutput =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner data.weightedOutput data.weightedOutput =
    ∑ t : Fin n, (d t : ℂ) ^ 2
  exact data.weightedOutput_inner_self_eq_sum_sq

/-- H78-facing real Parseval form for the S08 weighted Ind-chain output.

This consumes the same concrete S07 coherence witness as
`indChainDecomposition_of_isCoherent`, then immediately applies the S08 weighted
output norm identity to the resulting Ind-chain package. -/
theorem indChain_weightedOutput_inner_self_re_eq_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner data.weightedOutput data.weightedOutput).re =
      ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner data.weightedOutput data.weightedOutput).re =
    ∑ t : Fin n, (d t : ℝ) ^ 2
  exact data.weightedOutput_inner_self_re_eq_sum_sq

/-- H78-facing lower bound for the weighted output norm from the normalized
coefficient `d 0 = 1`. -/
theorem indChain_one_le_weightedOutput_inner_self_re_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    1 ≤ (ClassFunction.inner data.weightedOutput data.weightedOutput).re := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change 1 ≤ (ClassFunction.inner data.weightedOutput data.weightedOutput).re
  exact data.one_le_weightedOutput_inner_self_re

/-- H78-facing real scalar-coefficient form for the weighted Ind-chain source
difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re =
      1 - ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re =
    1 - ∑ t : Fin n, (d t : ℝ) ^ 2
  exact data.inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq

/-- H78-facing nonpositivity form for the weighted Ind-chain source difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_re_nonpos_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re ≤ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re ≤ 0
  exact data.inner_chi_zero_image_weightedDifferenceInput_re_nonpos

/-- If the abstract `ν` carried by `Hypothesis78` is identified with a concrete
S07 coherent extension, then `ν` sends the coherent lattice `ℤ[S]` into virtual
irreducible characters of `G`.

This is the S09-facing bridge to the real S07 coherence construction: it adds no
new field to `Hypothesis78`, but lets downstream (7.8)/(7.9) arguments use
`IsCoherent.extension_mem_ZIrr` whenever the concrete witness is available. -/
theorem nu_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S) :
    H78.nu φ ∈ ZIrr G := by
  rw [hnu]
  exact hcoh.extension_mem_ZIrr φ hφ

/-- Generator form of `nu_mem_ZIrr_of_isCoherent`: a member of the coherent set
itself is automatically in its `ℤ`-span. -/
theorem nu_mem_ZIrr_of_isCoherent_of_mem (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ S) :
    H78.nu φ ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent hcoh hnu (Submodule.subset_span hφ)

/-- If the concrete S07 coherent witness is built over the source set
`S = T \ {Ind 1_H}`, then every non-`Ind 1_H` indexed source character has
virtual-irreducible image under `ν`. -/
theorem nu_zeta_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.nu (H78.hyp76.zeta i) ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent_of_mem hcoh hnu (H78.zeta_mem_sourceSet hi)

/-- Distinguished-`ζ` specialization of `nu_zeta_mem_ZIrr_of_isCoherent`. -/
theorem nu_zetaDistinct_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension) :
    H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
  H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu H78.zetaDistinct_ne_ind1H

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- The residual `Δ = β - 1_G + ζ^ν` used in Peterfalvi (7.9). -/
noncomputable def delta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.beta - Hypothesis71.constOne G +
    H78.nu (H78.hyp76.zeta H78.zetaDistinct)

/-- If `β` is a virtual character and `ν` is a concrete coherent extension on
`S = T \ {Ind 1_H}`, then the residual `Δ = β - 1_G + νζ` is virtual. -/
theorem delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hbeta : H78.beta ∈ ZIrr G) :
    H78.delta ∈ ZIrr G := by
  have hconst : Hypothesis71.constOne G ∈ ZIrr G := by
    have htriv : OddOrder.RepresentationTheory.trivialClassFunction G ∈ ZIrr G :=
      OddOrder.RepresentationTheory.trivialClassFunction_isIrreducible.mem_ZIrr
    simpa [Hypothesis71.constOne, OddOrder.RepresentationTheory.trivialClassFunction]
      using htriv
  have hzeta : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
    H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh hnu
  simpa [delta] using Submodule.add_mem (ZIrr G)
    (Submodule.sub_mem (ZIrr G) hbeta hconst) hzeta

/-- If the `Ind 1_H` source term is virtual and the distinguished `ζ` is
irreducible, then coherence supplies the residual virtual character `Δ`. -/
theorem delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent hcoh hnu
    (H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- Source irreducibility and coherence supply the full virtual-character
residual `Δ = β - 1_G + νζ`. -/
theorem delta_mem_ZIrr_of_irreducible_sourceDiff_and_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    hcoh hnu hind_irr.mem_ZIrr hzeta_irr

/-- The defining rearrangement `β = 1_G - ζ^ν + Δ`. -/
theorem beta_eq_constOne_sub_zetaImage_add_delta (H78 : Hypothesis78 G A L) :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        H78.delta := by
  rw [delta]
  abel

/-- If `χ` is orthogonal to both `1_G` and the distinguished `ζ^ν`, then
`(β,χ) = (Δ,χ)`. -/
theorem beta_inner_eq_delta_inner_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner (Hypothesis71.constOne G) χ = 0)
    (hzeta : ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) χ = 0) :
    ClassFunction.inner H78.beta χ = ClassFunction.inner H78.delta χ := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, hone, hzeta]
  ring

/-- Right-hand variant: if `χ` is orthogonal on the left to `1_G` and the
 distinguished `ζ^ν`, then `(χ,β) = (χ,Δ)`. -/
theorem inner_beta_eq_inner_delta_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner χ (Hypothesis71.constOne G) = 0)
    (hzeta : ClassFunction.inner χ
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0) :
    ClassFunction.inner χ H78.beta = ClassFunction.inner χ H78.delta := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right, hone, hzeta]
  ring

/-- The real norm square `‖β‖²` used in Peterfalvi (7.8.b). -/
noncomputable def betaNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.beta H78.beta).re

/-- The source-side norm square `‖Ind 1_H - ζ‖²` corresponding to `β`. -/
noncomputable def sourceDiffNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)).re

/-- The Dade-isometry step in Peterfalvi (7.8.b): the norm of `β` equals the
norm of the source difference `Ind 1_H - ζ`.  The remaining `‖β‖² = e + 1`
calculation is therefore a source-side character computation. -/
theorem beta_inner_self_eq_sourceDiff_inner_self (H78 : Hypothesis78 G A L) :
    ClassFunction.inner H78.beta H78.beta =
      ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) := by
  simpa [beta, indMinusZetaSupp] using
    H78.hyp76.isDadeIsometry.inner_eq H78.indMinusZetaSupp H78.indMinusZetaSupp

/-- Real-valued form of `beta_inner_self_eq_sourceDiff_inner_self`. -/
theorem betaNormSq_eq_sourceDiffNormSq (H78 : Hypothesis78 G A L) :
    H78.betaNormSq = H78.sourceDiffNormSq := by
  rw [betaNormSq, sourceDiffNormSq, H78.beta_inner_self_eq_sourceDiff_inner_self]

/-- Source-side expansion of `‖Ind 1_H - ζ‖²`.  This isolates the remaining
character-theoretic facts needed to turn the source norm into `e + 1`. -/
theorem sourceDiff_inner_self_expand (H78 : Hypothesis78 G A L) :
    ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) =
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct) := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
  ring

/-- Real-valued source-side expansion corresponding to
`sourceDiff_inner_self_expand`. -/
theorem sourceDiffNormSq_expand (H78 : Hypothesis78 G A L) :
    H78.sourceDiffNormSq =
      (ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct)).re := by
  rw [sourceDiffNormSq, H78.sourceDiff_inner_self_expand]

/-- The weighted `S^ν`-sum occurring in Peterfalvi (7.8.a):
`Σ_{φ ∈ S} φ(1)/(e ‖φ‖²) · φ^ν`, where `S = T \ {Ind 1_H}` and
`e = ζ(1)` for the distinguished `ζ`. -/
noncomputable def weightedNuSum (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  ∑ i ∈ (Finset.univ.erase H78.ind1H),
    (H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
      H78.nu (H78.hyp76.zeta i)

/-- **Peterfalvi (7.8.a) target.**  The coherent images `S^ν` are orthogonal to
`1_G`, and `β` has the displayed decomposition
`β = 1_G - ζ^ν + a · Σ_{φ∈S} φ(1)/(e‖φ‖²) φ^ν + Γ`, with `a ∈ ℤ`
and `Γ` orthogonal to `S^ν ∪ {1_G}`.

This is a standalone target for the future proof of (7.8.a), not a field of
`Hypothesis78`; hence it does not add a new assumption to already-green results. -/
structure BetaDecomp (H78 : Hypothesis78 G A L) where
  /-- `S^ν ⊥ 1_G`. -/
  orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) (Hypothesis71.constOne G) = 0
  /-- The integer coefficient `a` in Peterfalvi (7.8.a). -/
  a : ℤ
  /-- The residual term `Γ`. -/
  Gamma : ClassFunction G ℂ
  /-- `Γ` is orthogonal to `S^ν`. -/
  Gamma_orth_nu : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner Gamma (H78.nu (H78.hyp76.zeta i)) = 0
  /-- `Γ` is orthogonal to `1_G`. -/
  Gamma_orth_one : ClassFunction.inner Gamma (Hypothesis71.constOne G) = 0
  /-- The displayed decomposition of `β`. -/
  beta_eq :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        (a : ℂ) • H78.weightedNuSum + Gamma

/-- Kernel order `h = |H|` for Peterfalvi (7.8.b). -/
noncomputable def kernelOrder (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card H78.hyp76.H

/-- Complement index `e = |L:H|` for Peterfalvi (7.8.b), stored as
`|L| / |H|` using the ambient normal-subgroup data. -/
noncomputable def complementIndex (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card L / Nat.card H78.hyp76.H

/-- The kernel order `h` is positive. -/
theorem kernelOrder_pos (H78 : Hypothesis78 G A L) : 0 < H78.kernelOrder := by
  rw [kernelOrder]
  exact Nat.card_pos

/-- The complement index `e = |L:H|` is positive. -/
theorem complementIndex_pos (H78 : Hypothesis78 G A L) : 0 < H78.complementIndex := by
  rw [complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.div_pos (Nat.le_of_dvd Nat.card_pos hdvd) Nat.card_pos

/-- Lagrange in the notation of (7.8.b): `h * e = |L|`. -/
theorem kernelOrder_mul_complementIndex_eq_card_L (H78 : Hypothesis78 G A L) :
    H78.kernelOrder * H78.complementIndex = Nat.card L := by
  rw [kernelOrder, complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.mul_div_cancel' hdvd

/-- Since `A = H#`, its cardinality is `h - 1`. -/
theorem card_A_eq_kernelOrder_sub_one (H78 : Hypothesis78 G A L) :
    Nat.card A = H78.kernelOrder - 1 := by
  conv_lhs => rw [H78.hyp76.A_eq_H_sharp]
  rw [kernelOrder, Nat.card_coe_set_eq]
  have hHcard : (H78.hyp76.H : Set G).ncard = Nat.card H78.hyp76.H := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1_mem : (1 : G) ∈ (H78.hyp76.H : Set G) := H78.hyp76.H.one_mem
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

/-- The local support ratio `|A|/|L|` in the `(h,e)` notation of (7.8.b). -/
theorem card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_complex
    (H78 : Hypothesis78 G A L) :
    (Nat.card A : ℂ) / (Nat.card L : ℂ) =
      ((H78.kernelOrder : ℂ) - 1) /
        ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) := by
  have hh1 : 1 ≤ H78.kernelOrder := Nat.succ_le_of_lt H78.kernelOrder_pos
  rw [H78.card_A_eq_kernelOrder_sub_one, ← H78.kernelOrder_mul_complementIndex_eq_card_L]
  norm_num [Nat.cast_sub hh1]

/-- Real-valued form of the local support ratio `|A|/|L| = (h-1)/(he)`. -/
theorem card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_real
    (H78 : Hypothesis78 G A L) :
    (Nat.card A : ℝ) / (Nat.card L : ℝ) =
      ((H78.kernelOrder : ℝ) - 1) /
        ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ)) := by
  have hh1 : 1 ≤ H78.kernelOrder := Nat.succ_le_of_lt H78.kernelOrder_pos
  rw [H78.card_A_eq_kernelOrder_sub_one, ← H78.kernelOrder_mul_complementIndex_eq_card_L]
  norm_num [Nat.cast_sub hh1]

/-- **Peterfalvi (7.8.b) source norm target.**  The remaining source-side
character computation for `‖β‖² = e + 1`, after the Dade-isometry bridge has
reduced the norm of `β` to `‖Ind 1_H - ζ‖²`.

This is standalone target data, not a field of `Hypothesis78`; completing it
requires evaluating the four source inner products isolated by
`sourceDiffNormSq_expand`. -/
structure SourceDiffNormEvaluation (H78 : Hypothesis78 G A L) : Prop where
  /-- `‖Ind 1_H - ζ‖² = e + 1`. -/
  sourceDiffNormSq_eq :
    H78.sourceDiffNormSq = (H78.complementIndex : ℝ) + 1

/-- Once the source-side norm computation is available, the beta norm identity
`‖β‖² = e + 1` follows from the Dade isometry. -/
theorem betaNormSq_eq_complementIndex_add_one (H78 : Hypothesis78 G A L)
    (hsrc : H78.SourceDiffNormEvaluation) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  rw [H78.betaNormSq_eq_sourceDiffNormSq, hsrc.sourceDiffNormSq_eq]

/-- The four source-side inner-product evaluations needed for
`‖Ind 1_H - ζ‖² = e + 1` imply `SourceDiffNormEvaluation`.

In the textbook proof these are the normal-subgroup character computations for
`Ind_H^L 1_H` and the chosen irreducible `ζ`: the induced principal character
has norm square `e`, it is orthogonal to `ζ` on both sides, and `ζ` has norm
one. -/
theorem sourceDiffNormEvaluation_of_inner_values (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation where
  sourceDiffNormSq_eq := by
    rw [H78.sourceDiffNormSq_expand, hind_norm, hzeta_ind, hind_zeta, hzeta_norm]
    simp

/-- Any indexed source character has norm one once it is known to be irreducible. -/
theorem zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)}
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
  simpa using
    (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L)
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L))

/-- The chosen non-principal `ζ` has norm one once it is known to be irreducible. -/
theorem zetaDistinct_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
  H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr

/-- Variant of `sourceDiffNormEvaluation_of_inner_values` using irreducibility of
the chosen `ζ` instead of a raw self-inner-product evaluation. -/
theorem sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_inner_values
    hind_norm hzeta_ind hind_zeta
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

/-- Variant using Hermitian symmetry: one orthogonality direction determines the other. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation := by
  refine H78.sourceDiffNormEvaluation_of_inner_values hind_norm hzeta_ind ?_ hzeta_norm
  rw [Hypothesis71.ClassFunction.inner_symm, hzeta_ind, star_zero]

/-- Variant using one orthogonality direction and irreducibility of the chosen `ζ`. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal
    hind_norm hzeta_ind
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

/-- Combined beta-norm form of `sourceDiffNormEvaluation_of_inner_values`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_inner_values
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_inner_values hind_norm hzeta_ind hind_zeta hzeta_norm)

/-- Combined beta-norm form using irreducibility of the chosen `ζ`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
      hind_norm hzeta_ind hind_zeta hzeta_irr)

/-- Combined beta-norm form using one orthogonality direction and irreducibility of `ζ`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hind_norm hzeta_ind hzeta_irr)

/-- The size hypothesis `e ≤ (h - 1) / 2`, written without division as
`2e + 1 ≤ h`. -/
noncomputable def smallIndex (H78 : Hypothesis78 G A L) : Prop :=
  2 * H78.complementIndex + 1 ≤ H78.kernelOrder

/-- Real-valued form of `smallIndex`, for the arithmetic in (7.8.b). -/
theorem smallIndex_real (H78 : Hypothesis78 G A L) (hsmall : H78.smallIndex) :
    2 * (H78.complementIndex : ℝ) + 1 ≤ (H78.kernelOrder : ℝ) := by
  rw [smallIndex] at hsmall
  exact_mod_cast hsmall

/-- The quadratic correction `u a² - 2 v a` in Peterfalvi (7.8.b), with
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
noncomputable def normQuadraticCorrection (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (1 / (H78.complementIndex : ℝ)) *
      (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
    2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ)

/-- The class function `(ζ^ν)^ρ` whose norm is estimated in Peterfalvi (7.8.b). -/
noncomputable def zetaNuRho (H78 : Hypothesis78 G A L) : ClassFunction L ℂ :=
  H78.hyp76.hyp71.chiRhoCF (H78.nu (H78.hyp76.zeta H78.zetaDistinct))

/-- The real norm square `‖(ζ^ν)^ρ‖²` from Peterfalvi (7.8.b). -/
noncomputable def zetaNuRhoNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re

/-- The real norm square `‖Γ‖²` from Peterfalvi (7.8.b). -/
noncomputable def gammaNormSq (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (ClassFunction.inner hBD.Gamma hBD.Gamma).re

/-- Arithmetic core of Peterfalvi (7.8.b): if `2e + 1 ≤ h`, then the
quadratic correction `u a² - 2 v a` is nonnegative for every integer `a`, where
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
lemma quadraticTerm_nonneg_of_smallIndex {e h : ℝ} (a : ℤ)
    (he : 0 < e) (hsmall : 2 * e + 1 ≤ h) :
    0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 - 2 * (1 / h) * (a : ℝ) := by
  have hh_pos : 0 < h := by linarith
  have he_ne : e ≠ 0 := ne_of_gt he
  have hh_ne : h ≠ 0 := ne_of_gt hh_pos
  have hsmall' : 2 * e ≤ h - 1 := by linarith
  have hu_eq : (1 / e) * (1 - 1 / h) = (h - 1) / (e * h) := by
    field_simp [he_ne, hh_ne]
  have hkey : 2 * (1 / h) ≤ (1 / e) * (1 - 1 / h) := by
    rw [hu_eq]
    rw [show 2 * (1 / h) = 2 / h by ring]
    rw [div_le_div_iff₀ hh_pos (mul_pos he hh_pos)]
    nlinarith
  have hv_nonneg : 0 ≤ 2 * (1 / h) := by
    rw [one_div]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hh_pos.le)
  have hu_nonneg : 0 ≤ (1 / e) * (1 - 1 / h) := le_trans hv_nonneg hkey
  by_cases ha_nonpos_int : a ≤ 0
  · have ha_nonpos : (a : ℝ) ≤ 0 := by exact_mod_cast ha_nonpos_int
    have hsq_nonneg : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg _
    have hterm1 : 0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 :=
      mul_nonneg hu_nonneg hsq_nonneg
    have hprod_nonpos : 2 * (1 / h) * (a : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv_nonneg ha_nonpos
    nlinarith
  · have ha_ge_one_int : 1 ≤ a := by omega
    have ha_ge_one : (1 : ℝ) ≤ a := by exact_mod_cast ha_ge_one_int
    have ha_nonneg : 0 ≤ (a : ℝ) := by linarith
    have ha_sq_ge : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    have hmul1 : 2 * (1 / h) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hkey ha_nonneg
    have hmul2 : ((1 / e) * (1 - 1 / h)) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left ha_sq_ge hu_nonneg
    nlinarith

/-- **Peterfalvi (7.8.b) target.**  Under `2e + 1 ≤ h`, the coherent
`ζ`-image satisfies `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`, and the residual term from
(7.8.a) satisfies `‖Γ‖² ≤ e - 1`.

As with `BetaDecomp`, this is a standalone future-proof target rather than a
new field of `Hypothesis78`. -/
structure NormEstimates (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : Prop where
  /-- `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`. -/
  zetaNuRho_norm_sq_ge :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq
  /-- `‖Γ‖² ≤ e - 1`. -/
  gamma_norm_sq_le :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1

/-- Raw class-function form of the `(ζ^ν)^ρ` lower bound supplied by
`NormEstimates`.  This is the input shape used by the later (7.5)/(7.10)
assembly, with `zetaNuRhoNormSq` unfolded. -/
theorem zetaNuRho_inner_self_re_ge_of_normEstimates
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hNE : H78.NormEstimates hBD) (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re := by
  simpa [zetaNuRhoNormSq] using hNE.zetaNuRho_norm_sq_ge hsmall

/-- Raw class-function form of the residual `Γ` upper bound supplied by
`NormEstimates`.  This is the `Γ` norm-bound shape consumed by the final
orthogonal-integer decomposition bridge for (7.10). -/
theorem gamma_inner_self_re_le_of_normEstimates
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hNE : H78.NormEstimates hBD) (hsmall : H78.smallIndex) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
      (H78.complementIndex : ℝ) - 1 := by
  simpa [gammaNormSq] using hNE.gamma_norm_sq_le hsmall

/-- Under `2e + 1 ≤ h`, Peterfalvi's quadratic correction is nonnegative. -/
theorem normQuadraticCorrection_nonneg_of_smallIndex
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.smallIndex → 0 ≤ H78.normQuadraticCorrection hBD := by
  intro hsmall
  rw [normQuadraticCorrection]
  have he : 0 < (H78.complementIndex : ℝ) := by
    exact_mod_cast H78.complementIndex_pos
  exact quadraticTerm_nonneg_of_smallIndex hBD.a he (H78.smallIndex_real hsmall)

/-- If `(ζ^ν)^ρ` has Peterfalvi's quadratic norm formula, its lower bound follows. -/
theorem zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq := by
  intro hsmall
  rw [hzeta]
  exact le_add_of_nonneg_left (H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall)

/-- If `Γ` has Peterfalvi's residual norm formula, its upper bound follows. -/
theorem gammaNormSq_le_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1 := by
  intro hsmall
  rw [hgamma]
  have hh_nonneg : 0 ≤ (H78.kernelOrder : ℝ) := by positivity
  have hquad := H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall
  have hprod : 0 ≤ (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
    mul_nonneg hh_nonneg hquad
  linarith

/-- Exact quadratic norm formulas are enough to package Peterfalvi (7.8.b)'s
`NormEstimates`.  This isolates the remaining character-theoretic work to proving
those two formulas from (7.7.b), `BetaDecomp`, and `‖β‖² = e + 1`. -/
theorem normEstimates_of_normQuadraticCorrection_eqs
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.NormEstimates hBD where
  zetaNuRho_norm_sq_ge :=
    H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD hzeta
  gamma_norm_sq_le :=
    H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD hgamma

/-- Once the orthogonal expansion of `‖β‖²` is known, the residual norm formula
for `Γ` is just the arithmetic rearrangement in Peterfalvi (7.8.b). -/
theorem gammaNormSq_eq_of_betaNormSq_expand
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hbetaNorm : H78.betaNormSq = (H78.complementIndex : ℝ) + 1)
    (hexpand : H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD := by
  have hh_ne : (H78.kernelOrder : ℝ) ≠ 0 := by
    exact_mod_cast H78.kernelOrder_pos.ne'
  have he_ne : (H78.complementIndex : ℝ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  rw [hbetaNorm] at hexpand
  have hquad :
      (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD =
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) := by
    rw [normQuadraticCorrection]
    field_simp [hh_ne, he_ne]
  rw [hquad]
  linarith

/-- The distinguished `νζ` is orthogonal to `1_G`, in the displayed direction. -/
theorem zetaImage_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (Hypothesis71.constOne G) = 0 :=
  hBD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `zetaImage_orth_one`. -/
theorem constOne_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G)
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.zetaImage_orth_one hBD, star_zero]

/-- The residual `Γ` is orthogonal to the distinguished `νζ`, in the displayed direction. -/
theorem gamma_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 :=
  hBD.Gamma_orth_nu H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `gamma_orth_zetaImage`. -/
theorem zetaImage_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.gamma_orth_zetaImage hBD, star_zero]

/-- Hermitian-symmetric form of `BetaDecomp.Gamma_orth_one`. -/
theorem constOne_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_one, star_zero]

/-- Each coherent image in `S^ν` is orthogonal to `Γ`, in the opposite direction. -/
theorem nu_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (i : Fin (H78.hyp76.n + 1)) (hi : i ≠ H78.ind1H) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_nu i hi, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to `1_G`. -/
theorem weightedNuSum_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum (Hypothesis71.constOne G) = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, hBD.orth_one i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_one`. -/
theorem constOne_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_one hBD, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to the residual `Γ`. -/
theorem weightedNuSum_orth_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum hBD.Gamma = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, H78.nu_orth_gamma hBD i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_gamma`. -/
theorem gamma_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_gamma hBD, star_zero]

/-- `BetaDecomp` identifies the (7.9) residual `Δ` with the weighted part plus
`Γ`. -/
theorem delta_eq_weightedNuSum_add_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.delta = (hBD.a : ℂ) • H78.weightedNuSum + hBD.Gamma := by
  rw [delta, hBD.beta_eq]
  abel

/-- The residual `Δ` is orthogonal to `1_G`. -/
theorem delta_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.delta (Hypothesis71.constOne G) = 0 := by
  rw [H78.delta_eq_weightedNuSum_add_gamma hBD, ClassFunction.inner_add_left,
    ClassFunction.inner_smul_left, H78.weightedNuSum_orth_one hBD,
    hBD.Gamma_orth_one, mul_zero, add_zero]

/-- Hermitian-symmetric form of `delta_orth_one`. -/
theorem constOne_orth_delta (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.delta = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.delta_orth_one hBD, star_zero]

/-- Orthogonal expansion of the beta decomposition in Peterfalvi (7.8.a).

After the remaining source-side computation of `‖Σ‖² = (h - 1)/e`, the displayed
decomposition of `β` gives the real norm formula used in (7.8.b). -/
theorem betaNormSq_eq_of_weightedNuSum_norm
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_zeta :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_norm :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  have hzeta_weighted :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        H78.weightedNuSum = 1 := by
    rw [Hypothesis71.ClassFunction.inner_symm, hweighted_zeta, star_one]
  have hinner :
      ClassFunction.inner H78.beta H78.beta =
        2 +
          (hBD.a : ℂ) * (hBD.a : ℂ) *
            ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) -
          2 * (hBD.a : ℂ) +
          ClassFunction.inner hBD.Gamma hBD.Gamma := by
    rw [hBD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      Hypothesis71.constOne_inner_self_eq_one, H78.zetaImage_orth_one hBD,
      H78.constOne_orth_zetaImage hBD, H78.weightedNuSum_orth_one hBD,
      H78.constOne_orth_weightedNuSum hBD, hBD.Gamma_orth_one,
      H78.constOne_orth_gamma hBD, H78.gamma_orth_zetaImage hBD,
      H78.zetaImage_orth_gamma hBD, H78.weightedNuSum_orth_gamma hBD,
      H78.gamma_orth_weightedNuSum hBD, hzeta_norm, hweighted_zeta, hzeta_weighted,
      hweighted_norm, star_intCast, mul_zero, add_zero, sub_zero, zero_add]
    ring
  rw [betaNormSq, hinner, gammaNormSq]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` does. -/
theorem nu_zeta_inner_self_eq_one (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 := by
  rw [H78.nu_isometry i i hi hi, hzeta_norm]

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` is irreducible. -/
theorem nu_zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 :=
  H78.nu_zeta_inner_self_eq_one hi
    (H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr)

/-- The distinguished image `νζ` has norm one once the source `ζ` has norm one. -/
theorem zetaImage_inner_self_eq_one (H78 : Hypothesis78 G A L)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.nu_zeta_inner_self_eq_one H78.zetaDistinct_ne_ind1H hzeta_norm

/-- The source irreducibility of the distinguished `ζ` gives `‖νζ‖² = 1`. -/
theorem zetaImage_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.nu_zeta_inner_self_eq_one_of_irreducible H78.zetaDistinct_ne_ind1H hzeta_irr

/-- Coherence makes an indexed image `νζᵢ` a signed irreducible character once
the source `ζᵢ` is irreducible.  This records exactly the sign ambiguity left by
the virtual-character norm-one criterion. -/
theorem exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta i) = ε • (ξ : ClassFunction G ℂ) :=
  OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
    (H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu hi)
    (H78.nu_zeta_inner_self_eq_one_of_irreducible hi hzeta_irr)

/-- Distinguished-`ζ` specialization of the signed image criterion. -/
theorem exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta H78.zetaDistinct) = ε • (ξ : ClassFunction G ℂ) :=
  H78.exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent hcoh hnu
    H78.zetaDistinct_ne_ind1H hzeta_irr

/-- If the coherent image `νζᵢ` has positive degree, the signed ambiguity collapses
and `νζᵢ` is an irreducible character. -/
theorem nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hpos : ∃ d : ℕ, 0 < d ∧
      (H78.nu (H78.hyp76.zeta i) : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta i)) :=
  OddOrder.RepresentationTheory.isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos
    (H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu hi)
    (H78.nu_zeta_inner_self_eq_one_of_irreducible hi hzeta_irr)
    hpos

/-- Distinguished-`ζ` specialization of the positive-degree image criterion. -/
theorem zetaImage_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hpos : ∃ d : ℕ, 0 < d ∧
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct) : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) :=
  H78.nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos hcoh hnu
    H78.zetaDistinct_ne_ind1H hzeta_irr hpos

/-- Irreducibility and distinctness of the source `S`-family give its
orthogonality matrix. -/
theorem sourceZeta_orthogonal_of_irreducible_distinct (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta i, hirr i hi⟩
    let ψ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta j, hirr j hj⟩
    have hne : χ ≠ ψ := by
      intro hχψ
      exact hdistinct i hi j hj hij (congrArg
        (fun θ : OddOrder.RepresentationTheory.IrreducibleCharacter L =>
          (θ : ClassFunction L ℂ)) hχψ)
    simpa [χ, ψ, hne] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ ψ)

/-- Natural distinguished-column form of the source `S` orthogonality matrix. -/
theorem sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
    (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i)
        (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0 := by
  intro i hi
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  have horth := H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct
  have hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
    H78.zetaDistinct_inner_self_eq_one_of_irreducible
      (hirr H78.zetaDistinct hzeta_mem)
  rw [horth i hi H78.zetaDistinct hzeta_mem]
  by_cases hiz : i = H78.zetaDistinct
  · subst i
    rw [if_pos rfl, if_pos rfl]
    exact hzeta_norm
  · simp [hiz]

/-- Irreducibility of the source `S`-family makes every source norm nonzero. -/
theorem sourceZeta_norm_ne_of_irreducible (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
  intro i hi
  let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
    ⟨H78.hyp76.zeta i, hirr i hi⟩
  have hχ : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
    simpa [χ] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ χ)
  rw [hχ]
  norm_num

/-- If the source `ζ_i` are orthogonal to the distinguished `ζ`, the weighted
`S^ν`-sum has inner product `1` with `νζ`.

This is the coefficient computation in Peterfalvi (7.8.a) that feeds the
`(β, ζ^ν) = a - 1` identity used in (7.8.b). -/
theorem weightedNuSum_inner_zetaImage_eq_one (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0)
    (hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0) :
    ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  rw [weightedNuSum, ← hs, inner_sum_left]
  have hsum :
      (∑ i ∈ s,
        ClassFunction.inner
          ((H78.hyp76.zeta i (1 : L) /
            (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
              ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
            H78.nu (H78.hyp76.zeta i))
          (H78.nu (H78.hyp76.zeta H78.zetaDistinct))) =
        ∑ i ∈ s,
          if i = H78.zetaDistinct then
            H78.hyp76.zeta i (1 : L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
                ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
          else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left,
      H78.nu_isometry i H78.zetaDistinct (Finset.ne_of_mem_erase (hs ▸ hi))
        H78.zetaDistinct_ne_ind1H, horth i hi]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, mul_one]
    · rw [if_neg hiz, if_neg hiz, mul_zero]
  rw [hsum, Finset.sum_ite_eq' s H78.zetaDistinct
    (fun i =>
      H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))),
    if_pos hzeta_mem, horth H78.zetaDistinct hzeta_mem]
  rw [if_pos rfl]
  field_simp [hzeta_one_ne_zero]

/-- Natural source-data version of `weightedNuSum_inner_zetaImage_eq_one`. -/
theorem weightedNuSum_inner_zetaImage_eq_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.weightedNuSum_inner_zetaImage_eq_one
    (H78.sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
      hirr hdistinct)
    (by
      rw [hzeta_degree]
      exact_mod_cast H78.complementIndex_pos.ne')

/-- Source orthogonality and the Burnside degree sum evaluate the norm of the
weighted `S^ν`-sum in Peterfalvi (7.8.a).

This is the source-side computation of `‖Σ‖² = (h - 1) / e`: after `ν` transports
orthogonality from `L` to `G`, only diagonal terms remain, and the degree sum
collapses to the non-principal part of the kernel. -/
theorem weightedNuSum_inner_self_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
      ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  let coeff : Fin (H78.hyp76.n + 1) → ℂ := fun i =>
    H78.hyp76.zeta i (1 : L) /
      (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
  have he_ne : (H78.complementIndex : ℂ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  have hinner :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ∑ i ∈ s, ∑ j ∈ s,
          coeff i * star (coeff j) *
            ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
              (H78.nu (H78.hyp76.zeta j)) := by
    rw [weightedNuSum, ← hs]
    change ClassFunction.inner
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i))
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i)) = _
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    ring
  have hcollapse :
      (∑ i ∈ s, ∑ j ∈ s,
        coeff i * star (coeff j) *
          ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
            (H78.nu (H78.hyp76.zeta j))) =
        ∑ i ∈ s,
          coeff i * star (coeff i) *
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hine : i ≠ H78.ind1H := Finset.ne_of_mem_erase (hs ▸ hi)
    rw [Finset.sum_eq_single i]
    · rw [H78.nu_isometry i i hine hine,
        horth i (by simpa [hs] using hi) i (by simpa [hs] using hi), if_pos rfl]
    · intro j hj hji
      rw [H78.nu_isometry i j hine (Finset.ne_of_mem_erase (hs ▸ hj)),
        horth i (by simpa [hs] using hi) j (by simpa [hs] using hj),
        if_neg (Ne.symm hji), mul_zero]
    · intro hnot
      exact False.elim (hnot hi)
  have hdiag :
      (∑ i ∈ s,
        coeff i * star (coeff i) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) /
          (H78.complementIndex : ℂ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn_star :
        star (ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) :=
      Hypothesis71.ClassFunction.star_inner_self _
    have hn_ne : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 :=
      hnorm_ne i (by simpa [hs] using hi)
    simp only [coeff, hzeta_degree]
    rw [star_div₀, star_mul', hn_star]
    simp only [star_natCast]
    field_simp [he_ne, hn_ne]
  rw [hinner, hcollapse, hdiag, show
      (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) from by
        simpa [hs] using hdegree_sum]
  field_simp [he_ne]
  norm_num [Complex.ofReal_div, Complex.ofReal_sub]
  ring

/-- Source orthogonality and the kernel degree sum give the full orthogonal
expansion of `‖β‖²` in Peterfalvi (7.8.b). -/
theorem betaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  have hzeta_src_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
    H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr
  have horth_zeta : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0 := by
    intro i hi
    have hi_s : i ∈ s := by simpa [hs] using hi
    rw [horth i hi H78.zetaDistinct (by simpa [hs] using hzeta_mem)]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, hiz, hzeta_src_norm]
    · rw [if_neg hiz, if_neg hiz]
  have hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0 := by
    rw [hzeta_degree]
    exact_mod_cast H78.complementIndex_pos.ne'
  exact H78.betaNormSq_eq_of_weightedNuSum_norm hBD
    (H78.zetaImage_inner_self_eq_one hzeta_src_norm)
    (H78.weightedNuSum_inner_zetaImage_eq_one horth_zeta hzeta_one_ne_zero)
    (H78.weightedNuSum_inner_self_eq_of_source_orthogonal
      horth hnorm_ne hzeta_degree hdegree_sum)

/-- Source-side beta norm data give Peterfalvi's residual norm formula for `Γ`. -/
theorem gammaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
  H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (H78.betaNormSq_eq_complementIndex_add_one hsrc)
    (H78.betaNormSq_eq_of_source_orthogonal hBD
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Once the remaining `(ζ^ν)^ρ` quadratic formula is supplied, the source-side
beta norm data package Peterfalvi (7.8.b)'s `NormEstimates`. -/
theorem normEstimates_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_normQuadraticCorrection_eqs hBD hzeta
    (H78.gammaNormSq_eq_of_source_orthogonal hBD hsrc
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Textbook `u,v,w` form of the `(ζ^ν)^ρ` norm rewrites to the internal
`normQuadraticCorrection + (1 - e / h)` form.

This is the arithmetic bridge from the (7.7.b) double-sum evaluation in
Peterfalvi (7.8.b), where
`u = (1/e)(1 - 1/h)`, `v = 1/h`, and `w = 1 - e/h`. -/
theorem zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) := by
  rw [hzeta, normQuadraticCorrection]

/-- Source-side beta norm data plus the textbook `u,v,w` formula package
Peterfalvi (7.8.b)'s `NormEstimates`.

The remaining character-theoretic input is now exactly the (7.7.b) evaluation
of `‖(ζ^ν)^ρ‖²` in `u,v,w` form; this theorem performs the API conversion and
reuses the already proved source-side `Γ` norm formula. -/
theorem normEstimates_of_source_orthogonal_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_source_orthogonal hBD hsrc
    horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr
    (H78.zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula hBD hzeta_uv)

/-- Version of `normEstimates_of_source_orthogonal` using the natural source
hypotheses that the `S`-family consists of distinct irreducible characters. -/
theorem normEstimates_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_source_orthogonal hBD hsrc
    (H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct)
    (H78.sourceZeta_norm_ne_of_irreducible hirr)
    hzeta_degree hdegree_sum (hirr H78.zetaDistinct hzeta_mem) hzeta

/-- Source irreducibility data plus the textbook `u,v,w` formula give
Peterfalvi (7.8.b)'s `NormEstimates`.

This is the natural source-data version of
`normEstimates_of_source_orthogonal_and_uv_formula`: it converts the `u,v,w`
formula to the internal quadratic-correction API and derives the source
orthogonality matrix from irreducibility and distinctness. -/
theorem normEstimates_of_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_irreducible_source_data hBD hsrc hirr hdistinct
    hzeta_degree hdegree_sum
    (H78.zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula hBD hzeta_uv)

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give Peterfalvi (7.8.b)'s `NormEstimates`.

This removes the standalone `SourceDiffNormEvaluation` premise by using the
already isolated source computation
`‖Ind 1_H - ζ‖² = e + 1` from the three source-side inputs
`⟨Ind1H,Ind1H⟩ = e`, `⟨ζ,Ind1H⟩ = 0`, and irreducibility of `ζ`. -/
theorem normEstimates_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_irreducible_source_data_and_uv_formula hBD
    (H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hind_norm hzeta_ind (hirr H78.zetaDistinct hzeta_mem))
    hirr hdistinct hzeta_degree hdegree_sum hzeta_uv

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give the raw `(ζ^ν)^ρ` lower bound used downstream. -/
theorem zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re :=
  H78.zetaNuRho_inner_self_re_ge_of_normEstimates hBD
    (H78.normEstimates_of_inner_values_irreducible_source_data_and_uv_formula hBD
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv)
    hsmall

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give the raw `Γ` norm-bound consumed by the (7.10)
orthogonal-integer decomposition bridge. -/
theorem gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
      (H78.complementIndex : ℝ) - 1 :=
  H78.gamma_inner_self_re_le_of_normEstimates hBD
    (H78.normEstimates_of_inner_values_irreducible_source_data_and_uv_formula hBD
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv)
    hsmall

/-- With the weighted-sum coefficient normalized, `BetaDecomp` gives
`(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one_of_weighted
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzetaImage_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 := by
  rw [hBD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    H78.constOne_orth_zetaImage hBD, hzetaImage_norm, hweighted,
    H78.gamma_orth_zetaImage hBD]
  ring

/-- Source-side orthogonality plus source irreducibility gives the coefficient
identity `(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0)
    (hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 :=
  H78.beta_inner_zetaImage_eq_int_sub_one_of_weighted hBD
    (H78.zetaImage_inner_self_eq_one_of_irreducible hzeta_irr)
    (H78.weightedNuSum_inner_zetaImage_eq_one horth hzeta_one_ne_zero)

/-- Natural source-data version of `(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 :=
  H78.beta_inner_zetaImage_eq_int_sub_one hBD
    (H78.sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
      hirr hdistinct)
    (by
      rw [hzeta_degree]
      exact_mod_cast H78.complementIndex_pos.ne')
    (hirr H78.zetaDistinct (by simp [H78.zetaDistinct_ne_ind1H]))

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

/-- Specialization of (7.8.c.ii) to the distinguished image `νζ`. -/
theorem zetaNuRhoNormSq_eq_card_ratio_mul (H78 : Hypothesis78 G A L)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0) :
    H78.zetaNuRhoNormSq =
      (((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) *
          star (ClassFunction.inner H78.beta
            (H78.nu (H78.hyp76.zeta H78.zetaDistinct))))).re := by
  rw [zetaNuRhoNormSq, zetaNuRho]
  exact congrArg Complex.re (H78.chiRho_norm_sq_eq_card_ratio_mul
    (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) hnu_irr hnu_orth)

/-- Combined (7.8.b) bridge: after the coefficient computation
`(β, ζ^ν) = a - 1`, the norm of `(ζ^ν)^ρ` is the card-ratio multiple of
`(a - 1)^2`. -/
theorem zetaNuRhoNormSq_eq_card_ratio_mul_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hbeta :
      ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
        (hBD.a : ℂ) - 1) :
    H78.zetaNuRhoNormSq =
      (((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1))).re := by
  rw [H78.zetaNuRhoNormSq_eq_card_ratio_mul hnu_irr hnu_orth, hbeta]
  rw [show star ((hBD.a : ℂ) - 1) = (hBD.a : ℂ) - 1 by simp]

/-- The same `(ζ^ν)^ρ` norm formula with `|A|/|L|` rewritten as `(h-1)/(he)`. -/
theorem zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hbeta :
      ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
        (hBD.a : ℂ) - 1) :
    H78.zetaNuRhoNormSq =
      (((H78.kernelOrder : ℝ) - 1) /
          ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) := by
  rw [H78.zetaNuRhoNormSq_eq_card_ratio_mul_int_sub_one hBD hnu_irr hnu_orth hbeta]
  rw [H78.card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_complex]
  let r : ℝ :=
    ((H78.kernelOrder : ℝ) - 1) /
      ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ)) *
    (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1))
  have hprodCast :
      ((H78.kernelOrder : ℂ) - 1) /
            ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) *
          (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1)) = (r : ℂ) := by
    norm_num [r, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  change
    (((H78.kernelOrder : ℂ) - 1) /
          ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) *
        (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1))).re = r
  exact (congrArg Complex.re hprodCast).trans (Complex.ofReal_re r)

/-- **Peterfalvi (7.8.c.ii).** Source-data bridge for the `(ζ^ν)^ρ` norm
formula.  The source irreducibility/distinctness data supplies the coefficient
`(β, ζ^ν) = a - 1`, while irreducibility and orthogonality of the image
`νζ` remain explicit inputs to the character-ρ norm formula. -/
theorem zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    H78.zetaNuRhoNormSq =
      (((H78.kernelOrder : ℝ) - 1) /
          ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) :=
  H78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one hBD hnu_irr hnu_orth
    (H78.beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data
      hBD hirr hdistinct hzeta_degree)

end Hypothesis78

end Section_7_8

section Section_7_9

/-! ### (7.9): two-family non-orthogonality

Peterfalvi (7.9) is the final two-family character-theoretic input used in the
proof of (7.10).  The proof combines (7.8.a), (5.9), odd-order non-realness
(1.1), and the cross-family disjointness of Dade supports.  Here we name the
faithful hypothesis bundle and conclusion predicate, without adding it as a new
assumption to the group-theoretic `(7.10)` theorem. -/

/-- **Peterfalvi (7.9) hypothesis interface.**  Two instances of the (7.8)
coherence/norm setup over the same odd-order group, with disjoint Dade supports
`A₁^{τ₁}` and `A₂^{τ₂}` as in Hypothesis (7.4) for `I = {1,2}`. -/
structure Hypothesis79 (G : Type*) [Group G] [Fintype G]
    (A₁ : Set G) (L₁ : Subgroup G) [Fintype L₁]
    [Invertible (Nat.card L₁ : ℂ)]
    (A₂ : Set G) (L₂ : Subgroup G) [Fintype L₂]
    [Invertible (Nat.card L₂ : ℂ)]
    [Invertible (Nat.card G : ℂ)] where
  /-- The ambient group has odd order. -/
  odd_card : Odd (Nat.card G)
  /-- The first coherent normal-subgroup setup. -/
  first : Hypothesis78 G A₁ L₁
  /-- The second coherent normal-subgroup setup. -/
  second : Hypothesis78 G A₂ L₂
  /-- The Dade supports `A₁^{τ₁}` and `A₂^{τ₂}` are disjoint. -/
  dadeSupport_disjoint :
    Disjoint first.hyp76.hyp71.hyp.dadeSupport second.hyp76.hyp71.hyp.dadeSupport

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]
variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]
variable [Invertible (Nat.card L₁ : ℂ)]
variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]
variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The image `ζ₁^{ν₁}` of the distinguished first `ζ`. -/
noncomputable def firstZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct)

/-- The image `ζ₂^{ν₂}` of the distinguished second `ζ`. -/
noncomputable def secondZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)

/-- Coherence supplies virtual-character membership for the two distinguished
`ζ` images used in (7.9). -/
theorem zetaImages_mem_ZIrr_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension) :
    H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  constructor
  · simpa [firstZetaImage] using
      H79.first.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₁ hnu₁
  · simpa [secondZetaImage] using
      H79.second.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₂ hnu₂

/-- Coherence plus virtual `Ind 1_H` sources package the four virtual-character
memberships used by the residual cross-term consumers. -/
theorem delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    H79.first.delta ∈ ZIrr G ∧ H79.second.delta ∈ ZIrr G ∧
      H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  have hδ₁ : H79.first.delta ∈ ZIrr G :=
    H79.first.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hind₁Z hzeta₁_irr
  have hδ₂ : H79.second.delta ∈ ZIrr G :=
    H79.second.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₂ hnu₂ hind₂Z hzeta₂_irr
  obtain ⟨hζ₁, hζ₂⟩ := H79.zetaImages_mem_ZIrr_of_isCoherent hcoh₁ hnu₁ hcoh₂ hnu₂
  exact ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩

/-- **Peterfalvi (7.9) conclusion.**  The two cross inner products cannot both
vanish: `(β₁, ζ₂^{ν₂}) ≠ 0` or `(β₂, ζ₁^{ν₁}) ≠ 0`. -/
def conclusion (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) : Prop :=
  ClassFunction.inner H79.first.beta H79.secondZetaImage ≠ 0 ∨
    ClassFunction.inner H79.second.beta H79.firstZetaImage ≠ 0

/-- Swapping the two families preserves the (7.9) hypothesis interface. -/
def swap (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    Hypothesis79 G A₂ L₂ A₁ L₁ where
  odd_card := H79.odd_card
  first := H79.second
  second := H79.first
  dadeSupport_disjoint := H79.dadeSupport_disjoint.symm

/-- The (7.9) conclusion is symmetric in the two families. -/
theorem conclusion_swap (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    H79.swap.conclusion ↔ H79.conclusion := by
  simp [conclusion, swap, firstZetaImage, secondZetaImage, or_comm]

/-- The two `β` functions are orthogonal when their Dade supports are disjoint. -/
theorem beta_inner_beta_eq_zero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction.inner H79.first.beta H79.second.beta = 0 := by
  have hdisj : Disjoint H79.first.beta.support H79.second.beta.support := by
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint
      (H79.first.beta_support_subset_dadeSupport hg₁)
      (H79.second.beta_support_subset_dadeSupport hg₂)
  exact ClassFunction.inner_eq_zero_of_disjoint_support hdisj

/-- If the two distinguished coherent images are supported in the corresponding
disjoint Dade supports, their cross inner product vanishes. -/
theorem zetaImage_cross_eq_zero_of_support_subset
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hζ₁_supp : H79.firstZetaImage.support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hζ₂_supp : H79.secondZetaImage.support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by
  have hdisj : Disjoint H79.firstZetaImage.support H79.secondZetaImage.support := by
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint (hζ₁_supp hg₁) (hζ₂_supp hg₂)
  exact ClassFunction.inner_eq_zero_of_disjoint_support hdisj

/-- Expanding `β₁ = 1_G - ζ₁^ν + Δ₁` and `β₂ = 1_G - ζ₂^ν + Δ₂`
gives the displayed algebraic identity used in Peterfalvi (7.9). -/
theorem beta_inner_beta_expand_delta (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    ClassFunction.inner H79.first.beta H79.second.beta =
      1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  have hzeta_cross' :
      ClassFunction.inner
        (H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct))
        (H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)) = 0 := by
    simpa [firstZetaImage, secondZetaImage] using hzeta_cross
  rw [H79.first.beta_eq_constOne_sub_zetaImage_add_delta,
    H79.second.beta_eq_constOne_sub_zetaImage_add_delta]
  simp only [firstZetaImage, secondZetaImage, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right]
  rw [Hypothesis71.constOne_inner_self_eq_one,
    H79.second.constOne_orth_zetaImage hBD₂,
    H79.second.constOne_orth_delta hBD₂,
    H79.first.zetaImage_orth_one hBD₁,
    H79.first.delta_orth_one hBD₁,
    hzeta_cross']
  ring

/-- The support and `ζ`-orthogonality inputs reduce Peterfalvi (7.9) to the
parity/nonzero statement for the two residual cross terms. -/
theorem delta_cross_equation (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    0 = 1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  rw [← H79.beta_inner_beta_expand_delta hBD₁ hBD₂ hzeta_cross,
    H79.beta_inner_beta_eq_zero]

/-- If one of the residual cross terms is nonzero, then the original (7.9)
non-orthogonality conclusion follows. -/
theorem conclusion_of_delta_cross_nonzero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta : ClassFunction.inner H79.first.delta H79.secondZetaImage ≠ 0 ∨
      ClassFunction.inner H79.firstZetaImage H79.second.delta ≠ 0) :
    H79.conclusion := by
  rcases hdelta with hdelta | hdelta
  · left
    rw [H79.first.beta_inner_eq_delta_inner_of_orthogonal H79.secondZetaImage
      (H79.second.constOne_orth_zetaImage hBD₂) hzeta_cross]
    exact hdelta
  · right
    have hleft : ClassFunction.inner H79.firstZetaImage H79.second.beta ≠ 0 := by
      rw [H79.second.inner_beta_eq_inner_delta_of_orthogonal H79.firstZetaImage
        (H79.first.zetaImage_orth_one hBD₁) hzeta_cross]
      exact hdelta
    intro hzero
    apply hleft
    rw [Hypothesis71.ClassFunction.inner_symm H79.second.beta H79.firstZetaImage,
      hzero, star_zero]

/-- Virtual-character residuals make the three residual cross terms integral. -/
theorem delta_cross_integral_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) := by
  exact ⟨ClassFunction.inner_mem_ZIrr_int hδ₁ hζ₂,
    ClassFunction.inner_mem_ZIrr_int hζ₁ hδ₂,
    ClassFunction.inner_mem_ZIrr_int hδ₁ hδ₂⟩

/-- Coherence, virtual `Ind 1_H` sources, and irreducible distinguished source
terms make the three residual cross terms integral. -/
theorem delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) := by
  obtain ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  exact H79.delta_cross_integral_of_ZIrr hδ₁ hδ₂ hζ₁ hζ₂

/-- Coherence and source irreducibility make the three residual cross terms integral. -/
theorem delta_cross_integral_of_irreducible_sourceDiff_and_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.ind1H))
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.ind1H))
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) :=
  H79.delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁_irr.mem_ZIrr hzeta₁_irr
    hind₂_irr.mem_ZIrr hzeta₂_irr

/-- Integer-parity form of the last step of Peterfalvi (7.9): once the two
residual cross terms are integers and `(Δ₁,Δ₂)` is an even integer, the displayed
`0 = 1 - ... + ...` equation forces one cross term to be nonzero. -/
theorem conclusion_of_delta_cross_integral_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hx : ∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ))
    (hy : ∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ))
    (hz : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  rcases hx with ⟨x, hx⟩
  rcases hy with ⟨y, hy⟩
  rcases hz with ⟨z, hz, hz_even⟩
  have heqC := H79.delta_cross_equation hBD₁ hBD₂ hzeta_cross
  rw [hx, hy, hz] at heqC
  have heqZ : (0 : ℤ) = 1 - y - x + z := by
    have hcast : ((0 : ℤ) : ℂ) = ((1 - y - x + z : ℤ) : ℂ) := by
      simpa [Int.cast_sub, Int.cast_add] using heqC
    exact_mod_cast hcast
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hnot
    push Not at hnot
    rcases hz_even with ⟨t, ht⟩
    omega
  apply H79.conclusion_of_delta_cross_nonzero hBD₁ hBD₂ hzeta_cross
  rcases hnonzero with hx_ne | hy_ne
  · left
    rw [hx]
    exact_mod_cast hx_ne
  · right
    rw [hy]
    exact_mod_cast hy_ne

/-- Virtual-character inputs supply the two integer cross terms needed by the
parity form of Peterfalvi (7.9). -/
theorem conclusion_of_delta_cross_even_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hx, hy, _hz⟩ := H79.delta_cross_integral_of_ZIrr hδ₁ hδ₂ hζ₁ hζ₂
  exact H79.conclusion_of_delta_cross_integral_parity hBD₁ hBD₂ hzeta_cross hx hy
    hdelta_even

/-- Coherence, virtual `Ind 1_H` sources, and irreducible distinguished source
terms supply the integer cross terms needed by the parity form of Peterfalvi
(7.9). -/
theorem conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  exact H79.conclusion_of_delta_cross_even_of_ZIrr hBD₁ hBD₂ hzeta_cross hδ₁ hδ₂
    hζ₁ hζ₂ hdelta_even

/-- Support-subset form of the weak parity consumer: the `ζ^ν` cross
orthogonality is obtained from disjoint Dade supports. -/
theorem conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity_of_zeta_support
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hζ₁_supp : H79.firstZetaImage.support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hζ₂_supp : H79.secondZetaImage.support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion :=
  H79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr hBD₁ hBD₂
    (H79.zetaImage_cross_eq_zero_of_support_subset hζ₁_supp hζ₂_supp) hdelta_even

/-- Coherence and source irreducibility supply the integer cross terms needed by
the parity form of Peterfalvi (7.9). -/
theorem conclusion_of_irreducible_sourceDiff_and_isCoherent_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.ind1H))
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.ind1H))
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion :=
  H79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁_irr.mem_ZIrr hzeta₁_irr
    hind₂_irr.mem_ZIrr hzeta₂_irr hBD₁ hBD₂ hzeta_cross hdelta_even

end Hypothesis79

end Section_7_9

section OrthogonalIntegerDecomposition

variable {ι : Type*}
variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Integer-coefficient Pythagoras bridge used in Peterfalvi (7.10): if a class
function decomposes as an orthogonal integer combination plus an orthogonal
residual, then an upper bound on its norm bounds the sum of the diagonal weights
for every nonzero coefficient. -/
theorem sum_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℝ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℝ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ M) :
    (∑ i ∈ B, m i) ≤ M := by
  classical
  have hpyth := inner_self_orthogonalSum_add_re (G := G) B v
    (fun i => (x i : ℝ)) m Γ₁ horth hΓ₁
  have hΓ_norm : (ClassFunction.inner Γ Γ).re =
      (∑ i ∈ B, (x i : ℝ) ^ 2 * m i) +
        (ClassFunction.inner Γ₁ Γ₁).re := by
    rw [hΓ]
    exact hpyth
  have hsum_le_sq : (∑ i ∈ B, m i) ≤
      ∑ i ∈ B, (x i : ℝ) ^ 2 * m i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hcases : x i ≤ -1 ∨ 1 ≤ x i := by
      have hxi := hx_nonzero i hi
      omega
    have hx_sq : (1 : ℝ) ≤ (x i : ℝ) ^ 2 := by
      rcases hcases with hle | hge
      · have hle' : (x i : ℝ) ≤ -1 := by exact_mod_cast hle
        nlinarith
      · have hge' : (1 : ℝ) ≤ x i := by exact_mod_cast hge
        nlinarith
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx_sq (hm_nonneg i hi)
  have hΓ₁_nonneg : 0 ≤ (ClassFunction.inner Γ₁ Γ₁).re :=
    inner_self_re_nonneg Γ₁
  rw [hΓ_norm] at hΓ_bound
  linarith

open scoped Classical in
/-- Rational-valued version of the integer-coefficient Pythagoras bridge.  This
matches the `𝓑`-sum in Peterfalvi (7.10), whose weights are rational ratios such
as `(h_j - 1) / e_j`, while the norm inequality lives in `ℝ`. -/
theorem sum_rat_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℚ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℚ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ)) :
    (∑ i ∈ B, m i) ≤ M := by
  have horth_real : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) =
        if i = j then (((m i : ℝ) : ℂ)) else 0 := by
    intro i hi j hj
    simpa using horth i hi j hj
  have hm_nonneg_real : ∀ i ∈ B, 0 ≤ (m i : ℝ) := by
    intro i hi
    exact_mod_cast hm_nonneg i hi
  have hreal := sum_weights_le_of_orthogonal_integer_decomposition
    B v x (fun i => (m i : ℝ)) Γ Γ₁ (M : ℝ) hΓ horth_real hΓ₁ hm_nonneg_real
    hx_nonzero hΓ_bound
  have hcast : ((∑ i ∈ B, m i) : ℝ) ≤ (M : ℝ) := by
    simpa using hreal
  exact_mod_cast hcast

end OrthogonalIntegerDecomposition

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

open scoped Classical in
/-- The identity contribution in Peterfalvi (7.10): since `1 ∈ G₀`, any class
function with `1 ≤ |χ(1)|²` contributes at least `1` to the `G₀` norm sum. -/
lemma one_le_G0_norm_sum_of_one_le_norm_one [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ)
    (hone : (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  classical
  have hmem : (1 : G) ∈ Finset.univ.filter (fun g : G => g ∈ F.G0) := by
    simp [F.one_mem_G0]
  exact hone.trans
    (Finset.single_le_sum (f := fun g : G => ‖(χ : G → ℂ) g‖ ^ 2)
      (fun g _ => sq_nonneg _) hmem)

/-- A signed irreducible character has `|χ(1)|² ≥ 1`.  This is the numerical
content behind the `χ₁(1)^2` term in Peterfalvi (7.10). -/
lemma one_le_norm_sq_apply_one_of_signed_irreducible
    (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1) :
    (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2 := by
  obtain ⟨d, hdpos, hd⟩ :=
    OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [hχ_one, hd]
  rcases hε with rfl | rfl
  · rw [Int.cast_one, one_mul, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul, norm_neg, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith

open scoped Classical in
/-- Signed-irreducible form of the `G₀` identity contribution used in (7.10). -/
lemma one_le_G0_norm_sum_of_signed_irreducible [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ : χ = ε • (ξ : ClassFunction G ℂ)) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  have hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1 := by
    rw [hχ, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ClassFunction.smul_apply]
  exact F.one_le_G0_norm_sum_of_one_le_norm_one χ
    (one_le_norm_sq_apply_one_of_signed_irreducible χ ε ξ hε hχ_one)

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

/-- **The Peterfalvi (7.1) Dade ρ-setup for the `i`-th family member.**  The kernel `H_i` of the
`i`-th Frobenius subgroup has `H_i^#` a TI-subset of `G` (`isTI`) with normalizer `L_i`
(`normalizer_eq`, so `L_i` conjugates `H_i^#` to itself, `mem_kernel_sharp_conj_iff_of_mem_L`), so
`Hypothesis71.of_isTISubset` builds the full (7.1) datum `Hypothesis71 G (H_i^#) L_i` (with all
`H(a) = ⊥` and the canonical Dade isometry `τ`).  This is the per-member (7.1) input assembled by
(7.4)/(7.10). -/
noncomputable def hypothesis71 [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)) (F.L i) :=
  Hypothesis71.of_isTISubset
    (fun x hx => OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
    (fun x hx => F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
    (fun l a ha => (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
    (F.isTI i)

/-- **The Dade support of the `i`-th (7.1) datum is the kernel spread** `(H_i^#)^G`.  For the
TI-subset construction every local subgroup `H(a) = ⊥`, so each coset `aH(a) = {a}`, and the Dade
support `⋃_{a ∈ H_i^#} {a}^G` is exactly the conjugacy spread `(H_i^#)^G = kernelSpread i`.  This
identifies the (7.4) disjointness hypothesis `Disjoint (dadeSupport i) (dadeSupport j)` with the
already-proven `kernelSpread_disjoint`. -/
lemma dadeSupport_hypothesis71_eq_kernelSpread [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    (F.hypothesis71 i).hyp.dadeSupport = F.kernelSpread i := by
  rw [F.kernelSpread_eq_conjugatesOfSet i]
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨a, h, hh, hconj⟩
    have hh1 : h = 1 := Subgroup.mem_bot.mp hh
    subst hh1
    exact ⟨a.1, a.2, by simpa using hconj⟩
  · rintro ⟨y, hy, hconj⟩
    exact ⟨⟨y, hy⟩, 1, Subgroup.one_mem _, by simpa using hconj⟩

/-- TI for H_i^# says that any element carrying one sharp-kernel element back
into H_i^# already lies in L_i. -/
lemma mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp
    (F : FrobeniusFamily G k) (i : Fin k) {g x : G}
    (hx : x ∈ (F.H i : Set G) \ {1})
    (hconj : g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}) :
    g ∈ F.L i :=
  F.isTI i g ⟨x, hx, hconj⟩

/-- Conjugate images of `H_i^#` are equal when the conjugators differ by
an element of `L_i = N_G(H_i)`. -/
lemma kernel_sharp_conj_image_eq_of_inv_mul_mem_L
    (F : FrobeniusFamily G k) (i : Fin k) {g h : G}
    (hmem : h⁻¹ * g ∈ F.L i) :
    ((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1})) =
      ((fun x : G => h * x * h⁻¹) '' ((F.H i : Set G) \ {1})) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(h⁻¹ * g) * a * (h⁻¹ * g)⁻¹, ?_, ?_⟩
    · exact (F.mem_kernel_sharp_conj_iff_of_mem_L i hmem).mpr ha
    · group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(h⁻¹ * g)⁻¹ * a * (h⁻¹ * g), ?_, ?_⟩
    · have hinv : (h⁻¹ * g)⁻¹ ∈ F.L i := (F.L i).inv_mem hmem
      simpa using (F.mem_kernel_sharp_conj_iff_of_mem_L i hinv).mpr ha
    · group

/-- Distinct `L_i`-cosets give disjoint conjugate images of `H_i^#`. -/
lemma disjoint_kernel_sharp_conj_image_of_inv_mul_notMem_L
    (F : FrobeniusFamily G k) (i : Fin k) {g h : G}
    (hnot : h⁻¹ * g ∉ F.L i) :
    Disjoint ((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1}))
      ((fun x : G => h * x * h⁻¹) '' ((F.H i : Set G) \ {1})) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hb_eq⟩
  have hconj : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ ∈ (F.H i : Set G) \ {1} := by
    have hb_eq' : h * b * h⁻¹ = g * a * g⁻¹ := by
      simpa only using hb_eq
    have hab0 : h⁻¹ * (g * a * g⁻¹) * h = b := by
      rw [← hb_eq']
      group
    have hab : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = b := by
      calc
        (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
        _ = b := hab0
    rw [hab]
    exact hb
  exact hnot (F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i ha hconj)

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
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

/-- A conjugate image of `H_i^#` has cardinality `|H_i| - 1`. -/
lemma ncard_kernel_sharp_conj_image [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (g : G) :
    (((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1})).ncard =
      Nat.card (F.H i) - 1) := by
  rw [Set.ncard_image_of_injective _]
  · exact F.ncard_kernel_sharp i
  · intro a b hab
    have hcancel := congrArg (fun z : G => g⁻¹ * z * g) hab
    simpa using hcancel

/-- `kernelSpread i` is the disjoint union, indexed by `G ⧸ L_i`, of the
conjugate images of `H_i^#` from a choice of coset representatives. -/
lemma kernelSpread_eq_iUnion_quotient (F : FrobeniusFamily G k) (i : Fin k) :
    F.kernelSpread i =
      ⋃ q : G ⧸ F.L i,
        ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
          ((F.H i : Set G) \ {1})) := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    let g : G := a⁻¹
    let q : G ⧸ F.L i := ⟦g⟧
    have hxg :
        x ∈ ((fun y : G => g * y * g⁻¹) '' ((F.H i : Set G) \ {1})) := by
      refine ⟨a * x * a⁻¹, ha, ?_⟩
      simp only [g]
      group
    have hout_mem : (Quotient.out q : G)⁻¹ * g ∈ F.L i := by
      have hq : (⟦(Quotient.out q : G)⟧ : G ⧸ F.L i) = ⟦g⟧ := by
        exact Quotient.out_eq' q
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hq)
    have himg := F.kernel_sharp_conj_image_eq_of_inv_mul_mem_L i
      (g := g) (h := (Quotient.out q : G)) hout_mem
    exact Set.mem_iUnion.mpr ⟨q, himg ▸ hxg⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
    rcases hxq with ⟨a, ha, rfl⟩
    refine ⟨(Quotient.out q : G)⁻¹, ?_⟩
    convert ha using 1
    group

/-- The quotient-indexed conjugate images of `H_i^#` are pairwise disjoint. -/
lemma kernel_sharp_conj_image_quotient_pairwiseDisjoint
    (F : FrobeniusFamily G k) (i : Fin k) :
    Pairwise (Function.onFun Disjoint fun q : G ⧸ F.L i =>
      ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
        ((F.H i : Set G) \ {1}))) := by
  intro q r hqr
  apply F.disjoint_kernel_sharp_conj_image_of_inv_mul_notMem_L i
  intro hmem
  have hrel : (QuotientGroup.leftRel (F.L i)) (Quotient.out r : G)
      (Quotient.out q : G) := by
    rw [QuotientGroup.leftRel_apply]
    exact hmem
  have hrq : r = q := Quotient.out_equiv_out.mp hrel
  exact hqr hrq.symm

/-- Cardinality of a kernel spread: `|(H_i^#)^G| = [G : L_i] (|H_i| - 1)`. -/
lemma ncard_kernelSpread_eq_index_mul [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (F.kernelSpread i).ncard = (F.L i).index * (Nat.card (F.H i) - 1) := by
  classical
  letI : Fintype (G ⧸ F.L i) := Fintype.ofFinite _
  let S : G ⧸ F.L i → Set G := fun q =>
    ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
      ((F.H i : Set G) \ {1}))
  have hpair : Pairwise (Function.onFun Disjoint S) := by
    simpa [S] using F.kernel_sharp_conj_image_quotient_pairwiseDisjoint i
  have h_union : (⋃ q : G ⧸ F.L i, S q).ncard =
      ∑ᶠ q : G ⧸ F.L i, (S q).ncard :=
    Set.ncard_iUnion_of_finite (s := S) (fun _ => Set.toFinite _) hpair
  have h_sum : ∑ᶠ q : G ⧸ F.L i, (S q).ncard =
      (F.L i).index * (Nat.card (F.H i) - 1) := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [S, F.ncard_kernel_sharp_conj_image]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    norm_num
  rw [F.kernelSpread_eq_iUnion_quotient i, h_union, h_sum]

/-- Cardinality of a kernel spread as a `Nat.card` identity. -/
lemma card_kernelSpread_eq_index_mul [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (F.kernelSpread i) = (F.L i).index * (Nat.card (F.H i) - 1) := by
  rw [Nat.card_coe_set_eq]
  exact F.ncard_kernelSpread_eq_index_mul i

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

/-- **The (7.4) `FamilyHypothesis71` of a Frobenius family** (Peterfalvi (7.10)(a)-(c) ⟹ (7.4)).
Each member `i` supplies the (7.1) datum `Hypothesis71 G (H_i^#) L_i` (`hypothesis71`), whose Dade map
is a genuine isometry (`isDadeIsometry_of_isDadeMap`, from `isDadeMap` + `HConjInvariant`); the
supports `A_i^{τ_i} = dadeSupport_i = (H_i^#)^G` are pairwise disjoint by the coprime-kernel
`kernelSpread_disjoint` (via `dadeSupport_hypothesis71_eq_kernelSpread`).  This assembles the (7.4)
input consumed by the (7.5)/(7.10) `characterEstimateData_of_family71_*` machinery. -/
noncomputable def familyHypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) : FamilyHypothesis71 G k where
  L := F.L
  A := fun i => OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  fintypeL := fun i => Fintype.ofFinite _
  invertibleL := fun i => invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  hyp71 := fun i => F.hypothesis71 i
  isDadeIsometry := fun i => by
    letI : Fintype ↥(F.L i) := Fintype.ofFinite _
    letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
    exact OddOrder.Peterfalvi.S04.isDadeIsometry_of_isDadeMap (F.hypothesis71 i).hyp
      (F.hypothesis71 i).τ (F.hypothesis71 i).isDadeMap (F.hypothesis71 i).hConjInvariant
  pairwise_disjoint := fun i j hij => by
    rw [F.dadeSupport_hypothesis71_eq_kernelSpread i, F.dadeSupport_hypothesis71_eq_kernelSpread j]
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

/-- The sum of spread cardinalities in normalizer-index form. -/
lemma sum_card_kernelSpread_eq_sum_index_mul [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, Nat.card (F.kernelSpread i)) =
      ∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1) := by
  exact Finset.sum_congr rfl (fun i _ => F.card_kernelSpread_eq_index_mul i)

/-- Difference form of the partition with each spread counted by normalizer index. -/
lemma card_G0_eq_card_G_sub_sum_index_mul [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card F.G0 =
      Nat.card G - ∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1) := by
  rw [F.card_G0_eq_card_G_sub_sum_card_kernelSpread,
    F.sum_card_kernelSpread_eq_sum_index_mul]

/-- The index-counted spreads have total size `|G| - |G₀|`. -/
lemma sum_index_mul_eq_card_G_sub_card_G0 [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1)) =
      Nat.card G - Nat.card F.G0 := by
  rw [← F.sum_card_kernelSpread_eq_sum_index_mul,
    F.sum_card_kernelSpread_eq_card_G_sub_card_G0]

/-- Kernel order `h_i = |H_i|`. -/
noncomputable def h (F : FrobeniusFamily G k) (i : Fin k) : ℕ := Nat.card (F.H i)

/-- Complement index `e_i = |L_i : H_i|` (exact, since `H_i ≤ L_i`). -/
noncomputable def e (F : FrobeniusFamily G k) (i : Fin k) : ℕ :=
  Nat.card (F.L i) / Nat.card (F.H i)

/-- If a local (7.8) package uses the `i`-th family kernel, its local
kernel order is the family quantity `h_i`. -/
lemma localKernelOrder_eq_h [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hH : H78.hyp76.H = F.H i) :
    H78.kernelOrder = F.h i := by
  simp [Hypothesis78.kernelOrder, FrobeniusFamily.h, hH]

/-- If a local (7.8) package uses the `i`-th family host and kernel, its local
complement index is the family quantity `e_i`. -/
lemma localComplementIndex_eq_e [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hL : L = F.L i)
    (hH : H78.hyp76.H = F.H i) :
    H78.complementIndex = F.e i := by
  simp [Hypothesis78.complementIndex, FrobeniusFamily.e, hL, hH]

/-- Family-side small-index data `2e_i + 1 ≤ h_i` supplies the local (7.8.b)
small-index hypothesis after identifying the local host and kernel. -/
lemma localSmallIndex_of_family_cardinalities [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hL : L = F.L i)
    (hH : H78.hyp76.H = F.H i)
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    H78.smallIndex := by
  rw [Hypothesis78.smallIndex]
  rw [F.localComplementIndex_eq_e H78 hL hH, F.localKernelOrder_eq_h H78 hH]
  exact hsmall

/-- Family-notated source-data form of the raw `(ζ^ν)^ρ` lower bound from
Peterfalvi (7.8.b).  This is the local estimate used before the reduced-family
inequality in (7.10), with `e` and `h` stated as `F.e i` and `F.h i`. -/
lemma zetaNuRho_inner_self_re_ge_of_family_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re := by
  have hlocal :
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re :=
    H78.zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
    using hlocal

/-- **Peterfalvi (7.8.b).** Family-notated source-data form of the residual
`Γ` upper bound.  This is the `Γ` estimate consumed by the orthogonal integer
decomposition in the final assembly, with the local `e` rewritten as `F.e i`. -/
lemma gamma_inner_self_re_le_of_family_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤ (F.e i : ℝ) - 1 := by
  have hlocal :
      (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
        (H78.complementIndex : ℝ) - 1 :=
    H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localComplementIndex_eq_e H78 hL hH] using hlocal

/-- **Peterfalvi (7.8.c.ii).** Family-notated source-data form of the
`(ζ^ν)^ρ` norm formula.  This rewrites the local ratio `(h - 1)/(he)` as
the family quantities `(h_i - 1)/(h_i e_i)`. -/
lemma zetaNuRhoNormSq_eq_familyRatio_mul_int_sub_one_of_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ r : Fin (H78.hyp76.n + 1), r ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta r)) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (F.e i : ℂ)) :
    H78.zetaNuRhoNormSq =
      (((F.h i : ℝ) - 1) / ((F.h i : ℝ) * (F.e i : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) := by
  have hlocal :
      H78.zetaNuRhoNormSq =
        (((H78.kernelOrder : ℝ) - 1) /
            ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
          (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) :=
    H78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data
      hBD hnu_irr hnu_orth hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
  simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
    using hlocal

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

/-- Lagrange plus the Frobenius product formula: `|G| = [G : L_i] h_i e_i`. -/
lemma index_mul_h_mul_e_eq_card_G [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (F.L i).index * (F.h i * F.e i) = Nat.card G := by
  rw [F.h_mul_e_eq_card_L i]
  exact (F.L i).index_mul_card

/-- The spread count in `h_i` notation. -/
lemma card_kernelSpread_eq_index_mul_h_sub_one [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (F.kernelSpread i) = (F.L i).index * (F.h i - 1) := by
  simpa [h] using F.card_kernelSpread_eq_index_mul i

/-- `H_i^#` has cardinality `h_i - 1` as a `Nat.card` statement. -/
lemma card_kernel_sharp_eq_h_sub_one [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) = F.h i - 1 := by
  rw [Nat.card_coe_set_eq]
  exact F.ncard_kernel_sharp i

/-- The local sharp-kernel ratio `|H_i^#| / |L_i| = (h_i - 1)/(h_i e_i)`. -/
lemma card_kernel_sharp_div_card_L_eq_h_sub_one_div_h_mul_e [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℚ) /
        (Nat.card (F.L i) : ℚ) =
      ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  rw [F.card_kernel_sharp_eq_h_sub_one i, ← F.h_mul_e_eq_card_L i]
  norm_num [Nat.cast_sub hh1]

/-- The local sharp-kernel ratio `|H_i^#| / |L_i|` as a real number, in the
denominator order used by the real reduced-family estimate. -/
lemma card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℝ) /
        (Nat.card (F.L i) : ℝ) =
      ((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ)) := by
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  rw [F.card_kernel_sharp_eq_h_sub_one i, ← F.h_mul_e_eq_card_L i]
  rw [Nat.cast_sub hh1, Nat.cast_mul]
  rw [mul_comm (F.h i : ℝ) (F.e i : ℝ)]
  norm_num

/-- The global spread ratio equals the same local ratio `(h_i - 1)/(h_i e_i)`. -/
lemma card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) =
      ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hidx_pos : 0 < (F.L i).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hidx_ne : ((F.L i).index : ℚ) ≠ 0 := by
    exact_mod_cast hidx_pos.ne'
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have hh_ne : (F.h i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F.H i)).ne'
  have he_ne : (F.e i : ℚ) ≠ 0 := by
    have h2 := F.two_le_e i
    positivity
  rw [F.card_kernelSpread_eq_index_mul_h_sub_one i, ← F.index_mul_h_mul_e_eq_card_G i]
  norm_num [Nat.cast_sub hh1]
  field_simp [hidx_ne, hh_ne, he_ne]

/-- The global spread ratio matches the local sharp-kernel ratio. -/
lemma card_kernelSpread_div_card_G_eq_card_kernel_sharp_div_card_L [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) =
      (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℚ) /
        (Nat.card (F.L i) : ℚ) := by
  rw [F.card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e,
    F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_h_mul_e]

/-- The sum of all spread ratios is the complement of the `G₀` ratio. -/
lemma sum_card_kernelSpread_div_card_G_eq_one_sub_card_G0_div_card_G [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ)) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) := by
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hG_ne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast hG_pos.ne'
  rw [← Finset.sum_div, ← Nat.cast_sum, F.sum_card_kernelSpread_eq_card_G_sub_card_G0,
    Nat.cast_sub (F.card_G0_le_card_G)]
  field_simp [hG_ne]

/-- The same balance formula in `h_i, e_i` notation. -/
lemma sum_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ))) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) := by
  calc
    (∑ i : Fin k, ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)))
        = ∑ i : Fin k, (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (F.card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e i).symm
    _ = 1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) :=
        F.sum_card_kernelSpread_div_card_G_eq_one_sub_card_G0_div_card_G

/-- The weighted spread ratio term is nonnegative. -/
lemma h_sub_one_div_h_mul_e_nonneg [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    0 ≤ ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hh1_nat : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have he1_nat : 1 ≤ F.e i := by
    have h2 := F.two_le_e i
    omega
  have hh1 : (1 : ℚ) ≤ F.h i := by exact_mod_cast hh1_nat
  have hhpos : (0 : ℚ) < F.h i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hh1_nat)
  have hepos : (0 : ℚ) < F.e i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he1_nat)
  exact div_nonneg (sub_nonneg.mpr hh1) (le_of_lt (mul_pos hhpos hepos))

/-- The unweighted `𝓑`-sum term from Peterfalvi (7.10) is nonnegative. -/
lemma h_sub_one_div_e_nonneg [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    0 ≤ ((F.h i : ℚ) - 1) / (F.e i : ℚ) := by
  have hh1_nat : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have he1_nat : 1 ≤ F.e i := by
    have h2 := F.two_le_e i
    omega
  have hh1 : (1 : ℚ) ≤ F.h i := by exact_mod_cast hh1_nat
  have hepos : (0 : ℚ) < F.e i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he1_nat)
  exact div_nonneg (sub_nonneg.mpr hh1) (le_of_lt hepos)

/-- Removing one index from the global weighted balance. -/
lemma sum_erase_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G_sub [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (∑ j ∈ (Finset.univ.erase i),
        ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) -
        ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hsum := F.sum_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G
  have hi : i ∈ (Finset.univ : Finset (Fin k)) := by simp
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
      (fun j => ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) hi] at hsum
  linarith

/-- A subset of the non-minimal indices has weighted sum bounded by the erased
weighted balance. -/
lemma sum_h_sub_one_div_h_mul_e_le_sum_erase [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} (s : Finset (Fin k))
    (hs : s ⊆ Finset.univ.erase i) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) ≤
      ∑ j ∈ (Finset.univ.erase i),
        ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ)) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun j _ _ =>
    F.h_sub_one_div_h_mul_e_nonneg j

/-- A subset of the non-minimal indices has unweighted sum bounded by the erased
unweighted sum. -/
lemma sum_h_sub_one_div_e_le_sum_erase [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} (s : Finset (Fin k))
    (hs : s ⊆ Finset.univ.erase i) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      ∑ j ∈ (Finset.univ.erase i), ((F.h j : ℚ) - 1) / (F.e j : ℚ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun j _ _ =>
    F.h_sub_one_div_e_nonneg j

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

/-- There is an index whose kernel order is minimal among the family. -/
lemma exists_min_h_index [Finite G] (F : FrobeniusFamily G k) :
    ∃ i : Fin k, ∀ j : Fin k, F.h i ≤ F.h j := by
  classical
  have hkpos : 0 < k := by
    have htwo : 2 ≤ k := F.two_le
    omega
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hkpos⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset (Fin k)) (fun i => F.h i) hne with
    ⟨i, _hi, hmin⟩
  exact ⟨i, fun j => hmin j (by simp)⟩

/-- If `h_i` is chosen minimal, then every other odd coprime kernel order is at
least `h_i + 2`. -/
lemma h_add_two_le_h_of_min [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) {i j : Fin k} (hij : i ≠ j)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) : F.h i + 2 ≤ F.h j := by
  have hcop : Nat.Coprime (F.h i) (F.h j) := by
    simpa [h] using F.coprime_kernel hij
  have hne : F.h i ≠ F.h j := by
    intro heq
    have hone : F.h i = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by
      rw [← heq])
    have h2 := F.two_le_h i
    omega
  have hi_odd : Odd (F.h i) := F.odd_h hodd i
  have hj_odd : Odd (F.h j) := F.odd_h hodd j
  have hlt : F.h i < F.h j := by
    have hle := hmin j
    omega
  obtain ⟨a, ha⟩ := hi_odd
  obtain ⟨b, hb⟩ := hj_odd
  omega

/-- A minimal kernel order gives the denominator comparison used in the
`𝓑`-sum estimate in Peterfalvi (7.10). -/
lemma h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i j : Fin k}
    (hij : i ≠ j) (hmin : ∀ l : Fin k, F.h i ≤ F.h l) :
    ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)) ≤
      (((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  have hden_le_nat : F.h i + 2 ≤ F.h j := F.h_add_two_le_h_of_min hodd hij hmin
  have hhj_ge2 : 2 ≤ F.h j := F.two_le_h j
  have hej_ge2 : 2 ≤ F.e j := F.two_le_e j
  have hhj_ne : (F.h j : ℚ) ≠ 0 := by positivity
  have hei_ne : (F.e j : ℚ) ≠ 0 := by positivity
  have hden_ne : (F.h i : ℚ) + 2 ≠ 0 := by positivity
  have hden_le : (F.h i : ℚ) + 2 ≤ (F.h j : ℚ) := by
    exact_mod_cast hden_le_nat
  field_simp [hhj_ne, hei_ne, hden_ne]
  have hsub_nonneg : 0 ≤ (F.h j : ℚ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ F.h j))
  nlinarith

/-- Summed denominator comparison for any set of indices avoiding the chosen
minimal index. -/
lemma sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  calc
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))
        ≤ ∑ j ∈ s, (((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
            ((F.h i : ℚ) + 2) := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact F.h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two
              hodd (hs j hj) hmin
    _ = (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
          ((F.h i : ℚ) + 2) := by
        rw [Finset.sum_div]

/-- If the unweighted `𝓑`-sum is bounded by `e_i - 1`, then the weighted sum is
bounded by `(e_i - 1)/(h_i + 2)`, as in Peterfalvi (7.10). -/
lemma sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j)
    (hsum : (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
  have hden_pos : 0 < (F.h i : ℚ) + 2 := by positivity
  have hweighted := F.sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two
    hodd hmin s hs
  have hscaled :
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) ≤
        ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
    exact div_le_div_of_nonneg_right hsum (le_of_lt hden_pos)
  linarith

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

/-- The final arithmetic rearrangement in Peterfalvi (7.10). -/
lemma lowerBoundTerm_final_rearrange [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) =
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he_ne : (F.e i : ℚ) ≠ 0 := by
    have h2 := F.two_le_e i
    positivity
  have hh_ne : (F.h i : ℚ) ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  have hh2_ne : (F.h i : ℚ) + 2 ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  field_simp [he_ne, hh_ne, hh2_ne]
  ring

/-- The penultimate estimate in Peterfalvi (7.10) implies the displayed lower
bound for the same index. -/
lemma lowerBoundTerm_of_penultimate [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k)
    (hpen : ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rw [← F.lowerBoundTerm_final_rearrange i]
  exact hpen

/-- Existential form of `lowerBoundTerm_of_penultimate`, matching the target shape
of Peterfalvi (7.10). -/
lemma exists_lowerBoundTerm_of_exists_penultimate [Finite G]
    (F : FrobeniusFamily G k)
    (hpen : ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2))) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hpen with ⟨i, hi⟩
  exact ⟨i, F.lowerBoundTerm_of_penultimate i hi⟩

/-- The `𝓑`-sum estimate in Peterfalvi (7.10) gives the penultimate displayed
inequality once the main character-theoretic estimate has isolated the same
`𝓑`-sum. -/
lemma penultimate_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) := by
  have hBweighted := F.sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two
    hodd hmin B hB_ne hBsum
  linarith

/-- The `𝓑`-sum estimate plus the main character-theoretic estimate gives the
final displayed lower bound for the same minimal index. -/
lemma lowerBoundTerm_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  exact F.lowerBoundTerm_of_penultimate i
    (F.penultimate_of_Bsum_bound hodd hmin B hB_ne hBsum hbase)

/-- Existential wrapper for the final assembly step of Peterfalvi (7.10): once a
minimal index and its `𝓑`-set satisfy the character-theoretic base estimate and
unweighted `𝓑`-sum bound, the displayed lower bound follows. -/
lemma exists_lowerBoundTerm_of_exists_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          1 - (F.e i : ℚ) / (F.h i : ℚ) -
            (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
            (∑ j ∈ B, ((F.h j : ℚ) - 1) /
              ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hbase⟩
  exact ⟨i, F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum hbase⟩

/-- The unweighted local contribution `(h_j - 1) / e_j` attached to an index in
Peterfalvi's `𝓑`-sum.  Naming it keeps the `ℚ`-to-`ℂ` coercion from being
elaborated as a complex division in orthogonality hypotheses. -/
noncomputable def BsumWeight (F : FrobeniusFamily G k) (j : Fin k) : ℚ :=
  ((F.h j : ℚ) - 1) / (F.e j : ℚ)

/-- **Peterfalvi (7.10) character-estimate target.**  This is the exact data
still to be built from the character-theoretic inputs (7.5), (7.8), (7.9), and
(6.8): a minimal kernel index, the corresponding `𝓑`-set, the unweighted
`𝓑`-sum bound, and the base estimate before the final arithmetic rearrangement.

It is standalone target data, not a field of `FrobeniusFamily`. -/
structure CharacterEstimateData [Finite G] (F : FrobeniusFamily G k) where
  /-- The index with minimal kernel order. -/
  i : Fin k
  /-- Minimality of `h_i`. -/
  hmin : ∀ l : Fin k, F.h i ≤ F.h l
  /-- The Peterfalvi `𝓑`-set of non-minimal indices. -/
  B : Finset (Fin k)
  /-- The chosen `𝓑`-indices avoid the minimal index. -/
  B_avoids_min : ∀ j ∈ B, i ≠ j
  /-- The unweighted `𝓑`-sum bound coming from (7.8.b) and (7.9). -/
  Bsum_le :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1
  /-- The base estimate isolated from (7.5), before bounding the `𝓑`-sum. -/
  base_estimate :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ)))

/-- Direct `𝓑`-sum bridge for Peterfalvi (7.10): an orthogonal integer
combination with diagonal weights `(h_j - 1) / e_j` and norm at most `e_i - 1`
gives exactly the `Bsum_le` field required by `CharacterEstimateData`. -/
lemma Bsum_le_of_orthogonal_integer_decomposition [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k} (B : Finset (Fin k))
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1) :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1 := by
  classical
  have horth' : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l))
          (F.BsumWeight j : ℂ) 0 := by
    intro j hj l hl
    by_cases h : j = l
    · simpa [h] using horth j hj l hl
    · simpa [h] using horth j hj l hl
  have hm_nonneg : ∀ j ∈ B, 0 ≤ F.BsumWeight j := by
    intro j _hj
    simpa [BsumWeight] using F.h_sub_one_div_e_nonneg j
  let M : ℚ := (F.e i : ℚ) - 1
  have hM_eq : (M : ℝ) = (F.e i : ℝ) - 1 := by
    dsimp [M]
    norm_num
  have hbound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ) := by
    rw [hM_eq]
    exact hΓ_bound
  have hrat := sum_rat_weights_le_of_orthogonal_integer_decomposition
    B v x F.BsumWeight Γ Γ₁ M hΓ horth' hΓ₁ hm_nonneg hx_nonzero hbound
  simpa [BsumWeight, M] using hrat

/-- The reduced output of Peterfalvi (7.5), after inserting the (7.8) lower
bounds and the identity contribution on `G₀`, is exactly the `base_estimate`
field of `CharacterEstimateData`.  This is the algebraic bridge from the real
family inequality to the rational display used in (7.10). -/
lemma base_estimate_of_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (B : Finset (Fin k))
    (hred :
      ((1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ)) +
        (1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) /
            ((F.e j : ℚ) * (F.h j : ℚ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  have hG_ne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hneg :
      (1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ) =
        -(((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ)) := by
    field_simp [hG_ne]
    ring
  rw [hneg] at hred
  linarith

/-- Real-valued input form of `base_estimate_of_reduced_family_inequality`.
This matches the actual codomain of (7.5), (7.8.b), and the norm estimates before
the final rational display of Peterfalvi (7.10). -/
lemma base_estimate_of_real_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (B : Finset (Fin k))
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  have hG_ne : (Nat.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hneg :
      (1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ) =
        -(((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ)) := by
    field_simp [hG_ne]
    ring
  rw [hneg] at hred
  have hreal :
      1 - (F.e i : ℝ) / (F.h i : ℝ) -
        (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
        (∑ j ∈ B, ((F.h j : ℝ) - 1) /
          ((F.e j : ℝ) * (F.h j : ℝ))) ≤
        ((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ) := by
    linarith
  rw [ge_iff_le]
  rw [← Rat.cast_le (K := ℝ)]
  norm_num
  have hG0_ncard : (F.G0.ncard : ℝ) = Nat.card F.G0 := by
    exact_mod_cast (Nat.card_coe_set_eq F.G0)
  rw [hG0_ncard]
  linarith

/-- Constructor form of `CharacterEstimateData` from the reduced family
inequality and the separately proved `𝓑`-sum bound. -/
noncomputable def characterEstimateData_of_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ)) +
        (1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) /
            ((F.e j : ℚ) * (F.h j : ℚ)))) ≤ 0) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate := F.base_estimate_of_reduced_family_inequality i B hred

/-- Real-valued constructor form of `CharacterEstimateData` from the reduced
family inequality and the separately proved `𝓑`-sum bound.  This is the direct
interface for the estimates produced by Peterfalvi (7.5), (7.8.b), and (7.9). -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate := F.base_estimate_of_real_reduced_family_inequality i B hred

open scoped Classical in
/-- Base-estimate form of Peterfalvi (7.10) obtained directly from the (7.5)
family inequality package and the per-index lower bounds.

This removes the former standalone `hred` input for the base estimate: the caller
only supplies the actual (7.5) family package, the identity contribution on
`G₀`, the selected (7.8.b) lower bound, and the nonnegative outside-`𝓑`
contributions.  The cardinality hypotheses identify the (7.5) local data with
the Frobenius-family notation used in (7.10). -/
lemma base_estimate_of_family71_reduced_estimates
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0sum :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  classical
  have hratio : ∀ j : Fin k,
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) =
        ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) := by
    intro j
    rw [hA j, hL j]
    exact F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real j
  have hgood' : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) ≤
        P.chiRhoNormSq χ j := by
    intro j hij hjB
    rw [hratio j]
    exact hgood j hij hjB
  have hG0sumP :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ P.G0),
          ‖(χ : G → ℂ) g‖ ^ 2 := by
    rw [hG0]
    exact hG0sum
  have hredP :=
    reduced_inequality_of_estimates P χ hχ i B
      (1 - (F.e i : ℝ) / (F.h i : ℝ))
      hB_ne hG0sumP hi hgood'
  have hredF :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0 := by
    have hredP' :
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (Nat.card (P.A i) : ℝ) / (Nat.card (P.L i) : ℝ) -
            (∑ j ∈ B,
              (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ))) ≤ 0 := by
      rw [← hG0]
      exact hredP
    have hsum_ratio :
        (∑ j ∈ B, (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ)) =
          ∑ j ∈ B, ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) :=
      Finset.sum_congr rfl (fun j _ => hratio j)
    rwa [hratio i, hsum_ratio] at hredP'
  exact F.base_estimate_of_real_reduced_family_inequality i B hredF

open scoped Classical in
/-- Constructor form of `CharacterEstimateData` from a concrete (7.5) family
package, per-index lower bounds, and the separately proved `𝓑`-sum bound. -/
noncomputable def characterEstimateData_of_family71_reduced_estimates
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hG0sum :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate :=
    F.base_estimate_of_family71_reduced_estimates P χ hχ B hL hA hG0
      hB_ne hG0sum hi hgood

open scoped Classical in
/-- Signed-irreducible variant of
`base_estimate_of_family71_reduced_estimates`.

This packages the exact first inequality in Peterfalvi (7.10):
`(|G₀|-1)/|G| ≥ (|G₀|-χ₁(1)^2)/|G|`, using that the selected `χ₁` is a signed
irreducible character and `1 ∈ G₀`. -/
lemma base_estimate_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) :=
  F.base_estimate_of_family71_reduced_estimates P χ hχ B hL hA hG0 hB_ne
    (F.one_le_G0_norm_sum_of_signed_irreducible χ ε ξ hε hχ_signed)
    hi hgood

open scoped Classical in
/-- Constructor form of the signed-irreducible `(7.5)` base assembly, retaining
only the `𝓑`-sum bound as a separate final-assembly input. -/
noncomputable def characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate :=
    F.base_estimate_of_family71_reduced_estimates_of_signed_irreducible
      P χ hχ B ε ξ hε hχ_signed hL hA hG0 hB_ne hi hgood

open scoped Classical in
/-- Constructor form of `CharacterEstimateData` from the concrete (7.5) family
estimates, a signed-irreducible selected character, and Peterfalvi's orthogonal
integer decomposition for the `𝓑`-sum.

Compared with `characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible`,
this no longer asks for the final `𝓑`-sum bound as an external input: it derives
that bound from the orthogonal decomposition used in (7.9). -/
noncomputable def characterEstimateData_of_family71_signed_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    P χ hχ hmin B ε ξ hε hχ_signed hL hA hG0 hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hi hgood

open scoped Classical in
/-- Coherence-source form of the concrete (7.5)+(7.9) final-assembly
constructor.

Here the selected character is the coherent image `νζ`.  The source
irreducibility of `ζ` and the coherence witness produce the signed-irreducible
witness internally, so the caller supplies neither `hG0sum` nor an explicit
`νζ = ±ξ` certificate. -/
noncomputable def characterEstimateData_of_family71_coherent_zeta_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    F.CharacterEstimateData := by
  classical
  let hsig :=
    H78.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent hcoh hnu hzeta_irr
  let ε : ℤ := Classical.choose hsig
  let hsigξ := Classical.choose_spec hsig
  let ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G := Classical.choose hsigξ
  have hχ_signed := Classical.choose_spec hsigξ
  exact F.characterEstimateData_of_family71_signed_decomposition
    P (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
    (H78.zetaImage_inner_self_eq_one_of_irreducible hzeta_irr)
    hmin B ε ξ hχ_signed.1 hχ_signed.2 hL hA hG0 hB_ne
    v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound hi hgood

open scoped Classical in
/-- Source-data form of the concrete (7.5)+(7.8.b)+(7.9) final-assembly
constructor.

This refines `characterEstimateData_of_family71_coherent_zeta_decomposition` by
deriving the residual `Γ` norm bound from the family-notated (7.8.b) source
data, rather than taking `hΓ_bound` as a separate input.  The selected character
is still the coherent image `νζ`, so the signed-irreducible witness and the
`G₀` identity contribution are also generated internally. -/
noncomputable def characterEstimateData_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_family71_coherent_zeta_decomposition
    P H78 hcoh hnu hzeta_irr hmin B hP_L hP_A hP_G0 hB_ne
    v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero
    (F.gamma_inner_self_re_le_of_family_source_data H78 hBD hLocalL hLocalH
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv hsmall)
    hi hgood

/-- Constructor form of `CharacterEstimateData` from the real reduced family
inequality and Peterfalvi's orthogonal integer decomposition for the `𝓑`-sum.

This combines the two final-assembly bridges: the norm bound on `Γ` gives the
`Bsum_le` field through `Bsum_le_of_orthogonal_integer_decomposition`, while the
real reduced family inequality supplies the `base_estimate` field. -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality hmin B hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hred

/-- Source-data constructor form of `CharacterEstimateData` from the real reduced
family inequality and Peterfalvi's orthogonal integer decomposition.

This is the same assembly as
`characterEstimateData_of_real_reduced_family_inequality_and_decomposition`, but
it obtains the required `Γ` norm-bound directly from the local (7.8.b) source
inputs for an `H78` package.  The only family/local cardinality bridge retained
as an explicit hypothesis is `H78.complementIndex = F.e i`. -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hindex : H78.complementIndex = F.e i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality_and_decomposition
    hmin B hB_ne v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero
    (by
      simpa [hindex] using
        H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
          hBD hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv hsmall)
    hred

/-- Source-data constructor with family-side cardinality hypotheses.

Compared with
`characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition`,
this wrapper consumes the natural family/local identifications `L = L_i` and
`H = H_i`, and the family-side small-index hypothesis `2e_i + 1 ≤ h_i`, rather
than asking the caller to rewrite them into local (7.8.b) notation. -/
noncomputable def characterEstimateData_of_source_decomposition_of_family_cardinalities
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition
    H78 hBD (F.localComplementIndex_eq_e H78 hL hH)
    hmin B hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
    hzeta_degree hdegree_sum hzeta_uv
    (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall) hred

/-- Source-data constructor with all cardinal source estimates stated in family
notation.

This is the downstream-facing form of the source-data final assembly: the source
norm, degree sum, and `u,v,w` formula use the family quantities `e_i` and `h_i`.
The wrapper rewrites them into the local `H78` notation before applying the
local/family cardinality constructor. -/
noncomputable def characterEstimateData_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_source_decomposition_of_family_cardinalities
    H78 hBD hL hH hmin B hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero
    (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
    hzeta_ind hirr hdistinct
    (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
    (by
      simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
        using hdegree_sum)
    (by
      simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
        using hzeta_uv)
    hsmall hred

/-- The named character-estimate data implies the displayed lower bound of
Peterfalvi (7.10). -/
lemma lowerBoundTerm_of_characterEstimateData [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : F.CharacterEstimateData) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hbase⟩
  exact ⟨i, F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum hbase⟩


/-- Concrete (7.5)+(7.8.b)+(7.9) source-data form of the displayed (7.10)
lower bound.

This is the lower-bound consumer for
`characterEstimateData_of_family71_coherent_zeta_source_data`: the concrete
`FamilyHypothesis71` reduced family inequality, the coherent `ζ` image, the
family-notated (7.8.b) source estimates, and the orthogonal integer
decomposition are assembled internally into `CharacterEstimateData` and then
converted to Peterfalvi's displayed rational bound. -/
lemma lowerBoundTerm_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) :=
  F.lowerBoundTerm_of_characterEstimateData hodd
    (F.characterEstimateData_of_family71_coherent_zeta_source_data P H78 hBD
      hcoh hnu hzeta_irr hLocalL hLocalH hmin B hP_L hP_A hP_G0 hB_ne
      v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hi hgood)

/-- Real-valued form of `lowerBoundTerm_of_Bsum_bound`, matching the reduced
inequality produced before Peterfalvi's final rational display. -/
lemma lowerBoundTerm_of_real_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  exact F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum
    (F.base_estimate_of_real_reduced_family_inequality i B hred)

/-- Direct displayed-bound form from the real reduced family inequality and the
orthogonal integer decomposition controlling the `𝓑`-sum.

This is the non-existential consumer for the final (7.10) assembly after the
character theory has supplied the chosen minimal index, `𝓑`, the integer
coefficients, and the norm bound on `Γ`. -/
lemma lowerBoundTerm_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) :=
  F.lowerBoundTerm_of_real_Bsum_bound hodd hmin B hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hred

/-- Source-data displayed-bound form for the final assembly step of Peterfalvi
(7.10).

This consumes the same family-notated local source data as
`characterEstimateData_of_family_source_decomposition`, but returns the displayed
lower bound for the chosen minimal index directly.  This is useful when the
caller wants the (7.10) bound without first packaging the intermediate
`CharacterEstimateData`. -/
lemma lowerBoundTerm_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  refine F.lowerBoundTerm_of_real_reduced_family_inequality_and_decomposition hodd
    hmin B hB_ne v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero ?_ hred
  have hΓ_bound_local :
      (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
        (H78.complementIndex : ℝ) - 1 :=
    H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localComplementIndex_eq_e H78 hL hH] using hΓ_bound_local

/-- Existential real-valued wrapper for the final assembly step of Peterfalvi
(7.10).  The input shape matches the real reduced estimate before converting to
the rational displayed lower bound. -/
lemma exists_lowerBoundTerm_of_exists_real_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
            (∑ j ∈ B, ((F.h j : ℝ) - 1) /
              ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hred⟩
  exact ⟨i, F.lowerBoundTerm_of_real_Bsum_bound hodd hmin B hB_ne hBsum hred⟩

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
  have hdata : F.CharacterEstimateData := by
    -- TODO: assemble from (7.5), (7.8), (7.9), and (6.8).
    sorry
  exact F.lowerBoundTerm_of_characterEstimateData hodd hdata

/-- **Peterfalvi (7.11), displayed-bound form.**  The final contradiction from the
existential lower bound displayed in (7.10).

This isolates the terminal arithmetic of (7.11): any proof of the displayed (7.10) bound,
including the still-open theorem `card_G0_lower_bound` or the conditional §9 assembly lemmas,
can be consumed without duplicating the `G₀ = {1}` contradiction proof. -/
theorem not_trivial_G0_of_lowerBoundTerm [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G))
    (hbound :
      ∃ i : Fin k,
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          ((F.e i : ℚ) - 1) *
            (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
                ((F.e i : ℚ) * (F.h i : ℚ)) +
              2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))))
    (hG0 : F.G0 = {(1 : G)}) : False := by
  obtain ⟨i, hi⟩ := hbound
  -- `G₀ = {1}` forces `|G₀| = 1`, so the left-hand side of (7.10) is `0`.
  have hcard : Nat.card F.G0 = 1 := by rw [hG0]; simp
  -- The right-hand side of (7.10) is strictly positive.
  have hRHS := F.lowerBoundTerm_pos hodd i
  -- But the conditional (7.10) lower bound says it is `≤ 0` — contradiction.
  rw [hcard] at hi
  have hlhs : ((1 : ℕ) : ℚ) - 1 = 0 := by norm_num
  rw [hlhs, zero_div] at hi
  linarith [hi, hRHS]

/-- **Peterfalvi (7.11), penultimate existential form.**  The penultimate
displayed lower bound from (7.10) already contradicts `G₀ = {1}`. -/
theorem not_trivial_G0_of_exists_penultimate [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hpen : ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)))
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_penultimate hpen) hG0

/-- **Peterfalvi (7.11), existential `𝓑`-sum form.**  If the final assembly
produces a minimal index, a `𝓑`-set, the unweighted `𝓑`-sum bound, and the
base estimate, then `G₀ = {1}` is impossible. -/
theorem not_trivial_G0_of_exists_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          1 - (F.e i : ℚ) / (F.h i : ℚ) -
            (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
            (∑ j ∈ B, ((F.h j : ℚ) - 1) /
              ((F.e j : ℚ) * (F.h j : ℚ))))
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_Bsum_bound hodd hdata) hG0

/-- **Peterfalvi (7.11), existential real `𝓑`-sum form.**  This is the terminal
consumer for the real-valued reduced estimate produced before the rational
display of (7.10). -/
theorem not_trivial_G0_of_exists_real_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
            (∑ j ∈ B, ((F.h j : ℝ) - 1) /
              ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_real_Bsum_bound hodd hdata) hG0

/-- **Peterfalvi (7.11), conditional form.**  The final contradiction from the named
`CharacterEstimateData` package used to prove (7.10).

This avoids routing through the still-open `card_G0_lower_bound`: once the §9 character theory has
constructed `F.CharacterEstimateData`, the terminal `G₀ ≠ {1}` contradiction is already closed by
the completed arithmetic and positivity lemmas. -/
theorem not_trivial_G0_of_characterEstimateData [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (hdata : F.CharacterEstimateData)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.lowerBoundTerm_of_characterEstimateData hodd hdata) hG0


/-- **Peterfalvi (7.11), concrete family/source-data form.**  The terminal
contradiction from the concrete (7.5) family inequality, coherent `ζ` image,
(7.8.b) source estimates, and the (7.9) orthogonal integer decomposition.

This bypasses the open top-level `card_G0_lower_bound`: once these textbook
source-data inputs are available, the displayed lower bound and the final
`G₀ = {1}` contradiction are already closed. -/
theorem not_trivial_G0_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ}
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.lowerBoundTerm_of_family71_coherent_zeta_source_data hodd P H78 hBD
      hcoh hnu hzeta_irr hLocalL hLocalH hmin B hP_L hP_A hP_G0 hB_ne
      v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hi hgood)
    hG0

/-- **Peterfalvi (7.11), `𝓑`-sum-bound form.**  The terminal contradiction from
the separately established `𝓑`-sum bound and the real reduced family inequality.

This is the direct consumer for final-assembly work that has already converted the
orthogonal decomposition into the rational `𝓑`-sum estimate, but has not packaged the result
as `CharacterEstimateData`. -/
theorem not_trivial_G0_of_real_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_characterEstimateData F hodd
    (F.characterEstimateData_of_real_reduced_family_inequality hmin B hB_ne hBsum hred)
    hG0

/-- **Peterfalvi (7.11), raw final-assembly form.**  The terminal contradiction from the
real reduced family inequality and Peterfalvi's orthogonal integer decomposition for the `𝓑`-sum.

This is the form closest to the outputs of (7.5), (7.8), and (7.9): it builds the named
`CharacterEstimateData` internally, then applies `not_trivial_G0_of_characterEstimateData`. -/
theorem not_trivial_G0_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_characterEstimateData F hodd
    (F.characterEstimateData_of_real_reduced_family_inequality_and_decomposition
      hmin B hB_ne v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound hred)
    hG0

/-- **Peterfalvi (7.11), family-source final-assembly form.**  The terminal
contradiction from the family-notated source data that produces the displayed
(7.10) lower bound.

This is the terminal consumer paired with
`FrobeniusFamily.lowerBoundTerm_of_family_source_decomposition`: once the
character-theoretic work has supplied the chosen local (7.8) source package, the
real reduced family inequality, and the orthogonal integer decomposition, the
case `G₀ = {1}` is already impossible without using the still-open
`card_G0_lower_bound`. -/
theorem not_trivial_G0_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ}
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    ⟨i, F.lowerBoundTerm_of_family_source_decomposition hodd H78 hBD hL hH hmin B
      hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hred⟩
    hG0

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
  exact not_trivial_G0_of_lowerBoundTerm F hodd (card_G0_lower_bound F hodd) hG0

end OddOrder.Peterfalvi.S09
