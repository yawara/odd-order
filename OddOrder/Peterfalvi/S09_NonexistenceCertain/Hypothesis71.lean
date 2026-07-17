import OddOrder.Peterfalvi.S08_CoherenceTheorems
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.GroupTheory.TISubset

/-!
# Peterfalvi (7.1)-(7.5) — TI-subset hypothesis, cardinality identity, family form

Split from the former monolithic `OddOrder.Peterfalvi.S09_NonexistenceCertain` (directory split, issue 0103).
-/

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

open scoped Classical in
/-- **The `ρ`-average collapses on a coset of constancy** (Peterfalvi (12.14), the
`ψ^ρ(x) = ψ(x)` step).  If `χ` is constant on the local coset `a·H(a)` — for the (12.14)
witness this follows from `ψ` being constant on `x·K ⊇ x·R(x)` ((12.3)/(12.4), with
`R(x) = C_K(x)` per Definition (8.14)) — then the `ρ`-average at `a` is just the value:
`χ^ρ(a) = χ(a)`. -/
theorem chiRho_apply_eq_of_forall_coset (H71 : Hypothesis71 G A L)
    (χ : ClassFunction G ℂ) {a : L} (ha : (a : G) ∈ A)
    (hconst : ∀ y : G, y ∈ H71.hyp.H ⟨(a : G), ha⟩ → χ ((a : G) * y) = χ (a : G)) :
    H71.chiRho χ a = χ (a : G) := by
  rw [H71.chiRho_of_mem _ ha]
  have hpt : ∀ x : H71.hyp.H ⟨(a : G), ha⟩,
      χ ((a : G) * (x : G)) = χ (a : G) := fun x => hconst (x : G) x.2
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

end OddOrder.Peterfalvi.S09
