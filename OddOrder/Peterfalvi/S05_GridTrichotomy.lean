/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Peterfalvi (3.8): the additive-grid trichotomy

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §3, pp. 15-20.

This file isolates the **abstract combinatorial core** of Peterfalvi Theorem (3.8).  In the source,
`a_{ij} = ⟨ψ, ω_{ij}^σ⟩` is the coefficient grid of a class function `ψ` against the `σ`-images of
the irreducible characters of `W = W₁ × W₂`; by (3.7) it is *additively separable*
(`a_{ij} + a_{i'j'} = a_{ij'} + a_{i'j}`), and `NC(ψ)` is the number of nonzero `a_{ij}`.  Theorem
(3.8) classifies such grids when `NC(ψ) < 2w₁` (and `w₁ < w₂`): the grid is zero, or a single
constant full column, or a single constant full row.

We state and prove this purely in terms of a `ℂ`-valued grid `a : ι × κ → ℂ` (no character theory):
the abstract lemma `grid_trichotomy` is then ready to be specialised to the `σ`-coefficient grid by
the §6 consumers (Peterfalvi (4.8)).  The companion `grid_eq_zero_of_ncard_support_lt`
(`S05_SigmaIsometry`) is the `NC < min(w₁,w₂)` corollary; this file supplies the full `NC < 2w₁`
trichotomy needed once `w₁` can be the smaller index.

The key simplification over the textbook's index-relabelling argument: an additively separable grid
factors as `a (i, j) = f i + g j` (`exists_param`).  Then the trichotomy is a clean case split on
whether `f` / `g` is constant, with a double-counting bound ruling out the "both non-constant" case.
-/

namespace OddOrder.Peterfalvi.S05

open scoped BigOperators

/-- **Additive separability ⟹ rank-one factorisation.**  A grid whose mixed differences vanish
(`a (i,j) + a (i',j') = a (i,j') + a (i',j)`, the (3.7) identity) factors as `a (i, j) = f i + g j`.
Fix base points `i₀, j₀`; take `f i = a (i, j₀)` and `g j = a (i₀, j) - a (i₀, j₀)`. -/
theorem exists_param {ι κ : Type*} [Nonempty ι] [Nonempty κ] (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j)) :
    ∃ (f : ι → ℂ) (g : κ → ℂ), ∀ i j, a (i, j) = f i + g j := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  refine ⟨fun i => a (i, j₀), fun j => a (i₀, j) - a (i₀, j₀), fun i j => ?_⟩
  have h := hadd i i₀ j j₀
  linear_combination h

/-- Support count when the grid depends only on the second coordinate: the nonzero set is a union
of full columns, so its size is `|ι| · #{j | b j ≠ 0}`. -/
theorem card_support_const_snd {ι κ : Type*} [Fintype ι] [Fintype κ] (b : κ → ℂ) :
    (Finset.univ.filter (fun p : ι × κ => b p.2 ≠ 0)).card
      = Fintype.card ι * (Finset.univ.filter (fun j => b j ≠ 0)).card := by
  classical
  have h : (Finset.univ.filter (fun p : ι × κ => b p.2 ≠ 0))
      = (Finset.univ : Finset ι) ×ˢ (Finset.univ.filter (fun j => b j ≠ 0)) := by
    ext ⟨i, j⟩
    simp [Finset.mem_filter, Finset.mem_product]
  rw [h, Finset.card_product, Finset.card_univ]

/-- Support count when the grid depends only on the first coordinate: the nonzero set is a union of
full rows, so its size is `#{i | c i ≠ 0} · |κ|`. -/
theorem card_support_const_fst {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℂ) :
    (Finset.univ.filter (fun p : ι × κ => c p.1 ≠ 0)).card
      = (Finset.univ.filter (fun i => c i ≠ 0)).card * Fintype.card κ := by
  classical
  have h : (Finset.univ.filter (fun p : ι × κ => c p.1 ≠ 0))
      = (Finset.univ.filter (fun i => c i ≠ 0)) ×ˢ (Finset.univ : Finset κ) := by
    ext ⟨i, j⟩
    simp [Finset.mem_filter, Finset.mem_product]
  rw [h, Finset.card_product, Finset.card_univ]

/-- A function with at most one nonzero value is either identically zero or supported on a single
point `j₀`. -/
theorem eq_zero_or_single {κ : Type*} [Fintype κ] (b : κ → ℂ)
    (h : (Finset.univ.filter (fun j => b j ≠ 0)).card ≤ 1) :
    (∀ j, b j = 0) ∨ ∃ j₀ : κ, b j₀ ≠ 0 ∧ ∀ j, j ≠ j₀ → b j = 0 := by
  classical
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left
    intro j
    by_contra hj
    have : j ∈ Finset.univ.filter (fun j => b j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [Finset.card_eq_zero.mp h0] at this
    simp at this
  · right
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp h1
    have hmem : ∀ j, b j ≠ 0 ↔ j = j₀ := by
      intro j
      rw [← Finset.mem_singleton, ← hj₀, Finset.mem_filter]
      exact ⟨fun hb => ⟨Finset.mem_univ j, hb⟩, fun h => h.2⟩
    refine ⟨j₀, (hmem j₀).mpr rfl, fun j hj => ?_⟩
    by_contra hb
    exact hj ((hmem j).mp hb)

/-- **Both factors non-constant ⟹ large support.**  For a rank-one grid `a (i,j) = f i + g j`
with neither `f` nor `g` constant, the support has at least `|ι| + |κ| - 2` elements.

Counting per row: each row has `≥ 1` nonzero entry (`g` non-constant), and two rows `i₁, i₂` with
`f i₁ ≠ f i₂` together have `≥ |κ|` nonzero entries (their zero-sets `{j | g j = -f i}` are
disjoint).
Summing: `#support = ∑_i (row count) ≥ |κ| + (|ι| - 2)·1 = |ι| + |κ| - 2`. -/
theorem card_support_ge_of_not_const {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℂ) (g : κ → ℂ) (hf : ¬ ∀ i i', f i = f i') (hg : ¬ ∀ j j', g j = g j') :
    Fintype.card ι + Fintype.card κ
      ≤ (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0)).card + 2 := by
  classical
  -- support card = ∑ i, (nonzeros in row i)
  have hcard : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0)).card
      = ∑ i, (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => (Finset.card_filter _ _).symm)
  -- each row has ≥ 1 nonzero
  have hrow1 : ∀ i, 1 ≤ (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j, f i + g j ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hg (fun j j' => by linear_combination hc j - hc j')
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  -- two distinguished rows together cover all columns
  obtain ⟨i₁, i₂, hi⟩ : ∃ i₁ i₂, f i₁ ≠ f i₂ := by
    by_contra hc; push_neg at hc; exact hf hc
  have hi12 : i₁ ≠ i₂ := fun h => hi (by rw [h])
  have hpair : Fintype.card κ
      ≤ (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0)).card
        + (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)).card := by
    -- zero-sets are disjoint; nonzero-sets cover κ
    have hcover : (Finset.univ : Finset κ)
        ⊆ (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0))
          ∪ (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)) := by
      intro j _
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : f i₁ + g j = 0
      · refine Or.inr ⟨Finset.mem_univ j, ?_⟩
        intro h2
        exact hi (by linear_combination h1 - h2)
      · exact Or.inl ⟨Finset.mem_univ j, h1⟩
    calc Fintype.card κ = (Finset.univ : Finset κ).card := (Finset.card_univ).symm
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
  -- assemble: split the sum off the pair `{i₁, i₂}`
  rw [hcard]
  have hsub : ({i₁, i₂} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub]
  have hpaircard : ({i₁, i₂} : Finset ι).card = 2 := Finset.card_pair hi12
  have hsdiffcard : (Finset.univ \ ({i₁, i₂} : Finset ι)).card + 2 = Fintype.card ι := by
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hpaircard, Finset.card_univ] at hc
    exact hc
  have hsumpair : ∑ i ∈ ({i₁, i₂} : Finset ι),
      (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card
      = (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0)).card
        + (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)).card :=
    Finset.sum_pair hi12
  have hsumsdiff : (Finset.univ \ ({i₁, i₂} : Finset ι)).card
      ≤ ∑ i ∈ Finset.univ \ ({i₁, i₂} : Finset ι),
        (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    calc (Finset.univ \ ({i₁, i₂} : Finset ι)).card
        = ∑ _i ∈ Finset.univ \ ({i₁, i₂} : Finset ι), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hrow1 i)
  rw [hsumpair]
  omega

/-- **Peterfalvi (3.8), abstract trichotomy.**  Let `a : ι × κ → ℂ` be an additively separable grid
(`a (i,j) + a (i',j') = a (i,j') + a (i',j)`) with `|ι| + 2 ≤ |κ|` (the odd-order gap `w₁ + 2 ≤ w₂`)
and whose support has fewer than `2|ι|` elements (`NC(ψ) < 2w₁`).  Then exactly one of:

* (a) `a` is identically zero (`ψ = β`);
* (b) `a` is a constant nonzero indicator of a single column `j₀` (`ψ = c·∑_i ω_{i,j₀}^σ + β`);
* (c) `a` is a constant nonzero indicator of a single row `i₀` (`ψ = c·∑_j ω_{i₀,j}^σ + β`).

Factor `a (i,j) = f i + g j` (`exists_param`).  If `f` is constant the grid depends only on the
column, and `< 2|ι|` support forces `≤ 1` nonzero column (`eq_zero_or_single`) — case (a)/(b).  If
`g`
is constant, symmetrically `≤ 1` nonzero row (using `|κ| > |ι|`) — case (a)/(c).  If neither is
constant, the support has `≥ |ι| + |κ| - 2 ≥ 2|ι|` elements (`card_support_ge_of_not_const`),
contradicting the hypothesis. -/
theorem grid_trichotomy {ι κ : Type*} [Finite ι] [Finite κ] [Nonempty ι] [Nonempty κ]
    (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j))
    (hgap : Nat.card ι + 2 ≤ Nat.card κ)
    (hlt : {x | a x ≠ 0}.ncard < 2 * Nat.card ι) :
    (∀ x, a x = 0) ∨
      (∃ (j₀ : κ) (c : ℂ), c ≠ 0 ∧ (∀ i, a (i, j₀) = c) ∧ ∀ i j, j ≠ j₀ → a (i, j) = 0) ∨
      (∃ (i₀ : ι) (c : ℂ), c ≠ 0 ∧ (∀ j, a (i₀, j) = c) ∧ ∀ i j, i ≠ i₀ → a (i, j) = 0) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite _
  haveI : Fintype κ := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Nat.card_eq_fintype_card] at hlt
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hgap
  obtain ⟨f, g, hfg⟩ := exists_param a hadd
  -- rewrite the support filter in terms of `f, g`
  have hsupp : (Finset.univ.filter (fun x : ι × κ => a x ≠ 0))
      = Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0) :=
    Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hfg i j])
  rw [hsupp] at hlt
  by_cases hfc : ∀ i i', f i = f i'
  · -- `f` constant: grid depends only on the column
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hbeq : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0))
        = Finset.univ.filter (fun p : ι × κ => (fun j => f i₀ + g j) p.2 ≠ 0) :=
      Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hfc i i₀])
    rw [hbeq, card_support_const_snd (fun j => f i₀ + g j)] at hlt
    have hNκ : (Finset.univ.filter (fun j => f i₀ + g j ≠ 0)).card ≤ 1 := by
      rw [mul_comm] at hlt
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    rcases eq_zero_or_single (fun j => f i₀ + g j) hNκ with hz | ⟨j₀, hj₀, hrest⟩
    · exact Or.inl (fun ⟨i, j⟩ => by rw [hfg i j, hfc i i₀]; exact hz j)
    · refine Or.inr (Or.inl ⟨j₀, f i₀ + g j₀, hj₀, fun i => ?_, fun i j hj => ?_⟩)
      · rw [hfg i j₀, hfc i i₀]
      · rw [hfg i j, hfc i i₀]; exact hrest j hj
  · by_cases hgc : ∀ j j', g j = g j'
    · -- `g` constant: grid depends only on the row
      obtain ⟨j₀⟩ := ‹Nonempty κ›
      have hceq : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0))
          = Finset.univ.filter (fun p : ι × κ => (fun i => f i + g j₀) p.1 ≠ 0) :=
        Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hgc j j₀])
      rw [hceq, card_support_const_fst (fun i => f i + g j₀)] at hlt
      have hNι : (Finset.univ.filter (fun i => f i + g j₀ ≠ 0)).card ≤ 1 := by
        by_contra hge
        push_neg at hge
        have h2 : 2 * Fintype.card κ
            ≤ (Finset.univ.filter (fun i => f i + g j₀ ≠ 0)).card * Fintype.card κ := by
          gcongr
          omega
        omega
      rcases eq_zero_or_single (fun i => f i + g j₀) hNι with hz | ⟨i₀, hi₀, hrest⟩
      · exact Or.inl (fun ⟨i, j⟩ => by rw [hfg i j, hgc j j₀]; exact hz i)
      · refine Or.inr (Or.inr ⟨i₀, f i₀ + g j₀, hi₀, fun j => ?_, fun i j hi => ?_⟩)
        · rw [hfg i₀ j, hgc j j₀]
        · rw [hfg i j, hgc j j₀]; exact hrest i hi
    · -- neither constant: support too large, contradiction
      exfalso
      have hge := card_support_ge_of_not_const f g hfc hgc
      omega

end OddOrder.Peterfalvi.S05
