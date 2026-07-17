/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Isaacs Thm 5.10: Dietzmann's theorem (p. 159)

**Isaacs, _Finite Group Theory_ (AMS GSM 92), §5B, pp. 158-159.**

Dietzmann's theorem (`dietzmann` below): let `G` be a (not necessarily finite) group and let
`X ⊆ G` be a finite subset that is closed under conjugation, and assume there is a positive
integer `n` with `x ^ n = 1` for all `x ∈ X`.  Then `⟨X⟩` is a finite subgroup of `G`.

In the book this is the final ingredient of the proof of **Thm 5.7** (Schur: if
`|G : Z(G)| < ∞` then `G'` is finite), together with Lemma 5.8 and Corollary 5.9.  On the
mathlib side Schur's theorem is already covered by
`Subgroup.card_commutator_le_of_finite_commutatorSet` (`Mathlib.GroupTheory.Schreier`), whose
proof goes through Schreier's lemma and `closureCommutatorRepresentatives` instead, so
Dietzmann's theorem was not needed there (see `OddOrder/Isaacs/Ch05_Transfer/Basic.lean` §5B).
Dietzmann's theorem itself is not in mathlib; we prove it here to complete the formalization
of Isaacs §5B at book strength.

## Proof outline (the book's proof, recast with lists)

1. `Dietzmann.exists_list_subset_prod_eq`: a product of elements of `X ∪ X⁻¹` is a product of
   elements of `X` alone: replace an entry `y` with `y⁻¹ ∈ X` by `n - 1` copies of `y⁻¹`,
   using `y = (y⁻¹) ^ (n - 1)`.  Combined with `Subgroup.closure_toSubmonoid` and
   `Submonoid.exists_list_of_mem_closure`, every element of `⟨X⟩` is a product of a list with
   all entries in `X` (the book's set `S`).
2. `Dietzmann.exists_cons_prod_eq_of_mem` (one step of the book's key rewriting argument): if
   `x` occurs in `l`, then `l.prod = x * l'.prod` where `l'` again has all entries in `X` (the
   factors before the first occurrence of `x` are conjugated by `x`, using closure of `X`
   under conjugation), `l'` is one entry shorter, and `l'` still contains at least
   `l.count x - 1` occurrences of `x`.
3. `Dietzmann.exists_pow_mul_prod_eq`: iterating step 2, if `k ≤ l.count x` then
   `l.prod = x ^ k * l'.prod` with entries of `l'` in `X` and `l'.length + k = l.length`.
4. `Dietzmann.exists_count_ge_of_length_gt` (the pigeonhole step): a list with entries in `X`
   of length `> (n - 1) * |X|` has some `x ∈ X` occurring at least `n` times.
5. `Dietzmann.exists_prod_eq_length_le`: combining 3 and 4 with `x ^ n = 1`, every product of
   members of `X` is a product of at most `(n - 1) * |X|` members of `X`.
6. `Dietzmann.finite_setOf_prod_of_length_le`: the set of products of at most `N` members of
   the finite set `X` is finite (induction on `N`).

## Main results

- `OddOrder.Isaacs.Ch05.dietzmann_setFinite`: **Isaacs Thm 5.10**, `Set.Finite` form.
- `OddOrder.Isaacs.Ch05.dietzmann`: **Isaacs Thm 5.10**, `Finite`-subtype form.
-/

namespace OddOrder.Isaacs.Ch05

section /- 5B: Central transfer, Schur, Dietzmann (pp. 153-159) -/

open Pointwise

variable {G : Type*} [Group G] {X : Set G}

namespace Dietzmann

/-- Step 1 of Dietzmann's theorem (**Isaacs Thm 5.10**): a product of elements of `X ∪ X⁻¹` is
a product of elements of `X` alone, provided `x ^ n = 1` (`n > 0`) for all `x ∈ X`: an entry
`y` with `y⁻¹ ∈ X` equals `(y⁻¹) ^ (n - 1)`, i.e. `n - 1` copies of the member `y⁻¹` of `X`. -/
theorem exists_list_subset_prod_eq {n : ℕ} (hn : 0 < n) (hexp : ∀ x ∈ X, x ^ n = 1)
    {l : List G} (hl : ∀ y ∈ l, y ∈ X ∨ y⁻¹ ∈ X) :
    ∃ l' : List G, (∀ y ∈ l', y ∈ X) ∧ l'.prod = l.prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons y t ih =>
    obtain ⟨t', ht'X, ht'prod⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rcases hl y (by simp) with hy | hy
    · refine ⟨y :: t', fun z hz => ?_, by rw [List.prod_cons, List.prod_cons, ht'prod]⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · exact ht'X z hz
    · have hpow : (y⁻¹ : G) ^ (n - 1) = y := by
        have h1 : (y⁻¹ : G) ^ (n - 1) * y⁻¹ = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
          exact hexp _ hy
        simpa using eq_inv_of_mul_eq_one_left h1
      refine ⟨List.replicate (n - 1) y⁻¹ ++ t', fun z hz => ?_, ?_⟩
      · rcases List.mem_append.mp hz with hz | hz
        · rw [List.eq_of_mem_replicate hz]; exact hy
        · exact ht'X z hz
      · rw [List.prod_append, List.prod_replicate, hpow, List.prod_cons, ht'prod]

section Count

variable [DecidableEq G]

/-- One step of the rewriting argument in the proof of **Isaacs Thm 5.10**: if `x` occurs in a
list `l` with entries in the conjugation-closed set `X`, then `l.prod = x * l'.prod` where
`l'` again has all entries in `X` (the factors preceding the first occurrence of `x` get
conjugated by `x`), `l'` is one entry shorter, and at most one occurrence of `x` is lost. -/
theorem exists_cons_prod_eq_of_mem (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X)
    {l : List G} (hl : ∀ y ∈ l, y ∈ X) {x : G} (hx : x ∈ l) :
    ∃ l' : List G, (∀ y ∈ l', y ∈ X) ∧ x * l'.prod = l.prod ∧
      l'.length + 1 = l.length ∧ l.count x ≤ l'.count x + 1 := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
    rcases eq_or_ne y x with rfl | hyx
    · exact ⟨t, fun z hz => hl z (List.mem_cons_of_mem _ hz), by rw [List.prod_cons],
        by rw [List.length_cons], by simp⟩
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hyx
        · exact h
      obtain ⟨t', ht'X, ht'prod, ht'len, ht'cnt⟩ :=
        ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hxt
      refine ⟨x⁻¹ * y * x :: t', fun z hz => ?_, ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · simpa using hconj y (hl y (by simp)) x⁻¹
        · exact ht'X z hz
      · rw [List.prod_cons, List.prod_cons, ← ht'prod]
        simp [mul_assoc]
      · simp only [List.length_cons]
        omega
      · have h1 : t'.count x ≤ (x⁻¹ * y * x :: t').count x := by
          rw [List.count_cons]
          omega
        rw [List.count_cons_of_ne hyx]
        omega

/-- Iterated form of `exists_cons_prod_eq_of_mem`: if `x` occurs at least `k` times in `l`
(entries in the conjugation-closed set `X`), then `l.prod = x ^ k * l'.prod` for a list `l'`
with entries in `X` and `l'.length + k = l.length`.  This is the book's "we can assume the
first `k` factors are all equal to `x`". -/
theorem exists_pow_mul_prod_eq (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) {x : G} :
    ∀ {k : ℕ} {l : List G}, (∀ y ∈ l, y ∈ X) → k ≤ l.count x →
      ∃ l' : List G, (∀ y ∈ l', y ∈ X) ∧ x ^ k * l'.prod = l.prod ∧
        l'.length + k = l.length := by
  intro k
  induction k with
  | zero =>
    intro l hl _
    exact ⟨l, hl, by rw [pow_zero, one_mul], rfl⟩
  | succ k ih =>
    intro l hl hcnt
    have hx : x ∈ l := List.count_pos_iff.mp (by omega)
    obtain ⟨l₁, hl₁X, hl₁prod, hl₁len, hl₁cnt⟩ := exists_cons_prod_eq_of_mem hconj hl hx
    obtain ⟨l', hl'X, hl'prod, hl'len⟩ := ih hl₁X (by omega)
    refine ⟨l', hl'X, ?_, by omega⟩
    rw [pow_succ', mul_assoc, hl'prod, hl₁prod]

omit [Group G] in
/-- The pigeonhole step in the proof of **Isaacs Thm 5.10**: a list with entries in the finite
set `X` of length greater than `(n - 1) * |X|` has some entry `x ∈ X` occurring at least `n`
times. -/
theorem exists_count_ge_of_length_gt (hfin : X.Finite) {n : ℕ} {l : List G}
    (hl : ∀ y ∈ l, y ∈ X) (hlen : (n - 1) * hfin.toFinset.card < l.length) :
    ∃ x ∈ X, n ≤ l.count x := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ x ∈ hfin.toFinset, l.count x = l.length := by
    rw [← List.sum_toFinset_count_eq_length l]
    refine (Finset.sum_subset
      (fun y hy => hfin.mem_toFinset.mpr (hl y (List.mem_toFinset.mp hy)))
      fun x _ hx => ?_).symm
    exact List.count_eq_zero_of_not_mem fun h => hx (List.mem_toFinset.mpr h)
  have hbound : l.length ≤ hfin.toFinset.card * (n - 1) := by
    calc l.length = ∑ x ∈ hfin.toFinset, l.count x := hsum.symm
      _ ≤ ∑ _x ∈ hfin.toFinset, (n - 1) :=
        Finset.sum_le_sum fun x hx => by
          have := hcon x (hfin.mem_toFinset.mp hx)
          omega
      _ = hfin.toFinset.card * (n - 1) := Finset.sum_const_nat fun _ _ => rfl
  exact absurd hlen (not_lt.mpr (hbound.trans_eq (Nat.mul_comm _ _)))

end Count

/-- Length reduction for **Isaacs Thm 5.10**: every product of members of `X` is a product of
at most `(n - 1) * |X|` members of `X`.  (The auxiliary bound `m` on the length drives the
induction; the book instead takes a representation of minimal length.) -/
theorem exists_prod_eq_length_le (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X)
    (hfin : X.Finite) {n : ℕ} (hn : 0 < n) (hexp : ∀ x ∈ X, x ^ n = 1) :
    ∀ (m : ℕ) {l : List G}, l.length ≤ m → (∀ y ∈ l, y ∈ X) →
      ∃ l' : List G, (∀ y ∈ l', y ∈ X) ∧ l'.prod = l.prod ∧
        l'.length ≤ (n - 1) * hfin.toFinset.card := by
  classical
  intro m
  induction m with
  | zero =>
    intro l hlen hl
    exact ⟨l, hl, rfl, hlen.trans (Nat.zero_le _)⟩
  | succ m ih =>
    intro l hlen hl
    by_cases hle : l.length ≤ (n - 1) * hfin.toFinset.card
    · exact ⟨l, hl, rfl, hle⟩
    · push Not at hle
      obtain ⟨x, hxX, hxcnt⟩ := exists_count_ge_of_length_gt hfin hl hle
      obtain ⟨l₁, hl₁X, hl₁prod, hl₁len⟩ := exists_pow_mul_prod_eq hconj hl hxcnt
      obtain ⟨l', hl'X, hl'prod, hl'len⟩ := ih (by omega) hl₁X
      refine ⟨l', hl'X, hl'prod.trans ?_, hl'len⟩
      rw [← hl₁prod, hexp x hxX, one_mul]

/-- The set of products of at most `N` members of a finite set `X` is finite (induction on
`N`: such a product is either the empty product or `y * (product of at most N - 1 members)`
with `y ∈ X`). -/
theorem finite_setOf_prod_of_length_le (hfin : X.Finite) (N : ℕ) :
    {g : G | ∃ l : List G, (∀ y ∈ l, y ∈ X) ∧ l.length ≤ N ∧ l.prod = g}.Finite := by
  induction N with
  | zero =>
    refine (Set.finite_singleton (1 : G)).subset ?_
    rintro g ⟨l, -, hlen, rfl⟩
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    simp [hlen]
  | succ N ih =>
    refine (ih.union (Set.Finite.image2 (· * ·) hfin ih)).subset ?_
    rintro g ⟨l, hlX, hlen, rfl⟩
    cases l with
    | nil => exact Set.mem_union_left _ ⟨[], by simp, Nat.zero_le _, rfl⟩
    | cons y t =>
      rw [List.prod_cons]
      refine Set.mem_union_right _ (Set.mem_image2_of_mem (hlX y (by simp)) ?_)
      refine ⟨t, fun z hz => hlX z (List.mem_cons_of_mem _ hz), ?_, rfl⟩
      simp only [List.length_cons] at hlen
      omega

end Dietzmann

/-- **Isaacs Thm 5.10** (Dietzmann), `Set.Finite` form: if `X` is a finite subset of a (not
necessarily finite) group `G`, closed under conjugation, and there is `n > 0` with `x ^ n = 1`
for all `x ∈ X`, then the carrier of `⟨X⟩` is a finite set.  Every element of `⟨X⟩` is a
product of at most `(n - 1) * |X|` members of `X`. -/
theorem dietzmann_setFinite (hfin : X.Finite)
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X)
    {n : ℕ} (hn : 0 < n) (hexp : ∀ x ∈ X, x ^ n = 1) :
    (Subgroup.closure X : Set G).Finite := by
  classical
  refine (Dietzmann.finite_setOf_prod_of_length_le hfin
    ((n - 1) * hfin.toFinset.card)).subset ?_
  intro g hg
  have hg' : g ∈ Submonoid.closure (X ∪ X⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hg
  obtain ⟨l, hlmem, hlprod⟩ := Submonoid.exists_list_of_mem_closure hg'
  simp only [Set.mem_union, Set.mem_inv] at hlmem
  obtain ⟨l₁, hl₁X, hl₁prod⟩ := Dietzmann.exists_list_subset_prod_eq hn hexp hlmem
  obtain ⟨l₂, hl₂X, hl₂prod, hl₂len⟩ :=
    Dietzmann.exists_prod_eq_length_le hconj hfin hn hexp l₁.length le_rfl hl₁X
  exact ⟨l₂, hl₂X, hl₂len, by rw [hl₂prod, hl₁prod, hlprod]⟩

/-- **Isaacs Thm 5.10** (Dietzmann): let `G` be a (not necessarily finite) group and let
`X ⊆ G` be a finite subset that is closed under conjugation.  Assume that there is a positive
integer `n` such that `x ^ n = 1` for all `x ∈ X`.  Then `⟨X⟩` is a finite subgroup of `G`. -/
theorem dietzmann (hfin : X.Finite)
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X)
    {n : ℕ} (hn : 0 < n) (hexp : ∀ x ∈ X, x ^ n = 1) :
    Finite ↥(Subgroup.closure X) :=
  (dietzmann_setFinite hfin hconj hn hexp).to_subtype

end

end OddOrder.Isaacs.Ch05
