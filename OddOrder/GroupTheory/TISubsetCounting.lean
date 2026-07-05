/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.TISubset
import OddOrder.GroupTheory.ConjClassSet
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Conjugation-invariant sums over the saturation of a TI-subset

`OddOrder.GroupTheory` shared module (issue 9011): for a TI-subset `A ⊆ G` with
stabilizing normalizer-bound `L`, the conjugacy saturation `𝒞_G(A) = A^G` is the
disjoint union of the `[G : L]` conjugates `g • A`, so a conjugation-invariant
function sums over it to `[G : L]` times its `A`-sum:

  `∑_{x ∈ A^G} f x = [G : L] · ∑_{a ∈ A} f a`.

This is the weighted refinement of the cardinality count
`OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset` (`|A^G| = |A|·[G:L]`, take
`f = 1`) and of the relative measure `OddOrder.Peterfalvi.S16.orbit_normSq_term`
(`|A^G|/|G| = |A|/|L|`).  The weighted form is what the norm cascade of
Peterfalvi §13 consumes: the Parseval splits (13.10.1)/(13.10.2) turn
`(1/|G|)·∑_{(H^#)^G} |χ|²` into `(1/|S|)·∑_{H^#} |χ|²` for the class function
`|χ|²`, and the disjoint-cover count (13.10.3) is the `f = 1` case.

## Main results

* `IsTISubset.sum_conjClassSet`: the sum transport above, for `f : G → M` with
  `M` an additive commutative monoid and `f` constant on conjugacy classes.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
  (13.10) — "Since `H^#` is a TI-subset of `G` with normalizer `S`".
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

open scoped Pointwise

/-- **Conjugation-invariant sums over a TI-saturation** (issue 9011): for a TI-subset `A`
with normalizer-bound `L` that stabilizes it (`A^l = A` for `l ∈ L`), and a
conjugation-invariant `f`, the sum of `f` over the saturation `𝒞_G(A) = A^G` is `[G : L]`
times the sum over `A`.  The saturation is the disjoint union of the conjugates `g • A`
indexed by the cosets `gL` (disjointness = the TI condition via `mem_of_conj_mem_conj`),
and each conjugate contributes the same sum (conjugation-invariance of `f`).

Weighted refinement of `OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset`; the
Parseval-split engine of the Peterfalvi (13.10) norm estimates. -/
theorem sum_conjClassSet [Finite G] {A : Set G} {L : Subgroup G}
    {M : Type*} [AddCommMonoid M] (f : G → M)
    (hTI : IsTISubset A L) (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) :
    ∑ x ∈ (Set.toFinite (conjClassSet A)).toFinset, f x
      = L.index • ∑ a ∈ (Set.toFinite A).toFinset, f a := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ L) := Fintype.ofFinite _
  -- The coset-indexed conjugate family `B (gL) = g • A` (well-defined by `L`-stability).
  have hwd : ∀ g₁ g₂ : G, QuotientGroup.leftRel L g₁ g₂ →
      MulAut.conj g₁ • A = MulAut.conj g₂ • A := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    calc MulAut.conj g₁ • A
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [hstab _ hrel]
      _ = MulAut.conj g₂ • A := by rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
  set B : G ⧸ L → Set G := Quotient.lift (fun g => MulAut.conj g • A) hwd with hBdef
  have hBval : ∀ g : G, B (QuotientGroup.mk g) = MulAut.conj g • A := fun g => rfl
  -- The saturation is the union of the conjugates.
  have hunion : conjClassSet A = ⋃ q : G ⧸ L, B q := by
    ext y
    rw [mem_conjClassSet, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, g, rfl⟩
      refine ⟨QuotientGroup.mk g, ?_⟩
      rw [hBval, Set.mem_smul_set]
      exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      rw [hBval, Set.mem_smul_set] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ⟨a, ha, g, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  -- Distinct cosets give disjoint conjugates (the TI condition).
  have hdisj : ∀ q q' : G ⧸ L, q ≠ q' → Disjoint (B q) (B q') := by
    intro q q' hqq'
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g', rfl⟩ := Quotient.exists_rep q'
    rw [hBval, hBval, Set.disjoint_left]
    rintro y hy hy'
    rw [Set.mem_smul_set] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨a', ha', heq⟩ := hy'
    have he : g * a * g⁻¹ = g' * a' * g'⁻¹ := by
      rw [MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply] at heq
      exact heq.symm
    refine hqq' (Quotient.sound ?_)
    change (QuotientGroup.leftRel L) g g'
    rw [QuotientGroup.leftRel_apply,
      show g⁻¹ * g' = (g'⁻¹ * g)⁻¹ from by group]
    exact L.inv_mem (hTI.mem_of_conj_mem_conj ha ha' he)
  -- Each conjugate sums to the `A`-sum (conjugation-invariance).
  have hBsum : ∀ q : G ⧸ L,
      ∑ x ∈ (Set.toFinite (B q)).toFinset, f x = ∑ a ∈ (Set.toFinite A).toFinset, f a := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    have himg : (Set.toFinite (B (QuotientGroup.mk g))).toFinset
        = Finset.image (fun a => g * a * g⁻¹) (Set.toFinite A).toFinset := by
      ext x
      rw [Set.Finite.mem_toFinset, hBval, Set.mem_smul_set, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, (Set.toFinite A).mem_toFinset.mpr ha,
          by rw [MulAut.smul_def, MulAut.conj_apply]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, (Set.toFinite A).mem_toFinset.mp ha,
          by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    have hinj : ∀ a ∈ (Set.toFinite A).toFinset, ∀ b ∈ (Set.toFinite A).toFinset,
        g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a _ b _ hab => by
      have := congrArg (fun x => g⁻¹ * x * g) hab
      simpa [mul_assoc] using this
    rw [himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun a _ => hf g a
  -- Assemble: sum over the union = index • the `A`-sum.
  have hsplit : (Set.toFinite (conjClassSet A)).toFinset
      = Finset.univ.biUnion (fun q : G ⧸ L => (Set.toFinite (B q)).toFinset) := by
    ext x
    rw [Set.Finite.mem_toFinset, hunion, Set.mem_iUnion, Finset.mem_biUnion]
    exact ⟨fun ⟨q, hq⟩ => ⟨q, Finset.mem_univ q, (Set.toFinite _).mem_toFinset.mpr hq⟩,
      fun ⟨q, _, hq⟩ => ⟨q, (Set.toFinite _).mem_toFinset.mp hq⟩⟩
  rw [hsplit, Finset.sum_biUnion (fun q _ q' _ hqq' =>
    Finset.disjoint_left.mpr (fun _ hx hx' =>
      Set.disjoint_left.mp (hdisj q q' hqq') ((Set.toFinite _).mem_toFinset.mp hx)
        ((Set.toFinite _).mem_toFinset.mp hx')))]
  rw [Finset.sum_congr rfl (fun q _ => hBsum q), Finset.sum_const, Finset.card_univ,
    Subgroup.index, Nat.card_eq_fintype_card]

/-- **Induced value on the TI-saturation** (Peterfalvi (7.2)/(13.2.e), value half): for a
TI-subset `A ⊆ L` with `L`-stable `A` and an `A`-supported class function `α` of `L`,
the induced class function `Ind_L^G α` takes the value `α(a)` at every conjugate
`g = y·a·y⁻¹` of every `a ∈ A`.  The nonvanishing induction summands are indexed by
exactly the coset `yL` (membership ⟸ `L`-stability, ⟹ the TI condition), each
contributing the class value `α(a)`; the normalization `⅟|L|` collapses the count.
This is what identifies the TI Dade isometry with `Ind_L^G` (Peterfalvi (2.5)+(7.2)). -/
theorem induce_apply_of_mem_conj {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (hTI : IsTISubset A L) (hAL : A ⊆ (L : Set G))
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {a g y : G} (ha : a ∈ A) (hg : g = y * a * y⁻¹) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = α ⟨a, hAL ha⟩ := by
  classical
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply]
  -- each summand is `α(a)` on the coset `yL` and `0` elsewhere
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm L α x g
      = if y⁻¹ * x ∈ L then α ⟨a, hAL ha⟩ else 0 := by
    intro x
    by_cases hx : y⁻¹ * x ∈ L
    · rw [if_pos hx]
      -- `x⁻¹ g x = (y⁻¹x)⁻¹ a (y⁻¹x) ∈ A` by `L`-stability
      have hxa : x⁻¹ * g * x = (y⁻¹ * x)⁻¹ * a * (y⁻¹ * x) := by
        rw [hg]; group
      have hmemA : x⁻¹ * g * x ∈ A := by
        rw [hxa]
        have h1 := hstab _ (inv_mem hx)
        rw [← h1]
        refine Set.mem_smul_set.mpr ⟨a, ha, ?_⟩
        rw [MulAut.smul_def, MulAut.conj_apply]
        group
      have hmemL : x⁻¹ * g * x ∈ L := hAL hmemA
      rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
      -- class value: `x⁻¹gx = (y⁻¹x)⁻¹ a (y⁻¹x)` is `L`-conjugate to `a`
      refine OddOrder.RepresentationTheory.ClassFunction.of_isConj α
        (isConj_iff.mpr ⟨⟨y⁻¹ * x, hx⟩, ?_⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxa]
      group
    · rw [if_neg hx]
      by_cases hmemL : x⁻¹ * g * x ∈ L
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
        -- the value vanishes: `x⁻¹gx ∉ A`, else the TI condition forces `y⁻¹x ∈ L`
        refine hsupp _ (fun hmemA => hx ?_)
        have hconj : (x⁻¹ * y) * a * (x⁻¹ * y)⁻¹ = x⁻¹ * g * x := by
          rw [hg]; group
        have h1 : (1 : G)⁻¹ * (x⁻¹ * y) ∈ L :=
          hTI.mem_of_conj_mem_conj ha hmemA (by rw [hconj]; group)
        rw [inv_one, one_mul] at h1
        have := inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem α hmemL]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero]
  -- the nonvanishing coset has exactly `|L|` elements
  have hcount : (Finset.univ.filter (fun x : G => y⁻¹ * x ∈ L)).card
      = Nat.card ↥L := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_bij
      (fun (x : G) (hx : x ∈ Finset.univ.filter (fun x : G => y⁻¹ * x ∈ L)) =>
        (⟨y⁻¹ * x, (Finset.mem_filter.mp hx).2⟩ : ↥L)) (fun _ _ => Finset.mem_univ _)
      ?_ ?_
    · intro x hx x' hx' hxx'
      have := congrArg Subtype.val hxx'
      simpa using this
    · intro l _
      refine ⟨y * (l : G), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [← mul_assoc, inv_mul_cancel, one_mul]; exact l.2⟩, ?_⟩
      apply Subtype.ext
      simp [← mul_assoc]
  rw [hcount, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

/-- **Induced value off the TI-saturation**: an `A`-supported class function of `L` induces to
a function vanishing off the conjugacy saturation `A^G` — every induction summand lands
outside the support. -/
theorem induce_apply_of_not_mem_conjClassSet {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {g : G} (hg : g ∉ conjClassSet A) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = 0 := by
  classical
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply]
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm L α x g = 0 := by
    intro x
    by_cases hmemL : x⁻¹ * g * x ∈ L
    · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
      refine hsupp _ (fun hmemA => hg ?_)
      rw [mem_conjClassSet]
      exact ⟨x⁻¹ * g * x, hmemA, x, by group⟩
    · exact OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem α hmemL
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero]

end IsTISubset

end OddOrder.GroupTheory
