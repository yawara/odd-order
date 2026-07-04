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

end IsTISubset

end OddOrder.GroupTheory
