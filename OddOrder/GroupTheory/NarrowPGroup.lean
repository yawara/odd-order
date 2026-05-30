/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRank
import Mathlib.GroupTheory.Complement

/-!
# Narrow p-Groups

`OddOrder.GroupTheory` shared module: the **narrow** `p`-group predicate `IsNarrow`
(Bender–Glauberman, _Local Analysis for the Odd Order Theorem_, §1 p.2 / §5 p.44).

This is a cross-cutting concept used by BG §5 (narrow `p`-groups proper) and cited in
§6/§10/§16 and Peterfalvi §9, so it lives in the shared `GroupTheory` namespace alongside
`pRank`, `Omega`, `SCN` rather than in a single `BG` section file.

## Main definitions

* `OddOrder.GroupTheory.IsNarrow p R`: a `p`-group `R` is *narrow* iff `r(R) ≤ 2`
  (`pRank R p ≤ 2`) **or** there is an order-`p` subgroup `R₀` whose centralizer is an
  internal direct product `R₀ × R₁` with `R₁` cyclic (BG `C_R(R₀) = R₀ × R₁`).

## Main results

* `OddOrder.GroupTheory.isNarrow_of_pRank_le_two`: `pRank R p ≤ 2 → IsNarrow p R`.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  Chapter I §1 (p.2), §5 (p.44), mmd `references/bg/local-analysis.mmd` L354, L1789.
-/

namespace OddOrder.GroupTheory

/-- **BG narrow `p`-group** (§1 p.2 / §5 p.44). For a prime `p`, a `p`-group `R` is
*narrow* iff `r(R) ≤ 2` (`pRank R p ≤ 2`) or there is an order-`p` subgroup `R₀` whose
centralizer is an internal direct product `R₀ × R₁` with `R₁` cyclic.

The internal direct product `C_R(R₀) = R₀ × R₁` is encoded as `Subgroup.IsComplement' R₀ R₁`
(so `R₀ ⊓ R₁ = ⊥` and `R₀ ⊔ R₁ = ⊤` as an internal direct product) together with the
equation `Subgroup.centralizer R₀ = R₀ ⊔ R₁` pinning the product down to the whole
centralizer. The naïve form `pRank R p ≤ 2` is used for `r(R) ≤ 2`; BG Theorem 5.3 /
Corollary 5.4 supply the equivalent characterisations when `r(R) ≥ 3`. -/
def IsNarrow (p : ℕ) (R : Type*) [Group R] : Prop :=
  pRank R p ≤ 2 ∨
    ∃ R₀ R₁ : Subgroup R, Nat.card R₀ = p ∧ IsCyclic R₁ ∧
      Subgroup.IsComplement' R₀ R₁ ∧ Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁

/-- A `p`-group of rank at most `2` is narrow (the first disjunct of `IsNarrow`). -/
theorem isNarrow_of_pRank_le_two {p : ℕ} {R : Type*} [Group R] (h : pRank R p ≤ 2) :
    IsNarrow p R :=
  Or.inl h

end OddOrder.GroupTheory
