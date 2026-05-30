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

/-- **`E*(R)`: maximal elementary abelian subgroup** (BG §5 p.45). A subgroup `E ≤ R` is
`p`-elementary abelian and is contained in no strictly larger `p`-elementary abelian
subgroup of `R`.

The "no larger" condition is phrased as: any `p`-elementary abelian `F` with `E ≤ F`
satisfies `F = E`. BG's `E²(R) ∩ E*(R)` (elementary abelian of order `p²` not contained
in any `E_{p³}`) is expressed at use sites as
`Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E` (no separate abbreviation). -/
def IsMaximalElementaryAbelian (p : ℕ) {R : Type*} [Group R] (E : Subgroup R) : Prop :=
  E.IsElementaryAbelian p ∧
    ∀ F : Subgroup R, F.IsElementaryAbelian p → E ≤ F → F = E

namespace IsMaximalElementaryAbelian

variable {p : ℕ} {R : Type*} [Group R] {E F : Subgroup R}

/-- A maximal elementary abelian subgroup is, in particular, elementary abelian. -/
theorem isElementaryAbelian (h : IsMaximalElementaryAbelian p E) : E.IsElementaryAbelian p :=
  h.1

/-- Maximality: any `p`-elementary abelian `F ⊇ E` collapses back to `E`. -/
theorem eq_of_le (h : IsMaximalElementaryAbelian p E) (hF : F.IsElementaryAbelian p)
    (hEF : E ≤ F) : F = E :=
  h.2 F hF hEF

end IsMaximalElementaryAbelian

/-- **Existence of a maximal elementary abelian subgroup above a given one** (used by
BG Theorem 5.3 ⇐). In a finite group, every `p`-elementary abelian subgroup `E` is
contained in some `E* ∈ E*(R)`, i.e. a `p`-elementary abelian subgroup maximal under
inclusion.

This is a pure finite-poset maximality statement: take a `≤`-maximal element of the
finite subgroup lattice among the `p`-elementary abelian subgroups containing `E`
(`Finite.exists_le_maximal`); the maximality witness upgrades to
`IsMaximalElementaryAbelian` via antisymmetry. -/
theorem exists_maximalElementaryAbelian_ge
    {p : ℕ} {R : Type*} [Group R] [Finite R] {E : Subgroup R}
    (hE : E.IsElementaryAbelian p) :
    ∃ F : Subgroup R, E ≤ F ∧ IsMaximalElementaryAbelian p F := by
  obtain ⟨F, hEF, hFmax⟩ :=
    Finite.exists_le_maximal (p := fun F : Subgroup R => F.IsElementaryAbelian p) hE
  exact ⟨F, hEF, hFmax.1, fun G hG hFG => le_antisymm (hFmax.2 hG hFG) hFG⟩

end OddOrder.GroupTheory
