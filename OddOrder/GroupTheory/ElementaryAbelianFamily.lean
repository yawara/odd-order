/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Elementary abelian subgroup families `ℰ_p^n(G)`

`OddOrder.GroupTheory` shared module: the Bender–Glauberman family `ℰ_p^n(G)` of elementary
abelian `p`-subgroups of a given order `p^n` (equivalently, rank `n`).

BG uses `ℰ_p^n(G)`, `ℰ^1(A)` and `ℰ²(R) ∩ ℰ*(R)` throughout §4–§16. The *maximal* family
`ℰ*` is the inclusion-maximal predicate `IsMaximalElementaryAbelian` (`NarrowPGroup`), so
`ℰ²(R) ∩ ℰ*(R)` is `Nat.card A = p^2 ∧ IsMaximalElementaryAbelian p A` at use sites; only the
order-indexed family `ℰ_p^n` is new and lives here.

## Main definitions

* `elemAbelianOfRank G p n` (BG `ℰ_p^n(G)`): elementary abelian `p`-subgroups of order `p^n`.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  Chapter I §4–§5, Chapter III §10–§13.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℰ_p^n(G)`**: the elementary abelian `p`-subgroups of `G` of order `p^n`
(equivalently, of rank `n`). The single-element form `ℰ^1(A)` (order-`p` subgroups of `A`)
is `{X ∈ elemAbelianOfRank G p 1 | X ≤ A}`. -/
def elemAbelianOfRank (G : Type*) [Group G] (p n : ℕ) : Set (Subgroup G) :=
  {A | A.IsElementaryAbelian p ∧ Nat.card A = p ^ n}

@[simp]
theorem mem_elemAbelianOfRank {p n : ℕ} {A : Subgroup G} :
    A ∈ elemAbelianOfRank G p n ↔ A.IsElementaryAbelian p ∧ Nat.card A = p ^ n :=
  Iff.rfl

/-- Membership of `ℰ_p^n` gives elementary abelianness. -/
theorem IsElementaryAbelian.of_mem_elemAbelianOfRank {p n : ℕ} {A : Subgroup G}
    (h : A ∈ elemAbelianOfRank G p n) : A.IsElementaryAbelian p :=
  h.1

end OddOrder.GroupTheory
