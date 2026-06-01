/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OpResidual

/-!
# `A`-invariant `π`-subgroup families `ℋ_H(A;π)` and `ℋ_H*(A;π)`

`OddOrder.GroupTheory` shared module for the Bender–Glauberman families of **`A`-invariant
`π`-subgroups** of a subgroup `H`, and their **maximal** members.

These are introduced in BG §7 (Hypothesis 7.1, mmd L2141) and are the carrier of the whole
Transitivity Theorem machinery; they recur through §8–§16. They live in the shared
`GroupTheory` namespace alongside `Subgroup.IsPiSubgroup` (`OpResidual`).

## Main definitions

* `hInvariant H A π` (BG `ℋ_H(A;π)`): the subgroups `Q ≤ H` that are `π`-subgroups
  (`Subgroup.IsPiSubgroup`) and are normalized by `A` (`A ≤ N_G(Q)`).
* `hInvariantStar H A π` (BG `ℋ_H*(A;π)`): the members of `ℋ_H(A;π)` that are maximal under
  inclusion within `ℋ_H(A;π)`.

The pervasive single-prime form `ℋ_H*(A;q)` is `hInvariantStar H A {q}`, and BG's `ℋ_G*(A;q)`
(taken inside all of `G`) is `hInvariantStar ⊤ A {q}`.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  Chapter II §7 (pp. 55-60).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℋ_H(A;π)`** (§7): the set of subgroups `Q ≤ H` that are `π`-subgroups and are
normalized by `A` (i.e. `A ⊆ N_G(Q)`). -/
def hInvariant (H A : Subgroup G) (π : Set ℕ) : Set (Subgroup G) :=
  {Q | Q ≤ H ∧ A ≤ Subgroup.normalizer Q ∧ Subgroup.IsPiSubgroup π Q}

/-- **BG `ℋ_H*(A;π)`** (§7): the members of `ℋ_H(A;π)` maximal under inclusion within the
family `ℋ_H(A;π)`. The Transitivity Theorem (§7) studies the `O_{π'}(C_G(A))`-action on this
set. The single-prime form `ℋ_H*(A;q)` is `hInvariantStar H A {q}`. -/
def hInvariantStar (H A : Subgroup G) (π : Set ℕ) : Set (Subgroup G) :=
  {Q | Q ∈ hInvariant H A π ∧ ∀ Q' ∈ hInvariant H A π, Q ≤ Q' → Q' = Q}

@[simp]
theorem mem_hInvariant {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G} :
    Q ∈ hInvariant H A π ↔
      Q ≤ H ∧ A ≤ Subgroup.normalizer Q ∧ Subgroup.IsPiSubgroup π Q :=
  Iff.rfl

@[simp]
theorem mem_hInvariantStar {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G} :
    Q ∈ hInvariantStar H A π ↔
      Q ∈ hInvariant H A π ∧ ∀ Q' ∈ hInvariant H A π, Q ≤ Q' → Q' = Q :=
  Iff.rfl

/-- A maximal `A`-invariant `π`-subgroup is in particular an `A`-invariant `π`-subgroup. -/
theorem hInvariantStar_subset_hInvariant {H A : Subgroup G} {π : Set ℕ} :
    hInvariantStar H A π ⊆ hInvariant H A π :=
  fun _ hQ => hQ.1

end OddOrder.GroupTheory
