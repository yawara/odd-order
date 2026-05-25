/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.Inertia
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

/-!
# Clifford's theorem on irreducible characters of a normal subgroup

For a normal subgroup `H ⊴ G` and an irreducible complex character `χ ∈ Irr G`,
**Clifford's theorem** ([Is] Thm 6.5) describes the restriction `Res_H^G χ` in terms of
the `G`-conjugation action on `Irr H`:

> Every irreducible component `θ ∈ Irr H` of `Res χ` is a `G`-conjugate of every other,
> all of them appear with the same multiplicity, and
>
>   `Res_H^G χ = e_χ · (θ^{g_1} + θ^{g_2} + … + θ^{g_t})`,
>
> where `{g_1, …, g_t}` runs over a transversal of the inertia subgroup `T = I_G(θ)`
> in `G` (so `t = [G : T]`) and `e_χ = ⟨Res χ, θ⟩_H` is the common multiplicity.

A companion result ([Is] Thm 6.11) is the **inertia bijection**: induction from `T`
gives a bijection between `Irr(T)` lying over `θ` and `Irr(G)` lying over `θ`. The
precise statement is left as a TODO since it requires extra setup
(`InducedCharacter` numerical Frobenius reciprocity + multiplicity counting).

## Status

* The Clifford decomposition `clifford_decomposition` is stated below; the proof is
  deferred. It will follow from `InducedCharacter` + `SecondOrthogonality` once those
  Wave 1a modules have working proofs.
* `clifford_orbit_subset_inertia` is immediate from `ClassFunction.subgroup_le_inertia`.
* Proof-core routing: the remaining Clifford theorem proof is split into
  `issues/0026-peterfalvi-clifford-core.md`.  The blocker is not the current
  statement shape; it is the missing character-level induction/restriction API:
  numerical Frobenius reciprocity, restriction multiplicities, orbit equality of
  irreducible constituents, and the inertia-bijection package.

## Main statements

* `OddOrder.RepresentationTheory.clifford_decomposition` — the Clifford decomposition.
* `OddOrder.RepresentationTheory.clifford_orbit_subset_inertia` — `H ≤ I_G(θ)`.

## References

* Isaacs, *Character Theory of Finite Groups*, Theorem 6.5 (Clifford) and Theorem 6.11
  (Induction from inertia).
* Peterfalvi §3 (1.5) (Clifford suite), (1.7) (multiplicity-one for cyclic inertia).
* Bender–Glauberman §2 Prop 2.2 (Clifford for cyclic quotient `G/H`) — uses the same
  decomposition.
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

/-- **Clifford's theorem** ([Is] Thm 6.5): for `H ⊴ G` and `χ ∈ Irr G`, the restriction
`Res_H^G χ` decomposes as a positive multiple of a `G`-orbit sum of irreducible characters
of `H`.

The data `(t, e, θ)` provided by the conclusion:
* `t ≥ 1` — the orbit size `[G : I_G(θ_0)]`;
* `e ≥ 1` — the common multiplicity `⟨Res χ, θ_i⟩_H`;
* `θ : Fin t → ClassFunction ↥H ℂ` — an enumeration of the `G`-orbit of the irreducible
  components, with each `θ i` an irreducible character and pairwise distinct.

(Proof deferred: requires `InducedCharacter` + `SecondOrthogonality` machinery.) -/
theorem clifford_decomposition
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ∃ (t : ℕ) (h_pos : 0 < t) (e : ℕ) (_ : 0 < e) (θ : Fin t → ClassFunction ↥H ℂ),
      Function.Injective θ ∧
      (∀ i, IsIrreducibleCharacter (θ i)) ∧
      (∀ i, ∃ g : G, ClassFunction.conjBy g (θ ⟨0, h_pos⟩) = θ i) ∧
      ClassFunction.restrict H χ = (e : ℂ) • (∑ i : Fin t, θ i) := by
  sorry

/-- A corollary of the Clifford / inertia setup: the inertia subgroup of any class
function on `H` contains `H` itself. Immediate from `ClassFunction.subgroup_le_inertia`. -/
theorem clifford_orbit_subset_inertia (θ : ClassFunction ↥H ℂ) :
    H ≤ ClassFunction.inertia θ :=
  ClassFunction.subgroup_le_inertia θ

end OddOrder.RepresentationTheory
