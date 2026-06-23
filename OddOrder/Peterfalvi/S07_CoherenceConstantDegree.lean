/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi (5.7): the *standalone* constant-degree coherence theorem

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §5, (5.7).

> **(5.7)** Assume Hypothesis (5.2) and that `χ(1)` is independent of `χ` for `χ ∈ S`.  Then `S` is
> coherent.  (`references/peterfalvi/04.7_pp_25_29_Coherence.mmd:107`)

The §11/§13 maximal-subgroup analysis (Peterfalvi (11.5), repo `S13_MaximalIII_IV.HC_le_secondDerived`)
needs this: since `M'/M''` is abelian, the constituents of `S(M'')` all have equal degree, so (5.7)
makes `S(M'')` coherent — the coherence content of `M'' = HC`.

**Status (lane-c relane #8, issue 4012): scoping + signature skeleton.**  All the proof ingredients
already live in `S07_Coherence`: the (5.2) hypothesis carrier `S07.Hypothesis`, the (5.4)
decomposition `CharacterPsiDecomposition`, the (5.4.b)/(5.5) norm lemmas
(`norm_eq_and_X_eq_sum_of_norm_Y_ge` / `eq_sum_of_psi_eq_zero`), and the coherence constructor
`retarget_isCoherent_of_decompositions`.  So (5.7) is an *assembly*, not a missing-machinery gap
(unlike lane-h's (6.2) which needed the `h62` index oracle).  The proof (base case `|S| = 2` from
(5.2.d); inductive build of the auxiliary isometry `τ₁` via per-member `ψ = 0` decompositions, then
`retarget_isCoherent_of_decompositions`) is the next session's work; design + framework mapping are
in `notes/peterfalvi/s05_57_constant_degree_coherence_producer.md`.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]
variable [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {S : Set (ClassFunction L ℂ)} {A : Set L}

/-- **Peterfalvi (5.7), standalone form**: under the (5.2) coherence hypotheses, if every member of
`S` has the same degree `χ(1)`, then `(S, A, τ)` is coherent.

The constant-degree hypothesis `hconst` is stated faithfully (Peterfalvi assumes it); pinning down
exactly which step of the assembly consumes it — versus its being needed only for the equal-degree
*application* — is part of the implementation (see the design note).  `hne` is the nondegeneracy
witness of the (5.1) coherence predicate (an `A`-supported nonzero element of `ℤ[S]`).

This is the producer that `S13_MaximalIII_IV.HC_le_secondDerived` (Peterfalvi (11.5)) will cite, once
a `Hypothesis (5.2)` instance for `S(M'')` is constructed on the §13 Dade side. -/
theorem coherent_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A)
    (hconst : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1)
    (hne : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A ∧ φ ≠ 0) :
    Nonempty (IsCoherent hyp.tau S A) := by
  -- Assembly over `S07_Coherence`: base case `|S| = 2` from (5.2.d); inductive build of the
  -- auxiliary isometry via `eq_sum_of_psi_eq_zero` (5.5) per member, then
  -- `retarget_isCoherent_of_decompositions`.  See the design note.
  sorry

end OddOrder.Peterfalvi.S07
