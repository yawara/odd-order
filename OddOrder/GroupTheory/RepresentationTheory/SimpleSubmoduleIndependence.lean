/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Independence of pairwise non-isomorphic simple submodules

This is a general module-theory helper for BG Lemma 2.3 (Fong–Swan), issue 3008.

Let `W : ι → Submodule R M` be a family of **simple** submodules of an `R`-module `M` that are
**pairwise non-isomorphic**. Then the family is independent (`iSupIndep W`): the sum of the `W i`
is direct.

The mathematical content is exactly "pairwise non-isomorphic simple submodules are independent",
with no assumption of semisimplicity on the ambient module `M`. The only semisimplicity used is
that of the internal sum `⨆_{j ≠ i} W j`, which is automatic as a sum of simple submodules.

## Proof idea

`iSupIndep W` reduces (via `iSupIndep_def'`) to `Disjoint (W i) (sSup (W '' {j | j ≠ i}))` for
each `i`. The intersection `W i ⊓ (sSup {j ≠ i})` is a submodule of the simple module `W i`, hence
is `⊥` or `W i` (the submodule `W i` is an atom of the lattice `Submodule R M`). If it were `W i`,
then `W i ≤ sSup {j ≠ i}`, so by `Submodule.linearEquiv_of_le_sSup` the simple module `W i` would be
isomorphic to one of the (simple) summands `W j` with `j ≠ i`, contradicting pairwise
non-isomorphism. Hence the intersection is `⊥` and the family is independent.
-/

namespace OddOrder.RepresentationTheory

open Submodule

/-- **Independence of pairwise non-isomorphic simple submodules.**

If `W : ι → Submodule R M` is a family of simple submodules that are pairwise non-isomorphic
(`¬ Nonempty (W i ≃ₗ[R] W j)` for `i ≠ j`), then the family is independent (`iSupIndep W`), i.e. the
internal sum `⨆ i, W i` is direct. No semisimplicity assumption on the ambient module `M` is
required: the sum of the remaining simples is semisimple automatically.

This is the general module-theoretic core behind BG Lemma 2.3 (Fong–Swan), issue 3008. -/
theorem iSupIndep_of_pairwise_not_linearEquiv_of_isSimpleModule
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (W : ι → Submodule R M)
    (hsimple : ∀ i, IsSimpleModule R (W i))
    (hpair : ∀ i j, i ≠ j → ¬ Nonempty (W i ≃ₗ[R] W j)) :
    iSupIndep W := by
  rw [iSupIndep_def']
  intro i
  rw [disjoint_iff]
  -- `s` is the family of the remaining simple submodules, whose sum we test against `W i`.
  set s : Set (Submodule R M) := W '' {j : ι | j ≠ i} with hs
  -- every member of `s` is a simple submodule.
  have hsimple_s : ∀ m : s, IsSimpleModule R (m : Submodule R M) := by
    rintro ⟨_, j, _, rfl⟩
    exact hsimple j
  haveI : IsSimpleModule R (W i) := hsimple i
  -- `W i` is an atom of `Submodule R M`, so any submodule below it is `⊥` or all of `W i`.
  have hatom : IsAtom (W i) := isSimpleModule_iff_isAtom.mp (hsimple i)
  rcases hatom.le_iff.mp (inf_le_left : W i ⊓ sSup s ≤ W i) with h | h
  · exact h
  · -- `W i ⊓ sSup s = W i` would force `W i ≤ sSup s`; derive a contradiction.
    have hle : W i ≤ sSup s := h ▸ (inf_le_right : W i ⊓ sSup s ≤ sSup s)
    obtain ⟨S, hS, ⟨e⟩⟩ :=
      Submodule.linearEquiv_of_le_sSup (N := W i) (s := s) (simple := hsimple_s) hle
    obtain ⟨j, hj, rfl⟩ := hS
    exact absurd ⟨e⟩ (hpair i j (Ne.symm hj))

end OddOrder.RepresentationTheory
