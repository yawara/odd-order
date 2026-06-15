/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeCharacters

/-!
# Peterfalvi §6: the certain-type `μ`-column induction relation, explicit form

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§4 (repo chunk 04.4), result (4.3.b).

This is a **signature-bridge leaf** for the FT critical path
(`notes/meta/ft_path_policy.md` §4, endpoint **D**).  The certain-type characters
`μ_{ij}` of (4.3.b) — the `columnFamily` of a certain-type hypothesis `h` — satisfy
the §13 induction identity `Ind_W^L(ω_{ij} − ω_{0j}) = δ_j (μ_{ij} − μ_{0j})`, which
is exactly the shape of `S15.Hypothesis.mu_definition` (Peterfalvi (13.1.e)).

The supply already exists as `induce_omegaColumnDiff_eq` (the (1.4) image, in
`signedDifference` form); this leaf restates it in the explicit
`δ · (μ_i − μ_0)` difference form that the §13 grid consumes, anchored at the clean
`W₁`-index `i` (via `w1CharEquiv`, `e⁻¹(e i) = i`).

**Gated note**: this is parametrized by the certain-type hypothesis `h : S06.Hypothesis L`
(`L = S` a maximal subgroup *of certain type* — a §10–16 / §14 structural fact).  The
remaining reconciliation with `S15.Hypothesis` (the `W₂`-column reindex `χ₂ ↦ Fin |W₂|`,
the `W₁` reindex via the grid's `charEquiv`, and the `compHom` transport form of
`Ind_W^S`) is the §13-spine owner's wiring step, since those are consumer-side
indexing conventions.  See `ft_path_policy.md` §4 endpoint D.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S05

namespace Hypothesis

/-- **Peterfalvi (13.1.e), per `W₂`-column, explicit `μ`-difference form** (endpoint D).
For a certain-type hypothesis `h` and a `W₂`-dual `χ₂`, the (4.3.b) certain-type
characters satisfy `Ind_W^L(ω_{iχ₂} − ω_{0χ₂}) = δ_{χ₂} (μ_{iχ₂} − μ_{0χ₂})`.  Direct
from `induce_omegaColumnDiff_eq` once the signed difference is written out. -/
theorem induce_omegaColumnDiff_mu_diff {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : Hypothesis L) [NeZero (Nat.card h.W1)]
    [Fintype (h.W1 ⊔ h.W2 : Subgroup L)]
    [Invertible (Nat.card (h.W1 ⊔ h.W2 : Subgroup L) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        (h.omegaColumnDiff (h.w1CharEquiv i) 1 χ₂ :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily χ₂).sign •
          ((h.columnFamily χ₂).classFunction i - (h.columnFamily χ₂).classFunction 0) := by
  rw [h.induce_omegaColumnDiff_eq χ₂ (h.w1CharEquiv i), Equiv.symm_apply_apply]

end Hypothesis

end OddOrder.Peterfalvi.S06
