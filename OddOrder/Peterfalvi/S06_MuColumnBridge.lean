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
    [Finite (h.W1 ⊔ h.W2 : Subgroup L)]
    [Invertible (Nat.card (h.W1 ⊔ h.W2 : Subgroup L) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        (h.omegaColumnDiff (h.w1CharEquiv i) 1 χ₂ :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily χ₂).sign •
          ((h.columnFamily χ₂).classFunction i - (h.columnFamily χ₂).classFunction 0) := by
  haveI : Fintype (h.W1 ⊔ h.W2 : Subgroup L) := Fintype.ofFinite _
  rw [h.induce_omegaColumnDiff_eq χ₂ (h.w1CharEquiv i), Equiv.symm_apply_apply]

/-- **Peterfalvi (13.1.e), the `ω`/`μ`-grid difference form** — the exact shape consumed by the
§13 character grids (`Section16CharacterData.mu_definition` / `S15.Hypothesis.mu_definition`).

Inducing the `W₂`-column `ω`-grid difference `ω_{ij} − ω_{0j}` of the certain-type
`W = W₁ ⊔ W₂` up to `L` yields the signed `μ`-grid difference `δ_j (μ_{ij} − μ_{0j})`, where the
`ω`-grid is the column `i ↦ chiColumn χ₂ i = ω(omegaProdChar (e i) χ₂)` and the `μ`-grid is the
`(4.3.b)` certain-type family `columnFamily χ₂ |>.mu`.  This restates
`induce_omegaColumnDiff_mu_diff` with the `chiColumn`-difference on the left and the irreducible
`μ_{ij}` (not the abstract `classFunction`) on the right — the literal `Ind_W^S(ω_{ij} − ω_{0j}) =
δ_j(μ_{ij} − μ_{0j})` of (13.1.e), so a §13/§16 grid producer reading off `ω`/`μ`/`δ` from a
certain-type member can discharge `mu_definition` by this lemma plus the column reindexing. -/
theorem induce_chiColumn_diff_mu_diff {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : Hypothesis L) [NeZero (Nat.card h.W1)]
    [Finite (h.W1 ⊔ h.W2 : Subgroup L)]
    [Invertible (Nat.card (h.W1 ⊔ h.W2 : Subgroup L) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))
      = (h.columnFamily χ₂).sign •
          (((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
            - ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) := by
  haveI : Fintype (h.W1 ⊔ h.W2 : Subgroup L) := Fintype.ofFinite _
  have hchi : (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.omegaColumnDiff (h.w1CharEquiv i) 1 χ₂ :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    rw [h.omegaColumnDiff_coe, h.chiColumn_zero]
    rfl
  rw [hchi, h.induce_omegaColumnDiff_mu_diff χ₂ i,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply]

end Hypothesis

end OddOrder.Peterfalvi.S06
