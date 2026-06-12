/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults

/-!
# Peterfalvi §10 ↔ BG §16 interface (shared-notation consumption layer)

BG §16 (`OddOrder.BG.Ch4.S16`) states Theorems A--E / Proposition 16.1 / Theorems
I--II in BG-internal notation (`M_σ = Msigma`, `σ = sigma`, `κ = kappa`, `A(M) =
ASet`, `A_0(M) = A0Set`, `\widetilde M = tildeM`).  Its own docstring directs the
Peterfalvi side to *consume these endpoints through the shared type predicates*
(`OddOrder.GroupTheory.IsTypeI`, `maxNilpotentNormalHall`, ...), but provides no
such shared-notation layer.  This file (Lane H owned) is that layer: it restates
the BG endpoints in the shared notation `OddOrder.Peterfalvi.S10` uses, citing the
BG-internal originals.  No new axioms are introduced — every lemma cites an
existing (currently `sorry`) BG §16 endpoint, so it becomes unconditional exactly
when BG §16 is proved.

## Coverage note (measured 2026-06-12, session 1)

The cleanly-bridgeable part is the *taxonomy dictionary* below.  The remaining
S10 wirings (8.11)--(8.18) additionally need *structural* bridges — that the
shared type-data complement equals the BG `(κ ∪ σ)ᶜ`-Hall complement, that
`A_1(M)`/`A_0(M)` (shared) equal `ASet`/`A0Set` (BG), that `σ(M) = π(M_σ)` —
for which BG §16 exposes no citeable statement; they bottom out on the (still
`sorry`) BG §14--§15 structure.  Those wirings are therefore gated on BG §14--§16
being *proved*, not merely stated.  See
`notes/peterfalvi/s10_13_maximal_structure.md` §5.
-/

namespace OddOrder.Peterfalvi.S10Interface

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ## Taxonomy dictionary (Proposition 16.1) -/

/-- **Shared-notation Proposition 16.1, `M_F = M_σ` clause** (type I/II).

For a maximal subgroup of Peterfalvi type I or II, Peterfalvi's `M_F`
(`maxNilpotentNormalHall`, definitionally `OddOrder.BG.Ch4.S15.MF`) coincides
with BG's σ-Hall subgroup `M_σ`.  Cites BG Proposition 16.1
(`proposition_type_classification`); unconditional once that is proved. -/
theorem maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) :
    maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
  (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.2.2.2.mpr
    (hType.imp_right Or.inl)

end OddOrder.Peterfalvi.S10Interface
