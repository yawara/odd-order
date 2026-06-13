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
open OddOrder.Isaacs

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

/-! ## Hall structure of `M_F` (the `(8.11)` first conjunct, types I/II) -/

/-- A `π`-Hall subgroup is also a Hall subgroup for the prime factors of its own
order.  (General lemma: `IsHallSubgroup` only constrains the order's primes to lie
in `π` and the index's primes to avoid `π`; shrinking `π` to `π(|H|)` keeps both.) -/
theorem isHall_primeFactors {π : Set ℕ} {H : Subgroup G}
    (h : Ch03.IsHallSubgroup π H) :
    Ch03.IsHallSubgroup (↑(Nat.card ↥H).primeFactors) H := by
  refine ⟨fun p hp => Finset.mem_coe.mpr hp, fun p hp hp' => ?_⟩
  exact h.2 p hp (h.1 p (Finset.mem_coe.mp hp'))

/-- **Shared-notation form of Peterfalvi (8.11), first conjunct, types I/II**:
`M_F` (`maxNilpotentNormalHall`) is a Hall subgroup of `G` for the primes dividing
its order.  Proof: for type I/II, `M_F = M_σ` (Proposition 16.1) and `M_σ` is the
σ-Hall subgroup (BG Theorem 10.2, `Msigma_isHall`), which is Hall for its own
prime factors by `isHall_primeFactors`.  No new axiom (cites the still-`sorry`
Proposition 16.1; the §10 Hall structure is already proved).

The full (8.11) additionally needs the type III/IV case, where `M_s = M'` and `M_F`
is a *proper* Hall subgroup of `M_σ`; that requires the (still `sorry`) BG §14--§15
structure and is therefore deferred. -/
theorem maxNilpotentNormalHall_isHall_of_typeI_or_II [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) :
    Ch03.IsHallSubgroup (↑(Nat.card ↥(maxNilpotentNormalHall M)).primeFactors)
      (maxNilpotentNormalHall M) := by
  rw [maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hM hType]
  exact isHall_primeFactors (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)

end OddOrder.Peterfalvi.S10Interface
