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

/-- **Type dictionary (Prop 16.1)**: Peterfalvi type I = BG type `F`.  Used to
translate the BG §14--§16 endpoints (whose conclusions are stated with `S14.IsTypeF`)
into the shared `IsTypeI` predicate that Peterfalvi §10--§13 uses. -/
theorem isTypeI_iff_isTypeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    IsTypeI M ↔ OddOrder.BG.Ch4.S14.IsTypeF M :=
  (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).1

/-- **Type dictionary (Prop 16.1)**: Peterfalvi type II = BG type `P2`.  The
companion of `isTypeI_iff_isTypeF` for translating BG endpoints stated with
`S14.IsTypeP2` (e.g. the type alternatives in Theorem II / Corollary 15.9). -/
theorem isTypeII_iff_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    IsTypeII M ↔ OddOrder.BG.Ch4.S14.IsTypeP2 M :=
  (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.1

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

/-! ## Support-set and maximality bridges -/

/-- **Support-set bridge (types I/II)**: Peterfalvi's `A_1(M) = M_s#` coincides with
BG's `\widetilde M = M_σ#` (`sigmaSharp`).  For types I/II, `M_s = M_F = M_σ`
(Proposition 16.1), so both are the `sharpSubgroup` of the same `M_F = M_σ`.

This is a genuine support-set equality — but a special one: the larger support sets
`A(M)`/`A_0(M)` (built from BG's `hatMsigma = {a ∈ M | M_σ ⊓ C(a) ≠ 1}`) are *not*
of this `sharpSubgroup` form, so they have no analogous bridge and stay gated on the
(still `sorry`) BG §14--§15 structure. -/
theorem A1_eq_sigmaSharp_of_typeI_or_II [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M)
    {tau : PeterfalviType} (htau : tau = PeterfalviType.I ∨ tau = PeterfalviType.II) :
    A1 M tau = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  have hmain : mainSubgroup M tau = maxNilpotentNormalHall M := by
    rcases htau with h | h <;> subst h <;> rfl
  change sharpSubgroup (mainSubgroup M tau) = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)
  rw [hmain, maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hM hType]

/-- **Maximality bridge**: a proper subgroup whose family of containing maximal
subgroups is a singleton `{M}` is uniquely maximal.  Converts the BG-style endpoint
`maximalSubgroupsContaining H = {M}` (the conclusion shape of BG Theorem B's
centralizer clause and Theorem II) into Peterfalvi's `IsUniquelyMaximal H`, as needed
by (8.12)/(8.13). -/
theorem isUniquelyMaximal_of_maximalSubgroupsContaining_eq_singleton {H M : Subgroup G}
    (h : maximalSubgroupsContaining H = {M}) (hlt : H < ⊤) :
    IsUniquelyMaximal H := by
  have hMmem : M ∈ maximalSubgroupsContaining H := by
    rw [h]; exact Set.mem_singleton_iff.mpr rfl
  rw [mem_maximalSubgroupsContaining] at hMmem
  refine IsUniquelyMaximal.of_unique_maximal hlt
    (mem_maximalSubgroups.mpr hMmem.1) hMmem.2 (fun N hN hHN => ?_)
  have hNmem : N ∈ maximalSubgroupsContaining H :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hN, hHN⟩
  rw [h] at hNmem
  exact Set.mem_singleton_iff.mp hNmem

end OddOrder.Peterfalvi.S10Interface
