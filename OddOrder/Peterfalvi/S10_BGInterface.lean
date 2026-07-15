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

/-! ## Type-P₂ complement Hall bridge -/

/-- **The `K`-invariant complement `U` to `M_F` is the `(κ∪σ)'`-Hall** (type-`P₂`).

For a type-`P₂` maximal subgroup `M`, `M_F = M_σ`, and the complement `U` to `M_σ` in
`M'` produced by `exists_kappaHall_invariant_complement_to_MF` shares the order `[M':M_σ]` with the
`(κ∪σ)'`-Hall of `typeP_exists_hall_derived_eq` (which also complements `M_σ` in `M'`).  Since
`IsHallSubgroup` is order-determined, any chosen complement `U` of `M_σ` in `M'` is
the same Hall.  This
discharges the `hUhall` hypothesis of downstream type-`P₂` data constructors for the canonical
invariant complement. -/
theorem isHall_kappaSigmaCompl_of_isTypeP2_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 M) (hUM : U ≤ M)
    (hUsup : derivedInG M = maxNilpotentNormalHall M ⊔ U)
    (hUinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) := by
  classical
  have hMFeq : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (OddOrder.BG.Ch4.S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hUM' : U ≤ derivedInG M := by
    rw [hUsup]
    exact le_sup_right
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _
  have hMσnormM' : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMσM').mpr (hM'M.trans hM_norm_Mσ)
  let U₀ := (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose
  have hU₀hall : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) :=
    (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose_spec.1
  have hU₀sup : derivedInG M = U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose_spec.2
  have hU₀M' : U₀ ≤ derivedInG M := by
    rw [hU₀sup]
    exact le_sup_left
  have hU₀M : U₀ ≤ M := hU₀M'.trans hM'M
  have hsupU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊔ U.subgroupOf (derivedInG M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMσM' hUM', ← hMFeq, ← hUsup, Subgroup.subgroupOf_self]
  have hsupU₀ : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊔ U₀.subgroupOf (derivedInG M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMσM' hU₀M', sup_comm, ← hU₀sup, Subgroup.subgroupOf_self]
  have hcopU₀ : Nat.Coprime (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) (Nat.card ↥U₀) := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
    · intro p hp
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p hp
    · intro p hp hpσ
      exact hU₀hall.1 p (by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M).toEquiv]) (Or.inr hpσ)
  have hinfU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊓ U.subgroupOf (derivedInG M) = ⊥ := by
    rw [show
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
          ⊓ U.subgroupOf (derivedInG M)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U).subgroupOf (derivedInG M) from
        (Subgroup.comap_inf _ _ _).symm,
      ← hMFeq, hUinf, Subgroup.bot_subgroupOf]
  have hinfU₀ : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊓ U₀.subgroupOf (derivedInG M) = ⊥ := by
    rw [show
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
          ⊓ U₀.subgroupOf (derivedInG M)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U₀).subgroupOf (derivedInG M) from
        (Subgroup.comap_inf _ _ _).symm,
      (Subgroup.disjoint_of_coprime_natCard hcopU₀).eq_bot, Subgroup.bot_subgroupOf]
  have hcU := Subgroup.card_mul_card_of_complement_normal hinfU hsupU
  have hcU₀ := Subgroup.card_mul_card_of_complement_normal hinfU₀ hsupU₀
  have hcard : Nat.card ↥(U.subgroupOf (derivedInG M)) = Nat.card ↥(U₀.subgroupOf (derivedInG M)) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcU.trans hcU₀.symm)
  refine Ch03.isHallSubgroup_of_card_eq (B := U₀.subgroupOf M) hU₀hall ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM').toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M').toEquiv]
  exact hcard

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
