/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_NonexistenceCertain
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.BG.Ch2_Uniqueness.Setup

/-!
# Peterfalvi Section 10: Structure of a Minimal Simple Group of Odd Order

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 10, pp. 44--49.

This section is the interface between BG local analysis and Peterfalvi's final
character-theoretic analysis.  It fixes the maximal-subgroup taxonomy
(type `F`, type I, type `P`, and types II--V) and records the BG Section 16
structural consequences consumed by Peterfalvi Sections 11--16.

The actual type definitions live in `OddOrder.GroupTheory.MaximalSubgroupType`
because BG Chapter IV uses the same taxonomy.  This file provides the
Peterfalvi-numbered entry points and the main scaffold statements.  Proofs of
(8.8), (8.11), (8.12), and (8.13) are intentionally left as `sorry`: they quote
BG Theorems A--E / Theorems I--II, which are not yet scaffolded in Lean.

The Nougat extract drops the statements around (8.14)--(8.17); those are left as
TODO comments until the PDF page is recovered.
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (8.1)--(8.7): type taxonomy -/

/-- **Peterfalvi (8.1)**: data for a group of type `F`.

The definition is shared as `OddOrder.GroupTheory.TypeFData`; the proposition
form is `OddOrder.GroupTheory.IsTypeF`. -/
abbrev TypeFData (M : Subgroup G) := OddOrder.GroupTheory.TypeFData M

/-- **Peterfalvi (8.3)**: data for a maximal subgroup of type I. -/
abbrev TypeIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIData M

/-- **Peterfalvi (8.4)**: data for a maximal subgroup of type `P`. -/
abbrev TypePData (M : Subgroup G) := OddOrder.GroupTheory.TypePData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type II. -/
abbrev TypeIIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIIData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type III. -/
abbrev TypeIIIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIIIData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type IV. -/
abbrev TypeIVData (M : Subgroup G) := OddOrder.GroupTheory.TypeIVData M

/-- **Peterfalvi (8.7)**: data for a maximal subgroup of type V. -/
abbrev TypeVData (M : Subgroup G) := OddOrder.GroupTheory.TypeVData M

/-- **Peterfalvi (8.2.a)**: in type `F`, the chosen `U_0` has order equal to the
exponent of the complement `U`.  The proof quotes BG Proposition 3.9. -/
theorem typeF_card_U0_eq_exponent [Finite G] {M : Subgroup G} (data : TypeFData M) :
    Nat.card ↥data.U0 = Monoid.exponent data.U := by
  sorry

/-- **Peterfalvi (8.2.b), one direction**: when the complement has cyclic Sylow
subgroups, type `F` collapses to a Frobenius group with kernel `M_F`.

The cyclic-Sylow hypothesis is represented by the cardinal/exponent equality
`|U| = exp(U)`, the finite cyclic-complement criterion used in the text. -/
theorem typeF_frobenius_of_card_eq_exponent [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hU : Nat.card ↥data.U = Monoid.exponent data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  sorry

/-! ## (8.8): BG maximal-subgroup dichotomy -/

/-- **Peterfalvi (8.8)**: BG Theorem I / Proposition 16.1 / Theorems B and C(3),
repackaged as Peterfalvi's maximal-subgroup dichotomy.

Either every maximal subgroup is type I, or there are two distinguished maximal
subgroups `S,T` of non-type-I kind such that at least one is type II and every
maximal subgroup is conjugate to `S`, conjugate to `T`, or type I. -/
theorem maximalSubgroup_type_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      ∃ S T : Subgroup G,
        S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
        IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
        (∀ M : Subgroup G, M ∈ maximalSubgroups G →
          IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
            (∃ g : G, MulAut.conj g • M = T)) := by
  sorry

/-! ## (8.10)--(8.13): `M_s`, support sets, and centralizer control -/

/-- **Peterfalvi (8.10)**: the notation `M_s`, shared as `mainSubgroup`. -/
noncomputable abbrev mainSubgroup (M : Subgroup G) (tau : PeterfalviType) :=
  OddOrder.GroupTheory.mainSubgroup M tau

/-- **Peterfalvi (8.10)**: the notation `A_1(M) = M_s#`, shared as `A1`. -/
noncomputable abbrev A1 (M : Subgroup G) (tau : PeterfalviType) := OddOrder.GroupTheory.A1 M tau

/-- **Peterfalvi (8.11)**: if `M` has one of the five Peterfalvi types, then
`M_F` and `M_s` are Hall subgroups of `G`.

The proof is a BG Section 16 consequence, not a local Peterfalvi argument. -/
theorem hall_maxNilpotentNormalHall_and_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
        (maxNilpotentNormalHall M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup M tau)).primeFactors
        (mainSubgroup M tau) := by
  sorry

/-- **Peterfalvi (8.12)**: type I/II Sylow-complement centralizer control.

If `M` is type I or II and `U` is the relevant complement, every nonempty subset
`X` of `U#` whose centralizer in `M_F` is nontrivial has ambient centralizer
contained in a unique maximal subgroup. -/
theorem typeI_or_typeII_centralizer_unique [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) (hUle : U ≤ M) :
    ∀ X : Set G, X.Nonempty → X ⊆ sharpSubgroup U →
      maxNilpotentNormalHall M ⊓ Subgroup.centralizer X ≠ ⊥ →
        IsUniquelyMaximal (Subgroup.centralizer X) := by
  sorry

/-- **Peterfalvi (8.13)**: centralizers escaping a maximal subgroup are controlled
by `A_1(M)` and a unique maximal subgroup of type I or II.

Here `X` is either `A_1(M)` or the type-`P` set `A_0(M)` from (8.10). -/
theorem escapingCentralizers_control [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) {X : Set G}
    (hX : X = A1 M tau ∨ ∃ data : TypePData M, X = typePA0 M data) :
    let D := escapingCentralizerSet M X
    D ⊆ A1 M tau ∧
      ∀ x : G, x ∈ D →
        ∃! L : Subgroup G,
          L ∈ maximalSubgroups G ∧ Subgroup.centralizer ({x} : Set G) ≤ L ∧
            (IsTypeI L ∨ IsTypeII L) := by
  sorry

/-- **Peterfalvi (8.18)**: the final support-exclusion relation in Section 10.

The statements (8.14)--(8.17) are absent from the current Nougat extraction; this
result is kept as the usable endpoint of that block, with the proof deferred
until the missing page is recovered. -/
theorem support_mutual_exclusion [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G) :
    ¬ (Supports (A1 S PeterfalviType.I) (A1 T PeterfalviType.I) ∧
        Supports (A1 T PeterfalviType.I) (A1 S PeterfalviType.I)) := by
  sorry

-- TODO (Peterfalvi (8.14)--(8.17)): recover the dropped statements from the PDF
-- page before adding Lean statements.  The current mmd has a missing-page marker
-- in this range, and fake statements here would break traceability.

end OddOrder.Peterfalvi.S10
