/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.Peterfalvi.S09_NonexistenceCertain
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults

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
Peterfalvi-numbered entry points and the main scaffold statements.  Those of
(8.11), (8.12), (8.13) quote BG Theorems A--E / Theorems I--II, which are now
stated (still `sorry`) in `OddOrder.BG.Ch4.S16` and are cited here as the
Peterfalvi-facing wiring is built; (8.8) is already wired to BG Theorem I
(`theoremI_nilpotentHall_conjugacy_and_type_dichotomy`).  The remaining `sorry`s
reduce to those BG endpoints plus a notation dictionary, not to new axioms;
see `notes/peterfalvi/s10_13_maximal_structure.md`.

The Nougat extract drops the statements around (8.14)--(8.17).  The PDF page
has now been recovered; this file records the `R(x)`/thickened-support notation,
the Type-II TI endpoint, the Dade (2.2) interface behind (8.15), and the BG
Theorem E covering interface.  The higher §4.6/§5.2 Dade specializations remain
as a precise TODO until their section-level carriers are stable enough to avoid
opaque placeholders.
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
  -- The cyclic-Sylow hypothesis `|U| = exp(U) = exp(U₀)` forces `U₀ = U`, so the
  -- Frobenius structure of `H ⊔ U₀` (a field of `TypeFData`) collapses to `M`.
  have hexp : Monoid.exponent ↥data.U0 = Nat.card ↥data.U :=
    data.exponent_eq.trans hU.symm
  have hdvd1 : Nat.card ↥data.U ∣ Nat.card ↥data.U0 := by
    rw [← hexp]; exact Group.exponent_dvd_nat_card
  have hdvd2 : Nat.card ↥data.U0 ∣ Nat.card ↥data.U :=
    Subgroup.card_dvd_of_le data.U0_le
  have hcard : Nat.card ↥data.U0 = Nat.card ↥data.U := Nat.dvd_antisymm hdvd2 hdvd1
  have hU0eq : data.U0 = data.U := Subgroup.eq_of_le_of_card_ge data.U0_le hcard.ge
  -- `H ⊔ U = M`, from the complement `H ⋊ U = M`.
  have hHU : data.H ⊔ data.U = M := by
    have htop : data.H.subgroupOf M ⊔ data.U.subgroupOf M = ⊤ := data.complement.sup_eq_top
    have hmap := congrArg (Subgroup.map M.subtype) htop
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left data.H_le, inf_of_le_left data.U_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
  -- Transport `frobenius_HU0 : IsFrobeniusGroup (H ⊔ U₀) H U₀` along `U₀ = U` and `H ⊔ U = M`.
  have hfrob := data.frobenius_HU0
  rw [hU0eq, hHU] at hfrob
  exact hfrob

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
  -- BG Theorem I (`OddOrder.BG.Ch4.S16`) supplies exactly this dichotomy, in the
  -- shared `IsTypeI`/`IsTypeNonI`/`IsTypeII` language, with extra `W₁,W₂,W` data
  -- that Peterfalvi (8.8) drops.  `S14.IsConjugateSubgroup M S` is *defeq* to
  -- `∃ g, MulAut.conj g • M = S`, so the covering clause transfers directly.
  rcases (OddOrder.BG.Ch4.S16.theoremI_nilpotentHall_conjugacy_and_type_dichotomy hG).2 with
    hI | ⟨S, T, _W1, _W2, _W, hS, hT, hST, _hW, _hWcyc, _hWinter, hSnonI, hTnonI, hII, hcov⟩
  · exact Or.inl hI
  · exact Or.inr ⟨S, T, hS, hT, hST, hSnonI, hTnonI, hII, hcov⟩

/-- **Peterfalvi (8.8)/(8.13) for the given `M`**: a non-type-I (type-`P`) maximal subgroup `M`
admits a Type-II maximal subgroup `S` whose cyclic-factor order `|S : [S,S]|` equals `|W₂|`.

This is the `M`-specific case-(b) datum of Theorem (8.8): the type-`P` maximal `M` participates in
the case-(b) configuration of (8.8), one of whose two distinguished maximal subgroups is of Type II
and shares the cyclic-factor order `w₂ = |W₂|`.  It is the §8 obligation behind both the (9.3) order
relations (`S11.typeIIIorIV_W2_prime`) and the (10.3) prime computation (`S12.Hypothesis.w2_prime`).

Stated here in `§8` on the bare `TypePData` (rather than the §10 `Hypothesis`) so it is citable from
`S11` (§9) as well as `S12` (§10).  Its proof is gated on the BG §16 partner-existence behind
`Peterfalvi.S14.theorem88_caseB_holds`; recorded as a faithful obligation. -/
theorem exists_typeII_maximal_with_w2_of_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (data : TypePData M)
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = Nat.card ↥data.W2 := by
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

/-! ## (8.14)--(8.17): support notation and TI-covering facts -/

/-- **Peterfalvi (8.16)**: for a maximal subgroup of Type II, the three sets
`A_0(M)`, `A(M)`, and `A_1(M)` are TI-subsets of `G` with normalizer `M`.

This is the directly usable part of the PDF-recovered missing page.  The proof is
BG Section 16 / Peterfalvi (2.3), not a local character-theoretic argument. -/
theorem typeII_A_sets_TI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIIData M) :
    IsTISubset (typePA0 M data.typeP) M ∧
      IsTISubset (typePA M data.typeP) M ∧
        IsTISubset (A1 M PeterfalviType.II) M := by
  sorry

/-- **Peterfalvi (8.16)**, normalizer form: for Type II, the normalizers of
`A_0(M)`, `A(M)`, and `A_1(M)` are all `M`. -/
theorem typeII_A_sets_normalizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIIData M) :
    Subgroup.normalizer (typePA0 M data.typeP) = M ∧
      Subgroup.normalizer (typePA M data.typeP) = M ∧
        Subgroup.normalizer (A1 M PeterfalviType.II) = M := by
  sorry

/-- **Peterfalvi (8.14)**: the subgroup `R(x)`, shared as
`OddOrder.GroupTheory.supportKernel`. -/
noncomputable abbrev supportKernel (L M : Subgroup G) (X : Set G) (x : G) :=
  OddOrder.GroupTheory.supportKernel L M X x

/-- **Peterfalvi (8.14)**: the thickened support set
`⋃_{x ∈ X} (x R(x))^G`, shared as `OddOrder.GroupTheory.thickenedSupport`. -/
noncomputable abbrev thickenedSupport (L M : Subgroup G) (X : Set G) :=
  OddOrder.GroupTheory.thickenedSupport L M X

/-- **Peterfalvi (8.14)**: the thickened `A_1(M)`. -/
noncomputable abbrev thickenedA1 (L M : Subgroup G) (tau : PeterfalviType) :=
  OddOrder.GroupTheory.thickenedA1 L M tau

/-- **Peterfalvi (8.14)**: the thickened `A(M)` for type-I data. -/
noncomputable abbrev typeIThickenedA (L M : Subgroup G) (data : TypeIData M) :=
  OddOrder.GroupTheory.typeIThickenedA L M data

/-- **Peterfalvi (8.14)**: the thickened `A(M)` for type-`P` data. -/
noncomputable abbrev typePThickenedA (L M : Subgroup G) (data : TypePData M) :=
  OddOrder.GroupTheory.typePThickenedA L M data

/-- **Peterfalvi (8.14)**: the thickened `A_0(M)` for type-`P` data. -/
noncomputable abbrev typePThickenedA0 (L M : Subgroup G) (data : TypePData M) :=
  OddOrder.GroupTheory.typePThickenedA0 L M data

/-- Carrier for the Dade-hypothesis part of **Peterfalvi (8.15)** for a single
support set `A`.

It records the part already expressible with the existing §4 API: `L = M`,
`N_G(A) = M`, the Dade Hypothesis (2.2), the recovered formula `H(a)=R(a)`, and
that the §4 Dade support is the thickened support from (8.14).  The later
Hypothesis (4.6)/(5.2) specializations add character-family data and are kept as
a separate TODO below. -/
structure DadeSupportHypothesisData [Fintype G] (M : Subgroup G) (A : Set G) where
  /-- Peterfalvi (8.15): `M = N_G(A)`. -/
  normalizer_eq : Subgroup.normalizer A = M
  /-- Peterfalvi (8.15): Hypothesis (2.2) holds with `L = M`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A M
  /-- Peterfalvi (8.15): the subgroups in Hypothesis (2.2) are the recovered
  `R(a)` from (8.14). -/
  H_eq_supportKernel :
    ∀ a : {a : G // a ∈ A}, dade.H a = supportKernel M M A a.1
  /-- The Dade support from §4 is the thickened support notation of (8.14). -/
  dadeSupport_eq_thickenedSupport : dade.dadeSupport = thickenedSupport M M A

/-- **Peterfalvi (8.15)** for type I: the Dade (2.2) support hypotheses hold
for `A(M)=A_0(M)` and `A_1(M)`, with `L=M` and `H(a)=R(a)`. -/
theorem dadeSupportHypotheses_typeI [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    Nonempty (DadeSupportHypothesisData M (typeIA M data)) ∧
      Nonempty (DadeSupportHypothesisData M (A1 M PeterfalviType.I)) := by
  sorry

/-- **Peterfalvi (8.15)** for type `P`: the Dade (2.2) support hypotheses hold
for `A_0(M)`, `A(M)`, and `A_1(M)`, with `L=M` and `H(a)=R(a)`. -/
theorem dadeSupportHypotheses_typeP [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Nonempty (DadeSupportHypothesisData M (typePA0 M data)) ∧
      Nonempty (DadeSupportHypothesisData M (typePA M data)) ∧
        Nonempty (DadeSupportHypothesisData M (A1 M tau)) := by
  sorry


/-- **Peterfalvi (8.17)**: BG Theorem E data for a set of conjugacy-class
representatives of maximal subgroups.

The field `ι` indexes the representatives `M_i`.  The prime-factor fields record
the statement that `π(G)` is the disjoint union of the `π((M_i)_s)`, while
`thickenedA1_card` records
`|⋃_{x ∈ A_1(M_i)} (x R(x))^G| = (|(M_i)_s| - 1) |G : M_i|`. -/
structure BGTheoremECoverData (G : Type*) [Group G] where
  /-- Indexing type for the representative maximal subgroups. -/
  ι : Type*
  /-- The representative maximal subgroup `M_i`. -/
  reps : ι → Subgroup G
  /-- The Peterfalvi type attached to `M_i`. -/
  tau : ι → PeterfalviType
  /-- The representatives form a finite family. -/
  finite_index : Fintype ι
  /-- Every representative is maximal. -/
  maximal : ∀ i : ι, reps i ∈ maximalSubgroups G
  /-- Every representative has its indicated Peterfalvi type. -/
  typed : ∀ i : ι, HasPeterfalviType (tau i) (reps i)
  /-- Every maximal subgroup is conjugate to one of the representatives. -/
  representatives :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      ∃ i : ι, ∃ g : G, MulAut.conj g • M = reps i
  /-- The representatives have no repeated conjugacy classes. -/
  nonconjugate :
    ∀ i j : ι, (∃ g : G, MulAut.conj g • reps i = reps j) → i = j
  /-- `π(G)` is covered by the `π((M_i)_s)`. -/
  primeFactors_cover :
    ∀ p : ℕ, p.Prime →
      (p ∈ (Nat.card G).primeFactors ↔
        ∃ i : ι, p ∈ (Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors)
  /-- The `π((M_i)_s)` are pairwise disjoint. -/
  primeFactors_disjoint :
    ∀ i j : ι, i ≠ j →
      Disjoint
        ((Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors : Finset ℕ)
        ((Nat.card ↥(mainSubgroup (reps j) (tau j))).primeFactors : Finset ℕ)
  /-- The cardinality formula for the thickened `A_1(M_i)` sets. -/
  thickenedA1_card :
    ∀ i : ι,
      Nat.card ↥(thickenedA1 (reps i) (reps i) (tau i)) =
        (Nat.card ↥(mainSubgroup (reps i) (tau i)) - 1) * (reps i).index

/-- **Peterfalvi (8.17), case (8.8.a)**: when all maximal subgroups are type I,
`G#` is the disjoint union of the thickened `A_1(M_i)` sets. -/
structure BGTheoremETypeICovering (data : BGTheoremECoverData G) : Prop where
  /-- The thickened `A_1(M_i)` sets cover all nonidentity elements of `G`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      ⋃ i : data.ι, thickenedA1 (data.reps i) (data.reps i) (data.tau i)
  /-- The cover by thickened `A_1(M_i)` sets is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i =>
      thickenedA1 (data.reps i) (data.reps i) (data.tau i)

/-- **Peterfalvi (8.17), case (8.8.b)**: in the two-exceptional-subgroup case,
`G#` is covered by the thickened `A_1(M_i)` sets together with the conjugates of
the exceptional `W#`. -/
structure BGTheoremENonTypeICovering (data : BGTheoremECoverData G) where
  /-- The exceptional subgroup whose nonidentity conjugates supplement the cover. -/
  W : Subgroup G
  /-- The thickened `A_1(M_i)` sets and the conjugates of `W#` cover `G#`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      (⋃ i : data.ι, thickenedA1 (data.reps i) (data.reps i) (data.tau i)) ∪
        conjClassSet (sharpSubgroup W)
  /-- The thickened `A_1(M_i)` part of the cover is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i =>
      thickenedA1 (data.reps i) (data.reps i) (data.tau i)
  /-- The exceptional part is disjoint from every thickened `A_1(M_i)`. -/
  exceptional_disjoint_thickened :
    ∀ i : data.ι,
      Disjoint (conjClassSet (sharpSubgroup W))
        (thickenedA1 (data.reps i) (data.reps i) (data.tau i))

/-- **Peterfalvi (8.17)**: BG Theorem E, repackaged as the Section 10 covering
interface.

This statement deliberately does not prove BG Theorem E.  It records the exact
data Peterfalvi uses after (8.14): the `π(G)` partition by the `M_i_s`, the
cardinality of each thickened `A_1(M_i)`, and the appropriate `G#` cover in the
two cases from (8.8). -/
theorem bgTheoremE_cover_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ data : BGTheoremECoverData G,
      BGTheoremETypeICovering data ∨ Nonempty (BGTheoremENonTypeICovering data) := by
  sorry

/-- **Peterfalvi (8.18)**: the final support-exclusion relation in Section 10.

The proof uses the recovered (8.14)--(8.17) support notation and BG Theorem E
covering facts.  It remains the usable endpoint of the block for downstream
files. -/
theorem support_mutual_exclusion [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G) :
    ¬ (Supports (A1 S PeterfalviType.I) (A1 T PeterfalviType.I) ∧
        Supports (A1 T PeterfalviType.I) (A1 S PeterfalviType.I)) := by
  sorry

-- TODO (Peterfalvi (8.15), higher Dade specializations): add the recovered
-- Hypothesis (4.6)/(5.2) statements with `K=M_prime` and `H=M_F` or `M_s`
-- once those section-level carriers expose the needed `L=M` specialization
-- without opaque placeholder propositions.
--

end OddOrder.Peterfalvi.S10
