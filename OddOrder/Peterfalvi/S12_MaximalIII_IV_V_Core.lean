/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S05_OmegaSigmaGrid
import OddOrder.Peterfalvi.S05_SigmaTrichotomy
import OddOrder.Peterfalvi.S08_CaseBEndgame
import OddOrder.Peterfalvi.S06_CertainTypeFourCorner
import Mathlib.GroupTheory.IsPerfect

/-!
# Peterfalvi Section 12 (core): Hypothesis (10.1) carrier and the (10.5)--(10.6) grid

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 12, pp. 58--63.

This section begins the type-by-type character-theoretic elimination.  It works
under Hypothesis (10.1), where `M` is a maximal subgroup of type III, IV, or V,
fixes the type-`P` notation from (8.4), and studies the Dade isometry attached
to `A_0(M)`.  The main outputs are:

* (10.7): if `S` is of type II, then `[S,S]` is Frobenius with kernel `S_F`;
* (10.8): the character family `S` of Hypothesis (10.1) is not coherent;
* (10.10): maximal subgroups of type V do not occur.

The quotient-module and virtual-character calculations in (10.5)--(10.10) are
kept as named proposition fields in the scaffolding structures.  This preserves
the downstream theorem surface while avoiding fake definitions for `mu_ij`,
`omega_ij^sigma`, and the quotient `M'/M''` before the §3--§6 character API is
fully wired into this layer.

Frozen prefix of the Section 12 formalization (hub prefix-split 2026-07-02,
issue 0076): the scoped `FiniteInduce` instances, the Hypothesis (10.1)
carrier with its API, `CharacterParameters`/`CoherentHypothesis`, and the
(10.5)--(10.6) `omega_ij^sigma` grid / `tau1` chains.  The active frontier —
(10.7), (10.8), (10.10) and the (11.8) orthogonality cluster — lives in
`S12_MaximalIII_IV_V.lean`, which imports this module; downstream imports
(`S13_MaximalIII_IV`) are unchanged.
-/

namespace OddOrder.Peterfalvi.S12
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! Scoped finiteness instances (the `S15.FiniteInduce` pattern) so the
`Hypothesis` carrier of (10.1) can pin the genuine Dade isometry / induced family
without leaking the `noncomputable` `Fintype`/`Invertible` data globally. -/
namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance finiteGFintype [Finite G] : Fintype G :=
  Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

noncomputable scoped instance natCardInvCG [Finite G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

open scoped FiniteInduce in
/-- Peterfalvi's character family `S` of Hypothesis (10.1):
`{Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1_{M'}}`, where `M' = [M,M]` is realised inside
`M` as `(derivedInG M).subgroupOf M`.  The induction is the canonical
`ClassFunction.induce`. -/
noncomputable def inducedFamily (M : Subgroup G) [Finite G] :
    Set (ClassFunction ↥M ℂ) :=
  { χ | ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
      χ = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) }

open scoped FiniteInduce in
/-- **The induced family `S` is closed under complex conjugation** (Peterfalvi §10): for
`χ = Ind_{M'}^M θ ∈ S` with `θ ∈ Irr M'`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_{M'}^M θ̄`
(`ClassFunction.induce_conj`), and `θ̄` is again a non-trivial irreducible of `M'`
(`IsIrreducibleCharacter.conj`, `irreducibleCharacter_conj_ne_trivial`).  This is the
`ζ̄ ∈ S` input to the `(α_{ij}^τ, (ζ−ζ̄)^τ)` step of the (10.5) `a = 0` argument. -/
theorem inducedFamily_closedUnderConjugate [Finite G] (M : Subgroup G) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (inducedFamily M) := by
  classical
  intro φ hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj, θ.isIrreducible.conj⟩,
    ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj
        = trivialClassFunction ↥((derivedInG M).subgroupOf M) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (c : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = trivialClassFunction ↥((derivedInG M).subgroupOf M)
    rw [← ClassFunction.conj_conj (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)

/-- **Complex conjugation commutes with `G`-conjugation** of class functions: for a normal
subgroup `H ⊴ G`, `(θ^g)‾ = (θ‾)^g`.  Both sides evaluate to `star (θ ⟨g·h·g⁻¹⟩)`.  This is the
`σ`-commutes-with-the-`M`-action input to the odd-order orbit argument showing that an induced
character `Ind_{M'}^M θ` (`θ ≠ 1`) is non-real. -/
theorem conjBy_conj {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    (g : K) (θ : ClassFunction ↥H ℂ) :
    (ClassFunction.conjBy g θ).conj = ClassFunction.conjBy g θ.conj := by
  ext h
  simp only [ClassFunction.conj_apply, ClassFunction.conjBy_apply]

/-- **The complex-conjugation involution `conjPerm` commutes with `M`-conjugation `conjBy`** on the
irreducible characters of a normal subgroup `H ⊴ K`.  Lifts `conjBy_conj` to `IrreducibleCharacter`
via the coercion lemmas.  This is what makes the conjugation orbit `conjByOrbit θ` invariant under
`conjPerm`, the key to the odd-order non-reality of `Ind_{M'}^M θ`. -/
theorem conjPerm_conjBy_comm {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    (g : K) (θ : IrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H (IrreducibleCharacter.conjBy g θ)
      = IrreducibleCharacter.conjBy g (IrreducibleCharacter.conjPerm ↥H θ) := by
  refine IrreducibleCharacter.ext ?_
  simp only [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.coe_conjBy]
  exact conjBy_conj g (θ : ClassFunction ↥H ℂ)

/-- **The conjugation orbit `conjByOrbit θ` is `conjPerm`-invariant** once it contains `θ̄`.  If the
complex conjugate `θ̄ = conjPerm θ` lies in the `M`-conjugation orbit of `θ`, then so does the
conjugate of every orbit member.  Combines `conjPerm_conjBy_comm` (`σ` commutes with the action)
with the group-action laws (`conjBy_mul`). -/
theorem conjPerm_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    {θ : IrreducibleCharacter ↥H}
    (hmem : IrreducibleCharacter.conjPerm ↥H θ ∈ IrreducibleCharacter.conjByOrbit (G := K) θ)
    {η : IrreducibleCharacter ↥H} (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  obtain ⟨g, rfl⟩ := hη
  rw [conjPerm_conjBy_comm]
  obtain ⟨g₀, hg₀⟩ := hmem
  rw [← hg₀, ← IrreducibleCharacter.conjBy_mul]
  exact IrreducibleCharacter.conjBy_mem_conjByOrbit θ (g₀ * g)

/-- **`G`-conjugation fixes the trivial character.** -/
theorem conjBy_trivial {K : Type*} [Group K] {H : Subgroup K} [H.Normal] (g : K) :
    IrreducibleCharacter.conjBy g (trivialIrreducibleCharacter ↥H)
      = trivialIrreducibleCharacter ↥H := by
  apply IrreducibleCharacter.ext
  ext h
  simp [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]

/-- **The trivial character is not in the conjugation orbit of a nontrivial character.**  If
`conjBy g θ = 1` then `θ = conjBy g⁻¹ 1 = 1` (`conjBy_trivial`). -/
theorem trivial_not_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    {θ : IrreducibleCharacter ↥H} (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    trivialIrreducibleCharacter ↥H ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  rintro ⟨g, hg⟩
  apply hθ
  have : θ = IrreducibleCharacter.conjBy g⁻¹ (trivialIrreducibleCharacter ↥H) := by
    rw [← hg]; exact (IrreducibleCharacter.conjBy_inv_conjBy g θ).symm
  rw [this, conjBy_trivial]

/-- **No `conjPerm`-fixed point in the conjugation orbit of a nontrivial character** (odd order).
A fixed point `η` of `conjPerm` is real (`conjPerm_eq_self_iff`), hence trivial in odd order
(`not_isReal_of_ne_trivial_of_odd_card'`); but the trivial character is not in `conjByOrbit θ` for
`θ ≠ 1` (`trivial_not_mem_conjByOrbit`). -/
theorem conjPerm_ne_self_of_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    [Finite ↥H] (hodd : Odd (Nat.card ↥H)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) {η : IrreducibleCharacter ↥H}
    (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ≠ η := by
  intro hfix
  have hreal : ClassFunction.IsReal (η : ClassFunction ↥H ℂ) :=
    (IrreducibleCharacter.conjPerm_eq_self_iff η).mp hfix
  have htriv : η = trivialIrreducibleCharacter ↥H := by
    by_contra hne
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hne hreal
  exact trivial_not_mem_conjByOrbit hθ (htriv ▸ hη)

/-- **`conjPerm` is an involution**: `(χ̄)‾ = χ`. -/
theorem conjPerm_conjPerm {L : Type*} [Group L] [Finite L] (χ : IrreducibleCharacter L) :
    IrreducibleCharacter.conjPerm L (IrreducibleCharacter.conjPerm L χ) = χ := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.conjPerm_apply_coe,
    ClassFunction.conj_conj]

/-- **A nontrivial character is not conjugate to its complex conjugate, in odd order** (the orbit
form of Peterfalvi (1.1)).  The conjugation orbit `conjByOrbit θ` has odd cardinality `[K : I_θ]`
(`card_conjByOrbit_eq_index_inertia`, a divisor of the odd `|K|`); were `θ̄ ∈ conjByOrbit θ`, the
involution `σ = conjPerm` would restrict to it, and by `card_fixedPoints_modEq` (`p = 2`) an
involution on an odd-cardinality set has a fixed point — a real, hence trivial, character in the
orbit, impossible by `conjPerm_ne_self_of_mem_conjByOrbit`. -/
theorem conjPerm_not_mem_conjByOrbit {K : Type*} [Group K] [Finite K] {H : Subgroup K} [H.Normal]
    (hodd : Odd (Nat.card K)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H θ ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  intro hmem
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  haveI : Invertible (Nat.card K : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥H : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  haveI : Fintype ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) := Fintype.ofFinite _
  have hoddH : Odd (Nat.card ↥H) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  set f : Function.End ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) :=
    fun η => ⟨IrreducibleCharacter.conjPerm ↥H η.1, conjPerm_mem_conjByOrbit hmem η.2⟩ with hf
  have hf2 : f ^ 2 = 1 := by
    funext η
    show f (f η) = η
    exact Subtype.ext (conjPerm_conjPerm η.1)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hodd_orbit : Odd (Fintype.card ↥(IrreducibleCharacter.conjByOrbit (G := K) θ)) := by
    rw [← Nat.card_eq_fintype_card, card_conjByOrbit_eq_index_inertia]
    exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)
  have hfp_pos : 0 < Fintype.card f.fixedPoints := by
    have h1 := Nat.odd_iff.mp hodd_orbit
    rw [Nat.ModEq] at hmod
    omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hfp_pos
  have hxf : f x.1 = x.1 := x.2
  have hfix : IrreducibleCharacter.conjPerm ↥H x.1.1 = x.1.1 := Subtype.ext_iff.mp hxf
  exact conjPerm_ne_self_of_mem_conjByOrbit hoddH hθ x.1.2 hfix

set_option maxHeartbeats 1000000 in
open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` has no real characters** (Peterfalvi §10, the
`no_real_characters` clause of the §7 coherence hypothesis for `S`).  Every `Ind_{M'}^M θ`
(`θ ∈ Irr M'`, `θ ≠ 1`) of the odd-order group `M` is non-real: its conjugate
`(Ind θ)‾ = Ind θ̄` (`induce_conj`) is orthogonal to `Ind θ`, because `θ̄ = conjPerm θ` is not
`M`-conjugate to `θ` (`conjPerm_not_mem_conjByOrbit`) so `inner_induce_eq_zero_of_not_conj` gives
`⟨Ind θ, Ind θ̄⟩ = 0`; but `⟨Ind θ, Ind θ⟩ ≠ 0` (`card_mul_inner_self_induce_eq_card_inertia`,
`|I_θ| ≠ 0`), and the two coincide when `Ind θ` is real. -/
theorem inducedFamily_hasNoRealCharacters {M : Subgroup G} [Finite G]
    (hodd : Odd (Nat.card ↥M)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (inducedFamily M) := by
  classical
  intro χ hχ hreal
  obtain ⟨θ, hθne, rfl⟩ := hχ
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hnotconj : ∀ g : ↥M, IrreducibleCharacter.conjBy g θ
      ≠ IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ :=
    fun g hg => conjPerm_not_mem_conjByOrbit hodd hθne ⟨g, hg⟩
  have hzero := inner_induce_eq_zero_of_not_conj θ
    (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ) hnotconj
  have hconjeq : (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction).conj
      = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ).toClassFunction := by
    rw [ClassFunction.induce_conj, IrreducibleCharacter.conjPerm_apply_coe]
  unfold ClassFunction.IsReal at hreal
  have heq : ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction
      = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ).toClassFunction :=
    hreal.symm.trans hconjeq
  have hself0 : ClassFunction.inner
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction)
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction) = 0 :=
    (congrArg (ClassFunction.inner
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction)) heq).trans hzero
  have hc := card_mul_inner_self_induce_eq_card_inertia θ
  rw [hself0, mul_zero] at hc
  exact (show (Nat.card ↥(ClassFunction.inertia θ.toClassFunction) : ℂ) ≠ 0 by
    exact_mod_cast Nat.card_pos.ne') hc.symm

open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` is pairwise orthogonal** (the `pairwise_orthogonal`
clause of the §7 coherence hypothesis for `S`).  Distinct members `Ind_{M'}^M θ ≠ Ind_{M'}^M θ'`
have non-`M`-conjugate sources (`induce_eq_induce_iff_conj`), so `inner_induce_eq_zero_of_not_conj`
gives `⟨Ind θ, Ind θ'⟩ = 0`. -/
theorem inducedFamily_pairwiseOrthogonal {M : Subgroup G} [Finite G] :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (inducedFamily M) := by
  intro χ ψ hχ hψ hne
  obtain ⟨θ, hθne, rfl⟩ := hχ
  obtain ⟨θ', hθ'ne, rfl⟩ := hψ
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  exact inner_induce_eq_zero_of_not_conj θ θ'
    (fun g hg => hne ((induce_eq_induce_iff_conj θ θ').mpr ⟨g, hg⟩))

open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` is finite**: it is contained in the image of the
finite type `IrreducibleCharacter M'` (`finite_irreducibleCharacter`, `M' = [M,M]`) under
`Ind_{M'}^M`, hence a finite set.  This is the `hXfin`/`hYfin` input when the (11.8.6) union
instantiates the S07 orthogonal glue `exists_integralCharacterMap_glue_of_orthogonal`. -/
theorem inducedFamily_finite {M : Subgroup G} [Finite G] : (inducedFamily M).Finite := by
  classical
  haveI : Finite (IrreducibleCharacter ↥((derivedInG M).subgroupOf M)) :=
    finite_irreducibleCharacter
  refine Set.Finite.subset (Set.finite_range
    (fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
      ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))) ?_
  rintro χ ⟨θ, -, rfl⟩
  exact ⟨θ, rfl⟩

open scoped FiniteInduce in
/-- **Members of `S = inducedFamily M` have nonzero norm.**  `Ind_{M'}^M θ (1) = [M:M']·θ(1) ≠ 0`
(positive index `Subgroup.index_ne_zero_of_finite`, positive irreducible degree
`exists_apply_one_eq_pos_natCast`), so `Ind_{M'}^M θ ≠ 0`, whence `⟨φ,φ⟩ ≠ 0` by positive-
definiteness (`eq_zero_of_inner_self_re_eq_zero`).  This is the `hXnorm`/`hYnorm` input (nonzero
self-inner) the S07 orthogonal glue needs — the non-orthonormal analogue of
`SHCSet_orthonormal`'s `⟨φ,φ⟩ = 1` for the reducible members of `S₂ = 𝒮(C) − 𝒮(HC)`. -/
theorem inducedFamily_inner_self_ne_zero {M : Subgroup G} [Finite G]
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedFamily M) :
    ClassFunction.inner φ φ ≠ 0 := by
  classical
  obtain ⟨θ, -, rfl⟩ := hφ
  have hne0 : ClassFunction.induce ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) ≠ 0 := by
    intro hzero
    have h1 : ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (1 : ↥M) = 0 := by
      rw [hzero]; rfl
    rw [ClassFunction.induce_apply_one] at h1
    obtain ⟨d, hd, hθ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    rw [hθ1] at h1
    exact mul_ne_zero (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite)
      (Nat.cast_ne_zero.mpr hd.ne') h1
  intro hself
  exact hne0 (eq_zero_of_inner_self_re_eq_zero (by rw [hself]; exact Complex.zero_re))

/-! ## (10.1): the type III/IV/V hypothesis -/

open scoped FiniteInduce in
/-- **Peterfalvi (10.1)**: the common setup for a maximal subgroup of type III,
IV, or V.

Finiteness of `G` is carried as the instance field `finiteG` (the `S15`
`FiniteInduce` pattern), so that the *genuine* Dade isometry `tau`, the induced
family `Sset`, and the support `A0 = A_0(M)` can be defined as honest projections
(see `Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A0`) rather than carried as
unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis for
`A_0(M)` (supplied by `S10.dadeSupportHypotheses_typeP`), and `hconj` is its
`L`-conjugation invariance, which together build the Dade isometry. -/
structure Hypothesis (M : Subgroup G) where
  [finiteG : Finite G]
  maximal : M ∈ maximalSubgroups G
  typeP : TypePData M
  type_alt : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (typePA0 M typeP)
  hconj : dadeData.dade.HConjInvariant

namespace Hypothesis

/-- Peterfalvi's `M'`, represented as an ambient subgroup. -/
def Mderiv {M : Subgroup G} (_hyp : Hypothesis M) : Subgroup G :=
  derivedInG M

/-- Peterfalvi's `M''`, represented as an ambient subgroup. -/
def Msecond {M : Subgroup G} (_hyp : Hypothesis M) : Subgroup G :=
  secondDerivedInAmbient M

/-- Peterfalvi's `W_1` from Definition (8.4). -/
def W1 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W1

/-- Peterfalvi's `W_2` from Definition (8.4). -/
def W2 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W2

/-- Peterfalvi's `V = W - (W_1 union W_2)`. -/
def V {M : Subgroup G} (hyp : Hypothesis M) : Set G :=
  typePV M hyp.typeP

/-- Peterfalvi's `w_1 = |W_1|`. -/
noncomputable def w1 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W1

/-- Peterfalvi's `w_2 = |W_2|`. -/
noncomputable def w2 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W2

/-- Peterfalvi's support `A_0(M)` from (8.10), as a subset of `M` (the
`supportInSubgroup` restriction of the ambient set `typePA0 M`).  This is the
genuine support for the Dade isometry, no longer an unconstrained field. -/
def A0 {M : Subgroup G} (hyp : Hypothesis M) : Set ↥M :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M

open scoped FiniteInduce in
/-- Peterfalvi's family `S` of (10.1), pinned to the genuine `inducedFamily M`
`= {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}`, no longer an unconstrained field. -/
noncomputable def Sset {M : Subgroup G} (hyp : Hypothesis M) :
    Set (ClassFunction ↥M ℂ) :=
  haveI := hyp.finiteG
  inducedFamily M

open scoped FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A_0(M), M, G)` from (10.1),
pinned to the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data
`dadeData` (no longer an unconstrained field). -/
noncomputable def tau {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)

open scoped FiniteInduce in
/-- **The §10 Dade isometry `τ` commutes with coefficientwise ring automorphisms** (Peterfalvi
`Dade_aut`): for `A_0`-supported `φ`, `(φ^{σc})^τ = (φ^τ)^{σc}`.  The Dade integral character map is
pointwise (its value is `φ(a)` at a base point, `0` elsewhere), so applying `σc` to coefficients
commutes with it (`dadeIntegralCharacterMap_mapRingEquiv_comm`).  Taking `σc = conjAe` this is the
`τ`-side Galois-equivariance feeding the (11.8.3) reality `β̄ = β`. -/
theorem tau_mapRingEquiv_comm [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (σc : ℂ ≃+* ℂ) {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) :
    hyp.tau (ClassFunction.mapRingEquiv σc φ) = ClassFunction.mapRingEquiv σc (hyp.tau φ) := by
  haveI := hyp.finiteG
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    hyp.dadeData.dade (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) σc hφ

open scoped FiniteInduce in
/-- **`A(M)` is `M`-invariant**: `M ≤ N_G(A(M))` — the easy half of Peterfalvi (8.16) for the
type-`P` support, self-contained group theory (no Dade data, no simplicity).
`A(M) = centralizerSupport (M#) M'` is `M`-invariant: `M` normalizes `M' = derivedInG M`
(`derivedInG_pointwise_smul` + `conj_smul_eq_self_of_mem`), permutes `M# = M \ {1}`
(`image_sharpSubgroup`), and conjugates the centralizer condition elementwise.

This is the `M`-stability input to `toHypothesis71` / `toFamilyHypothesis71` (the §7 inputs to
Peterfalvi (10.8)), so those §7 constructions are self-contained from the genuine `Hypothesis`. -/
theorem le_normalizer_typePA {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (typePA M hyp.typeP) := by
  haveI := hyp.finiteG
  intro m hm
  rw [Subgroup.mem_set_normalizer_iff]
  -- forward `M`-invariance, applied to both `m` and `m⁻¹`.
  suffices hfwd : ∀ a ∈ M, ∀ y, y ∈ typePA M hyp.typeP → a * y * a⁻¹ ∈ typePA M hyp.typeP by
    intro h
    refine ⟨hfwd m hm h, fun hh => ?_⟩
    have hb := hfwd m⁻¹ (inv_mem hm) _ hh
    simpa [mul_assoc] using hb
  intro a ha y hy
  simp only [typePA, centralizerSupport, Set.mem_setOf_eq] at hy ⊢
  obtain ⟨hyM', hy1, x, hxM, hyx⟩ := hy
  -- (i) `a y a⁻¹ ∈ M' = derivedInG M` (`M` normalizes its derived subgroup).
  have hM'inv : MulAut.conj a • derivedInG M = derivedInG M := by
    rw [derivedInG_pointwise_smul, Subgroup.conj_smul_eq_self_of_mem ha]
  have hyM'2 : a * y * a⁻¹ ∈ derivedInG M := by
    rw [← hM'inv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsm : (MulAut.conj a)⁻¹ • (a * y * a⁻¹) = y := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rw [hsm]; exact hyM'
  -- (ii) `a y a⁻¹ ≠ 1`.
  have hne : a * y * a⁻¹ ≠ 1 := by
    intro h1; apply hy1
    have hyrw : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [hyrw, h1]; group
  -- (iii) `a x a⁻¹ ∈ M# = sharpSubgroup M`.
  have hxM2 : a * x * a⁻¹ ∈ sharpSubgroup M := by
    have himg : (MulAut.conj a) '' sharpSubgroup M = sharpSubgroup M := by
      rw [image_sharpSubgroup, Subgroup.conj_smul_eq_self_of_mem ha]
    rw [← himg]
    exact ⟨x, hxM, by rw [MulAut.conj_apply]⟩
  -- (iv) `a y a⁻¹` centralizes `a x a⁻¹` (conjugate of `y ∈ C_G({x})`).
  have hcent : a * y * a⁻¹ ∈ Subgroup.centralizer ({a * x * a⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hyx ⊢
    have hxy : x * y = y * x := hyx x rfl
    rintro z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    calc a * x * a⁻¹ * (a * y * a⁻¹)
        = a * (x * y) * a⁻¹ := by group
      _ = a * (y * x) * a⁻¹ := by rw [hxy]
      _ = a * y * a⁻¹ * (a * x * a⁻¹) := by group
  exact ⟨hyM'2, hne, a * x * a⁻¹, hxM2, hcent⟩

open scoped FiniteInduce in
/-- **Peterfalvi (8.16) for the type-`P` support `A(M)`**: `N_G(A(M)) = M`.

`M ≤ N_G(A(M))` is the `M`-invariance `le_normalizer_typePA`.  Conversely, since
`A(M) = (M')#` (`typePA_eq_sharpSubgroup_derivedInG`), a normalizer of the *set* `A(M)`
normalizes the subgroup `M' = derivedInG M` (conjugation fixes `1`), so
`N_G(A(M)) ≤ N_G(M')`.  The latter contains the maximal `M`, so it is `M` or `G`; were it
`G`, then `M' ⊴ G` with `⊥ ≠ W₂ ≤ M' ≤ M < G` would contradict the simplicity of `G`.
Hence `N_G(M') = M`. -/
theorem normalizer_typePA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    Subgroup.normalizer (typePA M hyp.typeP) = M := by
  apply le_antisymm
  · -- Step 1: `N_G(A(M)) ≤ N_G(M')` (a set-normalizer of `(M')#` normalizes `M'`).
    have hstep : Subgroup.normalizer (typePA M hyp.typeP) ≤
        Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
      intro h
      by_cases h1 : h = 1
      · subst h1
        simp
      · have hg' := hg h
        rw [typePA_eq_sharpSubgroup_derivedInG] at hg'
        simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hg' ⊢
        constructor
        · intro hh
          exact (hg'.mp ⟨hh, h1⟩).1
        · intro hh
          have hc1 : g * h * g⁻¹ ≠ 1 := by
            intro he
            apply h1
            have hrw : h = g⁻¹ * (g * h * g⁻¹) * g := by group
            rw [hrw, he]
            group
          exact (hg'.mpr ⟨hh, hc1⟩).1
    -- Step 2: `N_G(M') = M` by maximality + simplicity.
    have hMle : M ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) := by
      intro m hm
      have hM'inv : MulAut.conj m • derivedInG M = derivedInG M := by
        rw [derivedInG_pointwise_smul, Subgroup.conj_smul_eq_self_of_mem hm]
      rw [Subgroup.mem_set_normalizer_iff]
      intro h
      have hiff : h ∈ derivedInG M ↔
          (MulAut.conj m) • h ∈ (MulAut.conj m) • derivedInG M :=
        (Subgroup.smul_mem_pointwise_smul_iff).symm
      rw [hM'inv] at hiff
      simpa [MulAut.smul_def, MulAut.conj_apply] using hiff
    by_cases hN : Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) = M
    · exact hstep.trans hN.le
    · exfalso
      have htop : Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) = ⊤ :=
        hyp.maximal.2 _ (hMle.lt_of_ne (Ne.symm hN))
      have hnormal : (derivedInG M).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnormal with hbot | htop'
      · -- `M' = ⊥` contradicts `⊥ ≠ W₂ ≤ H ≤ M'`.
        have hW2le : hyp.typeP.W2 ≤ derivedInG M :=
          hyp.typeP.W2_le.trans (inf_le_left.trans hyp.typeP.H_le)
        exact hyp.typeP.W2_nontrivial (le_bot_iff.mp (hbot ▸ hW2le))
      · -- `M' = ⊤` gives `M = ⊤`, contradicting the maximality (coatom) of `M`.
        exact hyp.maximal.1
          (top_le_iff.mp (htop' ▸ (Subgroup.map_subtype_le _ : derivedInG M ≤ M)))
  · exact hyp.le_normalizer_typePA

open scoped FiniteInduce in
/-- **The Peterfalvi (7.1) `ρ`-machinery data for `(L, A) = (M, A(M))`** — the §7 input to the
(10.8) non-coherence estimate.

Built genuinely from the §10 Dade isometry on `A_0(M)` (carried by `hyp.dadeData`/`hyp.hconj`) by
restricting to the `M`-stable subset `A(M) = typePA ⊆ A_0(M) = typePA0` (`Set.subset_union_left`):
`FullDadeIsometryData.restrict` restricts the Dade map and its `IsDadeMap` certificate, and
`S04.HConjInvariant.restrict` restricts the `L`-equivariance.  The `M`-stability
the `M`-stability of `A(M)` is supplied by `le_normalizer_typePA`, so this
construction is self-contained from the genuine `Hypothesis` (**sorry-free**, no external `hN`).

This is the foundational `S09.Hypothesis71` instance that lets the §10 estimate apply the family
inequality (7.5) `S09.family_inequality` and the coherence norm estimate (7.8.b)
`S09.Hypothesis78.NormEstimates` to `M` (Peterfalvi (10.8), 04.12 line 79). -/
noncomputable def toHypothesis71 {M : Subgroup G} [Finite G] (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (typePA M hyp.typeP) M :=
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  { hyp := hyp.dadeData.dade.restrict Set.subset_union_left hnorm
    τ := ((hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).restrict
      Set.subset_union_left hnorm).toDadeMap
    isDadeMap := ((hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).restrict
      Set.subset_union_left hnorm).toDadeIsometryData.isDadeMap
    hConjInvariant := hyp.hconj.restrict Set.subset_union_left hnorm }

open scoped FiniteInduce in
/-- **The Peterfalvi (7.4) one-member family `{(M, A(M))}`** — the direct input to the family
inequality (7.5) `S09.family_inequality` for the (10.8) estimate.  The single member's (7.1) data is
`toHypothesis71`; the `IsDadeIsometry` certificate is the restricted Dade isometry's
(`FullDadeIsometryData.toDadeIsometryData.isDadeIsometry`), and `pairwise_disjoint` is vacuous over
`Fin 1`.  Sorry-free and self-contained (the `M`-stability is `le_normalizer_typePA`). -/
noncomputable def toFamilyHypothesis71 {M : Subgroup G} [Finite G] (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S09.FamilyHypothesis71 G 1 where
  L := fun _ => M
  A := fun _ => typePA M hyp.typeP
  fintypeL := fun _ => inferInstance
  invertibleL := fun _ => inferInstance
  hyp71 := fun _ => hyp.toHypothesis71
  isDadeIsometry := fun _ => by
    have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
        (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
      ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
    exact ((hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).restrict
      Set.subset_union_left hnorm).toDadeIsometryData.isDadeIsometry
  pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end Hypothesis

open scoped FiniteInduce in
/-- **Peterfalvi (10.1), existence**: every maximal subgroup `M` of type III, IV,
or V carries the (10.1) Hypothesis.  The character family, support, and Dade
isometry are now the genuine `inducedFamily`, `A_0(M)`, and
`S07.dadeIntegralCharacterMap`; the only inputs are the (8.15) Dade support data
(`S10.dadeSupportHypotheses_typeP`) and the conjugation invariance `hconj` of the
support kernels (a (8.14)/(8.15) fact). -/
theorem exists_hypothesis_of_typeIIIorIVorV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    Nonempty (Hypothesis M) := by
  obtain ⟨data⟩ := typePData_of_isTypeNonI (Or.inr hType)
  -- Types III/IV/V are `P₁` (classification): III/IV via `(III∨IV) ↔ (P₁ ∧ M_F≠M_σ)`, V via
  -- `V ↔ (P₁ ∧ M_F=M_σ)`.  This routes the `A_0(M)` datum through the *`sorry`-free* type-`P₁`
  -- construction `dadeSupportHypothesisData_typePA0_of_isTypeP1` (not the general
  -- `dadeSupportHypotheses_typeP`, whose type-`P₂` branches are still `sorry`).
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification hG hM
    rcases hType with h | h | h
    · exact (hcls.2.2.1.mp (Or.inl h)).1
    · exact (hcls.2.2.1.mp (Or.inr h)).1
    · exact (hcls.2.2.2.1.mp h).1
  obtain ⟨dadeData⟩ :=
    OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1 hG hM data hP1
  -- (8.14)/(8.15): the kernel conjugation invariance is carried by the faithful datum.
  refine ⟨?_⟩
  exact
    { maximal := hM
      typeP := data
      type_alt := hType
      dadeData := dadeData
      hconj := dadeData.hconj }

/-! ## §10 → §5 ω-grid bridge prerequisites (gate #3)

The Peterfalvi §10 character analysis ((10.2)–(10.10)) consumes the §5 `ω_{ij}` grid
(`S05.TICyclicHypothesis.omegaGrid` / `omegaSigmaGrid`) on `W = W₁ × W₂`.  Building the
bridge `Hypothesis → S05.TICyclicHypothesis` rests on the cyclic-`TI` structure of `(W, V)`,
whose first prerequisites are the disjointness and coprimality of the factors `W₁`, `W₂`.
See `notes/peterfalvi/s12_s10_character_bridge.md`. -/

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup are disjoint:
`W₁` complements `M' = [M,M]` in `M` (`TypePData.M_complement`), and `W₂ ≤ M'`
(`W₂ ≤ H ⊓ M'' ≤ H ≤ M'`), so `W₁ ⊓ W₂ ≤ W₁ ⊓ M' = ⊥`. -/
theorem typePData_disjoint_W1_W2 {M : Subgroup G} (data : TypePData M) :
    Disjoint data.W1 data.W2 := by
  have hW2D : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (inf_le_left.trans data.H_le)
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  have hxM : x ∈ M := data.W1_le hx1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hmem1 : (⟨x, hxM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hW2D hx2)
  have hmem2 : (⟨x, hxM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx1
  exact Subtype.ext_iff.mp (hdisj hmem1 hmem2)

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup have coprime orders.
`W = W₁ × W₂` is cyclic (`TypePData.W_cyclic`) and `W₁`, `W₂` are disjoint
(`typePData_disjoint_W1_W2`), so the multiplication map `↥W₁ × ↥W₂ →* ↥W` is injective;
a group embedding into the cyclic `↥W` is cyclic, and a finite cyclic product forces
coprime factor orders (`coprime_card_of_isCyclic_prod`). -/
theorem typePData_coprime_card_W1_W2 [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥data.W2) := by
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := typePData_disjoint_W1_W2 data
  have hinj : Function.Injective
      ((Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.coprod_apply] at hab
    have hG : (a : G) * (b : G) = 1 := by
      have h2 := congrArg (Subtype.val (p := fun x => x ∈ data.W)) hab
      simpa [Subgroup.coe_inclusion] using h2
    have ha1 : (a : G) = 1 := by
      have haW2 : (a : G) ∈ data.W2 := by
        rw [mul_eq_one_iff_eq_inv.mp hG]; exact data.W2.inv_mem b.2
      have hmem : (a : G) ∈ data.W1 ⊓ data.W2 := ⟨a.2, haW2⟩
      rw [disjoint_iff.mp hdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb1 : (b : G) = 1 := by rw [ha1, one_mul] at hG; exact hG
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  haveI : IsCyclic (↥data.W1 × ↥data.W2) := isCyclic_of_injective _ hinj
  exact coprime_card_of_isCyclic_prod (↥data.W1) (↥data.W2)

/-- The cyclic factor product `W = W₁ × W₂` of a type-`P` maximal subgroup has odd order.
`W ≤ G`, so `|W| ∣ |G|`, and `G` has odd order; a divisor of an odd number is odd. -/
theorem typePData_W_card_odd [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G)) : Odd (Nat.card ↥data.W) :=
  hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.W)

/-- For a type-`P` maximal subgroup the exceptional set `V = W − (W₁ ∪ W₂)` is nonempty:
the product `x·y` of a nontrivial `x ∈ W₁` and a nontrivial `y ∈ W₂` lies in `W` but in neither
factor, since `W₁` and `W₂` are disjoint (`typePData_disjoint_W1_W2`). -/
theorem typePData_typePV_nonempty {M : Subgroup G} (data : TypePData M) :
    (typePV M data).Nonempty := by
  obtain ⟨x, hxW1, hxne⟩ := (data.W1.bot_or_exists_ne_one).resolve_left data.W1_nontrivial
  obtain ⟨y, hyW2, hyne⟩ := (data.W2.bot_or_exists_ne_one).resolve_left data.W2_nontrivial
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := disjoint_iff.mp (typePData_disjoint_W1_W2 data)
  refine ⟨x * y, ?_⟩
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
  refine ⟨mul_mem (hW1le hxW1) (hW2le hyW2), ?_, ?_⟩
  · intro hxy
    have hy1 : y ∈ data.W1 := by
      have he : y = x⁻¹ * (x * y) := by group
      rw [he]; exact mul_mem (inv_mem hxW1) hxy
    exact hyne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hy1, hyW2⟩))
  · intro hxy
    have hx1 : x ∈ data.W2 := by
      have he : x = (x * y) * y⁻¹ := by group
      rw [he]; exact mul_mem hxy (inv_mem hyW2)
    exact hxne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hxW1, hx1⟩))

/-- **The type-`P` torus has order `|W| = w₁·w₂`** (`W = W₁ × W₂`).  The factors `W₁`, `W₂` are
disjoint (`typePData_disjoint_W1_W2`) subgroups of the cyclic — hence abelian — `W`
(`W = W₁ ⊔ W₂`), so realised inside `↥W` they are a normal complement pair and the order is the
product (`card_sup_eq_card_mul_card_of_disjoint_normal`).  Fundamental structural fact of the
type-`P` torus, used throughout §10--§11 (the `(4.5)` reducible characters, the `V^G` counting). -/
theorem typePData_card_W [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥data.W = Nat.card ↥data.W1 * Nat.card ↥data.W2 := by
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  haveI hBnorm : (data.W2.subgroupOf data.W).Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [mul_comm g n]; group
    rw [h]; exact hn⟩
  have hdisjAB : data.W1.subgroupOf data.W ⊓ data.W2.subgroupOf data.W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have h1 : ((x : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx.1
    have h2 : ((x : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hx.2
    have hmem : ((x : ↥data.W) : G) ∈ data.W1 ⊓ data.W2 := ⟨h1, h2⟩
    rw [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hsupAB : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hcard := OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
    (T := data.W1.subgroupOf data.W) (M := data.W2.subgroupOf data.W) hdisjAB
  rw [hsupAB, Nat.card_congr (Subgroup.topEquiv (G := ↥data.W)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv] at hcard
  exact hcard

/-- **The exceptional set `V = W − (W₁ ∪ W₂)` has `|V| = w₁w₂ − w₁ − w₂ + 1`.**  Since `W₁, W₂ ⊆ W`
their union lies in `W`, so `|V| = |W| − |W₁ ∪ W₂|`; the factors meet only in `1`
(`typePData_disjoint_W1_W2`), so `|W₁ ∪ W₂| = w₁ + w₂ − 1`, and `|W| = w₁w₂`
(`typePData_card_W`).  This is the `|V^G| = |G:W|·(w₁w₂−w₁−w₂+1)` numerator of Peterfalvi (10.8). -/
theorem typePData_typePV_ncard [Finite G] {M : Subgroup G} (data : TypePData M) :
    (typePV M data).ncard
      = Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1 - Nat.card ↥data.W2 + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  -- set cardinalities of the subgroups
  have hcW1 : ((data.W1 : Set G)).ncard = Nat.card ↥data.W1 := (Nat.card_coe_set_eq _).symm
  have hcW2 : ((data.W2 : Set G)).ncard = Nat.card ↥data.W2 := (Nat.card_coe_set_eq _).symm
  have hcW : ((data.W : Set G)).ncard = Nat.card ↥data.W := (Nat.card_coe_set_eq _).symm
  -- `W₁ ∪ W₂ ⊆ W`
  have hsub : ((data.W1 : Set G) ∪ (data.W2 : Set G)) ⊆ (data.W : Set G) :=
    Set.union_subset hW1le hW2le
  -- `W₂ \ W₁ = W₂ \ {1}`: for `x ∈ W₂`, `x ∈ W₁ ↔ x = 1` (disjointness).
  have hW2diff : (data.W2 : Set G) \ (data.W1 : Set G) = (data.W2 : Set G) \ {1} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    refine ⟨fun ⟨hx2, hx1⟩ => ⟨hx2, fun h => hx1 (h ▸ data.W1.one_mem)⟩,
      fun ⟨hx2, hxne⟩ => ⟨hx2, fun hx1 => hxne ?_⟩⟩
    have hmem : x ∈ data.W1 ⊓ data.W2 := ⟨hx1, hx2⟩
    rw [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
    exact hmem
  -- `|W₁ ∪ W₂| = w₁ + w₂ − 1` (decompose `W₁ ∪ W₂ = W₁ ⊔ (W₂ \ W₁)`, disjoint).
  have hunion : ((data.W1 : Set G) ∪ (data.W2 : Set G)).ncard
      = Nat.card ↥data.W1 + Nat.card ↥data.W2 - 1 := by
    have h2pos : 1 ≤ Nat.card ↥data.W2 := Nat.card_pos
    rw [← Set.union_diff_self (s := (data.W1 : Set G)) (t := (data.W2 : Set G)),
      Set.ncard_union_eq disjoint_sdiff_self_right (Set.toFinite _) (Set.toFinite _), hW2diff,
      Set.ncard_sdiff (Set.singleton_subset_iff.mpr data.W2.one_mem), Set.ncard_singleton,
      hcW1, hcW2]
    omega
  -- `V = W \ (W₁ ∪ W₂)` has `|V| = |W| − |W₁ ∪ W₂|`
  have hdiff : (typePV M data).ncard = ((data.W : Set G)).ncard
      - ((data.W1 : Set G) ∪ (data.W2 : Set G)).ncard := by
    rw [typePV, Set.ncard_sdiff hsub]
  rw [hdiff, hunion, hcW, typePData_card_W]
  have hw1ge : 1 < Nat.card ↥data.W1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W1_nontrivial
  have hw2ge : 1 < Nat.card ↥data.W2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W2_nontrivial
  have hprod : Nat.card ↥data.W1 + Nat.card ↥data.W2 ≤ Nat.card ↥data.W1 * Nat.card ↥data.W2 :=
    Nat.add_le_mul hw1ge hw2ge
  omega

/-- For a type-`P` maximal subgroup, every `l ∈ W` stabilises the exceptional set `V` under
conjugation: `l ∈ N_G(V) = W` (`TypePData.normalizer_V` with `X = V`), so `(MulAut.conj l) • V = V`.
This is the `W`-stability input to the `|V^G|` TI-orbit count `ncard_conjClassSet_of_isTISubset`. -/
theorem typePData_W_normalizes_typePV [Finite G] {M : Subgroup G} (data : TypePData M) :
    ∀ l ∈ data.W, MulAut.conj l • (typePV M data) = typePV M data := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer (typePV M data) := by
    rw [data.normalizer_V (typePV M data) (typePData_typePV_nonempty data) Set.Subset.rfl]
    exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hlN v).mp hv
  · intro hx
    exact ⟨l⁻¹ * x * l, (hlN _).mpr (by rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx),
      by group⟩

/-- **The conjugacy-saturation `V^G` of the exceptional set has `|V^G| = |G:W|·(w₁w₂−w₁−w₂+1)`.**
`V` is a TI-subset with normalizer `W` (`typePData_V_ti` + `typePData_W_normalizes_typePV`), so the
orbit count is `|V|·|G:W|` (`ncard_conjClassSet_of_isTISubset`), with `|V| = w₁w₂−w₁−w₂+1`
(`typePData_typePV_ncard`).  This is the `|V^G|` numerator of the Peterfalvi (10.8) TI-counting
(lines 89--91, the `(w₁w₂−w₁−w₂+1)/(w₁w₂)` term once divided by `|G|`). -/
theorem typePData_conjClassSet_typePV_ncard [Finite G] {M : Subgroup G} (data : TypePData M) :
    (conjClassSet (typePV M data)).ncard
      = (Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1 - Nat.card ↥data.W2 + 1)
        * data.W.index := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset (OddOrder.Peterfalvi.S10.typePData_V_ti data)
    (typePData_W_normalizes_typePV data), typePData_typePV_ncard]

/-- `W₂ ≤ M` for type-`P` data (`W₂ ≤ H ⊓ M'' ≤ M' ≤ M`). -/
theorem typePData_W2_le_self {M : Subgroup G} (data : TypePData M) : data.W2 ≤ M :=
  (data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))).trans
    (Subgroup.map_subtype_le _)

/-- `W ≤ M` for type-`P` data (`W = W₁ ⊔ W₂`, both `≤ M`). -/
theorem typePData_W_le_self {M : Subgroup G} (data : TypePData M) : data.W ≤ M :=
  data.W_eq ▸ sup_le data.W1_le (typePData_W2_le_self data)

/-- The §6 `↥M`-level `W = W₁.subgroupOf M ⊔ W₂.subgroupOf M` is `W.subgroupOf M`: the `subgroupOf`
order-iso on subgroups `≤ M` preserves joins. -/
theorem typePData_sup_subgroupOf_eq {M : Subgroup G} (data : TypePData M) :
    data.W1.subgroupOf M ⊔ data.W2.subgroupOf M = data.W.subgroupOf M := by
  rw [← Subgroup.subgroupOf_sup data.W1_le (typePData_W2_le_self data), ← data.W_eq]

/-- The `W ≤ M ≤ G` isomorphism `↥W ≃* ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)` used to transport the
§6 `↥M`-level `ω`-grid (built on `W₁.subgroupOf M ⊔ W₂.subgroupOf M`) to the §5 `G`-level TI-cyclic
hypothesis (built on `W ≤ G`).  This is the `e` reconstructed inline in `alignedOmegaSigmaGrid`; named
here so the (10.6) column-structure argument can reason about how it respects the `W₁/W₂`
decomposition.  Both `subgroupOfEquivOfLe.symm` and `subgroupCongr` preserve the underlying
`G`-element, so does `e` (`typePData_WEquiv_coe`). -/
noncomputable def typePData_WEquiv {M : Subgroup G} (data : TypePData M) :
    ↥data.W ≃* ↥(data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) :=
  (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self data)).symm.trans
    (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq data).symm)

/-- `typePData_WEquiv` preserves the underlying `G`-element. -/
@[simp] theorem typePData_WEquiv_coe {M : Subgroup G} (data : TypePData M) (w : ↥data.W) :
    (((typePData_WEquiv data w : ↥(data.W1.subgroupOf M ⊔ data.W2.subgroupOf M)) : ↥M) : G)
      = (w : G) := rfl

/-- `typePData_WEquiv` maps the `W₁`-block into the `W₁`-block: if `w ∈ W₁.subgroupOf W` then
`e w ∈ (W₁.subgroupOf M).subgroupOf (W₁.subgroupOf M ⊔ W₂.subgroupOf M)`.  Underlying-element
preservation reduces both memberships to `(w : G) ∈ W₁`. -/
theorem typePData_WEquiv_mem_W1 {M : Subgroup G} (data : TypePData M) {w : ↥data.W}
    (hw : w ∈ (data.W1.subgroupOf data.W)) :
    typePData_WEquiv data w ∈
      (data.W1.subgroupOf M).subgroupOf (data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, typePData_WEquiv_coe]
  exact Subgroup.mem_subgroupOf.mp hw

/-- `typePData_WEquiv` maps the `W₂`-block into the `W₂`-block (see `typePData_WEquiv_mem_W1`). -/
theorem typePData_WEquiv_mem_W2 {M : Subgroup G} (data : TypePData M) {w : ↥data.W}
    (hw : w ∈ (data.W2.subgroupOf data.W)) :
    typePData_WEquiv data w ∈
      (data.W2.subgroupOf M).subgroupOf (data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, typePData_WEquiv_coe]
  exact Subgroup.mem_subgroupOf.mp hw

open scoped FiniteInduce in
/-- **§10 → §5 ω-grid bridge (gate #3)**: a type-`P` maximal subgroup's cyclic factor
`W = W₁ × W₂`, with the exceptional set `V = W − (W₁ ∪ W₂)`, is a Peterfalvi (3.1) TI-cyclic
normalizer setup in the ambient group `G`.  Every structural field is read off from the
`TypePData`: the `W`-block is disjoint (`typePData_disjoint_W1_W2`) / coprime
(`typePData_coprime_card_W1_W2`) / cyclic (`W_cyclic`), oddness comes from `Odd |G|`, and `V` is
`W`-normalized because the cyclic `W` is abelian.

The ambient TI property `V_ti : IsTISubset V W` — Peterfalvi (4.6.b), the `G`-version of (4.3.a) —
is the one field that does not read off directly from the `TypePData` fields; it is supplied by the
companion `typePData_V_ti`, which derives it from `normalizer_V` together with the cyclic factor
structure (`W₁`, `W₂` are the unique, hence characteristic, subgroups of their orders in the cyclic
`W`).  This makes the bridge **unconditional** (no external TI hypothesis; closes issue 1005).

Through this bridge the entire §5 ω/σ-grid (`TICyclicHypothesis.omegaGrid`, `omegaSigmaGrid`,
`sigmaIntegral`) becomes available for the §10 character analysis ((10.2)–(10.10)). -/
noncomputable def typePData_toTICyclicHypothesis [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis G where
  W := data.W
  W1 := data.W1
  W2 := data.W2
  W1_le_W := by rw [data.W_eq]; exact le_sup_left
  W2_le_W := by rw [data.W_eq]; exact le_sup_right
  W1_nontrivial := data.W1_nontrivial
  W2_nontrivial := data.W2_nontrivial
  W_sup := data.W_eq.symm
  W_disjoint := typePData_disjoint_W1_W2 data
  W_card_coprime := typePData_coprime_card_W1_W2 data
  W_card_odd := typePData_W_card_odd data hodd
  W_cyclic := data.W_cyclic
  V := typePV M data
  V_subset_sharp := by
    intro v hv
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    refine ⟨Set.mem_univ v, fun heq => hv.2 (Or.inl ?_)⟩
    rw [heq]; exact data.W1.one_mem
  V_subset_W := fun _ hv => hv.1
  W_normalizes_V := by
    intro w v hv
    have hcomm : Commute (w : G) v :=
      S06.commute_of_mem_of_isCyclic data.W_cyclic w.2 hv.1
    have h3 : (w : G) * v * (w : G)⁻¹ = v := by rw [hcomm.eq, mul_inv_cancel_right]
    rw [h3]; exact hv
  V_ti := OddOrder.Peterfalvi.S10.typePData_V_ti data

/-! ## §10 → §6 (4.2)+Dade bridge (μ-grid unlock)

Peterfalvi (10.1) states that Hypothesis (4.6) holds with `L = M`, `H = K = M' = [M,M]`.  Once that
instantiation is realised, the §6 certain-type apparatus (the `μ_{ij}`/`ω_{ij}`/`ζ` families, the
Brauer permutation lemma, the Clifford inertia computation) supplies (10.2), (10.3) and the `μ`-grid
directly.  This bridge builds the §6 *structural* Hypothesis (4.2) `S06.Hypothesis ↥M` from the
`TypePData`, then combines it with the §10 Dade datum (`dadeData.dade`, already a
`S04.Hypothesis G (A₀(M)) M`) into a `S06.CertainTypeHypothesis`.  See
`notes/peterfalvi/s12_s10_character_bridge.md` §6. -/

/-- **Peterfalvi (4.2.a) Hall coprimality** (issue 1006): for a type-`P` maximal subgroup `M`,
`gcd(|M'|, |W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M' = [M,M]` in `M`.

A bare complement need not be Hall, but the κ-Hall structure of a type-`P` maximal supplies it: a
Hall `κ(M)`-subgroup `K ≤ M` (`exists_isHallSubgroup_kappa_ge`) is cyclic (BG Theorem A, the
**sorry-free faithful** `S15.typeP_auxiliary_structure`), so it complements `M'` in `M`
(`typeP_derivedInG_isComplement_kappaHall`); hence `gcd(|K|, |M'|) = 1`
(`IsHallSubgroup.coprime_index`), and `|K| = [M:M'] = |W₁|` (`card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`).  Discharges the `hHall` obligation of the §10 → §6 bridge. -/
theorem typePData_W1_hall_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K ≤ M`.
  obtain ⟨K, hKM, hK, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by simp)
  -- A `(κ(M) ∪ σ(M))'`-Hall subgroup `U` (needed only to invoke BG Theorem A).
  obtain ⟨U', hU'hall, -⟩ :=
    Ch03.hall_D (G := ↥M)
      (π := (OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U := ⊥) (by simp)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'hall
  -- `K` is cyclic by BG Theorem A (the sorry-free faithful `typeP_auxiliary_structure`).
  haveI : IsCyclic ↥K :=
    (OddOrder.BG.Ch4.S15.typeP_auxiliary_structure hG hM hKM (Subgroup.map_subtype_le U')
      hK rfl hU).2.1
  -- Coprimality `gcd(|K|, |M'|) = 1` from the κ-Hall complement (mirrors S14_TypePComplement).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  -- `|K| = [M:M'] = |W₁|`.
  have hKW1 : Nat.card ↥K = Nat.card ↥data.W1 := by
    rw [OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index hG hM hP hKM hK,
      data.card_W1_eq_derived_index]
  rw [Nat.coprime_comm, ← hKW1]; exact hCop

/-- **§10 → §6 (4.2) bridge, structural part**: build the Peterfalvi Hypothesis (4.2)
`S06.Hypothesis ↥M` from a type-`P` maximal subgroup's `TypePData`, with `L = M`, `K = M' = [M,M]`
and the (8.4) cyclic factors `W₁, W₂` transported into `↥M` via `subgroupOf`.  Structural fields
come from `TypePData`: `M_complement → isComplement`, `centralizer_W1 → centralizer_W2` (through the
ambient↔`↥M` centralizer transport `S03h.centralizer_subgroupOf`), and cyclicity / oddness through
the order-preserving `subgroupOfEquivOfLe`; `K ⊴ ↥M` because `K = commutator ↥M`.

The Hall coprimality `card_coprime` (`gcd(|M'|,|W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M'`
in `M`) is **not** derivable from `TypePData` alone — a complement need not be Hall — so it is taken
as the input `hHall`.  This is the Peterfalvi (4.2.a) Hall condition, dischargeable at call sites
from the κ-Hall structure of a type-`P` maximal (`typeP_derivedInG_isComplement_kappaHall` +
`IsHallSubgroup.coprime_index`, since `|W₁| = [M:M'] = |κ-Hall K|`).  See issue 1006. -/
def typePData_toS06Hypothesis [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥M := by
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2leM' : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))
  have hW2leM : data.W2 ≤ M := hW2leM'.trans hM'le
  haveI := data.W1_cyclic
  haveI := data.W2_cyclic
  exact
    { K := (derivedInG M).subgroupOf M
      W1 := data.W1.subgroupOf M
      W2 := data.W2.subgroupOf M
      K_normal := by
        rw [show (derivedInG M).subgroupOf M = commutator ↥M by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
        infer_instance
      isComplement := data.M_complement
      W1_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W1_nontrivial (disjoint_self.mp (hdisj.mono_right data.W1_le))
      W1_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe data.W1_le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.W1_le).injective
      card_coprime := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
        exact hHall
      W2_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W2_nontrivial (disjoint_self.mp (hdisj.mono_right hW2leM))
      W2_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hW2leM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hW2leM).injective
      W2_le_K := Subgroup.comap_mono hW2leM'
      centralizer_W2 := by
        intro x hx1 hx2
        have hxW1 : (x : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx1
        have hxne : (x : G) ≠ 1 := fun h => hx2 (Subtype.ext h)
        have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = data.W2 := by
          rw [inf_comm]; exact data.centralizer_W1 (x : G) hxW1 hxne
        rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
        simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]
      W_odd := by
        rw [← Subgroup.subgroupOf_sup data.W1_le hW2leM,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le data.W1_le hW2leM)).toEquiv,
          ← data.W_eq]
        exact typePData_W_card_odd data hodd }

/-- The §10 Hypothesis (10.1) for a type III/IV/V maximal subgroup `M` exhibits `M` as a *BG*
type-`P` maximal (`(κ(M)).Nonempty`).  By BG Proposition 16.1
(`proposition_type_classification`, cited even though it currently carries a `sorry`), each
Peterfalvi type III/IV/V maps to `S14.IsTypeP1`, hence to `S14.IsTypeP`.  This is the BG type-`P`
input needed to discharge the Hall coprimality `typePData_W1_hall_coprime`. -/
theorem Hypothesis.bgTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) : OddOrder.BG.Ch4.S14.IsTypeP M := by
  have hclass := OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.maximal
  rcases hyp.type_alt with h | h | h
  · exact (hclass.2.2.1.mp (Or.inl h)).1.1
  · exact (hclass.2.2.1.mp (Or.inr h)).1.1
  · exact (hclass.2.2.2.1.mp h).1.1

open scoped FiniteInduce in
/-- **§10 → §6 (4.2)+Dade bridge**: from the §10 Hypothesis (10.1) for a type-`P` maximal subgroup
`M`, build the §6 certain-type Hypothesis `S06.CertainTypeHypothesis (A₀(M)) M`.  The structural
(4.2) part is `typePData_toS06Hypothesis`; the Dade datum is the §10 `dadeData.dade` (already a
`S04.Hypothesis G (typePA0 M typeP) M`), so no new Dade construction is needed.  This unlocks the
entire §6 μ/ω/ζ machinery with `L = M`, the common source of (10.2), (10.3) and the `μ`-grid.

The Hall coprimality is discharged internally via `typePData_W1_hall_coprime` (using the BG
type-`P` from `Hypothesis.bgTypeP`), so this bridge is **unconditional** — no external `hHall`
input (closes issue 1006 for the §10 consumer). -/
def Hypothesis.toCertainTypeHypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.CertainTypeHypothesis (typePA0 M hyp.typeP) M :=
  haveI := hyp.finiteG
  { toHypothesis := typePData_toS06Hypothesis hyp.typeP hodd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
    dade := hyp.dadeData.dade }

open scoped FiniteInduce in
/-- **Peterfalvi (8.15) for type `P` / the (10.1) sentence "Hypothesis (4.6) holds with `L = M`,
`K = M'`, `A = A(M)`, `A₀ = A₀(M)`, `H = M_s`"**: the §10 `Hypothesis` instantiates the §4/§6
Hypothesis (4.6) carrier `S06.Hypothesis46 (A(M)) M`.

Field sources:
* the (4.2) structural part and the `A`-side Dade datum: `toCertainTypeHypothesis`, with the
  Dade hypothesis restricted from `A₀(M)` to the `M`-stable `A(M)` (`S04.Hypothesis.restrict` +
  `le_normalizer_typePA`, as in `toHypothesis71`);
* the ambient (3.1) TI-cyclic data (4.6.b): `typePData_toTICyclicHypothesis`, whose `W`, `W₁`,
  `W₂`, `V = W − (W₁ ∪ W₂)` are the `TypePData` fields — the `subgroupOf`-vs-ambient matching
  `tic_W1`/`tic_W2` is `Subgroup.map_subgroupOf_eq_of_le`, and `tic_V` is definitional;
* (4.6.c): `H := K = M'` (the (10.1) choice `H = M_s`, which equals `M'` for types III/IV and,
  via `U = ⊥`, also for type V), so `W₂ ≤ H ≤ K` are inherited;
* (4.6.d): the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A` is trivial for `H = K`:
  `A(M) = (M')# = K#` (`typePA_eq_sharpSubgroup_derivedInG`) already contains every
  nonidentity element of `K`;
* (4.6.d)/(4.6.e): the `A₀`-side Dade datum and isometry are **definitionally** the (8.15)
  §10 data `hyp.dadeData.dade` / its `fullDadeIsometryData`: `A(M) ∪ conjClassSetIn M tic.V`
  unfolds to `typePA0 M` (`tic.V = typePV M` by construction) — the payoff of stating both
  (8.10) `typePA0` and (4.6.d) with `conjClassSetIn`.

This closes the instantiation gap flagged in issue 9004 and lets the §10 grid consume the §6
(4.8)/(4.10) Dade identities (`certainType_diff_dade_eq`, `fourCorner_dade_eq`) — the `h48`/`h410`
threads of the (11.8.3) `β`-reality argument. -/
noncomputable def Hypothesis.toHypothesis46 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M hyp.typeP) M :=
  haveI := hyp.finiteG
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  { toHypothesis := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
    dade := hyp.dadeData.dade.restrict Set.subset_union_left hnorm
    tic := typePData_toTICyclicHypothesis hyp.typeP hodd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le hyp.typeP.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self hyp.typeP)).symm
    tic_V := rfl
    subH := (hyp.toCertainTypeHypothesis hG hodd).K
    subH_normal := (hyp.toCertainTypeHypothesis hG hodd).K_normal
    W2_le_subH := (hyp.toCertainTypeHypothesis hG hodd).W2_le_K
    subH_le_K := le_refl _
    A_covers := fun _ _ _ x hx hx1 => by
      rw [typePA_eq_sharpSubgroup_derivedInG]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2,
        fun h1 => hx1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h1))⟩
    dade0 := hyp.dadeData.dade
    tau := hyp.dadeData.dade.fullDadeIsometryData hyp.hconj }

/-- **A finite non-perfect group has a non-trivial linear character.**  If `commutator K ≠ ⊤`
(the abelianization `K/[K,K]` is non-trivial), there is a non-trivial degree-one irreducible
character of `K`: a non-trivial element of `K/[K,K]` is separated by some `φ : (K/[K,K]) →* ℂˣ`
(Pontryagin duality over `ℂ`, `exists_apply_ne_one_of_hasEnoughRootsOfUnity`), pulled back along
`K ↠ K/[K,K]`.  This supplies the non-principal degree-`1` character of `M' = [M,M]` whose induction
to `M` is the (10.2) character `ζ`. -/
theorem exists_nontrivial_linearIrreducibleCharacter {K : Type*} [Group K] [Finite K]
    (hK : commutator K ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K, θ ≠ trivialIrreducibleCharacter K ∧
      (θ : ClassFunction K ℂ) 1 = 1 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : K, a ∉ commutator K := by
    by_contra h
    push Not at h
    exact hK (top_le_iff.mp fun x _ => h x)
  haveI : Finite (Abelianization K) := Quotient.finite _
  have hā : (Abelianization.of a) ≠ 1 := by
    rw [ne_eq, ← MonoidHom.mem_ker, Abelianization.ker_of]; exact ha
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (G := Abelianization K) (M := ℂ) hā
  set ψ : K →* ℂˣ := φ.comp Abelianization.of with hψdef
  have hψ : ψ ≠ 1 := fun h => hφ (by rw [← MonoidHom.comp_apply, ← hψdef, h, MonoidHom.one_apply])
  refine ⟨linearIrreducibleCharacter ψ, ?_, linearIrreducibleCharacter_apply_one ψ⟩
  rw [ne_eq, linearIrreducibleCharacter_eq_trivial_iff]
  exact hψ

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)**: the family `S = {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}` contains an
irreducible character `ζ` of degree `w₁ = |W₁|`.

Take a non-principal degree-`1` character `θ` of `M' = [M,M]` (exists since `M'` is not perfect:
`M'' < M'`, via `exists_nontrivial_linearIrreducibleCharacter`).  By the §6 Clifford engine `θ` is
none of the `chiRestrict χ₂` (the `W₁^#`-fixed irreducibles of `M'`): the trivial column gives
`chiRestrict 1 = Res_{M'} μ_{00} = Res_{M'} 1_M = 1_{M'}` (Peterfalvi (4.4) anchor), avoided since
`θ ≠ 1`; a non-trivial column `χ₂` gives `chiRestrict χ₂ = Res_{M'} μ_{0j}` of degree
`μ_{0j}(1) > 1` (else `μ_{0j}` is linear ⇒ `M'`-trivial ⇒ a column-`0` character by (4.4),
contradicting `columnFamily_mu_ne`), avoided by degree.  Hence `Ind_{M'}^M θ` is irreducible
(`induce_isIrreducible_of_forall_chiRestrict_ne`) of degree `[M:M']·1 = |W₁|` (`induce_apply_one`
and `TypePData.card_W1_eq_derived_index`).  The §6 hypothesis is supplied by the §10→§6 bridge
`typePData_toS06Hypothesis` (so `K = M'`), needing the same `hodd`/`hHall` inputs. -/
theorem exists_zeta_in_inducedFamily_degree_w1 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ζ 1 = (Nat.card ↥data.W1 : ℂ) := by
  classical
  let h : OddOrder.Peterfalvi.S06.Hypothesis ↥M := typePData_toS06Hypothesis data hodd hHall
  haveI hNeZ : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `M'` is not perfect (issue 7008, replacing the deleted `fitting_lt_derived`): `M' = M_F ⋊ U`
  -- is solvable — `M_F` nilpotent (`maxNilpotentNormalHall_isNilpotent`) is the normal kernel and the
  -- quotient `M'/M_F ≃ U` is nilpotent (`U_nilpotent`) via `derived_complement` — and nontrivial
  -- (`W₂ ≠ ⊥`, `W₂ ≤ M_F ≤ M'`); a nontrivial solvable group is not perfect.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  haveI hHnorm : (data.H.subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.H_le).mpr ?_
    rw [data.H_eq]
    exact hM'le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M)
  haveI : IsSolvable ↥(data.H.subgroupOf (derivedInG M)) := by
    haveI : Group.IsNilpotent ↥data.H := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    haveI : IsSolvable ↥data.H := IsNilpotent.to_isSolvable
    exact solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.H_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.H_le).injective
  haveI : IsSolvable ↥(data.U.subgroupOf (derivedInG M)) := by
    haveI : Group.IsNilpotent ↥data.U := data.U_nilpotent
    haveI : IsSolvable ↥data.U := IsNilpotent.to_isSolvable
    exact solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.U_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.U_le).injective
  haveI : IsSolvable (↥(derivedInG M) ⧸ data.H.subgroupOf (derivedInG M)) :=
    solvable_of_solvable_injective
      (f := data.derived_complement.symm.QuotientMulEquiv.toMonoidHom)
      data.derived_complement.symm.QuotientMulEquiv.injective
  haveI : IsSolvable ↥(derivedInG M) :=
    solvable_of_ker_le_range ((data.H.subgroupOf (derivedInG M)).subtype)
      (QuotientGroup.mk' (data.H.subgroupOf (derivedInG M)))
      (by rw [QuotientGroup.ker_mk']; exact (data.H.subgroupOf (derivedInG M)).range_subtype.ge)
  haveI : Nontrivial ↥(derivedInG M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot =>
      data.W2_nontrivial (le_bot_iff.mp (hbot ▸ data.W2_le.trans (inf_le_left.trans data.H_le)))
  have hcomm_K : commutator ↥h.K ≠ ⊤ := by
    intro hperf
    have hperfM' : Group.IsPerfect ↥(derivedInG M) := by
      haveI : Group.IsPerfect ↥((derivedInG M).subgroupOf M) := ⟨hperf⟩
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hM'le).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hM'le).surjective
    exact absurd hperfM'.commutator_eq_top
      (IsSolvable.commutator_lt_top_of_nontrivial ↥(derivedInG M)).ne
  obtain ⟨θ, hθne, hθ1⟩ := exists_nontrivial_linearIrreducibleCharacter hcomm_K
  -- the crux: `θ` avoids every `chiRestrict χ₂`.
  have havoid : ∀ χ₂, h.chiRestrict χ₂ ≠ θ := by
    intro χ₂ heq
    by_cases hχ₂ : χ₂ = 1
    · subst hχ₂
      refine hθne ?_
      rw [← heq]
      apply IrreducibleCharacter.ext
      rw [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, (h.certainType_zero_column_anchor).2,
        OddOrder.Peterfalvi.S03.restrict_trivialClassFunction]
      rfl
    · have hmu1 : ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) (1 : ↥M) = 1 := by
        have hval := congrArg
          (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) (1 : ↥h.K)) heq
        simp only [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
          Subgroup.coe_one] at hval
        rw [hval, hθ1]
      have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) := by
        intro x hx
        have hx1 := ((h.columnFamily χ₂).mu 0).isIrreducible
          |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
        rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
          OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
      obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
      exact h.columnFamily_mu_ne hχ₂ 0 i hi.symm
  refine ⟨ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ), ⟨θ, hθne, rfl⟩,
    h.induce_isIrreducible_of_forall_chiRestrict_ne havoid, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ1, mul_one, hKeq, ← data.card_W1_eq_derived_index]

/-! ## (10.2)--(10.4): basic character parameters and coherent extension -/

/-- **Pontryagin reindex** (the §5/§6 "`W₂`-dual ↔ `Fin w₂`" bridge): for a finite abelian group
`C`, the index set `Fin |C|` is equivalent to the character group `C →* ℂˣ`.  Since `ℂ` is
algebraically closed it has enough roots of unity, so `C ≃* (C →* ℂˣ)`
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`); composing with `C ≃ Fin |C|` reindexes
the character group by `Fin |C|`.  This is what lets the §6 `columnFamily` (indexed by `W₂`-duals)
populate the `Fin w₂`-indexed `μ`-grid of `CharacterParameters`.

The bijection is normalized to send `0` to the trivial character `1`
(`finCardEquivCharacterGroup_zero`, by composing with the transposition `(0 ↔ e⁻¹ 1)`), matching
Peterfalvi's convention that column `0` is the trivial column (`δ_0 = 1`, `μ_{00} = 1`, by (4.4))
and `0 < j < w₂` are the nontrivial columns of common degree `d` (10.3). -/
noncomputable def finCardEquivCharacterGroup (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
  let e : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
    (Finite.equivFin C).symm.trans
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity C ℂ).some.toEquiv.symm
  (Equiv.swap (0 : Fin (Nat.card C)) (e.symm 1)).trans e

/-- The normalized Pontryagin reindex sends `0` to the trivial character (Peterfalvi's column-`0`
convention). -/
theorem finCardEquivCharacterGroup_zero (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : finCardEquivCharacterGroup C 0 = 1 := by
  simp only [finCardEquivCharacterGroup, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]

instance instNeZeroW1 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w1 := by
  haveI := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

instance instNeZeroW2 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w2 := by
  haveI := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

open scoped FiniteInduce in
/-- **§10 μ-grid materialization** (Peterfalvi (10.1)/(4.3.b)): the `Fin w₁ × Fin w₂`-indexed family
of induced characters `μ_{ij}` of `M`, read off from the §6 `columnFamily` of the (now
unconditional) §10→§6 bridge `Hypothesis.toCertainTypeHypothesis`, reindexed by
`finCardEquivCharacterGroup` (the `W₂`-dual ↔ `Fin w₂` Pontryagin bijection) on the column index and
by the order identity `|W₁| = w₁` on the row index.  This is the genuine source for
`CharacterParameters.mu`. -/
noncomputable def Hypothesis.muGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  exact ((h.columnFamily χ₂).mu (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ)

open scoped FiniteInduce in
/-- **§10 ω^σ-grid materialization** (Peterfalvi (3.6)): the `Fin w₁ × Fin w₂`-indexed family of
virtual characters `ω_{ij}^σ` of `G`, read off from the §5 `TICyclicHypothesis.omegaSigmaGrid` of
the (now unconditional) §10→§5 bridge `typePData_toTICyclicHypothesis`.  The required §4 Dade
application is built directly: the TI-cyclic Dade hypothesis has trivial local subgroups
(`HConjInvariant.of_forall_H_eq_bot`), so `Hypothesis.fullDadeIsometryData` applies.  Its index set
`Fin |W₁| × Fin |W₂|` is definitionally `Fin w₁ × Fin w₂`.  This is the genuine source for
`CharacterParameters.omegaSigma`. -/
noncomputable def Hypothesis.omegaSigmaGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  exact fun i j => tic.omegaSigmaGrid hVeq app i j

open scoped FiniteInduce in
/-- **§10 aligned ω^σ-grid** (producer-local alignment fix for (10.5)): the §5 `σ`-image of the
*same* ω that `muGrid` is built from — `h.chiColumn χ₂ i` (`χ₂ = finCardEquivCharacterGroup j`,
`i` via `w1CharEquiv`) — transported from the §6 `↥M`-level `W = W₁ ⊔ W₂` to the §10 `G`-level
`tic.W = data.W` along the `W ≤ M ≤ G` isomorphism `e` (`subgroupOfEquivOfLe` ∘ `subgroupCongr` of
`typePData_sup_subgroupOf_eq`).

Unlike `omegaSigmaGrid` (which reindexes via the *independent* §5 `charEquiv`), this grid shares
`muGrid`'s indexing by construction, so on `V` it satisfies `alignedOmegaSigma_{ij}(v) =
chiColumn(v)` — matching `(μ_{ij} − δ·μ_{i0})(v) = δ·(chiColumn_{ij} − chiColumn_{i0})(v)` ((4.3.c))
needed by the (10.5) Dade-image identity.  This is the genuine `CharacterParameters.omegaSigma`. -/
noncomputable def Hypothesis.alignedOmegaSigmaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  -- §6 host (the source of `muGrid`'s ω `chiColumn`) — mirror `muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  -- §5 `G`-level TI-cyclic hypothesis (for `σ`) — mirror `omegaSigmaGrid`.
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  -- the `W ≤ M ≤ G` isomorphism `↥tic.W ≃* ↥(h.W₁ ⊔ h.W₂)`.
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- `σ` of the transported `chiColumn` (= `muGrid`'s own ω).
  exact tic.sigmaIntegral rfl app
    (ClassFunction.compHom e.toMonoidHom
      (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))

open scoped FiniteInduce in
/-- The canonical `(3.2)` Dade application of the type-`P` `TICyclicHypothesis`: the source of the
`σ`-grids (`omegaSigmaGrid`, `alignedOmegaSigmaGrid`).  The TI-cyclic Dade hypothesis has trivial
local subgroups (`HConjInvariant.of_forall_H_eq_bot`), so `Hypothesis.fullDadeIsometryData` applies.
Definitionally equal to the `app` reconstructed inline in the grids, so any `σ`-machinery lemma
(`chiFam`, `sigma`, `sigmaCoeff`) stated with this `app` aligns with the grids by `rfl`. -/
noncomputable def Hypothesis.canonicalFullDadeApp [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication
      (typePData_toTICyclicHypothesis hyp.typeP hodd) :=
  ⟨(typePData_toTICyclicHypothesis hyp.typeP hodd).toDadeHypothesis.fullDadeIsometryData
    (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), aligned ω^σ-grid is a `χ`-family member** (the §10 analogue of the §6
`certainTypeOmegaSigma_eq_chiFam`): `alignedOmegaSigmaGrid i j` is the `σ`-image of the irreducible
(linear) character `η = compHom e (chiColumn χ₂ i)` of `tic.W` — `chiColumn` is `ω(omegaProdChar …)`
hence a `linearIrreducibleCharacter`, and `compHom` of a linear character is again linear
(`compHom_linearIrreducibleCharacter`).  By `sigma_irreducibleCharacter` it is the orthonormal family
vector `χ_P` at the index `P = omegaIrrEquiv.symm η`.  This is what lets the (10.5) Dade-image
trichotomy reuse the §6 `(4.8)` endgame (`sigmaCoeff_psi_eq`, `grid_trichotomy`). -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_chiFam_family [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ P : Fin hyp.w2 →
        (((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ) ×
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
      Function.Injective P ∧
        ∀ j, hyp.alignedOmegaSigmaGrid hG hodd i j
          = (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
              (hyp.canonicalFullDadeApp hG hodd) (P j) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the lets of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported `chiColumn` is the linear (irreducible) character `η j` of `tic.W`.
  let η : Fin hyp.w2 → IrreducibleCharacter ↥tic.W := fun j =>
    linearIrreducibleCharacter
      ((h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j)).comp
        e.toMonoidHom)
  refine ⟨fun j => tic.omegaIrrEquiv.symm (η j), ?_, ?_⟩
  · -- injectivity: peel off the injective maps `omegaIrrEquiv.symm`, `linearIrreducibleCharacter`,
    -- precompose-`e`, `omegaProdChar(·, ·)`, `finCardEquivCharacterGroup`, `finCongr`.
    intro j j' hjj'
    have h1 : η j = η j' := tic.omegaIrrEquiv.symm.injective hjj'
    have h2 := linearIrreducibleCharacter_injective h1
    have h3 := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp h2
    have h4 := (h.sdiffTICyclicHypothesis.omegaProdChar_inj h3).2
    exact (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective h4)
  · -- value: `alignedOmegaSigmaGrid i j = σ(η j) = χ_{omegaIrrEquiv.symm (η j)}`.
    intro j
    have step1 : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
          = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
    rw [step1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_irreducibleCharacter]

open scoped FiniteInduce in
/-- **§10 σ-grid orthonormality** (the (3.2) isometry on the aligned `ω^σ`-grid): the `G`-level
σ-images `alignedOmegaSigmaGrid i j` form an **orthonormal** family indexed by `Fin w₁ × Fin w₂`,
`⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = [i = i' ∧ j = j']`.

Each `ω_{ij}^σ = σ(η_{ij})` is the σ-image of the irreducible (linear) character
`η_{ij} = (omegaProdChar (w1CharEquiv i) (χ₂ j)).comp e` of `tic.W`; `σ` is an isometry on
irreducibles (`sigma_inner_irreducibleCharacter`), and the index map `(i, j) ↦ η_{ij}` is **jointly
injective** (`linearIrreducibleCharacter`/`e`-precompose/`omegaProdChar_inj`/`w1CharEquiv`/`χ₂` all
injective), so the Gram matrix is the identity.  This is the `orthonormal` field of the column
`OrthonormalCharacterImageFamily` (issue 1009): it makes the `2w₁` signed σ-images
`{δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` orthonormal (same-column rows `i ≠ i'` and cross-column `j ≠ j'`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i i' : Fin hyp.w1) (j j' : Fin hyp.w2) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j)
        (hyp.alignedOmegaSigmaGrid hG hodd i' j')
      = (if i = i' ∧ j = j' then 1 else 0) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the context of `alignedOmegaSigmaGrid` / `exists_alignedOmegaSigmaGrid_chiFam_family`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the linear (irreducible) source character `η_{ij}` of `tic.W`
  let η : Fin hyp.w1 → Fin hyp.w2 → IrreducibleCharacter ↥tic.W := fun i j =>
    linearIrreducibleCharacter
      ((h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i))
        (χ₂ j)).comp e.toMonoidHom)
  -- `alignedOmegaSigmaGrid i j = σ(η_{ij})` (mirrors `exists_alignedOmegaSigmaGrid_chiFam_family`).
  have step1 : ∀ a b, hyp.alignedOmegaSigmaGrid hG hodd a b
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ) := by
    intro a b
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ)
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- `(i, j) ↦ η_{ij}` is jointly injective.
  have hηinj : ∀ a b a' b', η a b = η a' b' → a = a' ∧ b = b' := by
    intro a b a' b' he
    have h2 := linearIrreducibleCharacter_injective he
    have h3 := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp h2
    have h4 := h.sdiffTICyclicHypothesis.omegaProdChar_inj h3
    refine ⟨(finCongr hcardW1.symm).injective (h.w1CharEquiv.injective h4.1), ?_⟩
    exact (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective h4.2)
  -- compute the Gram entry through the σ-isometry.
  rw [step1, step1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_inner_irreducibleCharacter,
    irreducibleCharacter_inner_eq_ite]
  by_cases hij : i = i' ∧ j = j'
  · rw [if_pos hij, if_pos (by rw [hij.1, hij.2])]
  · rw [if_neg hij, if_neg fun he => hij (hηinj i j i' j' he)]

open scoped FiniteInduce in
/-- **§10 σ-grid product structure** (Peterfalvi (10.6) column-structure linchpin): the `G`-level
σ-images factor through a *product* index, `ω_{ij}^σ = χ_{(ρ i, κ j)}`, for an injective `W₁`-row
family `ρ` and an injective `W₂`-column family `κ`.  Crucially the `W₂`-index `κ j` depends only on
the column `j` (not on the row `i`), and the `W₁`-indices `ρ i` exhaust `Ŵ₁` as `i` ranges — this is
what makes `μ_j^{τ₁}`'s σ-coefficient grid *two-column* supported (columns `κ j`, `κ j'`) and lets the
(5.8) full-column endgame translate `∑_p χ_{(p, κ j)} = ∑_i ω_{ij}^σ`.

`ω_{ij}^σ = σ(ω(ξ_{ij})) = χ_{omegaProdEquiv.symm ξ_{ij}}` (`sigma_omega`) for the transported product
character `ξ_{ij} = ω^{sdiff}_{χ₁ i, χ₂ j} ∘ e`.  By `omegaProdEquiv_symm_eq` the index pair is
`(ξ_{ij}|_{W₁}, ξ_{ij}|_{W₂})`, and because `e` respects the `W₁/W₂` decomposition
(`typePData_WEquiv_mem_W1/W2`: on the `W₁`-block the `ω_{0j}` factor `χ₂ ∘ wSnd ∘ e` is trivial, and
on the `W₂`-block the `ω_{i0}` factor `χ₁ ∘ wFst ∘ e` is trivial) these restrictions are the
single-factor characters `ρ i = χ₁ i ∘ wFst ∘ e`, `κ j = χ₂ j ∘ wSnd ∘ e`.  Injectivity of `ρ`/`κ`
follows from the joint orthonormality `alignedOmegaSigmaGrid_inner`. -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_chiFam_product [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ (ρ : Fin hyp.w1 →
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ))
      (κ : Fin hyp.w2 →
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)),
      Function.Injective ρ ∧ Function.Injective κ ∧
        ∀ i j, hyp.alignedOmegaSigmaGrid hG hodd i j
          = (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
              (hyp.canonicalFullDadeApp hG hodd) (ρ i, κ j) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero hyp.w1 := ⟨by have := h.one_lt_card_W1; rw [hcardW1] at this; omega⟩
  haveI : NeZero hyp.w2 := ⟨by rw [← hcardW2sub]; exact Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let χ₁ : Fin hyp.w1 → (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun i => h.w1CharEquiv (finCongr hcardW1.symm i)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥h.sdiffTICyclicHypothesis.W := typePData_WEquiv hyp.typeP
  let app := hyp.canonicalFullDadeApp hG hodd
  -- the row/column families.
  let ρ : Fin hyp.w1 → ((tic.W1.subgroupOf tic.W) →* ℂˣ) :=
    fun i => (((χ₁ i).comp h.sdiffTICyclicHypothesis.wFst).comp e.toMonoidHom).comp
      (tic.W1.subgroupOf tic.W).subtype
  let κ : Fin hyp.w2 → ((tic.W2.subgroupOf tic.W) →* ℂˣ) :=
    fun j => (((χ₂ j).comp h.sdiffTICyclicHypothesis.wSnd).comp e.toMonoidHom).comp
      (tic.W2.subgroupOf tic.W).subtype
  -- the value identity `ω_{ij}^σ = χ_{(ρ i, κ j)}`.
  have hval : ∀ i j, hyp.alignedOmegaSigmaGrid hG hodd i j
      = tic.chiFam rfl app (ρ i, κ j) := by
    intro i j
    -- `ω_{ij}^σ = σ(ω(ξ_{ij}))`
    have hAOS : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ)
        = tic.sigma rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ)
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
    -- `ξ_{ij}|_{W₁} = ρ i`, `ξ_{ij}|_{W₂} = κ j` (the cross factor is trivial on each block).
    have hc1 : ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom).comp
          (tic.W1.subgroupOf tic.W).subtype = ρ i := by
      apply MonoidHom.ext
      intro x
      have hm : e.toMonoidHom ((tic.W1.subgroupOf tic.W).subtype x) ∈
          h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
        typePData_WEquiv_mem_W1 hyp.typeP x.2
      have hz := h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hm
      simp only [ρ, MonoidHom.comp_apply,
        OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply]
      rw [hz, map_one]; exact mul_one _
    have hc2 : ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom).comp
          (tic.W2.subgroupOf tic.W).subtype = κ j := by
      apply MonoidHom.ext
      intro x
      have hm : e.toMonoidHom ((tic.W2.subgroupOf tic.W).subtype x) ∈
          h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
        typePData_WEquiv_mem_W2 hyp.typeP x.2
      have hz := h.sdiffTICyclicHypothesis.wFst_eq_one_of_mem_W2 hm
      simp only [κ, MonoidHom.comp_apply,
        OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply]
      rw [hz, map_one]; exact one_mul _
    rw [hAOS, tic.sigma_omega rfl app
        ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom),
      tic.omegaProdEquiv_symm_eq
        ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom),
      hc1, hc2]
  refine ⟨ρ, κ, ?_, ?_, hval⟩
  · -- `ρ` injective (joint orthonormality at column `0`)
    intro i i' hii'
    by_contra hne
    have h1 : hyp.alignedOmegaSigmaGrid hG hodd i 0 = hyp.alignedOmegaSigmaGrid hG hodd i' 0 := by
      rw [hval i 0, hval i' 0, hii']
    have h2 := hyp.alignedOmegaSigmaGrid_inner hG hodd i i' 0 0
    rw [if_neg (fun hh => hne hh.1), h1, hyp.alignedOmegaSigmaGrid_inner hG hodd i' i' 0 0,
      if_pos ⟨rfl, rfl⟩] at h2
    exact one_ne_zero h2
  · -- `κ` injective (joint orthonormality at row `0`)
    intro j j' hjj'
    by_contra hne
    have h1 : hyp.alignedOmegaSigmaGrid hG hodd 0 j = hyp.alignedOmegaSigmaGrid hG hodd 0 j' := by
      rw [hval 0 j, hval 0 j', hjj']
    have h2 := hyp.alignedOmegaSigmaGrid_inner hG hodd 0 0 j j'
    rw [if_neg (fun hh => hne hh.2), h1, hyp.alignedOmegaSigmaGrid_inner hG hodd 0 0 j' j',
      if_pos ⟨rfl, rfl⟩] at h2
    exact one_ne_zero h2

open scoped FiniteInduce in
/-- **§10 σ-grid full-column collapse** (the output translation of the (5.8) σ-endgame): there is an
injective `W₂`-column family `κ` with `∑_p χ_{(p, κ j)} = ∑_i ω_{ij}^σ` for every column `j`.  This is
what turns the σ-endgame conclusion `μ_j^{τ₁} = δ·∑_p χ_{(p, κ j)}` into the (10.6)(a) summed isometry
`μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.

From the product structure (`exists_alignedOmegaSigmaGrid_chiFam_product`, `ω_{ij}^σ = χ_{(ρ i, κ j)}`),
the row family `ρ : Fin w₁ → Ŵ₁` is injective and `|Fin w₁| = |Ŵ₁|` (`card_charGroup_subgroupOf`,
`tic.W₁` is `W₁`), hence bijective; reindexing the `p`-sum along `ρ` collapses
`∑_p χ_{(p, κ j)} = ∑_i χ_{(ρ i, κ j)} = ∑_i ω_{ij}^σ`. -/
theorem Hypothesis.exists_kappa_sum_chiFam_column_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ κ : Fin hyp.w2 →
        (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
      Function.Injective κ ∧
        ∀ j, ∑ p, (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
            (hyp.canonicalFullDadeApp hG hodd) (p, κ j)
          = ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  let app := hyp.canonicalFullDadeApp hG hodd
  obtain ⟨ρ, κ, hρinj, hκinj, hval⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  -- `ρ : Fin w₁ → Ŵ₁` is bijective (injective + matching cardinality `|Ŵ₁| = |W₁| = w₁`).
  have hcardW1 : Nat.card ((tic.W1.subgroupOf tic.W) →* ℂˣ) = hyp.w1 := by
    rw [tic.card_charGroup_subgroupOf tic.W1_le_W]; rfl
  have hcard : Fintype.card (Fin hyp.w1) = Fintype.card ((tic.W1.subgroupOf tic.W) →* ℂˣ) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardW1]
  have hρbij : Function.Bijective ρ :=
    (Fintype.bijective_iff_injective_and_card ρ).mpr ⟨hρinj, hcard⟩
  refine ⟨κ, hκinj, fun j => ?_⟩
  calc ∑ p, tic.chiFam rfl app (p, κ j)
      = ∑ i, tic.chiFam rfl app (ρ i, κ j) :=
        (Fintype.sum_bijective ρ hρbij _ _ (fun _ => rfl)).symm
    _ = ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j :=
        Finset.sum_congr rfl (fun i _ => (hval i j).symm)

open scoped FiniteInduce in
/-- **§10 σ-grid lands in `ℤ[Irr G]`**: each `alignedOmegaSigmaGrid i j = chiFam(P_{ij}) ∈ ZIrr G`
(`exists_alignedOmegaSigmaGrid_chiFam_family` + `chiFam_spec`).  The `mem_ZIrr` field of the column
`OrthonormalCharacterImageFamily`. -/
theorem Hypothesis.alignedOmegaSigmaGrid_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.alignedOmegaSigmaGrid hG hodd i j ∈ ZIrr G := by
  obtain ⟨P, _, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hP j]
  exact ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)).2.1 _

open scoped FiniteInduce in
/-- **§10 within-column degree constancy** (Peterfalvi (4.5.a), the `i`-independence half of
(10.3)): within a fixed `W₂`-column `j`, the degree `μ_{ij}(1)` of the materialized `μ`-grid does
not depend on the row `i`.  This is the §6 fact `columnFamily_difference_apply_one` (the
within-column difference `μ_{ij} − μ_{0j}` vanishes at `1`) read through the `muGrid` definition. -/
theorem Hypothesis.muGrid_apply_one_within_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd 0 j 1 := by
  haveI := hyp.finiteG
  classical
  have key : ∀ (h : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h.W1)]
      (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ₂).mu k : ClassFunction (↥M) ℂ) 1
        = ((h.columnFamily χ₂).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h _ χ₂ k
    have hd := h.columnFamily_difference_apply_one χ₂ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]

open OddOrder.Peterfalvi.S06 in
/-- The `k`-th power of the row-`0` product source `ω(1, χ₂)` is the row-`0` source of the
`k`-th power dual: `(omegaProdChar 1 χ₂)^k = omegaProdChar 1 (χ₂^k)` (on the §6 `toTICyclicHypothesis`).
Row `0` is the trivial `W₁`-dual, fixed by powering, so only the `W₂`-factor `χ₂` is raised. -/
theorem omegaProdChar_one_pow {L : Type*} [Group L] [Fintype L]
    (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : ℕ) :
    (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ^ k
      = h.toTICyclicHypothesis.omegaProdChar 1 (χ₂ ^ k) := by
  rw [h.toTICyclicHypothesis.omegaProdChar_one_left,
    h.toTICyclicHypothesis.omegaProdChar_one_left]
  refine MonoidHom.ext fun w => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ₂ k _).symm

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy** (Peterfalvi (10.3) via (3.9.b) + (4.3.b)): the degree
`μ_{0j}(1)` of the column-`0` certain-type character is unchanged when the `W₂`-dual `χ₂` indexing
the column is replaced by a Galois power `χ₂ ^ k` (with `k` coprime to the order of the row-`0`
source character).  This is the cross-column half of (10.3): by (3.9.b) there is a ring
automorphism `u` of `ℂ` with `σ(ω_{0,χ₂^k}) = (σ(ω_{0,χ₂}))^u`, hence by (4.3.b)
`δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`; evaluating at `1` and using that `u` fixes the
integer `δ·μ(1)` (degrees are positive, signs `±1`) forces `μ_{0,χ₂^k}(1) = μ_{0,χ₂}(1)`. -/
theorem columnFamily_mu_zero_apply_one_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    ((h.columnFamily (χ₂ ^ k)).mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  classical
  -- (3.9.b): the Galois automorphism `u` relating the row-`0` source to its `k`-th power
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  -- the `k`-th power of the row-`0` source is the row-`0` source of column `χ₂ ^ k`
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  -- (4.3.b) at row `0`, stated in `omega`/source form (`chiColumn ψ 0 = ω(omegaProdChar 1 ψ)`)
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  -- `hu : δ' • μ'_0 = (δ • μ_0)^u`; evaluate at `1`
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  -- `h1 : δ' * d' = u (δ * d)`; `u` fixes the integer `δ * d`
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- magnitudes: signs are `±1`, degrees positive, so `d' = d`
  rw [hd, hd']
  have hdd : d' = d := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simpa using habs
  rw [hdd]

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column *sign* constancy** (Peterfalvi (10.3), the `δ`-part of the (3.9.b) argument):
the sign `δ_{χ₂}` of the column-`0` certain-type difference family is unchanged when the `W₂`-dual
`χ₂` is replaced by a Galois power `χ₂ ^ k` (`k` coprime to the order of the row-`0` source).

This is the sign companion of `columnFamily_mu_zero_apply_one_pow`: the same (3.9.b)+(4.3.b) Galois
identity `δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`, evaluated at `1` and read in `ℤ`, gives
`δ_{χ₂^k}·d' = δ_{χ₂}·d`; since the degrees agree (`d' = d > 0`) the signs agree.  Peterfalvi's
(10.3): "It follows that `δ_j = δ_1` and `μ_{0j}(1) = μ_{01}(1)`." -/
theorem columnFamily_mu_zero_sign_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    (h.columnFamily (χ₂ ^ k)).sign = (h.columnFamily χ₂).sign := by
  classical
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- the degrees agree (same Galois argument); cancel the positive degree to equate the signs
  have hdd : (d' : ℤ) = (d : ℤ) := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simp_all
  rw [hdd] at hZ
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  exact mul_right_cancel₀ hdne hZ

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column sign constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order, every nontrivial column shares the common sign `δ`.  Mirrors
`columnFamily_mu_zero_apply_one_eq_of_ne_one` (any two nontrivial duals are coprime powers of each
other) but for the sign via `columnFamily_mu_zero_sign_pow`. -/
theorem columnFamily_mu_zero_sign_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    (h.columnFamily χ₂').sign = (h.columnFamily χ₂).sign := by
  classical
  haveI : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_sign_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order (`w₂` prime), every nontrivial column shares the common degree.  Any two
nontrivial duals `χ₂`, `χ₂'` are powers of each other (the dual group is cyclic of prime order, so
a nontrivial element generates), with the power coprime to `w₂`;
`columnFamily_mu_zero_apply_one_pow` then equates the column-`0` degrees.  This is the full
cross-column (j-independence) half of (10.3):
all the columns `0 < j < w₂` have degree `d = μ_{0j}(1)` independent of `j`. -/
theorem columnFamily_mu_zero_apply_one_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  classical
  -- a prime cardinality forces the dual group to be finite
  haveI : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  -- `orderOf χ₂ = |D|` (a nontrivial element of a prime-order group generates it)
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  -- `χ₂'` is a power of `χ₂`
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  -- `k` is coprime to `orderOf χ₂ = |D| = p`
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  -- transfer coprimality to the order of the row-`0` source character
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_apply_one_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column degree constancy** (Peterfalvi (10.3), the `j`-independence half at the
materialized `μ`-grid level): the degree `μ_{0j}(1)` of the row-`0` materialized `μ`-grid is
independent of the *nontrivial* column `0 < j < w₂`.

This wires the §6 prime-order corollary `columnFamily_mu_zero_apply_one_eq_of_ne_one` through the
`muGrid` materialization.  The required prime cardinality of the `W₂`-dual group is supplied by the
Pontryagin count `|Ŵ₂| = |W₂| = w₂` (`card_charGroup_W2`) together with the hypothesis `hw2` that
`w₂` is prime (Theorem (8.8), supplied at producer-construction time to avoid the
`no_typeV_maximal` → parameter-producer dependency cycle); the two columns are nontrivial duals
because the `Fin w₂`-reindex `finCardEquivCharacterGroup` is injective and sends only `0` to the
trivial character.  Together with `muGrid_apply_one_within_column` this gives the full (10.3) degree
independence `μ_{ij}(1) = d` for all `0 ≤ i < w₁`, `0 < j < w₂`. -/
theorem Hypothesis.muGrid_apply_one_cross_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd 0 j 1 = hyp.muGrid hG hodd 0 j' 1 := by
  haveI := hyp.finiteG
  classical
  -- Reconstruct the §6 host and the instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The `W₂`-dual group has prime cardinality `w₂` (Pontryagin count + (8.8)).
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  -- A nontrivial column index gives a nontrivial `W₂`-dual.
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  -- The within-column degree-constancy key (Peterfalvi (4.5.a)), as in
  -- `muGrid_apply_one_within_column`, used here only to strip the row index to `0`.
  have key : ∀ (h' : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h'.W1)]
      (χ : (h'.W2.subgroupOf (h'.W1 ⊔ h'.W2)) →* ℂˣ) (k : Fin (Nat.card h'.W1)),
      ((h'.columnFamily χ).mu k : ClassFunction (↥M) ℂ) 1
        = ((h'.columnFamily χ).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h' _ χ k
    have hd := h'.columnFamily_difference_apply_one χ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]
  exact (columnFamily_mu_zero_apply_one_eq_of_ne_one h hp (hcol_ne j hj) (hcol_ne j' hj')).symm

/-- **§10 degree independence** (Peterfalvi (10.3), full statement at the materialized `μ`-grid
level): for nontrivial columns (`0 < j, j' < w₂`) the common degree `μ_{ij}(1) = d` is independent
of *both* the row `i` and the (nontrivial) column `j`.  This is the genuine (10.3) degree constancy,
combining the within-column constancy `muGrid_apply_one_within_column` (the `i`-independence (4.5.a))
with the cross-column constancy `muGrid_apply_one_cross_column` (the `j`-independence via Theorem
(8.8) `w₂` prime + Pontryagin).  It is exactly what populates `CharacterParameters.degree_independent`
once the common value `d` is named (at producer-construction time, where `hw2` is available). -/
theorem Hypothesis.muGrid_apply_one_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd i' j' 1 := by
  rw [hyp.muGrid_apply_one_within_column hG hodd i j,
    hyp.muGrid_apply_one_cross_column hG hodd hw2 hj hj',
    ← hyp.muGrid_apply_one_within_column hG hodd i' j']

open scoped FiniteInduce in
/-- **§10 column sign** (Peterfalvi (10.3) `δ_j`): the sign `δ_j ∈ {±1}` of the `j`-th materialized
column, read off from the §6 `columnFamily` of the §10→§6 bridge (the same reconstruction as
`Hypothesis.muGrid`).  This is the genuine source for `CharacterParameters.delta`. -/
noncomputable def Hypothesis.muColumnSign [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) : ℤ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  exact (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column sign constancy** (Peterfalvi (10.3), the `δ_j`-independence): the column sign
`δ_j` is independent of the nontrivial column `0 < j < w₂`.  Wires the §6 prime-order sign corollary
`columnFamily_mu_zero_sign_eq_of_ne_one` through the `muColumnSign` materialization (same Pontryagin
prime count + nontrivial-dual argument as `muGrid_apply_one_cross_column`). -/
theorem Hypothesis.muColumnSign_eq_of_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muColumnSign hG hodd j = hyp.muColumnSign hG hodd j' := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  unfold Hypothesis.muColumnSign
  exact columnFamily_mu_zero_sign_eq_of_ne_one h hp (hcol_ne j' hj') (hcol_ne j hj)

open scoped FiniteInduce in
/-- **§10 column-`0` sign** (Peterfalvi (10.3) / (4.4) `δ_0 = 1`): the sign `δ_0` of the trivial
column is `1`.  The column-`0` dual is the trivial character (`finCardEquivCharacterGroup_zero`), and
the trivial column has sign `1` (`certainType_zero_column_anchor.1`, the `μ_{00} = 1_L` anchor).
This is the `δ_0 = 1` normalisation used by the (10.5) Dade-image identity (the column-`0` term in
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is reconciled against `ω_{i0}^σ` with unit sign). -/
theorem Hypothesis.muColumnSign_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.muColumnSign hG hodd 0 = 1 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have esign : hyp.muColumnSign hG hodd 0
      = (h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [esign, hdual0]
  exact h.certainType_zero_column_anchor.1

open scoped FiniteInduce in
/-- **Peterfalvi (10.3), the sign `δ_j ∈ {±1}`**: every column sign `δ_j = muColumnSign j` is a unit
(`±1`).  Immediate from the §6 certain-type `columnFamily`'s `.sign_eq` (the Pontryagin sign of a
linear character is `±1`).  Combined with the `(10.3)` `δ_j`-independence and `δ_j = δ` (the
`muColumnSign j = δ` returned by `exists_charParamArith`), this gives the `δ = ±1` (`hδpm`) input to
the (10.6) Dade-value lemmas `tau1_values_and_norm_bound` / `zeta_tau1_norm_ge_one`. -/
theorem Hypothesis.muColumnSign_eq_one_or_neg_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    hyp.muColumnSign hG hodd j = 1 ∨ hyp.muColumnSign hG hodd j = -1 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have esign : hyp.muColumnSign hG hodd j
      = (h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm j))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [esign]
  exact (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign_eq

open scoped FiniteInduce in
/-- **§10 μ-grid normalization** (Peterfalvi (4.1)/(4.3.b)): each materialized certain-type
character `μ_{ij}` is an irreducible character of `M`, hence has norm one, `(μ_{ij}, μ_{ij}) = 1`.
Read off the §6 `columnFamily` (whose `mu` are irreducible) through the `muGrid` reconstruction. -/
theorem Hypothesis.muGrid_inner_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i j) = 1 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, OddOrder.RepresentationTheory.irreducibleCharacter_inner, if_pos rfl]

open scoped FiniteInduce in
/-- **§10 μ-grid cross-column orthogonality** (Peterfalvi (4.3.b)): certain-type characters from
*different* `W₂`-columns are orthogonal, `(μ_{ij}, μ_{i'j'}) = 0` for `j ≠ j'` (any rows `i, i'`).
The §6 `columnFamily_cross_products_zero` (via (4.1)), read through `muGrid`, with a case split on
which rows are `0`.  In particular `(μ_{ij}, μ_{i0}) = 0` for `0 < j`, the cross term in the
norm `‖α_{ij}‖² = 2 + n²` of the (10.5) Dade-image argument. -/
theorem Hypothesis.muGrid_inner_cross_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j') = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The two `W₂`-duals differ (different columns).
  have hχne : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j)
      ≠ finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j') :=
    fun heq => hjj' ((finCongr hcardW2sub.symm).injective
      ((finCardEquivCharacterGroup _).injective heq))
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j'
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j'))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj']
  have hz : (⟨1, h.one_lt_card_W1⟩ : Fin (Nat.card h.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rcases eq_or_ne (finCongr hcardW1.symm i) 0 with hi | hi <;>
    rcases eq_or_ne (finCongr hcardW1.symm i') 0 with hi' | hi'
  · rw [hi, hi']; exact (h.columnFamily_cross_products_zero hχne hz hz).2.2.2
  · rw [hi]; exact (h.columnFamily_cross_products_zero hχne hz hi').2.2.1
  · rw [hi']; exact (h.columnFamily_cross_products_zero hχne hi hz).2.1
  · exact (h.columnFamily_cross_products_zero hχne hi hi').1

open scoped FiniteInduce in
/-- **§10 μ-grid within-column orthogonality** (Peterfalvi (4.3.b)): distinct rows of the same
`W₂`-column give orthogonal certain-type characters, `(μ_{ij}, μ_{i'j}) = 0` for `i ≠ i'`.  The
§6 `columnFamily` `mu` are distinct irreducibles (`irreducibleCharacter_inner` + the family's
`injective` field), read through `muGrid`.  With `muGrid_inner_self` this completes the
orthonormality of the full `μ`-grid. -/
theorem Hypothesis.muGrid_inner_within_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i i' : Fin hyp.w1} (j : Fin hyp.w2) (hii' : i ≠ i') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j) = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hrowne : (finCongr hcardW1.symm i) ≠ (finCongr hcardW1.symm i') :=
    fun heq => hii' ((finCongr hcardW1.symm).injective heq)
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj', OddOrder.RepresentationTheory.irreducibleCharacter_inner,
    if_neg (fun heq => hrowne ((h.columnFamily _).injective heq))]

open scoped FiniteInduce in
/-- **§10 μ-grid entries are irreducible** (Peterfalvi (4.3.b)): each `μ_{ij}` is an irreducible
character of `M`, being the §6 certain-type character `(columnFamily χ₂).mu i` (an
`IrreducibleCharacter`).  This is the `μ_{ij} ∈ ℤ[Irr M]` input that makes `α_{ij}^τ` a virtual
character of `G`, hence the inner products of the (10.5) `a = 0` argument integers. -/
theorem Hypothesis.muGrid_isIrreducible [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  rw [show hyp.muGrid hG hodd i j
    = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
        (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl]
  exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _

open scoped FiniteInduce in
/-- **§10 column sum is induced from `M'`, hence vanishes off `M'`** (Peterfalvi (10.5)/(4.5.a)):
the `W₂`-column sum `μ_k = ∑_{0≤i<w₁} μ_{ik}` equals the induced character `Ind_{M'}^M (Res_{M'} μ_{0k})`
(`induce_restrict_certainType_eq`), so it vanishes on every `x ∉ M' = [M,M]`.

This is the structural fact making `μ_k − dζ̄` `A_0`-supported in the (10.5) `a = 0` argument (both
`μ_k` and `ζ̄` vanish off `M'`, and the degrees cancel) — so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`), with no Dade–coherence adjunction needed. -/
theorem Hypothesis.muGrid_column_sum_vanishes_off_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {x : ↥M} (hx : x ∉ (derivedInG M).subgroupOf M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) x = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The column sum is the induced character `Ind_{M'}^M (Res_{M'} μ_{0k})` (`induce_restrict`).
  have hsum : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      = ClassFunction.induce h.K
          (ClassFunction.restrict h.K
            ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
              : ClassFunction ↥M ℂ)) := by
    rw [h.induce_restrict_certainType_eq, ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
        : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  rw [hsum]
  -- `K = M' = [M,M]` is normal, so the induced character vanishes off it.
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  haveI : h.K.Normal := hKnormal
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hx

open scoped FiniteInduce in
/-- **§10 column sum lies in the family `S`** (Peterfalvi (10.5)/(4.5.a)): for `0 < k < w₂`, the
`W₂`-column sum `μ_k = ∑_{i} μ_{ik}` is the induced character `Ind_{M'}^M θ` of a *non-trivial*
irreducible `θ` of `M'` (`exists_irreducible_restrict_certainType`), hence lies in
`S = inducedFamily M`.  Non-triviality follows from the degree: `θ(1) = (Res_{M'} μ_{0k})(1) =
μ_{0k}(1) ≠ 1` (the caller supplies `μ_{0k}(1) = d > 1` from (10.3)).

This is the `μ_k ∈ ℤ[S]` input that the coherent extension `τ₁` consumes: it lets `μ_k^{τ₁}`
participate in the isometry (`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁`) and the `(μ_k − dζ̄)^τ = μ_k^{τ₁} −
dζ̄^{τ₁}` split of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_mem_inducedFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) ∈ inducedFamily M := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨θ, hθeq, hind⟩ :=
    h.exists_irreducible_restrict_certainType (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))
  -- row-0 entry equals the certain-type character `μ_{0k}` (`finCongr` fixes `0`).
  have hrow0 : hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ) := by
    have hfc : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = (0 : Fin (Nat.card h.W1)) := by simp
    rw [show hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl, hfc]
  -- `θ ≠ 1`: else `μ_{0k}(1) = θ(1) = 1`, contradicting `hdk1`.
  have hθne : θ ≠ trivialIrreducibleCharacter ↥h.K := by
    intro htriv
    apply hdk1
    rw [hrow0]
    have h2 : (ClassFunction.restrict h.K
        ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ)) (1 : ↥h.K) = (θ : ClassFunction ↥h.K ℂ) (1 : ↥h.K) := by
      rw [hθeq]
    rw [ClassFunction.restrict_apply] at h2
    rw [htriv] at h2
    simpa using h2
  -- The column sum is `Ind_{M'}^M θ`, so it lies in `S`.
  refine ⟨θ, hθne, ?_⟩
  show (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
    = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)
  rw [hind, ← Equiv.sum_comp (finCongr hcardW1.symm)
    (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
      : ClassFunction ↥M ℂ))]
  exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)

open scoped FiniteInduce in
/-- **§10 column-sum norm** (Peterfalvi (10.5)/(10.6), `‖μ_k‖² = w₁`): the `W₂`-column sum
`μ_k = ∑_{0≤i<w₁} μ_{ik}` has squared norm `w₁`, since its `w₁` summands are orthonormal
(`muGrid_inner_self` on the diagonal, `muGrid_inner_within_column` off it).  This is the
`‖μ_k^{τ₁}‖² = w₁` factor in the Cauchy–Schwarz bound of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (j : Fin hyp.w2) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) = (hyp.w1 : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- per-pair inner products: `1` on the diagonal, `0` off it.
  have hpair : ∀ i i' : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (hyp.muGrid hG hodd i' j) = (if i' = i then 1 else 0) := by
    intro i i'
    by_cases h : i' = i
    · subst h; rw [if_pos rfl]; exact hyp.muGrid_inner_self hG hodd i' j
    · rw [if_neg h]; exact hyp.muGrid_inner_within_column hG hodd j (Ne.symm h)
  have hrow : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) = 1 := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl (fun i' _ => hpair i i'), Finset.sum_ite_eq' Finset.univ i]
    simp
  rw [OddOrder.RepresentationTheory.inner_sum_left,
    Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

open scoped FiniteInduce in
/-- **§10 μ-grid ⊥ a degree-distinct irreducible** (Peterfalvi (10.5), `(μ_{ij}, ζ) = 0`): the
certain-type character `μ_{ij}` is orthogonal to any irreducible character `χ` of a *different*
degree.  Both are irreducible, so `(μ_{ij}, χ) ∈ {0, 1}` and equals `1` only if `μ_{ij} = χ`; a
degree mismatch `μ_{ij}(1) ≠ χ(1)` rules that out.

This is the orthogonality `(μ_{ij}, ζ) = 0` (and `(μ_{ij}, ζ̄) = 0`) to the degree-`w₁` member
`ζ ∈ S` in the norm `‖α_{ij}‖² = 2 + n²` of the (10.5) `a = 0` argument: the caller supplies the
degree mismatch (`μ_{i0}(1) = 1 ≠ w₁`, and `μ_{ij}(1) = d ≠ w₁` since `n·w₁ = d − δ`, `d > 1`,
`w₁ > 1`).  It needs no Clifford theory — only orthonormality of irreducibles. -/
theorem Hypothesis.muGrid_inner_eq_zero_of_apply_one_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {χ : ClassFunction ↥M ℂ} (hχirr : IsIrreducibleCharacter χ)
    (hne : hyp.muGrid hG hodd i j 1 ≠ χ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) χ = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have hμirr : IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
    rw [emj]; exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _
  rw [OddOrder.RepresentationTheory.irr_cf_inner hμirr hχirr,
    if_neg (fun heq => hne (by rw [heq]))]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}‖² = 2 + n²`**: the squared norm of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  The triple `{μ_{ij}, μ_{i0}, ζ}` is orthonormal — `μ_{ij}` and
`μ_{i0}` are orthonormal certain-type characters (`muGrid_inner_self` / `muGrid_inner_cross_column`,
`j ≠ 0`), and both are orthogonal to the degree-distinct irreducible `ζ`
(`muGrid_inner_eq_zero_of_apply_one_ne`, from the degree mismatches `hdζ`/`h0ζ`) — so
`‖α‖² = 1 + δ² + n² = 2 + n²` (`δ² = 1`).  The reversed inner products use `inner_conj_symm`.

This is the `‖α_{ij}^τ‖²` input to the Cauchy–Schwarz bound of the (10.5) `a = 0` argument (the
Dade isometry `τ` preserves the norm).  The caller supplies the degree mismatches
`μ_{i0}(1) = 1 ≠ w₁` and `μ_{ij}(1) = d ≠ w₁` (from `n·w₁ = d − δ`, `d > 1`, `w₁ > 1`). -/
theorem Hypothesis.muGridAlpha_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = 2 + (n : ℂ) ^ 2 := by
  haveI := hyp.finiteG
  classical
  have hA := hyp.muGrid_inner_self hG hodd i j
  have hB := hyp.muGrid_inner_self hG hodd i 0
  have hZ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hP := hyp.muGrid_inner_cross_column hG hodd i i hj0
  have hP' := hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hj0)
  have hQ := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hR := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hQ' : ClassFunction.inner ζ (hyp.muGrid hG hodd i j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i j) ζ, hQ, star_zero]
  have hR' : ClassFunction.inner ζ (hyp.muGrid hG hodd i 0) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i 0) ζ, hR, star_zero]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hA, hB, hZ, hP, hP', hQ, hQ', hR, hR', star_intCast, star_natCast,
    mul_zero, zero_mul, sub_zero, zero_sub, mul_one, mul_neg, neg_neg, neg_zero]
  rcases hδpm with h | h <;> subst h <;> push_cast <;> ring

open scoped FiniteInduce in
/-- **§10 `W₁`-vanishing of the column difference** (Peterfalvi (10.5), first step, via (4.3.c) +
(4.4)): on `W₁^#`, the materialized character `μ_{ij}` equals `δ_j` times the column-`0` character
`μ_{i0}`.  Indeed `x ∈ W₁^# ⊆ V = W − W₂`, so (4.3.c) gives `μ_{ij}(x) = δ_j·ω_{ij}(x)` and
`μ_{i0}(x) = δ_0·ω_{i0}(x) = ω_{i0}(x)` (`δ_0 = 1` by (4.4)); on `W₁` the linear characters `ω_{ij}`
and `ω_{i0}` agree (the `W₂`-dual is trivial on `W₁`, `wSnd = 1`), so `μ_{ij}(x) = δ_j·μ_{i0}(x)`.
This is the `μ`-grid form of the (10.5) claim that `α_{ij}` vanishes on `W₁`. -/
theorem Hypothesis.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {x : ↥M} (hxW1 : (x : G) ∈ hyp.typeP.W1) (hx1 : x ≠ 1) :
    hyp.muGrid hG hodd i j x
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.muGrid hG hodd i 0 x := by
  haveI := hyp.finiteG
  classical
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`/`muColumnSign`
  -- (instances synthesized, *not* provided explicitly, to match the def's `unfold; rfl`).
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- `x` as an element of `h.W1` and of `sdiff.V = W − W₂`.
  have hxhW1 : x ∈ h.W1 := Subgroup.mem_subgroupOf.mpr hxW1
  have hxV : x ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨(le_sup_left : h.W1 ≤ _) hxhW1, fun hxW2 => hx1 ?_⟩
    exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hxhW1, hxW2⟩))
  -- The generic `W₁`-collapse: `(columnFamily χ).mu k x = δ_χ · (columnFamily 1).mu k x`.
  have keyW1 : ∀ (χ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ).mu k : ClassFunction ↥M ℂ) x
        = ((h.columnFamily χ).sign : ℂ) * ((h.columnFamily 1).mu k : ClassFunction ↥M ℂ) x := by
    intro χ k
    have hwsub : (⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hxhW1
    have hwsnd : h.sdiffTICyclicHypothesis.wSnd
        ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ = 1 :=
      h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hwsub
    -- chiColumn value formula (inline, valid for the bare `Hypothesis`).
    have hchiform : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (h.chiColumn χ' k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
          = ((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ)
            * (χ' (h.sdiffTICyclicHypothesis.wSnd
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ) := by
      intro χ'
      rw [OddOrder.Peterfalvi.S06.Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
      change (((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst _)
          * χ' (h.sdiffTICyclicHypothesis.wSnd _) : ℂˣ) : ℂ) = _
      rw [Units.val_mul]
    -- the `W₂`-dual factor is trivial on `W₁` (`wSnd = 1`), so the value is `χ`-independent.
    have hsnd1 : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (χ' (h.sdiffTICyclicHypothesis.wSnd ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂˣ)
          = 1 := fun χ' => by rw [hwsnd]; exact map_one χ'
    have hchieq : (h.chiColumn χ k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
        = (h.chiColumn 1 k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ := by
      rw [hchiform χ, hchiform 1, hsnd1 χ, hsnd1 1]
    rw [h.certainType_apply_eq_of_mem_V χ k hxV, h.certainType_apply_eq_of_mem_V 1 k hxV,
      h.certainType_zero_column_anchor.1, hchieq, Int.cast_one, one_mul]
  -- Evaluate `muGrid`/`muColumnSign` in `columnFamily` terms (the `unfold; rfl` idiom of the
  -- producer's `hmg`), then apply `keyW1` (column `0` is the trivial dual).
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have em0 : hyp.muGrid hG hodd i 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j
      = (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, em0, esign, hdual0]
  exact keyW1 _ _

open scoped FiniteInduce in
/-- **§10 reconciliation on `V`** (the M-side ↔ σ-side link of (10.5)): for `v ∈ V = typePV`,
`μ_{ij}(v) = δ_j · ω_{ij}^σ(v)` where `ω^σ = alignedOmegaSigmaGrid`.  Both sides reduce to the §6
column character `chiColumn χ₂ i` evaluated at `v`: the M-side by (4.3.c)
(`certainType_apply_eq_of_mem_V`, giving `μ_{ij}(v) = δ_j·chiColumn(v)`), the σ-side because
`alignedOmegaSigma` is `σ_∫` of the transported `chiColumn`, restored on `V` by
`sigmaIntegral_apply_of_mem_V`; the `W ≤ M ≤ G` isomorphism `e` carries `v` to itself, so the two
`chiColumn` arguments agree.  This is the alignment that makes the (10.5) Dade-image identity hold
(impossible with the independently-indexed `omegaSigmaGrid`). -/
theorem Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.muGrid hG hodd i j ⟨v, hvM⟩
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.alignedOmegaSigmaGrid hG hodd i j v := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j)
    with hχ₂
  have hvtic : v ∈ tic.V := hv
  have hWeq : h.W1 ⊔ h.W2 = hyp.typeP.W.subgroupOf M := typePData_sup_subgroupOf_eq hyp.typeP
  have hvW : (⟨v, hvM⟩ : ↥M) ∈ h.W1 ⊔ h.W2 := by
    rw [hWeq, Subgroup.mem_subgroupOf]; exact hv.1
  -- `⟨v, hvM⟩ ∈ sdiff.V = W − W₂` (`v ∈ typePV = W − (W₁ ∪ W₂) ⊆ W − W₂`).
  have hvsdiffV : (⟨v, hvM⟩ : ↥M) ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨hvW, ?_⟩
    intro hvW2
    exact hv.2 (Or.inr (Subgroup.mem_subgroupOf.mp hvW2))
  -- the transport `e` carries `v` to itself (same underlying `G`-element).
  have he_coe : ((e ⟨v, tic.V_subset_W hvtic⟩ : ↥(h.W1 ⊔ h.W2)) : ↥M) = ⟨v, hvM⟩ := by
    apply Subtype.ext
    show ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm
          ⟨v, tic.V_subset_W hvtic⟩) : ↥M) : G) = v
    rw [MulEquiv.subgroupCongr_apply]; rfl
  -- the two `chiColumn` arguments (from (4.3.c) and from `e`) agree.
  have harg : (⟨⟨v, hvM⟩, h.sdiffTICyclicHypothesis.V_subset_W hvsdiffV⟩
        : ↥h.sdiffTICyclicHypothesis.W)
      = e ⟨v, tic.V_subset_W hvtic⟩ := by
    apply Subtype.ext; rw [he_coe]
  -- unfold `alignedOmegaSigma` to `chiColumn (e ⟨v⟩)` on `V`.
  have eaos : hyp.alignedOmegaSigmaGrid hG hodd i j v
      = (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          (e ⟨v, tic.V_subset_W hvtic⟩) := by
    unfold Hypothesis.alignedOmegaSigmaGrid
    rw [tic.sigmaIntegral_apply_of_mem_V rfl app _ hvtic, ClassFunction.compHom_apply]
    rfl
  -- unfold `muGrid`/`muColumnSign` and apply (4.3.c); the two `chiColumn` arguments agree.
  have emj : hyp.muGrid hG hodd i j = (h.columnFamily χ₂).mu (finCongr hcardW1.symm i) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, esign, eaos,
    h.certainType_apply_eq_of_mem_V χ₂ (finCongr hcardW1.symm i) hvsdiffV, harg]

open scoped FiniteInduce in
/-- **§10 column-`0` degree** (Peterfalvi (4.4)): `μ_{i0}(1) = 1`.  The column-`0` character is
`K`-trivial (`μ_{00} = 1_L` by the (4.4) anchor), of degree `1`; by within-column degree constancy
(`muGrid_apply_one_within_column`) every `μ_{i0}` has the same degree. -/
theorem Hypothesis.muGrid_zero_column_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    hyp.muGrid hG hodd i 0 1 = 1 := by
  haveI := hyp.finiteG
  classical
  rw [hyp.muGrid_apply_one_within_column hG hodd i 0]
  -- Reconstruct the §6 host, as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have hrow0 : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 := by apply Fin.ext; simp
  have e00 : hyp.muGrid hG hodd 0 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [e00, hdual0, hrow0, h.certainType_zero_column_anchor.2,
    OddOrder.RepresentationTheory.trivialClassFunction_apply]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), support half**: the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` (for `ζ` induced from `M'`, the materialized degrees `d`, sign
`δ_j = δ`, and `n` with `n·w₁ = d − δ`) is supported on `A_0(M)`.

This is the **dade0-free** half of (10.5), following Peterfalvi's argument verbatim:
* `α_{ij}` vanishes at `1` (by `n·w₁ = d − δ` and `μ_{i0}(1) = 1`) and on `W₁^#`
  (`muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1` and `ζ` vanishing off `M'`);
* `ζ`, being induced from the normal `M'`, vanishes off `M'`, so a support point `z ∉ M'` is, by
  (2.1) (`mem_compl_conj_into_W`), `M`-conjugate to `x·y` with `x ∈ W₁^#`, `y ∈ W₂`; `y ≠ 1` (else
  `z` is conjugate into `W₁^#`, where `α` vanishes), so `x·y ∈ V` and `z ∈ V^M`;
* a support point `z ∈ M'` lies in `(M')^# ⊆ A(M)` (it centralizes itself).

Hence `Supp(α_{ij}) ⊆ A(M) ∪ V^M = A_0(M)`. -/
theorem Hypothesis.muGrid_alpha_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (_hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  -- `ζ` is induced from the normal `M'`, hence vanishes off `M'`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  -- the §6 host (for (2.1)) and the abbreviation `α`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  set α : ClassFunction ↥M ℂ :=
    hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ with hαdef
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `α(1) = 0`, hence `z ≠ 1`.
  have hα1 : α 1 = 0 := by
    rw [hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
      ClassFunction.smul_apply, hdeg, hμ0, hζ1, mul_one]
    have hnfC : (n : ℂ) * (hyp.w1 : ℂ) = (d : ℂ) - (δ : ℂ) := by exact_mod_cast hnf
    rw [hnfC]; ring
  have hz1 : z ≠ 1 := fun h0 => hz (h0 ▸ hα1)
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  by_cases hzM' : (z : G) ∈ derivedInG M
  · -- `z ∈ M'`: lands in `A(M)` (it centralizes itself).
    left
    exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
      ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  · -- `z ∉ M'`: use (2.1) to conjugate into `W`, landing in `V^M`.
    right
    have hzK : z ∉ h.K := fun hk => hzM' (Subgroup.mem_subgroupOf.mp hk)
    obtain ⟨c, x, hxW1, hx1, y, hyW2, hconj⟩ := h.mem_compl_conj_into_W hzK
    have hxG : (x : G) ∈ hyp.typeP.W1 := Subgroup.mem_subgroupOf.mp hxW1
    have hyG : (y : G) ∈ hyp.typeP.W2 := Subgroup.mem_subgroupOf.mp hyW2
    -- `α` is conjugation-invariant, so `α z = α (x·y)`.
    have hconjα : α z = α (x * y) := by
      rw [← hconj]
      have hce := α.conj_eq z c⁻¹
      rw [inv_inv] at hce
      exact hce.symm
    -- `x ∉ M'` (`W₁ ∩ M' = 1`, `M_complement`), so `ζ` also vanishes at `x`.
    have hxK : x ∉ h.K := fun hk =>
      hx1 ((Subgroup.disjoint_def.mp h.isComplement.disjoint) hk hxW1)
    -- `y ≠ 1`: otherwise `α z = α x = 0`, contradicting `z ∈ Supp(α)`.
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hz
      rw [hconjα, mul_one, hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply,
        ClassFunction.smul_apply, ClassFunction.smul_apply,
        hyp.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 hG hodd i j hxG hx1, hδj,
        hζvanish hxK]
      ring
    -- `x·y ∈ V`, so `z ∈ V^M` (the conjugator `c` lies in `M`).
    rw [OddOrder.GroupTheory.mem_conjClassSetIn]
    refine ⟨(x : G) * (y : G), ?_, (c : G), c.2, ?_⟩
    · -- `(x:G)·(y:G) ∈ typePV`
      have hxyW : (x : G) * (y : G) ∈ hyp.typeP.W := by
        rw [hyp.typeP.W_eq]; exact mul_mem (Subgroup.mem_sup_left hxG) (Subgroup.mem_sup_right hyG)
      simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
      refine ⟨hxyW, ?_, ?_⟩
      · intro hmem
        apply hy1
        have hyW1 : (y : G) ∈ hyp.typeP.W1 := by
          have heq : (y : G) = (x : G)⁻¹ * ((x : G) * (y : G)) := by group
          rw [heq]; exact mul_mem (inv_mem hxG) hmem
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hyW1, hyG⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
      · intro hmem
        apply hx1
        have hxW2 : (x : G) ∈ hyp.typeP.W2 := by
          have heq : (x : G) = ((x : G) * (y : G)) * (y : G)⁻¹ := by group
          rw [heq]; exact mul_mem hmem (inv_mem hyG)
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hxG, hxW2⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
    · -- `(c:G)·((x:G)·(y:G))·(c:G)⁻¹ = (z:G)`
      have hconjG : (c : G)⁻¹ * (z : G) * (c : G) = (x : G) * (y : G) := by
        have := congrArg (M.subtype) hconj
        rwa [map_mul, map_mul, map_inv] at this
      rw [← hconjG]; group

/-- The character parameters obtained in Peterfalvi (10.2)--(10.3).

The arithmetic fields are now de-opaqued to genuine identities: `degree_independent` is the
degree constancy `μ_{ij}(1) = d` (4.5.a), `n_formula` is `n·w₁ = d − δ`, and `alpha` is the
genuine virtual character `μ_{ij} − δ·μ_{i0} − n·ζ` (10.5).  The `δ_j`-independence (10.3) is now a
genuine clause of `w2_prime_and_parameter_independence` (via `Hypothesis.muColumnSign`), no longer a
placeholder field. -/
structure CharacterParameters {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_S : zeta ∈ hyp.Sset
  /-- (10.2): `ζ` is irreducible.  De-opaqued from a placeholder `Prop` to the genuine
  irreducibility predicate, now that `exists_zeta_in_inducedFamily_degree_w1` constructs such a
  `ζ`. -/
  zeta_irreducible : IsIrreducibleCharacter zeta
  d : ℕ
  delta : ℤ
  n : ℕ
  w2_prime : hyp.w2.Prime
  d_gt_one : 1 < d
  mu : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  omegaSigma : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ
  /-- (10.3) degree independence (4.5.a): `d = μ_{ij}(1)` is independent of the indices, for
  `0 ≤ i < w₁` and `0 < j < w₂`.  De-opaqued from a placeholder `Prop` to the genuine degree
  identity. -/
  degree_independent : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → mu i j 1 = (d : ℂ)
  /-- (10.3) the index relation `n = (d − δ)/w₁ ∈ ℕ`, in the cleared form `n·w₁ = d − δ`.
  De-opaqued from a placeholder `Prop`. -/
  n_formula : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta
  /-- (10.3) the parity input: `n` is even and positive, so `n ≥ 2`.  `d = μ_{ij}(1)` divides the
  odd `|M|` (a character degree), hence is odd; with `δ = ±1`, `w₁` odd and `n·w₁ = d − δ`, `n` is
  even, and `d > 1` forces `n > 0`.  This is the (10.3) fact used by (10.5)'s Cauchy–Schwarz
  (`n < 2` contradiction); de-opaqued (no longer a carried hypothesis of the §10 (10.5) endpoint). -/
  two_le_n : 2 ≤ n
  /-- (10.5): `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  De-opaqued from a free field + placeholder
  formula to the genuine definition in terms of the `μ`-grid, `δ`, `n` and `ζ`. -/
  alpha : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ :=
    fun i j => mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta
  alpha_def : ∀ i j, alpha i j = mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta := by
    intro i j; rfl
  /-- (10.5), support half: for `0 < j < w₂`, `α_{ij}` is supported on `A_0(M)`.  De-opaqued (and
  dade0-free) — materialized in the producer from `Hypothesis.muGrid_alpha_support`. -/
  alpha_support : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (alpha i j).support ⊆ hyp.A0
  typeV_parameter_formula : Prop
  typeV_coherence_formula : Prop

/-- **Peterfalvi (10.4)**: the coherent-extension hypothesis for the family of
characters in (10.1).

De-opaqued: instead of an unconstrained `tau1` field plus an opaque `tau1_extends_tau_on_S : Prop`,
this carries the *genuine* coherence datum `IsCoherent hyp.tau hyp.Sset hyp.A0` (Peterfalvi (5.1)).
Its bundled `extension` is Peterfalvi's `τ₁`, exposed as `CoherentHypothesis.tau1`: a lattice
isometry on `ℤ[S]` (`coherent.extension_inner_eq`) extending `τ` on the supported lattice
`ℤ[S, A₀]` (`coherent.extends_on_supported`).  This is exactly the content of (10.4.b) ("`S` is
coherent and `τ₁` is an extension of `τ` to `ℤ[S]`"), no longer a free map + placeholder `Prop`. -/
structure CoherentHypothesis {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (params : CharacterParameters hyp) where
  /-- (10.4.b): the family `S` is coherent; the bundled `extension` is Peterfalvi's `τ₁`. -/
  coherent : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0

namespace CoherentHypothesis

/-- **Peterfalvi's `τ₁`** (10.4.b): the coherent extension of the Dade isometry `τ` to `ℤ[S]`,
projected out of the bundled `IsCoherent` datum.  It is a lattice isometry on `ℤ[S]` and agrees
with `τ` on the supported lattice `ℤ[S, A₀(M)]`. -/
noncomputable def tau1 {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  coh.coherent.extension

end CoherentHypothesis

/-- **Peterfalvi (8.8) for `M`, used at the start of (10.3)**: there is a maximal subgroup `S` of `G`
of **Type II** such that `|S : [S,S]| = w₂`.

This is exactly the opening sentence of the proof of (10.3) ("By Theorem (8.8), there is a maximal
subgroup `S` of `G` of Type II such that `|S:[S,S]| = w₂`"): the type-`P` maximal `M` of (10.1)
participates in the case-(b) configuration of Theorem (8.8), one of whose two maximal subgroups is
of Type II and shares the cyclic factor order `w₂`.  Tying the generic case-(b) datum
(`theorem88_caseB_holds`) to the *given* `M` is the content of (8.8)/(8.13) applied to `M`; it is
recorded here as a faithful obligation (its proof is currently a `sorry`, gated on the BG §16
partner-existence behind `theorem88_caseB_holds`). -/
theorem Hypothesis.exists_typeII_maximal_with_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = hyp.w2 := by
  -- The `M`-specific (8.8) partner now lives in §8 (`S10.exists_typeII_maximal_with_w2_of_typeP`),
  -- stated on the bare `TypePData`; here `hyp.w2 = |W₂(hyp.typeP)|`.
  simpa only [Hypothesis.w2, Hypothesis.W2] using
    OddOrder.Peterfalvi.S10.exists_typeII_maximal_with_w2_of_typeP hG hyp.typeP hyp.maximal
      hyp.type_alt

/-- **Peterfalvi (10.3), first clause**: `w₂` is prime.

By Theorem (8.8) there is a Type-II maximal subgroup `S` with `|S:[S,S]| = w₂`
(`exists_typeII_maximal_with_w2`); a Type-II maximal's cyclic factor `W₁(S)` has prime order
(Peterfalvi (8.6.a), carried by `TypePNontrivialCore`) and equals `|S:[S,S]|`
(`card_W1_eq_derived_index`), so `w₂` is prime.

This follows Peterfalvi's own proof of (10.3) verbatim and is **non-circular**: it does *not* route
through `no_typeV_maximal` (the way a generic case-(b) datum would, since `TypeVData` carries no
prime-order field), so it may be used to populate `CharacterParameters.w2_prime` *upstream* of the
(10.10) Type-V elimination — which is what unblocks the (10.2)/(10.3) producer below. -/
theorem Hypothesis.w2_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) : (hyp.w2).Prime := by
  obtain ⟨S, -, hSII, hindex⟩ := hyp.exists_typeII_maximal_with_w2 hG
  obtain ⟨dataII⟩ := hSII
  have hcard : Nat.card ↥dataII.typeP.W1 = hyp.w2 := by
    rw [dataII.typeP.card_W1_eq_derived_index]; exact hindex
  rw [← hcard]
  exact dataII.common.2.1

open scoped FiniteInduce in
/-- **Peterfalvi (10.3), arithmetic data**: the common nontrivial-column degree `d`, the sign
`δ`, and the integer `n = (d − δ)/w₁`, materialized from the §6 column family.

We pick a nontrivial column `j₀` (which exists because `w₂` is prime, hence `≥ 2`) and read off
`d = μ_{0 j₀}(1)` as a natural number (the degree of an irreducible character,
`exists_natDegree_characterDegree_dvd_card`).  `d > 1` is Peterfalvi (4.4): if `μ_{0 j₀}` had degree
`1` it would be linear, hence `K`-trivial, hence a column-`0` character — contradicting `χ₂ ≠ 1`
(`columnFamily_mu_ne`); this mirrors the crux of `exists_zeta_in_inducedFamily_degree_w1`.  `δ` is the
column sign; and the congruence `μ_{0 j₀}(1) ≡ δ (mod w₁)` (Peterfalvi (4.3.d),
`certainType_degree_modEq`) gives `n` with `n·w₁ = d − δ`.  The degree independence
`μ_{ij}(1) = d` for all `i` and all nontrivial `j` is the materialized (10.3) constancy
`muGrid_apply_one_eq`. -/
theorem Hypothesis.exists_charParamArith [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ (d : ℕ) (delta : ℤ) (n : ℕ), 1 < d ∧ (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta ∧ 2 ≤ n ∧
      (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → hyp.muGrid hG hodd i j 1 = (d : ℂ)) ∧
      (∀ (j : Fin hyp.w2), j ≠ 0 → hyp.muColumnSign hG hodd j = delta) := by
  haveI := hyp.finiteG
  classical
  have hw2 := hyp.w2_prime hG
  have hw2ge : 2 ≤ hyp.w2 := hw2.two_le
  -- a nontrivial column index `j₀`
  let j₀ : Fin hyp.w2 := ⟨1, by omega⟩
  have hj₀ : j₀ ≠ 0 := Fin.ne_of_val_ne (by simp [j₀])
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j₀)
  let k₀ : Fin (Nat.card h.W1) := finCongr hcardW1.symm 0
  -- `χ₂` is a nontrivial dual (the column-`0` dual is the trivial one).
  have hχ₂ne : χ₂ ≠ 1 := by
    intro heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm j₀ = 0 := (finCardEquivCharacterGroup _).injective heq
    have : (j₀ : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact hj₀ (Fin.ext this)
  -- `muGrid 0 j₀ = (h.columnFamily χ₂).mu k₀` definitionally.
  have hmg : hyp.muGrid hG hodd 0 j₀ = ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- `h.K = commutator ↥M` (so (4.4) applies).
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `d := μ_{0 j₀}(1) ∈ ℕ`, with `d ∣ |M|` (a character degree divides the group order).
  obtain ⟨d, hd0, hdeg, hdvd⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card
      ((h.columnFamily χ₂).mu k₀)
  rw [OddOrder.Peterfalvi.S03.characterDegree_def] at hdeg
  -- `d > 1` by (4.4): a nontrivial column is not linear (mirrors the `exists_zeta` crux).
  have hne1 : ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) 1 ≠ 1 := by
    intro hmu1
    have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
      intro x hx
      have hx1 := ((h.columnFamily χ₂).mu k₀).isIrreducible
        |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
        OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
    obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
    exact h.columnFamily_mu_ne hχ₂ne k₀ i hi.symm
  have hd1 : 1 < d := by
    rw [hdeg] at hne1
    have : d ≠ 1 := fun hd => hne1 (by rw [hd]; norm_num)
    omega
  -- (4.3.d): `μ_{0 j₀}(1) = δ + w₁·a`.
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ k₀
  have hcardW1c : (Nat.card ↥h.W1 : ℂ) = (hyp.w1 : ℂ) := by exact_mod_cast hcardW1
  have hcombine : (d : ℂ) = ((h.columnFamily χ₂).sign : ℂ) + (hyp.w1 : ℂ) * (a : ℂ) := by
    rw [← hdeg, ha, hcardW1c]
  have hZ : (d : ℤ) = (h.columnFamily χ₂).sign + (hyp.w1 : ℤ) * a := by exact_mod_cast hcombine
  -- `a ≥ 0` (so `n := a.toNat` realizes `n·w₁ = d − δ`).
  have hw1posN : 0 < hyp.w1 := Nat.pos_of_ne_zero (NeZero.ne hyp.w1)
  have hw1pos : (0 : ℤ) < (hyp.w1 : ℤ) := by exact_mod_cast hw1posN
  have hdsign : (0 : ℤ) < (d : ℤ) - (h.columnFamily χ₂).sign := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> omega
  have hapos : 0 ≤ a := by
    by_contra hlt
    push Not at hlt
    have hwa : (hyp.w1 : ℤ) * a < 0 := mul_neg_of_pos_of_neg hw1pos hlt
    linarith [hZ, hdsign, hwa]
  -- (10.3): `n = a` is even (hence `≥ 2`).  `d = μ_{0 j₀}(1)` divides the odd `|M|` (a character
  -- degree), so `d` is odd; with `δ = ±1` and `w₁` odd, `n·w₁ = d − δ` is even, forcing `n` even;
  -- and `n > 0` (from `d > 1`), so `n ≥ 2`.  This is the parity input of (10.5)'s Cauchy–Schwarz.
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hdodd : Odd (d : ℤ) := by exact_mod_cast hModd.of_dvd_nat hdvd
  have hw1odd : Odd (hyp.w1 : ℤ) := by
    exact_mod_cast hModd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.typeP.W1_le)
  have hδodd : Odd ((h.columnFamily χ₂).sign) := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> decide
  have hwa : (hyp.w1 : ℤ) * a = (d : ℤ) - (h.columnFamily χ₂).sign := by linarith [hZ]
  have haeven : Even a := by
    have heven : Even ((hyp.w1 : ℤ) * a) := by rw [hwa]; exact hdodd.sub_odd hδodd
    rcases Int.even_mul.mp heven with hcon | h
    · obtain ⟨k, hk⟩ := hw1odd; obtain ⟨m, hm⟩ := hcon; omega
    · exact h
  have ha2 : 2 ≤ a := by
    have hwapos : 0 < (hyp.w1 : ℤ) * a := by rw [hwa]; exact hdsign
    have hapos' : 0 < a := by
      rcases eq_or_lt_of_le hapos with h | h
      · rw [← h, mul_zero] at hwapos; exact absurd hwapos (lt_irrefl 0)
      · exact h
    obtain ⟨b, hb⟩ := haeven
    omega
  have hn2 : 2 ≤ a.toNat := by omega
  -- degree independence (the materialized (10.3) constancy).
  have hdi : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hodd i j 1 = (d : ℂ) := by
    intro i j hj
    rw [hyp.muGrid_apply_one_eq hG hodd hw2 i 0 hj hj₀, hmg]
    exact hdeg
  refine ⟨d, (h.columnFamily χ₂).sign, a.toNat, hd1, ?_, hn2, hdi, ?_⟩
  · rw [Int.toNat_of_nonneg hapos, mul_comm]
    linarith [hZ]
  · -- `δ_k = δ_{j₀} = δ` for every nontrivial column `k` (the (10.3) sign-independence).
    intro k hk
    refine (hyp.muColumnSign_eq_of_ne hG hodd hw2 hk hj₀).trans ?_
    unfold Hypothesis.muColumnSign
    rfl

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)+(10.3), the character parameters of (10.4)**: assemble a genuine
`CharacterParameters` for the §10 Hypothesis from the materialized §6 data.

`ζ` is the degree-`w₁` irreducible of (10.2) (`exists_zeta_in_inducedFamily_degree_w1`), the `μ`- and
`ω^σ`-grids are `muGrid`/`omegaSigmaGrid`, `w₂` is prime by the non-circular (10.3) first clause
(`Hypothesis.w2_prime`), and the degree data `d > 1`, `n·w₁ = d − δ`, `μ_{ij}(1) = d` come from
`exists_charParamArith`.  The `δ_j`-independence `δ_j = δ_{j'}` (10.3) is the genuine
`muColumnSign_eq_of_ne`.  Only the `τ₁`-level `Prop` placeholders remain trivial, pending the
(10.5)/(10.6) Dade calculations. -/
theorem Hypothesis.exists_charParameters [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      (params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
          params.zeta 1 = ((hyp.w1 : ℕ) : ℂ)) ∧
        (1 < params.d ∧
          (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
          (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
              hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
          ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta)) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hodd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hδindep⟩ := hyp.exists_charParamArith hG hodd
  exact ⟨{ zeta := ζ
           zeta_mem_S := hζS
           zeta_irreducible := hζirr
           d := d
           delta := delta
           n := n
           w2_prime := hyp.w2_prime hG
           d_gt_one := hd1
           mu := hyp.muGrid hG hodd
           omegaSigma := hyp.alignedOmegaSigmaGrid hG hodd
           degree_independent := hdi
           n_formula := hnf
           two_le_n := hn2
           alpha_support := fun i j hj =>
             hyp.muGrid_alpha_support hG hodd hj hζS (hdi i j hj)
               (hyp.muGrid_zero_column_apply_one hG hodd i) hζdeg hnf (hδindep j hj)
           typeV_parameter_formula := True
           typeV_coherence_formula := True },
    ⟨hζS, hζirr, hζdeg⟩, hd1, hdi,
    (fun _ _ hj hj' => hyp.muColumnSign_eq_of_ne hG hG.odd (hyp.w2_prime hG) hj hj'), hnf⟩

/-- **Peterfalvi (10.2)**: the family `S` contains an irreducible character
`zeta` of degree `w_1`. -/
theorem exists_zeta_degree_w1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
        params.zeta 1 = ((hyp.w1 : ℕ) : ℂ) := by
  obtain ⟨params, h1, -⟩ := hyp.exists_charParameters hG
  exact ⟨params, h1⟩

/-- **Peterfalvi (10.3)**: `w_2` is prime and the parameters `d`, `delta`, and
`n = (d - delta) / w_1` are well-defined and independent of the indices. -/
theorem w2_prime_and_parameter_independence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      hyp.w2.Prime ∧ 1 < params.d ∧
        (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
        (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
            hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
        ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta) := by
  obtain ⟨params, -, h2⟩ := hyp.exists_charParameters hG
  exact ⟨params, hyp.w2_prime hG, h2⟩

/-- **Every degree-`w₁` irreducible of `M` is non-real (`χ̄ ≠ χ`), Peterfalvi (1.1)**.  A degree-`w₁`
irreducible character `χ` of the *odd-order* group `M` is *nontrivial* (`χ(1) = w₁ > 1`), so by
`not_isReal_of_ne_trivial_of_odd_card'` (the only self-conjugate irreducible of an odd group is the
trivial one) `χ` is not real, i.e. `χ.conj ≠ χ`.  No induced-character / orbit argument is needed.
This is the general form feeding both `zeta_conj_ne` and the `S(HC)` `τ₁`-vanishing arguments (each
`S(HC)` member `λ` — a degree-`w₁` irreducible — is non-real, so `λ^{τ₁}` vanishes on `V`). -/
theorem Hypothesis.inducedFamily_degree_w1_conj_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ} (hχirr : IsIrreducibleCharacter χ) (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    χ.conj ≠ χ := by
  haveI := hyp.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hne : (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ≠ trivialIrreducibleCharacter ↥M := by
    intro h
    have hz : χ 1 = (1 : ℂ) := by
      have hcoe := congrArg (fun c : IrreducibleCharacter ↥M => (c : ClassFunction ↥M ℂ) 1) h
      simpa using hcoe
    rw [hχ1] at hz
    have : hyp.w1 = 1 := by exact_mod_cast hz
    omega
  exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hModd hne

/-- **`ζ` is non-real (`ζ̄ ≠ ζ`)** — the `hzconj` input to the (10.6.b) Dade-value lemmas, **directly
from Peterfalvi (1.1)**.  Thin `CharacterParameters` specialisation of
`inducedFamily_degree_w1_conj_ne` at `χ = params.zeta`. -/
theorem Hypothesis.zeta_conj_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {params : CharacterParameters hyp} (hz1 : params.zeta 1 = (hyp.w1 : ℂ)) :
    (params.zeta).conj ≠ params.zeta :=
  hyp.inducedFamily_degree_w1_conj_ne hG params.zeta_irreducible hz1

/-- **Parameter package with all (10.6.b) hypotheses** (the `tau1_values_and_norm_bound` /
`zeta_tau1_norm_ge_one` inputs).  Strengthens `exists_charParameters` to also expose the seven
conditions those Dade-value lemmas require, now that each is establishable: `mu`/`omegaSigma` are the
materialized grids (`rfl`), `ζ ∈ S` and `ζ(1) = w₁` come from `(10.2)`, `δ_j = δ` from
`exists_charParamArith`, `δ = ±1` from `muColumnSign_eq_one_or_neg_one`, and `ζ̄ ≠ ζ` from
`zeta_conj_ne` (Peterfalvi (1.1)).  This is the single producer the `(10.8)` line-83 step consumes
(via the re-wrapped coherence `⟨coh.coherent⟩` for this `params`). -/
theorem Hypothesis.exists_charParameters_full [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.mu = hyp.muGrid hG hG.odd ∧
      params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd ∧
      params.zeta ∈ inducedFamily M ∧ params.zeta 1 = (hyp.w1 : ℂ) ∧
      params.zeta.conj ≠ params.zeta ∧
      (params.delta = 1 ∨ params.delta = -1) ∧
      (∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hδindep⟩ := hyp.exists_charParamArith hG hG.odd
  refine ⟨{ zeta := ζ
            zeta_mem_S := hζS
            zeta_irreducible := hζirr
            d := d
            delta := delta
            n := n
            w2_prime := hyp.w2_prime hG
            d_gt_one := hd1
            mu := hyp.muGrid hG hG.odd
            omegaSigma := hyp.alignedOmegaSigmaGrid hG hG.odd
            degree_independent := hdi
            n_formula := hnf
            two_le_n := hn2
            alpha_support := fun i j hj =>
              hyp.muGrid_alpha_support hG hG.odd hj hζS (hdi i j hj)
                (hyp.muGrid_zero_column_apply_one hG hG.odd i) hζdeg hnf (hδindep j hj)
            typeV_parameter_formula := True
            typeV_coherence_formula := True },
    rfl, rfl, hζS, hζdeg, ?_, ?_, hδindep⟩
  · exact hyp.zeta_conj_ne hG hζdeg
  · have hw2 : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
    have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by simp [Fin.ext_iff]
    have hde := hδindep ⟨1, by omega⟩ hj
    have hs := hyp.muColumnSign_eq_one_or_neg_one hG hG.odd ⟨1, by omega⟩
    rw [hde] at hs
    exact hs

/-! ## (10.5)--(10.6): Dade-isometry calculations -/

open scoped FiniteInduce in
/-- **Peterfalvi (4.8) on the §10 aligned grid, row `0`** (coherence-free): for two nonzero
columns `j, k`, `(μ_{0j} − μ_{0k})^τ = δ_j·(ω_{0j}^σ − ω_{0k}^σ)`, where `τ = hyp.tau`,
`ω^σ = alignedOmegaSigmaGrid`, and `δ_j = muColumnSign j`.

This is the §6 isometry identity `certainType_diff_dade_eq` cited through the (8.15)
instantiation `toHypothesis46`: the §10 Dade map is *definitionally* the certain-type
`dadeIntegralCharacterMap h46.dade0 h46.tau`, `muGrid`/`muColumnSign` unfold to the §6
`columnFamily` data (`unfold … rfl`), the equal-degree input is the (10.3) cross-column
constancy `muGrid_apply_one_eq` (whence `hw2`), and the §6 σ-image `certainTypeOmegaSigma`
is the aligned grid (the ω-arguments agree pointwise along `ticWEquivSdiffW = e`).  This
discharges the `h48` thread of the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_zeroRow_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime)
    {j k : Fin hyp.w2} (hj : j ≠ 0) (hk : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := by
  haveI := hyp.finiteG
  classical
  by_cases hjk : j = k
  · subst hjk
    simp
  -- §6 host context (the standard `muGrid`/`alignedOmegaSigmaGrid` let-context)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set χ₂' := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm k) with hχ₂'def
  set i0 : Fin (Nat.card h.W1) := finCongr hcardW1.symm (0 : Fin hyp.w1) with hi0def
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  haveI : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- column-character facts
  have hcol_ne : ∀ (l : Fin hyp.w2), l ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm l) ≠ 1 := by
    intro l hl heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hl0 : finCongr hcardW2sub.symm l = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hl
    have hval : (l : ℕ) = 0 := by simpa using congrArg Fin.val hl0
    exact Fin.ext hval
  have hχ₂ne1 : χ₂ ≠ 1 := hcol_ne j hj
  have hχ₂'ne1 : χ₂' ≠ 1 := hcol_ne k hk
  have hχne : χ₂ ≠ χ₂' := by
    intro heq
    apply hjk
    rw [hχ₂def, hχ₂'def] at heq
    have := (finCardEquivCharacterGroup _).injective heq
    have hval : (j : ℕ) = (k : ℕ) := by simpa using congrArg Fin.val this
    exact Fin.ext hval
  -- `muGrid` unfolds (definitional, the `unfold … rfl` idiom)
  have emj : hyp.muGrid hG hodd 0 j = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  have emk : hyp.muGrid hG hodd 0 k = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- equal degree: the (10.3) cross-column constancy
  have hdeg : ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) 1
      = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) 1 := by
    rw [← emj, ← emk]
    exact hyp.muGrid_apply_one_eq hG hodd hw2 0 0 hj hk
  -- σ-bridge: `certainTypeOmegaSigma (toHypothesis46) = alignedOmegaSigmaGrid`
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    show (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    show (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- `hyp.tau` on the (4.8) supported difference is the certain-type Dade map
  have hsupp : (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46 hχ₂ne1 hχ₂'ne1 i0 hdeg).2
  have happly : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = h46.tau.toDadeMap
          (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46 hχ₂ne1 hχ₂'ne1 i0 hdeg) := by
    have h1 : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = h46.dade0.dadeMap (k := ℂ)
            ⟨hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k,
              ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    have hval : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k
        = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ)
          - ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
      rw [emj, emk]
    exact congrArg _ (Subtype.ext hval)
  -- assemble: (4.8) + σ-bridge + sign reconciliation
  have esign : hyp.muColumnSign hG hodd j = (h46.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  rw [happly]
  refine (OddOrder.Peterfalvi.S06.certainType_diff_dade_eq h46 hχne hχ₂ne1 hχ₂'ne1 i0 hdeg).trans ?_
  rw [hbridge χ₂ i0 0 j hχ₂def hi0def, hbridge χ₂' i0 0 k hχ₂'def hi0def,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact congrArg (fun s : ℤ => (s : ℂ) •
    (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) esign.symm

open scoped FiniteInduce in
/-- **Peterfalvi (4.10) on the §10 aligned grid** (coherence-free, `δ_j`-scaled): the four-corner
Dade identity `(μ_{ij} − μ_{0j} − δ_j μ_{i0} + δ_j μ_{00})^τ = δ_j·(ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ
+ ω_{00}^σ)`.

This is the §6 `fourCorner_dade_eq` cited through the (8.15) instantiation `toHypothesis46`
(same bridging as `tau_muGrid_zeroRow_diff`), with the book's `δ_j(μ_{ij} − μ_{0j}) − (μ_{i0} −
μ_{00})` form rescaled by `δ_j` (`δ_j² = 1`, `muColumnSign_eq_one_or_neg_one`) and the trivial
column-`0` sign `δ_0 = 1` (`muColumnSign_zero`) absorbed.  This discharges the `h410` thread of
the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_fourCorner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
        + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
  haveI := hyp.finiteG
  classical
  -- §6 host context
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set i' : Fin (Nat.card h.W1) := finCongr hcardW1.symm i with hi'def
  have hi00 : (0 : Fin (Nat.card h.W1)) = finCongr hcardW1.symm (0 : Fin hyp.w1) := by
    apply Fin.ext; simp
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  haveI : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- signs: `δ_j` matches the §6 column sign, and the trivial column has sign `1`
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  have hδ1 : (h.columnFamily
      (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).sign = 1 := by
    have e0 : hyp.muColumnSign hG hodd 0 = (h.columnFamily
        (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
      unfold Hypothesis.muColumnSign
      rfl
    rw [hyp.muColumnSign_zero hG hodd, hdual0] at e0
    exact e0.symm
  -- σ-bridge (as in `tau_muGrid_zeroRow_diff`)
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    show (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    show (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- the (4.10) four-corner carrier and its `A₀`-support
  set u : ClassFunction ↥M ℂ :=
    (h.columnFamily χ₂).signedDifference i'
      - (h.columnFamily (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).signedDifference i'
    with hudef
  have hsupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i').2
  have happly : hyp.tau u = h46.tau.toDadeMap
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i') := by
    have h1 : hyp.tau u = h46.dade0.dadeMap (k := ℂ)
        ⟨u, ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    exact congrArg _ (Subtype.ext rfl)
  -- the target τ-argument is `δ_j • u` (`δ_j² = 1`, `δ_0 = 1`)
  have hXeq : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
      - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
      + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0
      = (hyp.muColumnSign hG hodd j : ℂ) • u := by
    rw [hudef,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      hδ1, one_zsmul, ← esign]
    have emij : hyp.muGrid hG hodd i j
        = ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em0j : hyp.muGrid hG hodd 0 j
        = ((h.columnFamily χ₂).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have emi0 : hyp.muGrid hG hodd i 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em00 : hyp.muGrid hG hodd 0 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu (finCongr hcardW1.symm 0)
          : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    rw [emij, em0j, emi0, em00, hdual0, ← hi00]
    simp only [OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.difference,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.classFunction]
    rcases hyp.muColumnSign_eq_one_or_neg_one hG hodd j with hδ | hδ <;> rw [hδ] <;> push_cast <;>
      module
  rw [hXeq, Int.cast_smul_eq_zsmul ℂ, map_smul, happly]
  rw [show h46.tau.toDadeMap (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i')
      = OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
        - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
        - (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
          - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0) from
    OddOrder.Peterfalvi.S06.fourCorner_dade_eq h46 χ₂ i']
  have hb1 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
      = hyp.alignedOmegaSigmaGrid hG hodd i j := hbridge χ₂ i' i j hχ₂def hi'def
  have hb2 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 j := hbridge χ₂ 0 0 j hχ₂def hi00
  have hb3 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
      = hyp.alignedOmegaSigmaGrid hG hodd i 0 := hbridge 1 i' i 0 hdual0.symm hi'def
  have hb4 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 0 := hbridge 1 0 0 0 hdual0.symm hi00
  rw [hb1, hb2, hb3, hb4, ← Int.cast_smul_eq_zsmul ℂ]
  module

/-- **Peterfalvi (10.5), support half**: for `0 < j < w₂`, the virtual character `α_{ij}` is
supported on `A_0(M)`.  This is now a genuine (dade0-free) theorem, carried by the
`CharacterParameters` field `alpha_support` and discharged in the producer from
`Hypothesis.muGrid_alpha_support`. -/
theorem alpha_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (params : CharacterParameters hyp) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (params.alpha i j).support ⊆ hyp.A0 :=
  params.alpha_support

open scoped FiniteInduce in
/-- **§10 Dade value on `V`** (Peterfalvi's "by definition of `τ`").  For a class function `φ` on
`M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *restores* `φ`'s value at any
`v ∈ V = typePV M`: `(φ^τ)(v) = φ(v)`.

Since `V = typePV ⊆ V^M ⊆ A_0(M)` (`subset_conjClassSetIn`), this is exactly the
value-on-support property `dadeIntegralCharacterMap_apply_mem` of the genuine §10 Dade isometry
`hyp.tau`.  It is the reusable "agrees/vanishes on `V` by definition of `τ`" step underlying the
Dade-image half of (10.5) (`α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`), and the (10.6.b) /
(10.9) value computations. -/
theorem Hypothesis.tau_apply_of_mem_typePV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.tau φ v = φ ⟨v, hvM⟩ := by
  haveI := hyp.finiteG
  have hvA0 : v ∈ typePA0 M hyp.typeP := by
    rw [typePA0]
    exact Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hv)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_mem hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ hvA0

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), the Dade-image value on `V`** (the "vanishes on `V`" leg of the Dade-image
half): on the exceptional set `V = typePV`, the Dade image `α_{ij}^τ` of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` equals `δ·(ω_{ij}^σ − ω_{i0}^σ)`, where `ω^σ` is the *aligned*
σ-grid `alignedOmegaSigmaGrid` (the σ-image of the same ω that `μ` is built from).

This is Peterfalvi's step *"By (3.2.c), (4.3.c) and the definition of `τ`, `α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ)` vanishes on `V`"*, assembled from:
* the cornerstone `tau_apply_of_mem_typePV` — `α` is supported on `A_0(M)` (the support half,
  `muGrid_alpha_support`), so `τ` restores `α`'s value on `V`;
* the reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` —
  `μ_{ij}(v) = δ_j·ω_{ij}^σ(v)` on `V`, both at `j` and at column `0`;
* `muColumnSign_zero` — `δ_0 = 1`;
* `ζ` vanishing on `V` — `ζ` is induced from the normal `M' = [M,M]` and `v ∉ M'`
  (`typePData_typePV_not_mem_derived`).

It is the reusable on-`V` identity feeding the `(10.5)`/`(10.6.b)`/`(10.9)` value computations; the
*global* Dade-image identity additionally requires the `a = 0` norm/Cauchy–Schwarz argument and the
(3.8) trichotomy. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v
      = ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v := by
  haveI := hyp.finiteG
  classical
  -- `v ∈ M` (`V ⊆ W ⊆ M`).
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- The (10.5) support half, so `τ` restores `α` on `V`.
  have hsupp := hyp.muGrid_alpha_support hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` vanishes on `V`: induced from the normal `M'`, and `v ∉ M'`.
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    rw [hζeq]
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  -- Evaluate `α ⟨v⟩` via the reconciliation (`μ = δ_j·ω^σ`), `δ_0 = 1`, and `ζ(v) = 0`.
  rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
    ClassFunction.smul_apply,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i j hv hvM,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i 0 hv hvM,
    hδj, hyp.muColumnSign_zero hG hodd, hζv,
    ClassFunction.smul_apply, ClassFunction.sub_apply]
  push_cast
  ring

open scoped FiniteInduce in
/-- **§10 Dade isometry on the support lattice** (the inner-product half of (10.5)/(10.6)): the
genuine Dade map `τ = hyp.tau` preserves the class-function inner product on functions supported in
`A_0(M)`.  This is the §7 `dadeIntegralCharacterMap_inner_eq_on_supported_span` for the (8.15) Dade
data `hyp.dadeData`, instantiated on the two-element set `{φ, ψ}` whose members are `A_0`-supported.

It is the isometry input to the (10.5) `a = 0` argument: every `(α_{ij}^τ, …)` inner product is
computed on the `M`-side via this transfer, since `α_{ij}` is `A_0`-supported by
`muGrid_alpha_support`. -/
theorem Hypothesis.tau_inner_eq_of_supported [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) (hψ : ψ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  haveI := hyp.finiteG
  classical
  have hS : ∀ s ∈ ({φ, ψ} : Set (ClassFunction ↥M ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hφ
    · exact hψ
  have hφ' : φ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hψ' : ψ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS hφ' hψ'

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}^τ‖² = 2 + n²`**: the Dade image `α_{ij}^τ` has the same norm as
`α_{ij}`.  The genuine Dade map `τ` is an isometry on `A_0`-supported functions
(`tau_inner_eq_of_supported`), and `α_{ij}` is `A_0`-supported (`muGrid_alpha_support`), so
`‖α_{ij}^τ‖² = ‖α_{ij}‖² = 2 + n²` (`muGridAlpha_inner_self`).  This is the `‖α_{ij}^τ‖²` factor of
the (10.5) Cauchy–Schwarz bound `d²a² ≤ ‖α_{ij}^τ‖²‖μ_k^{τ₁}‖² = (2 + n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = 2 + (n : ℂ) ^ 2 := by
  haveI := hyp.finiteG
  classical
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
  exact hyp.muGridAlpha_inner_self hG hodd i hj0 hζirr hdζ h0ζ hδpm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, ζ − ζ̄) = −n`** (M-side): the inner product of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `ζ − ζ̄`.  The certain-type characters `μ_{ij}`, `μ_{i0}`
are degree-distinct from `ζ` and its conjugate `ζ̄` (both of degree `w₁ = ζ(1)`), so they are
orthogonal to both (`muGrid_inner_eq_zero_of_apply_one_ne`); `ζ ≠ ζ̄` (no real characters) gives
`(ζ, ζ̄) = 0`, while `(ζ, ζ) = 1`.  The only surviving term is `−n·(ζ, ζ) = −n`.

This is the `M`-side of the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step of the (10.5)
`a = 0` argument (`ζ − ζ̄` is `A_0`-supported, so the Dade isometry transfers it). -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - ζ.conj) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number, fixed by `star`.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijζc : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
  have hμi0ζc : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijζc, hμi0ζc, hζζ, hζζc,
    star_intCast, star_natCast, mul_zero, zero_mul, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), `(α_{ij}, ζ − η) = −n`** for any degree-`w₁` irreducible `η ∈ S(HC)`
distinct from `ζ`.  General-`η` companion of `muGridAlpha_inner_zeta_sub_conj` (the `η = ζ̄` case):
since `η` has the same degree as `ζ` (`hη1 : η(1) = ζ(1)`), both `μ_{ij}, μ_{i0}` are degree-distinct
from — hence orthogonal to — `η` (`muGrid_inner_eq_zero_of_apply_one_ne`), and `(ζ, η) = 0`
(`η ≠ ζ`, both irreducible), so only the `−nζ` term survives:
`(α_{ij}, ζ − η) = −n(ζ, ζ) = −n` (independent of `δ`).

This is the source value that (11.8.2) lifts (via the `τ`-isometry) to `(α_{ij}^τ, (ζ − η)^τ) = −n`
for every `η ∈ S₁ = S(HC)`, `η ≠ ζ` — pinning the `ζ^{τ₁}`-coefficient of the `α_{ij}^τ` projection
onto the orthonormal `S₁^{τ₁}` (`SHC_extension_inner_*`) to `−n`. -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ η : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hηirr : IsIrreducibleCharacter η)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hη1 : η 1 = ζ 1) (hηne : η ≠ ζ) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - η) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijη : ClassFunction.inner (hyp.muGrid hG hodd i j) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hηirr (by rw [hη1]; exact hdζ)
  have hμi0η : ClassFunction.inner (hyp.muGrid hG hodd i 0) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hηirr (by rw [hη1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζη : ClassFunction.inner ζ η = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hηirr, if_neg (Ne.symm hηne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijη, hμi0η, hζζ, hζη,
    star_intCast, star_natCast, mul_zero, zero_mul, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, μ_k − dζ̄) = 0`** (M-side, `0 < k < w₂`, `k ≠ j`): the inner
product of `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `μ_k − dζ̄`, where `μ_k = ∑_{0≤i'<w₁} μ_{i'k}`
is the `W₂`-column-`k` sum.  Since `k ≠ j` and `k ≠ 0`, every `μ_{i'k}` is cross-column-orthogonal
to `μ_{ij}` and `μ_{i0}` (`muGrid_inner_cross_column`), and degree-distinct from `ζ`
(`hkζ`), so `(α_{ij}, μ_k) = 0`; and `(α_{ij}, ζ̄) = 0` (degree distinctness + `(ζ, ζ̄) = 0`), so
`(α_{ij}, dζ̄) = 0`.  Hence `(α_{ij}, μ_k − dζ̄) = 0`.

This is the `M`-side of the `(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = (α_{ij}, μ_k − dζ̄) = 0` step of
the (10.5) `a = 0` argument (whence `(α_{ij}^τ, μ_k^{τ₁}) = da`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j k : Fin hyp.w2)
    (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj) = 0 := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'k}) = 0` for each `i'`: cross-column (`k ≠ j`, `k ≠ 0`) + degree (`k`-column ≠ ζ).
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' k) = 0 := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hjk
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hk0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' k) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' k) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' k hζirr (hkζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_eq_zero (fun i' _ => hrow i'),
    OddOrder.RepresentationTheory.inner_smul_right, hαζc, mul_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}, μ_j − dζ̄) = 1`** (M-side, `0 < j < w₂`): the diagonal
companion of `muGridAlpha_inner_muColumn_sub_conj`, where `μ_j = ∑_{0≤i'<w₁} μ_{i'j}` is the
`W₂`-column-`j` sum (the column of `μ_{ij}` itself).  Within column `j` the `μ_{i'j}` are
orthonormal (`muGrid_inner_self`/`muGrid_inner_within_column`), so `(μ_{ij}, μ_j) = 1`; `μ_{i0}` and
`ζ` are cross-column resp. degree-distinct from column `j` (`muGrid_inner_cross_column`, `hjζ`), so
`(δμ_{i0}, μ_j) = (nζ, μ_j) = 0`, giving `(α_{ij}, μ_j) = 1`; and `(α_{ij}, ζ̄) = 0` (degree
distinctness + `(ζ, ζ̄) = 0`).  Hence `(α_{ij}, μ_j − dζ̄) = 1`.

This is the `M`-side opening `1 = (α_{ij}, μ_j − dζ̄)` of Peterfalvi (10.6)(a), feeding the
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1` step (then Peterfalvi (5.8) gives the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj) = 1 := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr
      (by rw [hconj1]; exact hjζ i)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr
      (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'j}) = δ_{i,i'}`: within-column orthonormal; `μ_{i0}, ζ` off column `j`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' j) = (if i = i' then (1 : ℂ) else 0) := by
    intro i'
    have h1 : ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i j
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd j hii'
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hj0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' j) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' j) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' j hζirr (hjζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, hαζc,
    mul_zero, sub_zero, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i')]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) M-side inner product** `(α_{ij}, μ₀ − ζ) = n − δ`, where `μ₀ = ∑_{i'} μ_{i'0}`
is the column-`0` sum (`0 < j`).  Within column `0` the `μ_{i'0}` are orthonormal, so only `i' = i`
survives in `(δ·μ_{i0}, μ₀)`, giving `−δ`; `μ_{ij}` (column `j ≠ 0`) is cross-column to column `0`;
`ζ` (degree `w₁ > 1`) is degree-distinct from every `μ_{i'0}` (degree `1`) and from `μ_{ij}`/`μ_{i0}`,
and `(ζ, ζ) = 1` gives `(α_{ij}, ζ) = −n`.  Hence `(α_{ij}, μ₀ − ζ) = −δ − (−n) = n − δ`.  This is the
`M`-side of the (11.8.5) two-way computation of `((μ₀ − ζ)^τ, α_{ij}^τ) = (μ₀ − ζ, α_{ij})` (Dade
isometry), which together with the `G`-side (via (11.8.4)) forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) = (n : ℂ) - (δ : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hcol0ζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0 1 ≠ ζ 1 := fun i' => by
    rw [hyp.muGrid_zero_column_apply_one hG hodd i', hζ1]
    intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  -- `(α_{ij}, ζ) = −n`: `μ_{ij}`, `μ_{i0}` degree-distinct from `ζ`, and `(ζ, ζ) = 1`.
  have hαζ : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ = -(n : ℂ) := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
    have a3 : ClassFunction.inner ζ ζ = 1 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero, mul_one, zero_sub]
  -- `(α_{ij}, μ_{i'0}) = −δ·[i = i']`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' 0) = (if i = i' then -(δ : ℂ) else 0) := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hj0
    have h2 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (hyp.muGrid hG hodd i' 0)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i 0
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd 0 hii'
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' 0) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' 0) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' 0 hζirr (hcol0ζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, zero_sub, sub_zero]
    by_cases hii' : i = i' <;> simp [hii']
  rw [ClassFunction.inner_sub_right, hαζ, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i'), Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- **§10 support of an equal-degree difference in `S`** (Peterfalvi (10.5)/(11.8)): for two members
`ζ₁, ζ₂ ∈ S = inducedFamily M` of *equal degree* (`ζ₁(1) = ζ₂(1)`), the difference `ζ₁ − ζ₂` is
supported in `A_0(M)`.  Both are induced from the normal `M' = [M,M]`, hence vanish off `M'`; and
`(ζ₁ − ζ₂)(1) = 0`, so the support lies in `M'^# = M' − {1}`.  Every element of `M'^#` centralizes
itself, hence lies in `A(M) ⊆ A_0(M)` (the left disjunct of `typePA0`, as in `muGrid_alpha_support`).

This is the `hsuppdiff` precondition feeding the (5.7)/(1.4) equal-degree coherence producer
`coherentEqualDegree_fromDade` on the degree-`w₁` subfamily `S(HC)` (Peterfalvi (11.8)); the
conjugate-pair special case `ζ₂ = ζ̄` is `zeta_sub_conj_support`, used in the `(α_{ij}^τ, (ζ−ζ̄)^τ)`
step of the (10.5) `a = 0` argument. -/
theorem Hypothesis.inducedFamily_sub_support [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {ζ₁ ζ₂ : ClassFunction ↥M ℂ} (hζ₁ : ζ₁ ∈ inducedFamily M) (hζ₂ : ζ₂ ∈ inducedFamily M)
    (hdeg : ζ₁ 1 = ζ₂ 1) :
    (ζ₁ - ζ₂).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ₁, _hθ₁ne, hζ₁eq⟩ := hζ₁
  obtain ⟨θ₂, _hθ₂ne, hζ₂eq⟩ := hζ₂
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζ₁vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₁ w = 0 := fun {w} hw => by
    rw [hζ₁eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hζ₂vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₂ w = 0 := fun {w} hw => by
    rw [hζ₂eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `ζ₁ z = ζ₂ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hζ₁vanish hzK, hζ₂vanish hzK, sub_zero]
  -- `z ≠ 1`: `(ζ₁ − ζ₂)(1) = 0` by equal degree.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hdeg, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **§10 support of `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the difference `ζ − ζ̄` of a
degree-`w₁` irreducible `ζ ∈ S` and its conjugate is supported in `A_0(M)`.  The conjugate-pair
special case of `inducedFamily_sub_support`: `ζ̄ = ζ.conj ∈ S` (`inducedFamily_closedUnderConjugate`)
has the same degree `ζ̄(1) = ζ(1)` (the degree is a real natural number).

This makes `ζ − ζ̄` `A_0`-supported, so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`) in the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄)` step. -/
theorem Hypothesis.zeta_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    (ζ - ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  exact hyp.inducedFamily_sub_support hζS (inducedFamily_closedUnderConjugate M hζS) hconj1.symm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`**: the Dade-image inner product, transferred to
the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `ζ − ζ̄` (`zeta_sub_conj_support`) are
`A_0`-supported, so the Dade isometry `τ` preserves their inner product
(`tau_inner_eq_of_supported`), and the `M`-side value is `−n`
(`muGridAlpha_inner_zeta_sub_conj`).  This is the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step
of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (ζ - ζ.conj)) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_inner_eq_of_supported hαsupp hζsupp]
  exact hyp.muGridAlpha_inner_zeta_sub_conj hG hodd i j hζirr hζne hdζ h0ζ

open scoped FiniteInduce in
/-- **§10 support of `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the column sum
`μ_k = ∑_{i} μ_{ik}` (an induced character of degree `dw₁`) minus `d` times the conjugate `ζ̄` (also
degree `w₁`) is supported in `A_0(M)`.  Both `μ_k` and `ζ̄` are induced from the normal `M'`, hence
vanish off `M'` (`muGrid_column_sum_vanishes_off_derived`, induced-from-`M'` for `ζ̄`); and the
degrees cancel, `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`, so the support lies in `M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `zeta_sub_conj_support`: it makes `μ_k − dζ̄` `A_0`-supported, so the Dade
isometry `τ` transfers `(α_{ij}, μ_k − dζ̄) = (α_{ij}^τ, (μ_k − dζ̄)^τ)` with no adjunction. -/
theorem Hypothesis.muColumn_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- evaluation of a finite sum of class functions at a point is the sum of values.
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i k) w = ∑ i ∈ s, hyp.muGrid hG hodd i k w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_k z = ζ̄ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hzK, hζvanish hzK, star_zero,
      mul_zero, sub_zero]
  -- `z ≠ 1`: `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hζ1,
      hsumapply 1, Finset.sum_congr rfl (fun i _ => hcol1 i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, star_natCast]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **`∑_{i'} μ_{i'0} − ζ` is `A_0`-supported** (Peterfalvi (11.8.5)).  The column-`0` sum `μ₀` and the
degree-`w₁` irreducible `ζ` are both induced from the normal `M' = [M,M]`, so both vanish off `M'`;
and `(μ₀ − ζ)(1) = w₁·1 − w₁ = 0`, so the support lies in `M'^# ⊆ A_0`.  Companion of
`muColumn_sub_conj_support` with `k = 0`, `d = 1` and `ζ` in place of `ζ̄`, used to transport the
(11.8.5) `M`-side inner product `(α_{ij}, μ₀ − ζ)` to the Dade image via `tau_inner_eq_of_supported`. -/
theorem Hypothesis.zeroColumnSum_sub_zeta_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK, hζvanish hzK, sub_zero]
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `M`-side transferred to the Dade image** `(α_{ij}^τ, (μ₀ − ζ)^τ) = n − δ`,
where `μ₀ = ∑_{i'} μ_{i'0}`.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ₀ − ζ`
(`zeroColumnSum_sub_zeta_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `n − δ`
(`muGridAlpha_inner_zeroColumnSum_sub_zeta`).  Under the (11.8.4) by-contradiction hypothesis
`(μ₀ − ζ)^τ = ∑ ω_{r0}^σ − ζ^{τ₁}`, this becomes `(α_{ij}^τ, ∑ ω_{r0}^σ − ζ^{τ₁}) = n − δ`, whose
`G`-side expansion (via the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`) equals
`n − δ − a`, forcing `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (n : ℂ) - (δ : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.zeroColumnSum_sub_zeta_support hG hodd hζS hζirr hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_zeroColumnSum_sub_zeta hG hodd i j hj0 hζirr hζ1 hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0`** (`0 < k < w₂`, `k ≠ j`): the Dade-image
inner product, transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ_k − dζ̄`
(`muColumn_sub_conj_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `0`
(`muGridAlpha_inner_muColumn_sub_conj`).

Since `μ_k`, `ζ̄ ∈ ℤ[S]`, on the coherent side `(μ_k − dζ̄)^τ = (μ_k − dζ̄)^{τ₁} = μ_k^{τ₁} − dζ̄^{τ₁}`
(the coherent extension agrees with `τ` on this `A_0`-supported lattice element), so this is the
`(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = 0` step of the (10.5) `a = 0` argument, whence
`(α_{ij}^τ, μ_k^{τ₁}) = da`.  No Dade–coherence adjunction is needed: the combination `μ_k − dζ̄`,
not `μ_k` alone, is supported. -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj)) = 0 := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_sub_conj hG hodd i j k hjk hk0 hζirr hζne hkζ hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, (μ_j − dζ̄)^τ) = 1`** (diagonal, `0 < j < w₂`): the
Dade-image inner product transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and
the diagonal column `μ_j − dζ̄` (`muColumn_sub_conj_support`) are `A_0`-supported, so `τ` preserves
the inner product (`tau_inner_eq_of_supported`); the `M`-side value is `1` (the diagonal
`muGridAlpha_inner_muColumn_self_sub_conj`, vs `0` for the off-diagonal companion).

This is the opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a) (on the coherent
side `(μ_j − dζ̄)^τ = μ_j^{τ₁} − dζ̄^{τ₁}`, `tau_muColumn_sub_conj_eq_tau1`), which by Peterfalvi
(5.8) gives the summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion). -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj)) = 1 := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd j hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_self_sub_conj hG hodd i j hj0 hζirr hζne hjζ h0ζ

/-- **§10 τ/τ₁ compatibility on `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(ζ − ζ̄)^τ` equals `ζ^{τ₁} − ζ̄^{τ₁}` for the coherent extension `τ₁`.  Since `ζ ∈ S` and
`ζ̄ ∈ S` (`inducedFamily_closedUnderConjugate`), the difference `ζ − ζ̄` lies in the supported
lattice `ℤ[S, A_0]` (`zeta_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); linearity of `τ₁` (`map_sub`) then splits the image.

This converts the pure-`τ` identity `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`
(`muGridAlpha_tau_inner_zeta_sub_conj`) into the `τ₁` form, giving `(α_{ij}^τ, ζ̄^{τ₁}) = a`
(with `a − n := (α_{ij}^τ, ζ^{τ₁})`) in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    hyp.tau (ζ - ζ.conj) = coh.tau1 ζ - coh.tau1 ζ.conj := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  rfl

open scoped FiniteInduce in
/-- **§10 τ/τ₁ compatibility on `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(μ_k − dζ̄)^τ` equals `μ_k^{τ₁} − dζ̄^{τ₁}` for the coherent extension `τ₁`.  Since
`μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`
(`inducedFamily_closedUnderConjugate`), the combination `μ_k − dζ̄` lies in the supported lattice
`ℤ[S, A_0]` (`muColumn_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); `τ₁`-linearity (`map_sub`, `map_nsmul`) then splits the image.

This converts `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) into the
`τ₁` form, giving `(α_{ij}^τ, μ_k^{τ₁}) = da` in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_muColumn_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      = coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • coh.tau1 ζ.conj := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hsmulmem : (d : ℂ) • ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hspanζc d
  have hmem : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanμ hsmulmem,
      hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- **The (10.5) `a = 0` numeric core.**  If `a ∈ ℤ` satisfies the Cauchy–Schwarz bound
`(d·a)² ≤ (2+n²)w₁` with `d = nw₁ + δ`, `δ = ±1`, `w₁ ≥ 3` (odd, since `|G|` is odd) and `n ≥ 2`
(even and positive), then `a = 0`.  Else `a² ≥ 1` gives `d² ≤ (2+n²)w₁`, but `d² = (nw₁+δ)² >
(2+n²)w₁` for `w₁ ≥ 3, n ≥ 2` — a contradiction (Peterfalvi: "`n < 2`, contradicting `n` even,
`n > 0`"). -/
private theorem cauchySchwarz_numeric {d n w₁ : ℕ} {δ a : ℤ}
    (hd : (d : ℤ) = (n : ℤ) * (w₁ : ℤ) + δ) (hδ : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ w₁) (hn2 : 2 ≤ n)
    (hbound : ((d : ℝ) * (a : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ)) : a = 0 := by
  by_contra ha
  have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ a ^ 2 := by
      rcases lt_or_gt_of_ne ha with h | h <;> nlinarith [sq_nonneg a]
    exact_mod_cast this
  have hdpos : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hd2 : ((d : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ) := by nlinarith [hbound, ha1, hdpos]
  have hdR : (d : ℝ) = (n : ℝ) * (w₁ : ℝ) + (δ : ℝ) := by exact_mod_cast hd
  have hw1R : (3 : ℝ) ≤ (w₁ : ℝ) := by exact_mod_cast hw1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hδR : (δ : ℝ) = 1 ∨ (δ : ℝ) = -1 := by rcases hδ with h | h <;> [left; right] <;> exact_mod_cast h
  rw [hdR] at hd2
  rcases hδR with hδ1 | hδ1 <;> rw [hδ1] at hd2 <;>
    nlinarith [hd2, hw1R, hn2R, mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) - 2) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3)]

/-- **Cauchy–Schwarz for the class-function inner product** (real-part form): for class functions
`φ, ψ` of any finite group `H`, `⟨φ, ψ⟩.re² ≤ ⟨φ, φ⟩.re · ⟨ψ, ψ⟩.re`.

Proof by the discriminant: the real quadratic `t ↦ ⟨φ − tψ, φ − tψ⟩.re = ⟨ψ,ψ⟩.re·t² −
2⟨φ,ψ⟩.re·t + ⟨φ,φ⟩.re` is `≥ 0` for every real `t` (positive semidefiniteness,
`inner_self_re_nonneg`), so its discriminant is `≤ 0` (`discrim_le_zero`).  This is the
`(α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖²` of the (10.5) `a = 0` argument. -/
private theorem classFunction_inner_re_sq_le {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (φ ψ : ClassFunction H ℂ) :
    (ClassFunction.inner φ ψ).re ^ 2
      ≤ (ClassFunction.inner φ φ).re * (ClassFunction.inner ψ ψ).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (ClassFunction.inner ψ ψ).re * (t * t)
      + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
    intro t
    have key : ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)
        = ClassFunction.inner φ φ - (t : ℂ) * ClassFunction.inner φ ψ
          - (t : ℂ) * ClassFunction.inner ψ φ + (t : ℂ) * (t : ℂ) * ClassFunction.inner ψ ψ := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        Complex.star_def, Complex.conj_ofReal]
      ring
    have hre : (ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)).re
        = (ClassFunction.inner ψ ψ).re * (t * t)
          + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
      rw [key, OddOrder.RepresentationTheory.inner_conj_symm φ ψ]
      simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      ring
    rw [← hre]
    exact inner_self_re_nonneg _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, μ_k^{τ₁}) = da`** (`0 < k < w₂`, `k ≠ j`): the key inner
product of the (10.5) `a = 0` argument, where `a := (α_{ij}^τ, ζ^{τ₁}) + n`.

From the two pure-`τ` Dade-image identities and their `τ₁` forms:
* `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n` (`muGridAlpha_tau_inner_zeta_sub_conj`) with `(ζ−ζ̄)^τ = ζ^{τ₁}−ζ̄^{τ₁}`
  (`tau_zeta_sub_conj_eq_tau1`) gives `(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n = a`;
* `(α_{ij}^τ, (μ_k−dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) with
  `(μ_k−dζ̄)^τ = μ_k^{τ₁}−dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) gives
  `(α_{ij}^τ, μ_k^{τ₁}) = d·(α_{ij}^τ, ζ̄^{τ₁}) = d·a`.

This `d·a` is the `(α_{ij}^τ, μ_k^{τ₁})` term of the Cauchy–Schwarz bound
`d²a² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
      = (d : ℂ) * (ClassFunction.inner
          (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
          (coh.tau1 ζ) + (n : ℂ)) := by
  -- `(α^τ, ζ̄^{τ₁}) = (α^τ, ζ^{τ₁}) + n` from the `ζ − ζ̄` identity.
  have h12 := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
    ClassFunction.inner_sub_right] at h12
  -- `(α^τ, μ_k^{τ₁}) = d·(α^τ, ζ̄^{τ₁})` from the `μ_k − dζ̄` identity.
  have h45 := hyp.muGridAlpha_tau_inner_muColumn_sub_conj hG hodd i hj0 k hjk hk0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1,
    ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at h45
  linear_combination h45 - (d : ℂ) * h12

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`** (diagonal): the coherent-side
form of the G-side diagonal inner product `muGridAlpha_tau_inner_muColumn_self_sub_conj`.  Since
`μ_j = ∑_i μ_{ij} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`, the supported
combination `(μ_j − dζ̄)^τ` splits as `μ_j^{τ₁} − dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`).

This is the reduction opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a);
dropping the `⊥ Im σ` terms (`ζ^{τ₁}, ζ̄^{τ₁} ⊥ Im σ`, `ζ^{τ₁} ⊥ μ_j^{τ₁}`) gives
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1`, and Peterfalvi (5.8) then yields the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion, still gated on (5.8)). -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn_self_sub_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ))
    (hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j)
          - (d : ℂ) • coh.tau1 ζ.conj) = 1 := by
  have hG_side := hyp.muGridAlpha_tau_inner_muColumn_self_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj h0ζ hjζ hcol1
  rwa [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd j coh hζS hζirr hcol1 hζ1 hdj1] at hG_side

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖μ_k^{τ₁}‖² = w₁`** (`0 < k < w₂`): the coherent extension `τ₁` is an
isometry on `ℤ[S]`, and `μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`), so
`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁` (`coherent.extension_inner_eq` + `muGrid_column_sum_inner_self`).

This is the `‖μ_k^{τ₁}‖²` factor of the (10.5) Cauchy–Schwarz bound
`d²a² = (α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muColumn_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ) := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  show ClassFunction.inner (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
      (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ)
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan]
  exact hyp.muGrid_column_sum_inner_self hG hodd k

open scoped FiniteInduce in
/-- **§10 `α_{ij}^τ` is a virtual character of `G`** (Peterfalvi (10.5)): `α_{ij} = μ_{ij} − δ·μ_{i0}
− n·ζ` is a virtual character of `M` (`muGrid_isIrreducible`, `ζ` irreducible) and is `A_0`-supported
(`muGrid_alpha_support`), so its Dade image lies in `ℤ[Irr G]`
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`).  Together with `ζ^{τ₁}, μ_k^{τ₁} ∈ ℤ[Irr G]` this
makes the inner products of the `a = 0` argument integers. -/
theorem Hypothesis.muGridAlpha_tau_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2}
    (hj0 : j ≠ 0) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr G := by
  haveI := hyp.finiteG
  have hαZ : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr ↥M := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hyp.muGrid_isIrreducible hG hodd i j).mem_ZIrr ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr δ
    · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζirr.mem_ZIrr n
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj hsupp hαZ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `a = 0`**: the integer `a = (α_{ij}^τ, ζ^{τ₁}) + n` of the (10.5) Cauchy–
Schwarz argument vanishes, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.

`(α_{ij}^τ, ζ^{τ₁}) = m ∈ ℤ` (`α_{ij}^τ, ζ^{τ₁} ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`); set `a = m + n`.
Then `(α_{ij}^τ, μ_k^{τ₁}) = da` (`muGridAlpha_tau1_inner_muColumn`), and Cauchy–Schwarz
(`classFunction_inner_re_sq_le`) with `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) and
`‖μ_k^{τ₁}‖² = w₁` (`muColumn_tau1_inner_self`) gives `(da)² ≤ (2+n²)w₁`.  By the numeric core
(`cauchySchwarz_numeric`; `d = nw₁+δ`, `δ = ±1`, `w₁ ≥ 3` odd, `n ≥ 2` even) this forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau1_zeta_eq_neg_n [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 ζ) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- `(α^τ, ζ^{τ₁}) = m ∈ ℤ`.
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζZ : coh.tau1 ζ ∈ ZIrr G := coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hαZ hζZ
  -- `(α^τ, μ_k^{τ₁}) = d·(m + n)` and the two norms.
  have hda := hyp.muGridAlpha_tau1_inner_muColumn hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1
  rw [hm] at hda
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hnorm_mu := hyp.muColumn_tau1_inner_self hG hodd k coh hdk1
  -- Cauchy–Schwarz, with the three inner products substituted.
  have hcs := classFunction_inner_re_sq_le
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
    (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
  rw [hda, hnorm_a, hnorm_mu] at hcs
  have hre1 : ((d : ℂ) * ((m : ℂ) + (n : ℂ))).re = (d : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hre2 : ((2 : ℂ) + (n : ℂ) ^ 2).re = 2 + (n : ℝ) ^ 2 := by
    simp [Complex.add_re, pow_two, Complex.mul_re, Complex.mul_im]
  rw [hre1, hre2, Complex.natCast_re] at hcs
  -- Apply the numeric core with `a = m + n`.
  have ha0 : m + (n : ℤ) = 0 := by
    refine cauchySchwarz_numeric (d := d) (n := n) (w₁ := hyp.w1) (δ := δ) (a := m + n)
      (by linarith [hnf]) hδpm hw1 hn2 ?_
    push_cast
    convert hcs using 2
  rw [hm]
  have hmn : m = -(n : ℤ) := by omega
  rw [hmn]; push_cast; ring

open scoped FiniteInduce in
/-- **§10 `‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.5)): the coherent extension `τ₁` is an isometry on
`ℤ[S]` and `ζ ∈ S` is irreducible, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`. -/
theorem Hypothesis.zeta_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 := by
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  show ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ) = 1
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

open scoped FiniteInduce in
/-- **`ζ^{τ₁} ⊥ ζ̄^{τ₁}`** (Peterfalvi (10.6)(a) reduction): the coherent images of the degree-`w₁`
irreducible `ζ` and its conjugate `ζ̄` are orthogonal.  As `ζ, ζ̄ ∈ 𝒮`
(`inducedFamily_closedUnderConjugate`) and `τ₁ = coh.extension` is an isometry on `ℤ[𝒮]`
(`extension_inner_eq`), `(ζ^{τ₁}, ζ̄^{τ₁}) = (ζ, ζ̄) = 0` (`ζ ≠ ζ̄`, both irreducible).

One of the three orthogonalities dropping out of the (10.6)(a) reduction `(α_{ij}^τ, μ_j^{τ₁} −
dζ̄^{τ₁}) = (δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁})`; the remaining `ζ̄^{τ₁} ⊥ Im σ`
is the §5 (5.3.b)/(5.5) input still to be formalised. -/
theorem Hypothesis.zeta_tau1_inner_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζcS
  show ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
  rw [coh.coherent.extension_inner_eq _ _ hspan hspanc,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj, if_neg (Ne.symm hζne)]

open scoped FiniteInduce in
/-- **`ζ^{τ₁} ⊥ μ_k^{τ₁}`** (Peterfalvi (10.6)(a) reduction): the coherent image of the degree-`w₁`
irreducible `ζ` is orthogonal to that of the column character `μ_k = ∑_i μ_{ik} ∈ 𝒮`.  By the
isometry, `(ζ^{τ₁}, μ_k^{τ₁}) = (ζ, ∑_i μ_{ik}) = ∑_i (ζ, μ_{ik}) = 0`, each summand `0` by the
degree mismatch `μ_{ik}(1) = d ≠ w₁ = ζ(1)` (`muGrid_inner_eq_zero_of_apply_one_ne` + conjugate
symmetry).  A second orthogonality of the (10.6)(a) reduction (see `zeta_tau1_inner_conj`). -/
theorem Hypothesis.zeta_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 ζ)
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0 := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  show ClassFunction.inner (coh.coherent.extension ζ)
    (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0
  rw [coh.coherent.extension_inner_eq _ _ hspanζ hspanμ,
    OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h0 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i k hζirr (hkζ i)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`** where `X = α_{ij}^τ + n·ζ^{τ₁}`: with
`(α_{ij}^τ, ζ^{τ₁}) = −n` (`a = 0`, `muGridAlpha_tau1_zeta_eq_neg_n`), `‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`zeta_tau1_inner_self`):
`(X, ζ^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n‖ζ^{τ₁}‖² = −n + n = 0`, and
`‖X‖² = ‖α_{ij}^τ‖² + 2n·(α_{ij}^τ, ζ^{τ₁}) + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.

So `α_{ij}^τ = X − n·ζ^{τ₁}` with `X` a virtual character of `G` orthogonal to `ζ^{τ₁}` of squared
norm `2` — the decomposition the (10.5) `(v)`/`(vi)` argument (`NC(ψ) ≤ 4`, (3.8)) operates on. -/
theorem Hypothesis.muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) (coh.tau1 ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) = 2 := by
  have ha0 := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have ha0' : ClassFunction.inner (coh.tau1 ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)) = -(n : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, ha0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, ha0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha0, ha0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), (vi) precursor — `ψ` vanishes on `V`**: the virtual character
`ψ = α_{ij}^τ + n·ζ^{τ₁} − δ(ω_{ij}^σ − ω_{i0}^σ)` (this is `X − δ(ω^σ diff)` of the (10.5) endgame,
since `α^τ = X − nζ^{τ₁}`) vanishes on `V`.

Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV` (`α^τ = δ(ω^σ diff)` on `V`, by
(3.2.c)/(4.3.c) and the definition of `τ`) with the vanishing of `ζ^{τ₁}` on `V` (`hζvanish`, the
§5/§7 input of (10.5): "By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").  The remaining
step to `alpha_tau_image` is `NC(ψ) ≤ 4 < 2·inf(w₁,w₂)` + Theorem (3.8)
(`S05.sigmaCoeff_trichotomy`, requiring a `FullDadeApplication` for the type-`P` `TICyclicHypothesis`)
forcing `ψ ⊥ ω^σ`, hence `ψ = 0`. -/
theorem Hypothesis.muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζvanish v hv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(ζ − ζ̄)^τ` vanishes on `V`** (the "by definition of `τ`" step underlying
the (5.3.b)/(5.5)/(3.2.d) `ζ^{τ₁}`-vanishing argument).  Since `ζ` is induced from the normal
`M' = [M,M]` and every `v ∈ V = typePV` lies outside `M'` (`typePData_typePV_not_mem_derived`),
both `ζ` and its conjugate `ζ̄` vanish at `v`; the difference `ζ − ζ̄` is `A_0(M)`-supported
(`zeta_sub_conj_support`), so the Dade isometry restores its value at `v`
(`tau_apply_of_mem_typePV`), giving `(ζ − ζ̄)^τ(v) = 0`. -/
theorem Hypothesis.tau_zeta_sub_conj_vanishes_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (ζ - ζ.conj) v = 0 := by
  haveI := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  have hsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` (induced from the normal `M'`) vanishes at `v ∉ M'`, hence so does `ζ̄ = star ∘ ζ`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hζv, star_zero, sub_zero]

open scoped FiniteInduce in
/-- **`(χ − χ̄)^τ` is orthogonal to every aligned `σ`-grid entry** (Peterfalvi (5.3.b),
generalised from `ζ` to any irreducible member of `S`): the difference image vanishes on `V`
(`tau_zeta_sub_conj_vanishes_on_typePV`), lies in `ℤ[Irr G]` with norm `2`, so by the
`(3.7)/(3.8)` all-zero trichotomy (`sigmaCoeff_eq_zero_of_vanishOnV`) every `σ`-coefficient —
in particular every `⟨·, ω_{ik}^σ⟩` — vanishes.  This is the (5.2.e) member-vs-column
orthogonality core (issue 2022). -/
theorem Hypothesis.tau_chidiff_inner_alignedOmega_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {χ : ClassFunction ↥M ℂ}
    (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (i : Fin hyp.w1) (k : Fin hyp.w2) :
    ClassFunction.inner (hyp.tau (χ - χ.conj))
      (hyp.alignedOmegaSigmaGrid hG hodd i k) = 0 := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `T`-facts
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hχne : χ.conj ≠ χ := inducedFamily_hasNoRealCharacters hModd hχS
  have hvanish : ∀ w ∈ tic.V, hyp.tau (χ - χ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hχS hχirr hw
  have hsupp := hyp.zeta_sub_conj_support hG hodd hχS hχirr
  have hTZ : hyp.tau (χ - χ.conj) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp ?_
    exact Submodule.sub_mem _ hχirr.mem_ZIrr hχcirr.mem_ZIrr
  have hT2 : ClassFunction.inner (hyp.tau (χ - χ.conj)) (hyp.tau (χ - χ.conj)) = 2 := by
    have hset : ∀ s ∈ ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : χ - χ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
        ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) from rfl, hpres,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    have h11 : ClassFunction.inner χ χ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ⟨χ, hχirr⟩
    have hcc : ClassFunction.inner χ.conj χ.conj = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ.conj, hχcirr⟩ : IrreducibleCharacter ↥M) ⟨χ.conj, hχcirr⟩
    have hcross : ClassFunction.inner χ χ.conj = 0 :=
      inducedFamily_pairwiseOrthogonal hχS hχcS (Ne.symm hχne)
    have hcross' : ClassFunction.inner χ.conj χ = 0 :=
      inducedFamily_pairwiseOrthogonal hχcS hχS hχne
    rw [h11, hcc, hcross, hcross']
    ring
  -- engine + `P`-enumeration
  have hall := tic.sigmaCoeff_eq_zero_of_vanishOnV hVeq app hTZ hT2 hvanish
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hk := hall (P k)
  rw [show tic.sigmaCoeff hVeq app (hyp.tau (χ - χ.conj)) (P k)
      = ClassFunction.inner (hyp.tau (χ - χ.conj)) (tic.chiFam hVeq app (P k)) from rfl,
    ← hP k] at hk
  exact hk

/-- **Norm-`1` projection orthogonality.**  If `a, s ∈ ℤ[Irr G]` with `‖a‖² = ‖b‖² = ‖s‖² = 1`,
`a ⊥ b`, and the difference `a − b` is orthogonal to `s`, then `a ⊥ s`.

Since `⟨a,s⟩ = ⟨b,s⟩ =: x ∈ ℤ` (`a, s ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`), the projection norm
`‖s − x·a − x·b‖² = 1 − 2x² ≥ 0` forces `2x² ≤ 1`, hence `x = 0`.  This is the integral-geometry
core that lets the §10 `ζ^{τ₁}`-vanishing argument bypass the (5.4)/(5.5) `R(ζ)` machinery:
applied with `a = ζ^{τ₁}`, `b = ζ̄^{τ₁}`, `s = ω^σ`, the orthogonality of `(ζ − ζ̄)^τ = a − b` to the
`σ`-image (Peterfalvi (5.3.b), via (3.8)) gives `ζ^{τ₁} ⊥ ω^σ` directly. -/
theorem inner_left_eq_zero_of_inner_sub_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b s : ClassFunction G ℂ} (haZ : a ∈ ZIrr G) (hsZ : s ∈ ZIrr G)
    (ha1 : ClassFunction.inner a a = 1) (hb1 : ClassFunction.inner b b = 1)
    (hs1 : ClassFunction.inner s s = 1) (hab : ClassFunction.inner a b = 0)
    (hdiff : ClassFunction.inner (a - b) s = 0) :
    ClassFunction.inner a s = 0 := by
  obtain ⟨x, hx⟩ := ClassFunction.inner_mem_ZIrr_int haZ hsZ
  -- `⟨b,s⟩ = ⟨a,s⟩ = x` from `⟨a − b, s⟩ = 0`.
  have hbs : ClassFunction.inner b s = (x : ℂ) := by
    rw [ClassFunction.inner_sub_left, hx, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- the conjugate-symmetric companions (`x` is real, being an integer).
  have hsa : ClassFunction.inner s a = (x : ℂ) := by
    rw [inner_conj_symm a s, hx, star_intCast]
  have hsb : ClassFunction.inner s b = (x : ℂ) := by
    rw [inner_conj_symm b s, hbs, star_intCast]
  have hba : ClassFunction.inner b a = 0 := by
    rw [inner_conj_symm a b, hab, star_zero]
  -- the projection norm `‖s − x·a − x·b‖² = 1 − 2x²`.
  have key : ClassFunction.inner (s - (x : ℂ) • a - (x : ℂ) • b)
      (s - (x : ℂ) • a - (x : ℂ) • b) = 1 - 2 * (x : ℂ) ^ 2 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha1, hb1, hs1, hab, hba, hx, hbs, hsa, hsb, star_intCast]
    ring
  have hnn := inner_self_re_nonneg (s - (x : ℂ) • a - (x : ℂ) • b)
  rw [key] at hnn
  have hcast : (1 : ℂ) - 2 * (x : ℂ) ^ 2 = ((1 - 2 * x ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.intCast_re] at hnn
  have hint : (0 : ℤ) ≤ 1 - 2 * x ^ 2 := by exact_mod_cast hnn
  have h0 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
  have hsq : x ^ 2 = 0 := by omega
  have hx0 : x = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  rw [hx, hx0, Int.cast_zero]

open scoped FiniteInduce in
/-- **Per-element orthogonality of a difference-image family** (Peterfalvi (5.5)-style upgrade):
if `s` is a norm-`1` virtual character orthogonal to the *sum* `(χ−χ̄)^τ = ∑ R(χ)`, then `s` is
orthogonal to each element of `R(χ)`.  With `β := T − α` (the complementary part), `α − (−β) = T`
and the norm-`1` projection lemma applies. -/
theorem OrthonormalCharacterImageFamily.elt_inner_eq_zero {M : Subgroup G} [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G} {χ : ClassFunction ↥M ℂ}
    (R : OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily τ χ)
    {α : ClassFunction G ℂ} (hα : α ∈ R.imageSet)
    {s : ClassFunction G ℂ} (hsZ : s ∈ ZIrr G)
    (hs1 : ClassFunction.inner s s = 1)
    (hT2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2)
    (hTs : ClassFunction.inner (τ (χ - χ.conj)) s = 0) :
    ClassFunction.inner α s = 0 := by
  classical
  set T := τ (χ - χ.conj) with hT
  have hTsum : T = ∑ β ∈ R.imageSet, β := R.image_eq
  have hαZ : α ∈ ZIrr G := R.mem_ZIrr α hα
  have hα1 : ClassFunction.inner α α = 1 := by
    have := R.orthonormal α hα α hα
    rwa [if_pos rfl] at this
  have hTZ : T ∈ ZIrr G := by
    rw [hTsum]
    exact Submodule.sum_mem _ fun β hβ => R.mem_ZIrr β hβ
  have hαT : ClassFunction.inner α T = 1 := by
    rw [hTsum, OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single α]
    · rw [hα1]
    · intro β hβ hne
      have := R.orthonormal α hα β hβ
      rwa [if_neg (fun h => hne h.symm)] at this
    · intro habs
      exact absurd hα habs
  -- `b := −(T − α)`; then `α − b = T`
  set b : ClassFunction G ℂ := -(T - α) with hb
  have hbZ : b ∈ ZIrr G := by
    rw [hb]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ hTZ hαZ)
  have hbb : ClassFunction.inner b b = 1 := by
    have hexp : ClassFunction.inner (T - α) (T - α)
        = ClassFunction.inner T T - ClassFunction.inner T α
          - ClassFunction.inner α T + ClassFunction.inner α α := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]
      ring
    have hTα : ClassFunction.inner T α = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hαT]
      norm_num
    rw [hb, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
      hexp, hT2, hTα, hαT, hα1]
    ring
  have hαb : ClassFunction.inner α b = 0 := by
    have hTα : ClassFunction.inner α (T - α) = 0 := by
      rw [ClassFunction.inner_sub_right, hαT, hα1]
      ring
    rw [hb, ClassFunction.inner_neg_right, hTα, neg_zero]
  have hdiff : ClassFunction.inner (α - b) s = 0 := by
    have : α - b = T := by
      rw [hb]
      abel
    rw [this]
    exact hTs
  exact inner_left_eq_zero_of_inner_sub_eq_zero hαZ hsZ hα1 hbb hs1 hαb hdiff


open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`** (the genuine §5/§7 input, the textbook's
"By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").

Reorganized to avoid the (5.4)/(5.5) `R(ζ)`-extraction machinery, using the integral norm-`1`
projection (`inner_left_eq_zero_of_inner_sub_eq_zero`) instead:
* `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` vanishes on `V` (`tau_zeta_sub_conj_vanishes_on_typePV`) and has
  `NC ≤ 2 < min(w₁, w₂)`: each of `ζ^{τ₁}`, `ζ̄^{τ₁}` is a norm-`1` virtual character with at most
  one nonzero `σ`-coefficient (`ncard_inner_chiFam_ne_zero_le_one`), so by the (3.8) corollary
  `sigmaCoeff_eq_zero_of_sigmaNC_lt` every `σ`-coefficient of `(ζ − ζ̄)^τ` vanishes (Peterfalvi
  (5.3.b));
* `ζ^{τ₁}, ζ̄^{τ₁}` are orthonormal norm-`1` virtual characters (coherence isometry on `ℤ[S]`), so
  the projection lemma upgrades `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0` to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0`
  (Peterfalvi (5.5));
* orthogonality to every `χ_{pq} = ω_{pq}^σ` forces `ζ^{τ₁}` to vanish on `V` (Peterfalvi (3.2.d),
  `eq_zero_of_mem_V_of_inner_chiFam_eq_zero`).

This is the last analytic input of the (10.5) Dade-image identity; with the value-on-`V` leg it
gives `ψ = X − δ(ω^σ diff)` vanishing on `V` (`muGridPsi_vanishes_on_typePV`), unconditionally. -/
theorem Hypothesis.tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 ζ v = 0 := by
  haveI := hyp.finiteG
  classical
  -- the §5 `G`-level TI-cyclic hypothesis + Dade application (the ready (10.5) `σ` pattern).
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `ζ̄ ∈ S` irreducible; the `τ₁`-images are orthonormal norm-`1` virtual characters of `G`.
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`.
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- (3.2.d): orthogonality to every `χ_{pq}` forces vanishing on `V`.
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b'))
      (tic.chiFam hVeq app (a', b')) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half (grid level)**: the genuine `μ`-grid statement of the
Dade-image identity, `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`, with `ω^σ` the *aligned*
`σ`-grid `alignedOmegaSigmaGrid` and `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.

This is the full (10.5) endgame.  Writing `X = α_{ij}^τ + n·ζ^{τ₁}`, the goal reduces to
`X = δ·(ω_{ij}^σ − ω_{i0}^σ)`.  Now `X` is a virtual character of `G` with `‖X‖² = 2`
(`muGridAlpha_tau_X_inner`), the aligned `σ`-grid entries are members `χ_{P_{ij}}` of the
orthonormal `σ`-image family (`exists_alignedOmegaSigmaGrid_chiFam_family`), and the difference
`X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V` (`muGridPsi_vanishes_on_typePV` together with the
`ζ^{τ₁}`-vanishing `tau1_zeta_vanishes_on_typePV`).  The norm-`2` Dade-image trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` (the §5 generalisation of the §6 `(4.8)` endgame) then forces
`X = δ·(χ_{P_{ij}} − χ_{P_{i0}})`.  (`alpha_tau_image` is the thin `CharacterParameters` corollary.) -/
theorem Hypothesis.tau_muGridAlpha_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.tau1 ζ := by
  haveI := hyp.finiteG
  classical
  -- `X = α_{ij}^τ + n·ζ^{τ₁}` has `‖X‖² = 2` and lies in `ℤ[Irr G]`.
  have hXfacts := hyp.muGridAlpha_tau_X_inner hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hτ1ζZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      + (n : ℂ) • coh.tau1 ζ ∈ ZIrr G := by
    refine Submodule.add_mem _ hαZ ?_
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hτ1ζZ n
  -- the aligned `σ`-grid entries as `χ`-family members (piece 1).
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  -- `ψ = X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`.
  have hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0 :=
    fun v hv => hyp.tau1_zeta_vanishes_on_typePV hG hodd coh hζS hζirr hζne hv
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    exact hyp.muGridPsi_vanishes_on_typePV hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj coh hζvanish hv
  -- the norm-`2` Dade-image trichotomy.
  rw [eq_sub_iff_add_eq, ← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hXfacts.2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), coherence-free row-difference form**: for nontrivial columns
`j ≠ k` in the same row `i`, `(μ_{ij} − μ_{ik})^τ = δ·(ω_{ij}^σ − ω_{ik}^σ)`.

Unlike `alpha_tau_image` this needs **no** `CoherentHypothesis`: the `n·ζ` legs of the two
`α`'s cancel in the row difference (equal degrees, (10.3) `degree_independent`), so the
`V`-vanishing legs (`tau_muGridAlpha_apply_eq_on_typePV`, coherence-free) subtract to give the
`ψ`-vanishing, and the norm-2 trichotomy engine applies to `X = (μ_{ij} − μ_{ik})^τ` directly.
This is the repo analogue of Coq's coherence-free `FTtypeP_subcoherent` `R`-datum for the
μ-grid (issue 2022, the (5.2.d) reducible-column route). -/
theorem Hypothesis.tau_muGrid_row_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  haveI := hyp.finiteG
  classical
  -- degrees and the `α`-difference identity
  have hdegj : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hdegk : hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hα : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]
    abel
  -- `X ∈ ℤ[Irr G]`: the difference is `A₀`-supported and integral
  have hsupp : (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k).support ⊆ hyp.A0 := by
    rw [hα]
    intro x hx
    rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hx
    by_cases h1 : params.alpha i j x = 0
    · refine params.alpha_support i k hk0 ?_
      rw [ClassFunction.mem_support]
      intro h2
      exact hx (by rw [h1, h2, sub_zero])
    · exact params.alpha_support i j hj0 (ClassFunction.mem_support.mpr h1)
  -- `X ∈ ℤ[Irr G]` via the two `α`-legs
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) ∈ ZIrr G := by
    rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub]
    exact Submodule.sub_mem _
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hzS params.zeta_irreducible hdegj hμ0 hz1
        params.n_formula (hδj j hj0))
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hk0 hzS params.zeta_irreducible hdegk hμ0 hz1
        params.n_formula (hδj k hk0))
  -- `‖X‖² = 2`: Dade preserves the inner product on the supported difference
  have hsrc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      hyp.muGrid_inner_self hG hodd i j, hyp.muGrid_inner_self hG hodd i k,
      hyp.muGrid_inner_cross_column hG hodd i i hjk,
      hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hjk)]
    ring
  have hX2 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k))
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)) = 2 := by
    have hset : ∀ s ∈ ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
        Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k ∈
        OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
            Set (ClassFunction ↥M ℂ)) :=
      Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) from rfl]
    rw [hpres]
    exact hsrc
  -- the σ-grid enumeration and the trichotomy engine
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hPk' : tic.chiFam hVeq app (P k) = hyp.alignedOmegaSigmaGrid hG hodd i k := (hP k).symm
  have hPne : P j ≠ P k := fun h => hjk (hPinj h)
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
        - (params.delta : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P k))) v
        = 0 := by
    intro v hv
    have hlegj := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj0 hzS hdegj hμ0 hz1
      params.n_formula (hδj j hj0) hv
    have hlegk := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hk0 hzS hdegk hμ0 hz1
      params.n_formula (hδj k hk0) hv
    have hXv : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) v
        = ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i k)) v := by
      rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub, ClassFunction.sub_apply,
        hlegj, hlegk]
      simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
      ring
    rw [ClassFunction.sub_apply, hXv, hPj', hPk']
    simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
    ring
  rw [← hPj', ← hPk']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hX2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Column-sum form of `tau_muGrid_row_diff`** (coherence-free (10.5) for columns):
`(μ_j − μ_k)^τ = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)` for nontrivial columns `j ≠ k`. -/
theorem Hypothesis.tau_muGrid_columnSum_diff_cohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    hyp.tau_muGrid_row_diff hG hodd hmu hzS hz1 hδpm hδj i hj0 hk0 hjk

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half** (`CharacterParameters` corollary).  For the (10.2)/(10.3)
character data — the `μ`-grid (`hmu`), the aligned `σ`-grid (`hos`), the degree-`w₁` irreducible `ζ`
of (10.2) (`hzS`/`hz1`) and the column sign `δ = ±1` (`hδpm`/`hδj`) — the Dade image of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is `δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.

Thin corollary of the grid identity `tau_muGridAlpha_eq`.  All arithmetic inputs are discharged from
the (10.3) data carried by `CharacterParameters` (`degree_independent`, `n_formula`, `d_gt_one`,
`two_le_n`) and the structural bounds `w₁, w₂ ≥ 3` (`three_le_card_W1/W2`): the auxiliary nontrivial
column `k ≠ j`, the degree distinctness `d ≠ w₁`/`1 ≠ w₁`, and the parity `n ≥ 2` (Peterfalvi (10.3),
now `params.two_le_n`).  The only hypotheses beyond the (10.2)/(10.3) construction pins are `hzconj`
— the non-realness `ζ̄ ≠ ζ` (Peterfalvi (1.1): a nontrivial irreducible of an odd-order group is not
real; carried per the §10 (10.5) chain convention, derivable via
`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem alpha_tau_image [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.tau (params.alpha i j) =
          (params.delta : ℂ) • (params.omegaSigma i j - params.omegaSigma i 0)
            - (params.n : ℂ) • coh.tau1 params.zeta := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  have hn2 : 2 ≤ params.n := params.two_le_n
  -- structural bounds `w₁, w₂ ≥ 3` from the §10 TI-cyclic hypothesis.
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  intro i j hj0
  -- choose an auxiliary nontrivial column `k ≠ j` (possible as `w₂ ≥ 3`).
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp),
        Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  -- (10.3) degree facts on the `μ`-grid.
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcol1 0]; exact_mod_cast hd1
  -- `d ≠ w₁` from `d = n·w₁ + δ`, `n ≥ 2`, `w₁ ≥ 3`, `δ = ±1`.
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by
    rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcol1 i', hz1]; exact_mod_cast hdw1
  -- discharge via the grid identity `tau_muGridAlpha_eq`.
  rw [params.alpha_def, hmu, hos]
  exact hyp.tau_muGridAlpha_eq hG hodd i hj0 k hjk hk0 coh hzS params.zeta_irreducible hzconj
    hdeg hμ0 hz1 params.n_formula (hδj j hj0) hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a) reduction**: `(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` for `0 < j < w₂`.

This is the inner-product identity opening the (10.6)(a) proof:
`1 = (α_{ij}, μ_j − dζ̄) = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = (δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁})`.
From the diagonal reduction `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`
(`muGridAlpha_tau1_inner_muColumn_self_sub_conj`), the vanishing `(α_{ij}^τ, ζ̄^{τ₁}) = 0`
(from `(α_{ij}^τ, ζ^{τ₁}) = −n` (`muGridAlpha_tau1_zeta_eq_neg_n`, the (10.5) `a = 0`) and
`(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n` (`muGridAlpha_tau_inner_zeta_sub_conj`)), the (10.5)
Dade image `α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`) and `(ζ^{τ₁}, μ_j^{τ₁}) = 0`
(`zeta_tau1_inner_muColumn`): `1 = (α_{ij}^τ, μ_j^{τ₁}) = δ(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁})`, hence
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`δ² = 1`).  This pins the `j`-column coefficient of
`μ_j^{τ₁}` along `ω_{ij}^σ` to `δ` for every `i`, which together with `‖μ_j^{τ₁}‖² = w₁` forces the
(10.6)(a) summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (see `muColumn_tau1_pin`).  Crucially this
specialised reduction avoids Peterfalvi's general (5.8) machinery (separability / `σ`-coefficients):
the diagonal inner product `= 1` directly determines the `j`-column. -/
theorem Hypothesis.omegaSigmaDiff_inner_muColumn_tau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) (i : Fin hyp.w1) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j)) = (params.delta : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- discharge the standard (10.3) degree/parity hypotheses (cf. `alpha_tau_image`).
  have hn2 : 2 ≤ params.n := params.two_le_n
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp), Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcolj : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' j hj0
  have hcolk : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1 := by rw [hcolj 0]; exact_mod_cast hd1
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolj i', hz1]; exact_mod_cast hdw1
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolk i', hz1]; exact_mod_cast hdw1
  have hζirr := params.zeta_irreducible
  have hδjj := hδj j hj0
  -- (1) the diagonal reduction `(α^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`.
  have hdiag := hyp.muGridAlpha_tau1_inner_muColumn_self_sub_conj hG hodd i hj0 coh hzS hζirr
    hzconj hdeg hμ0 hz1 params.n_formula hδjj h0ζ hjζ hcolj hdj1
  -- (2) `(α^τ, ζ^{τ₁}) = −n` (the (10.5) `a = 0`).
  have haζ := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ hkζ hcolk hdk1 hδpm hw1 hn2
  -- (3) `(α^τ, ζ^{τ₁}) − (α^τ, ζ̄^{τ₁}) = −n`, hence `(α^τ, ζ̄^{τ₁}) = 0`.
  have hzsc := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS hζirr, ClassFunction.inner_sub_right] at hzsc
  have haζbar : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (params.delta : ℂ) • hyp.muGrid hG hodd i 0
        - (params.n : ℂ) • params.zeta)) (coh.tau1 params.zeta.conj) = 0 := by
    linear_combination haζ - hzsc
  -- (4) `(α^τ, μ_j^{τ₁}) = 1`.
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, haζbar,
    mul_zero, sub_zero] at hdiag
  -- (5) substitute the (10.5) Dade image and drop the `ζ^{τ₁}` term (`(ζ^{τ₁}, μ_j^{τ₁}) = 0`).
  have hαimg := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  rw [params.alpha_def, hmu, hos] at hαimg
  have hζμ := hyp.zeta_tau1_inner_muColumn hG hodd j coh hzS hζirr hjζ hdj1
  rw [hαimg, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hζμ, mul_zero, sub_zero] at hdiag
  -- `δ · (ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = 1`, so the inner product is `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))
      = (params.delta : ℂ) * ((params.delta : ℂ) * ClassFunction.inner
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))) := by
        rw [← mul_assoc, hδsq, one_mul]
    _ = (params.delta : ℂ) * 1 := by rw [hdiag]
    _ = (params.delta : ℂ) := mul_one _

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column difference (per row)**: for two nontrivial columns `j, k ≠ 0`, the
Dade image of the difference `μ_{ij} − μ_{ik}` of certain-type characters is
`δ·(ω_{ij}^σ − ω_{ik}^σ)`.

The `−δ·μ_{i0} − n·ζ` tails of `α_{ij}` and `α_{ik}` are identical, so `μ_{ij} − μ_{ik} =
α_{ij} − α_{ik}`, and applying `alpha_tau_image` to both columns the `−n·ζ^{τ₁}` parts cancel.  This
is the per-row ingredient of the column image-family `image_eq` (the §10 analogue of the Peterfalvi
(4.9) summed Dade identity), feeding the (5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_column_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  have hatj := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  have hatk := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
  have halpha : hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  rw [halpha, map_sub, hatj, hatk, hos]
  simp only [smul_sub]; abel

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column-sum difference**: summing `tau_muGrid_column_diff` over the rows
`0 ≤ i < w₁`, the Dade image of the difference of the two column characters `μ_j = ∑_i μ_{ij}` and
`μ_k = ∑_i μ_{ik}` (`j, k ≠ 0`) is `δ·(∑_i ω_{ij}^σ − ∑_i ω_{ik}^σ)`.

This is the §10 analogue of the Peterfalvi (4.9) summed Dade identity: it computes
`(μ_j − μ_k)^τ = ∑_{α ∈ R} α` over the signed `σ`-image family
`R = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ik}^σ}`, the `image_eq` field of the column image family used by the
(5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_columnSum_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    tau_muGrid_column_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj i hj0 hk0

open scoped FiniteInduce in
/-- **Peterfalvi (5.8)/(10.6)(a), `μ_k^{τ₁}` vanishes on `V`**: the coherent image of the column
character `μ_k = ∑_i μ_{ik}` (`k ≠ 0`) vanishes on `V = typePV`.  This is the "vanishes on `V`"
hypothesis of the (5.8) `σ`-coefficient full-column endgame `eq_smul_chiFam_column_of_vanishOnV`.

Running Peterfalvi's (5.8) argument with `χ = ζ̄` (a degree-`w₁` irreducible of `S ∩ Irr(L)`, the
conjugate of `ζ`): by (4.7) the combination `μ_k − dζ̄` is `A_0(M)`-supported
(`muColumn_sub_conj_support`), so the Dade isometry restores its value on `V`
(`tau_apply_of_mem_typePV`); both `μ_k` and `ζ̄` (induced from the normal `M'`) vanish at `v ∉ M'`
(`typePData_typePV_not_mem_derived`), giving `(μ_k − dζ̄)^τ(v) = 0`.  Splitting
`(μ_k − dζ̄)^τ = μ_k^{τ₁} − dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) and discharging the
already-established `ζ̄^{τ₁}`-vanishing (`tau1_zeta_vanishes_on_typePV` for `ζ̄`) forces
`μ_k^{τ₁}(v) = 0`.

Crucially this route avoids the `ζ̄^{τ₁} ⊥ Im σ` (§5 (5.3.b)/(5.5)) input that the direct (10.6)(a)
reduction would require: the `(5.5)`-for-columns decomposition determines `μ_k^{τ₁}` directly, and
its vanishing on `V` uses only the (already-honest) single-character `ζ̄^{τ₁}`-vanishing plus (4.7). -/
theorem Hypothesis.muColumn_tau1_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ))
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) v = 0 := by
  haveI := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- `(μ_k − dζ̄)^τ(v) = 0`: `A_0`-supported (4.7), and `μ_k`, `ζ̄` vanish at `v ∉ M'`.
  have hsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  have hτvan : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj) v = 0 := by
    rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    have hμv : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hnotmem
    have hζv : ζ ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hμv,
      hζv, star_zero, mul_zero, sub_zero]
  -- split `(μ_k − dζ̄)^τ = μ_k^{τ₁} − dζ̄^{τ₁}` and discharge `ζ̄^{τ₁}(v) = 0`.
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1] at hτvan
  have hζcvan : coh.tau1 ζ.conj v = 0 := by
    have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
    have hζcne : ζ.conj.conj ≠ ζ.conj := by
      intro h; rw [ClassFunction.conj_conj] at h; exact hζne h.symm
    exact hyp.tau1_zeta_vanishes_on_typePV hG hodd coh hζcS hζirr.conj hζcne hv
  simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, hζcvan, mul_zero,
    sub_zero] at hτvan
  exact hτvan

open scoped FiniteInduce in
/-- **§10 conjugate column** (Peterfalvi (4.9)(a) at §10): for a nontrivial column `j ≠ 0`, the
complex conjugate of the column character `μ_j = ∑_i μ_{ij}` is another nontrivial column
`μ_{j'} = ∑_i μ_{ij'}` with `j' ≠ 0` and `j' ≠ j` (`j'` is the column of `χ₂⁻¹`).

Reduces to the §6 `certainType_columnSum_conj` (`μ̄_j = ∑_i μ_{i,χ₂⁻¹}`), which (issue 1010, HUB) is
now stated on the structural `Hypothesis ↥M`, hence applies to the §10 muGrid host
`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis`.  The `muGrid ↔ columnFamily` row reindexing
gives `∑_i μ_{ij} = ∑_{i'} (h.columnFamily (χ₂ j)).mu i'`; complex conjugation (`ClassFunction.conj`
= `mapRingEquiv conj` pointwise) sends it to the `χ₂⁻¹`-column.  `j' ≠ 0` from
`finCardEquivCharacterGroup_zero` (the column-`0` dual is trivial) and `j' ≠ j` from the odd order of
the column character group (`W_odd`/`card_charGroup_W2`, no involutions; the `column_inv_ne_self`
argument inlined).  This is the conjugate-column input `(μ_j)‾ = μ_{j'}` for the (5.5)-for-columns
route to (10.6)(a): `tau_muGrid_columnSum_diff` (with `k = j'`) then supplies the column
`OrthonormalCharacterImageFamily.image_eq` field `τ(μ_j − μ̄_j) = ∑ R(μ_j)`. -/
theorem Hypothesis.exists_conj_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j).conj
        = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j' := by
  haveI := hyp.finiteG
  haveI : Finite ↥M := inferInstance
  classical
  -- reconstruct the §6 structural host (as in `muGrid`)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- the column character as a function of the index
  let χ₂ : Fin hyp.w2 → ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    fun jj => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm jj)
  -- the `muGrid ↔ columnFamily` row-reindexing bridge
  have hbridge : ∀ jj : Fin hyp.w2,
      ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj
        = ∑ i' : Fin (Nat.card h.W1), ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ) := by
    intro jj
    rw [← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- `ClassFunction.conj = mapRingEquiv conj` pointwise
  have hconjbridge : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  -- `χ₂` injective; `χ₂ jj = 1 ↔ jj = 0`
  have hχ₂inj : Function.Injective χ₂ := fun a b hab =>
    (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective hab)
  have hχ₂one : ∀ jj : Fin hyp.w2, χ₂ jj = 1 ↔ jj = 0 := by
    intro jj
    rw [show (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
        = finCardEquivCharacterGroup _ 0 from (finCardEquivCharacterGroup_zero _).symm,
      (finCardEquivCharacterGroup _).injective.eq_iff]
    constructor
    · intro he; exact (finCongr hcardW2sub.symm).injective (by rw [he]; simp)
    · intro he; subst he; simp
  -- the conjugate-column index `j'` with `χ₂ j' = (χ₂ j)⁻¹`
  let j' : Fin hyp.w2 :=
    (finCongr hcardW2sub.symm).symm ((finCardEquivCharacterGroup _).symm (χ₂ j)⁻¹)
  have hj'χ : χ₂ j' = (χ₂ j)⁻¹ := by simp only [χ₂, j', Equiv.apply_symm_apply]
  have hχ₂jne : χ₂ j ≠ 1 := fun he => hj0 ((hχ₂one j).mp he)
  -- `(χ₂ j)⁻¹ ≠ χ₂ j` (column char group has odd order — no involutions; `column_inv_ne_self` inline)
  have hinvne : (χ₂ j)⁻¹ ≠ χ₂ j := by
    have hodd' : Odd (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [h.card_charGroup_W2]
      exact h.W_odd.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_right)
    intro heq
    apply hχ₂jne
    have hsq : (χ₂ j) ^ 2 = 1 := by
      have hm := mul_inv_cancel (χ₂ j); rw [heq] at hm; rwa [pow_two]
    have hcardodd : Odd (orderOf (χ₂ j)) := hodd'.of_dvd_nat (orderOf_dvd_natCard (χ₂ j))
    have h1 : orderOf (χ₂ j) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ hcardodd) (by decide)
    exact orderOf_eq_one_iff.mp h1
  refine ⟨j', ?_, ?_, ?_⟩
  · -- `j' ≠ 0`
    intro he
    exact hχ₂jne (inv_eq_one.mp (hj'χ ▸ (hχ₂one j').mpr he))
  · -- `j' ≠ j`
    intro he
    exact hinvne (hj'χ ▸ (congrArg χ₂ he))
  · -- the conjugate identity, via the generalized §6 `certainType_columnSum_conj`
    rw [hbridge j, hbridge j', hconjbridge,
      OddOrder.Peterfalvi.S06.certainType_columnSum_conj h (χ₂ j), hj'χ]

/-- **§10 `R(μ_j)` member family** (Peterfalvi (5.3.b) at §10).  Indexed by `Bool × Fin w₁`:
`(false, i) ↦ δ·ω_{ij}^σ`, `(true, i) ↦ −δ·ω_{ij'}^σ` (sign `δ = params.delta`, columns `j`, `j'`).
Its image is the orthonormal difference-image family `R(μ_j)` of the column
`OrthonormalCharacterImageFamily`. -/
noncomputable def Hypothesis.columnRImage [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    Bool × Fin hyp.w1 → ClassFunction G ℂ
  | (false, i) => (δ : ℂ) • hyp.alignedOmegaSigmaGrid hG hodd i j
  | (true, i) => (-(δ : ℂ)) • hyp.alignedOmegaSigmaGrid hG hodd i j'

open scoped FiniteInduce in
/-- **Orthonormality of `R(μ_j)`** at §10: the signed σ-image family `columnRImage` is orthonormal,
`⟨R p, R q⟩ = δ_{p,q}`.  The sign `δ = ±1` gives `δ·δ̄ = 1`, the σ-grid orthonormality
`alignedOmegaSigmaGrid_inner` supplies `⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = [i=i' ∧ j=j']`, and the two halves
(`j ≠ j'`) are cross-orthogonal. -/
theorem Hypothesis.columnRImage_inner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') (p q : Bool × Fin hyp.w1) :
    ClassFunction.inner (hyp.columnRImage hG hodd δ j j' p) (hyp.columnRImage hG hodd δ j j' q)
      = if p = q then (1 : ℂ) else 0 := by
  have hδstar : star ((δ : ℂ)) = (δ : ℂ) := by rcases hδ with h | h <;> rw [h] <;> norm_num
  have hδsq : (δ : ℂ) * (δ : ℂ) = 1 := by rcases hδ with h | h <;> rw [h] <;> norm_num
  obtain ⟨bp, ip⟩ := p
  obtain ⟨bq, iq⟩ := q
  cases bp <;> cases bq <;>
    simp only [Hypothesis.columnRImage, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hodd,
      hδstar, star_neg, mul_neg, neg_mul, neg_neg, Prod.mk.injEq, reduceCtorEq, false_and,
      true_and, and_true, eq_self_iff_true, ↓reduceIte]
  · -- (false,false): same column `j`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]
  · -- (false,true): cross column `j ≠ j'`
    rw [if_neg (fun hcon => hjj' hcon.2)]; ring
  · -- (true,false): cross column `j' ≠ j`
    rw [if_neg (fun hcon => hjj' hcon.2.symm)]; ring
  · -- (true,true): same column `j'`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]

open scoped FiniteInduce in
/-- `R(μ_j)` is injective on `Bool × Fin w₁` (distinct orthonormal vectors are distinct). -/
theorem Hypothesis.columnRImage_injective [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    Function.Injective (hyp.columnRImage hG hodd δ j j') := by
  intro p q hpq
  by_contra hpqne
  have h0 := hyp.columnRImage_inner hG hodd hδ hjj' p q
  rw [if_neg hpqne, hpq, hyp.columnRImage_inner hG hodd hδ hjj', if_pos rfl] at h0
  exact one_ne_zero h0

open scoped FiniteInduce in
/-- The sum of the §10 `R(μ_j)` family over `Bool × Fin w₁` is `δ·∑_i (ω_{ij}^σ − ω_{ij'}^σ)`, the
image side of the (10.6)(a) summed isometry (`tau_muGrid_columnSum_diff`). -/
theorem Hypothesis.columnRImage_sum [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    ∑ p : Bool × Fin hyp.w1, hyp.columnRImage hG hodd δ j j' p
      = (δ : ℂ) • ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i j') := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.smul_sum]
  simp only [Hypothesis.columnRImage, neg_smul, smul_sub]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by abel)

open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`** (Peterfalvi (5.2.d) for the reducible column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, tau_muGrid_columnSum_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0,
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]


open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`, coherence-free** ((5.2.d) for the reducible column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamilyCohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, hyp.tau_muGrid_columnSum_diff_cohFree hG hG.odd hmu hzS hz1 hδpm hδj hj0 hj'0 hjj',
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]

open scoped Classical FiniteInduce in
/-- **§10 column image family exists** (issue 1009): the conjugate column `j'`
(`exists_conj_column`) packages the column `OrthonormalCharacterImageFamily` for `μ_j` together with
the `j' ≠ 0` datum (so the downstream `ofProjection`/(5.5) can read off `R(μ_j)`). -/
theorem Hypothesis.exists_columnImageFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      Nonempty (OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
        (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) := by
  obtain ⟨j', hj'0, hj'j, hconj⟩ := hyp.exists_conj_column hG hG.odd hj0
  exact ⟨j', hj'0, hj'j, ⟨hyp.columnImageFamily hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0
    (Ne.symm hj'j) hconj⟩⟩

open scoped Classical FiniteInduce in
/-- **§10 (5.5) for the column `μ_j`** (Peterfalvi (5.5) applied to the reducible column character):
`μ_j^{τ₁} = ∑_{α ∈ E} α` for some `E ⊆ R(μ_j)` with `|E| = ‖μ_j‖² = w₁`.

Builds the (5.4) `CharacterPsiDecomposition` for `(μ_j, ψ = 0)` against `τ = hyp.tau`,
`τ₁ = coh.tau1` via `ofProjection` — the column `OrthonormalCharacterImageFamily`
(`columnImageFamily`) supplies `R(μ_j)`; the coherence isometry `coh.coherent` supplies the
lattice-relative inner-preservation (`extension_inner_eq`, on `ℤ[S] ⊇ {μ_j − μ̄_j, μ_j}`), the
`τ`-agreement (`extends_on_supported`, `μ_j − μ̄_j` is `A_0`-supported), and the `ZIrr`-membership
(`extension_mem_ZIrr`, `μ_j ∈ S`); the orthogonalities `⟨μ_j, 0⟩ = ⟨μ̄_j, 0⟩ = 0` are trivial and
`⟨μ_j, μ̄_j⟩ = 0` is the cross-column Gram entry (`muGrid_inner_cross_column`, `j ≠ j'`).  Then
`eq_sum_of_psi_eq_zero` extracts the (5.5) sum.  This is the second-to-last step of (10.6)(a); the
final (5.8) full-column endgame then pins `E` to the single full column `{δ·ω_{ij}^σ}`. -/
theorem Hypothesis.exists_muColumn_tau1_eq_sum_R [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      ∃ E ⊆ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j'),
        coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ α ∈ E, α ∧
          (E.card : ℂ) = (hyp.w1 : ℂ) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨j', hj'0, hj'j, hconj⟩ := hyp.exists_conj_column hG hG.odd hj0
  set χ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j with hχdef
  have hχS : χ ∈ inducedFamily M := hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j (hd1 j hj0)
  have hχcS : χ.conj ∈ inducedFamily M := by
    rw [hχdef, hconj]; exact hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j' (hd1 j' hj'0)
  -- `χ − χ̄ = ∑_i (α_{ij} − α_{ij'})` is `A_0`-supported and lies in `ℤ[S]`.
  have hμdiff : χ - χ.conj
      = ∑ i : Fin hyp.w1, (params.alpha i j - params.alpha i j') := by
    rw [hχdef, hconj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  have hsumsupp : ∀ s : Finset (Fin hyp.w1),
      (∑ i ∈ s, (params.alpha i j - params.alpha i j')).support ⊆ hyp.A0 := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, ClassFunction.support_zero]; exact Set.empty_subset _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        refine (ClassFunction.support_add_subset _ _).trans (Set.union_subset ?_ ih)
        exact (ClassFunction.support_sub_subset _ _).trans
          (Set.union_subset (params.alpha_support i j hj0) (params.alpha_support i j' hj'0))
  have hsuppmem : (χ - χ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS),
      by rw [hμdiff]; exact hsumsupp Finset.univ⟩
  -- the running coherence isometry preserves inner products on `ℤ[S] ⊇ zSpan {χ − χ̄, χ − 0}`.
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥M) {χ - χ.conj, χ - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS)
    · rw [sub_zero]; exact Submodule.subset_span hχS
  -- `⟨μ_j, μ̄_j⟩ = 0` (cross-column Gram entry).
  have hχχbar : ClassFunction.inner χ χ.conj = 0 := by
    rw [hχdef, hconj, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => hyp.muGrid_inner_cross_column hG hG.odd i i' hj'j.symm
  -- assemble the (5.4) decomposition via `ofProjection` and apply (5.5).
  let R := hyp.columnImageFamily hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0 (Ne.symm hj'j) hconj
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau χ 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection R coh.tau1
      (fun φ ζ hφ hζ => coh.coherent.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (coh.coherent.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact coh.coherent.extension_mem_ZIrr χ (Submodule.subset_span hχS))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  obtain ⟨_, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  refine ⟨j', hj'0, hj'j, E, hEsub, ?_, ?_⟩
  · rw [← hEsum]; exact hτ1
  · rw [hEcard, hχdef, hyp.muGrid_column_sum_inner_self hG hG.odd j]

open scoped FiniteInduce in
/-- **§10 column-independent `τ₁`-residual** (the reduction step of Peterfalvi (10.6)(a)): for any
two nontrivial columns `j, k ≠ 0`, the coherent images satisfy
`μ_j^{τ₁} − μ_k^{τ₁} = δ·(∑_i ω_{ij}^σ − ∑_i ω_{ik}^σ)`, i.e. the residual
`μ_j^{τ₁} − δ·∑_i ω_{ij}^σ` does **not depend on the column `j`**.

This is the honest §10-native column reduction of (10.6)(a): the difference
`μ_j − μ_k = ∑_i(α_{ij} − α_{ik})` is `A_0(M)`-supported (each `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is,
`CharacterParameters.alpha_support`), so the coherent extension agrees there with the Dade isometry
`τ` (`CoherentHypothesis.coherent.extends_on_supported`), and
`τ(μ_j − μ_k) = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)` is the landed (10.5) column-sum identity
`tau_muGrid_columnSum_diff`.  Combined with `map_sub` for `τ₁` this gives the column-independence,
reducing the full (10.6)(a) `μ_j^{τ₁} = δ·∑_i ω_{ij}^σ` to a single column — the remaining content
being the (5.8) full-column endgame that pins that one column. -/
theorem Hypothesis.muColumn_tau1_diff_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0)
    (hdj1 : hyp.muGrid hG hG.odd 0 j 1 ≠ 1) (hdk1 : hyp.muGrid hG hG.odd 0 k 1 ≠ 1) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        - coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      = (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  haveI := hyp.finiteG
  classical
  -- `μ_j − μ_k = ∑_i (α_{ij} − α_{ik})` (the `δμ_{i0}`, `nζ` tails cancel).
  have hμdiff : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
        = ∑ i : Fin hyp.w1, (params.alpha i j - params.alpha i k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  -- each partial sum `∑_{i∈s}(α_{ij} − α_{ik})` is `A_0`-supported (induction; `α_{ij}` is).
  have hsumsupp : ∀ s : Finset (Fin hyp.w1),
      (∑ i ∈ s, (params.alpha i j - params.alpha i k)).support ⊆ hyp.A0 := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, ClassFunction.support_zero]; exact Set.empty_subset _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        refine (ClassFunction.support_add_subset _ _).trans (Set.union_subset ?_ ih)
        exact (ClassFunction.support_sub_subset _ _).trans
          (Set.union_subset (params.alpha_support i j hj0) (params.alpha_support i k hk0))
  -- `μ_j − μ_k ∈ ℤ[S, A_0]`: in `ℤ[S]` (both column sums lie in `S`), supported on `A_0`.
  have hmem : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 := by
    refine ⟨Submodule.sub_mem _
      (Submodule.subset_span (hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j hdj1))
      (Submodule.subset_span (hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd k hdk1)), ?_⟩
    rw [hμdiff]; exact hsumsupp Finset.univ
  -- `τ₁(μ_j − μ_k) = τ(μ_j − μ_k) = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)`.
  have key : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k))
        = hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
          - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)) :=
    coh.coherent.extends_on_supported _ hmem
  rw [map_sub] at key
  rw [key, tau_muGrid_columnSum_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hk0]

open scoped FiniteInduce in
/-- **(10.6.a) reduces to a single column**: if the summed isometry `μ_{j₀}^{τ₁} = δ·∑_i ω_{i j₀}^σ`
holds for **one** nontrivial column `j₀ ≠ 0`, then it holds for **every** nontrivial column `j ≠ 0`.

Immediate from the column-independence `muColumn_tau1_diff_eq`: for any `j ≠ 0`,
`μ_j^{τ₁} = μ_{j₀}^{τ₁} + (μ_j^{τ₁} − μ_{j₀}^{τ₁}) = δ·∑_i ω_{i j₀}^σ + δ·(∑_i ω_{ij}^σ − ∑_i ω_{i j₀}^σ)
= δ·∑_i ω_{ij}^σ`.  This isolates the remaining content of the full (10.6)(a) summed isometry to the
**(5.8) full-column endgame on a single column `j₀`** (which, once the column
`OrthonormalCharacterImageFamily` is available — HUB issue 1010 — pins that one column). -/
theorem Hypothesis.muColumn_tau1_eq_of_single_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muGrid hG hG.odd 0 j 1 ≠ 1)
    {j₀ : Fin hyp.w2} (hj₀0 : j₀ ≠ 0)
    (hpin : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀)
      = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j₀) :
    ∀ j : Fin hyp.w2, j ≠ 0 →
      coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  intro j hj0
  have hdiff := hyp.muColumn_tau1_diff_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj₀0
    (hd1 j hj0) (hd1 j₀ hj₀0)
  -- `μ_j^{τ₁} = (μ_j^{τ₁} − μ_{j₀}^{τ₁}) + μ_{j₀}^{τ₁}`, then substitute the two known pieces.
  have hrw : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
          - coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀))
        + coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀) := by abel
  rw [hrw, hdiff, hpin, smul_sub]; abel

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.6)(a) summed isometry**: for every nontrivial column `0 < j < w₂`,
`μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.

This is the §10 specialisation of Peterfalvi's (5.8) — proved here *without* the general (5.8)
machinery (separability / `σ`-coefficients), using only the (10.6)(a) reduction and a cardinality
count.  By (5.5) (`exists_muColumn_tau1_eq_sum_R`), `μ_j^{τ₁} = ∑_{x ∈ T} R(x)` where
`R = R(μ_j) = {δ·ω_{ij}^σ}∪{−δ·ω_{ij'}^σ}` (`columnRImage`, `j'` the conjugate column) is an
orthonormal family and `|T| = ‖μ_j^{τ₁}‖² = w₁`.  The reduction
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`omegaSigmaDiff_inner_muColumn_tau1`) computes, against the
`T`-sum, to `δ·[(false, i) ∈ T]` (the cross-column `j'` and the trivial column `0` are orthogonal);
since `δ ≠ 0`, every `(false, i) ∈ T`.  So `{false} × univ ⊆ T` with both of cardinality `w₁`, forcing
`T = {false} × univ` and `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`. -/
theorem Hypothesis.muColumn_tau1_pin [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  haveI := hyp.finiteG
  classical
  -- (5.5): `μ_j^{τ₁} = ∑_{α ∈ E} α` for `E ⊆ R(μ_j)`, `|E| = w₁`.
  obtain ⟨j', hj'0, hj'j, E, hEsub, hEsum, hEcard⟩ :=
    hyp.exists_muColumn_tau1_eq_sum_R hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  set R := hyp.columnRImage hG hG.odd params.delta j j' with hRdef
  have hRinj : Function.Injective R := hyp.columnRImage_injective hG hG.odd hδpm (Ne.symm hj'j)
  -- the preimage `T ⊆ Bool × Fin w₁` of `E` under the injective family `R`.
  set T : Finset (Bool × Fin hyp.w1) := Finset.univ.filter (fun x => R x ∈ E) with hTdef
  have hImT : T.image R = E := by
    apply Finset.ext; intro α
    simp only [Finset.mem_image, hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hα
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hEsub hα)
      exact ⟨x, by rw [hx]; exact hα, hx⟩
  have hSumT : ∑ x ∈ T, R x = ∑ α ∈ E, α := by
    rw [← hImT, Finset.sum_image (fun x _ y _ h => hRinj h)]
  have hCardT : T.card = hyp.w1 := by
    have hc : (T.image R).card = E.card := by rw [hImT]
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hRinj h)] at hc
    rw [hc]; exact_mod_cast hEcard
  -- `μ_j^{τ₁} = ∑_{x ∈ T} R x`.
  have hμT : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ x ∈ T, R x := by
    rw [hEsum, hSumT]
  -- inner product of `ω_{ij}^σ − ω_{i0}^σ` against each `R(x)` (only `x = (false, i)` survives).
  have hval : ∀ (i : Fin hyp.w1) (x : Bool × Fin hyp.w1),
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x)
      = if x = (false, i) then (params.delta : ℂ) else 0 := by
    intro i x
    have hδstar : star ((params.delta : ℂ)) = (params.delta : ℂ) := by
      rcases hδpm with h | h <;> rw [h] <;> norm_num
    obtain ⟨b, i'⟩ := x
    cases b <;>
      simp only [hRdef, Hypothesis.columnRImage, ClassFunction.inner_sub_left,
        OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hG.odd,
        hδstar, star_neg, Prod.mk.injEq, reduceCtorEq, false_and, true_and, and_true,
        eq_self_iff_true, ↓reduceIte, mul_one, mul_zero, mul_neg, neg_mul, neg_neg]
    · -- (false, i'): `δ · [i = i'] − δ · [i = i' ∧ 0 = j] = if i' = i then δ else 0`
      rw [if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j) from fun hh => hj0 hh.2.symm),
        mul_zero, sub_zero]
      by_cases hii : i = i'
      · rw [if_pos hii, mul_one, if_pos hii.symm]
      · rw [if_neg hii, mul_zero, if_neg (fun h => hii h.symm)]
    · -- (true, i'): both columns orthogonal (`j ≠ j'`, `j' ≠ 0`)
      rw [if_neg (show ¬(i = i' ∧ j = j') from fun hh => hj'j hh.2.symm),
        if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j') from fun hh => hj'0 hh.2.symm)]
      ring
  -- the (10.6)(a) reduction forces every `(false, i) ∈ T`.
  have hfalseT : ∀ i : Fin hyp.w1, (false, i) ∈ T := by
    intro i
    by_contra hni
    have hRi := hyp.omegaSigmaDiff_inner_muColumn_tau1 hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 i
    rw [hμT, OddOrder.RepresentationTheory.inner_sum_right] at hRi
    rw [show (∑ x ∈ T, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x))
        = if (false, i) ∈ T then (params.delta : ℂ) else 0 by
      rw [Finset.sum_congr rfl (fun x _ => hval i x)]; exact Finset.sum_ite_eq' T (false, i) _,
      if_neg hni] at hRi
    rcases hδpm with h | h <;> rw [h] at hRi <;> norm_num at hRi
  -- `{false} × univ ⊆ T` and `|T| = w₁ = |{false} × univ|`, so `T = {false} × univ`.
  have hFsub : Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) ⊆ T := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfalseT i
  have hFinj : Function.Injective (fun i : Fin hyp.w1 => (false, i)) :=
    fun a b h => congrArg Prod.snd h
  have hFcard : (Finset.univ.image (fun i : Fin hyp.w1 => (false, i))).card = hyp.w1 := by
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fin]
  have hTeq : T = Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) :=
    (Finset.eq_of_subset_of_card_le hFsub (by rw [hFcard, hCardT])).symm
  -- conclude: `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`.
  rw [hμT, hTeq, Finset.sum_image (fun a _ b _ h => hFinj h)]
  simp only [hRdef, Hypothesis.columnRImage]
  rw [Finset.smul_sum]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b) reduction identity** (the `Ã(M)`-independent half of (10.6)(b)):
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` as a class function on `G`.

Picks a fixed nontrivial column `k`; the `M`-level identity
`δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}` (from `α_{ik} = μ_{ik} − δμ_{i0} − nζ` and `d = w₁n + δ`)
is mapped through the `ℤ`-linear Dade map `τ`.  Then `τ(μ_k − dζ) = δ∑_i ω_{ik}^σ − dζ^{τ₁}`
(`μ_k − dζ = (μ_k − dζ̄) + d(ζ̄ − ζ)` reduces it to `tau_muColumn_sub_conj_eq_tau1` +
`tau_zeta_sub_conj_eq_tau1`, then `muColumn_tau1_pin` for `μ_k^{τ₁}`) and
`τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`); the `δ∑ω_{ik}^σ` cancel and
`(w₁n − d)ζ^{τ₁} = −δζ^{τ₁}`, giving `δ·τ(μ_0 − ζ) = δ∑ω_{i0}^σ − δζ^{τ₁}`; cancel `δ` (`δ² = 1`).

This is `STEP 1` of (10.6)(b) (issue 1009); the remaining `STEP 2` (`τ(μ_0 − ζ)` vanishes off `Ã(M)`,
the tame support) + `STEP 3` parity then give `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) - coh.tau1 params.zeta := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- a fixed nontrivial column `k`.
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hk0⟩ : ∃ k : Fin hyp.w2, k ≠ 0 :=
    ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp)⟩
  have hcolk : ∀ i, hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := fun i => by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hd1k : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hodd 0 jj 1 ≠ 1 := fun jj hjj => by
    rw [← hmu, params.degree_independent 0 jj hjj]; exact_mod_cast hd1
  -- `d = w₁·n + δ`.
  have hd : (params.d : ℂ) = (hyp.w1 : ℂ) * (params.n : ℂ) + (params.delta : ℂ) := by
    have h : (params.n : ℂ) * (hyp.w1 : ℂ) = (params.d : ℂ) - (params.delta : ℂ) := by
      exact_mod_cast params.n_formula
    linear_combination -h
  -- `τ` commutes with the natural scalar `d`.
  have hsmul_tau : ∀ (x : ClassFunction ↥M ℂ),
      hyp.tau ((params.d : ℂ) • x) = (params.d : ℂ) • hyp.tau x := fun x => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ℂ)]
  -- `τ(μ_k − dζ) = δ∑ω_{ik}^σ − dζ^{τ₁}` via the conjugate decomposition.
  have htauμk : hyp.tau ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta)
      = (params.delta : ℂ) • (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
        - (params.d : ℂ) • coh.tau1 params.zeta := by
    have hdecomp : (∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta
        = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta.conj)
          + (params.d : ℂ) • (params.zeta.conj - params.zeta) := by
      rw [smul_sub]; abel
    have htauzc : hyp.tau (params.zeta.conj - params.zeta)
        = coh.tau1 params.zeta.conj - coh.tau1 params.zeta := by
      rw [show params.zeta.conj - params.zeta = -(params.zeta - params.zeta.conj) by abel, map_neg,
        hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS params.zeta_irreducible]
      abel
    rw [hdecomp, map_add,
      hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hzS params.zeta_irreducible hcolk hz1 hdk1,
      hsmul_tau, htauzc,
      muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1k hk0]
    module
  -- `τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (the (10.5) Dade image).
  have htauα : ∀ i, hyp.tau (params.alpha i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
          - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta := by
    intro i
    have h := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
    rwa [hos] at h
  -- the `M`-level identity `δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}`.
  have hMlevel : (params.delta : ℂ) • ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta) - ∑ i, params.alpha i k := by
    have hαe : (∑ i, params.alpha i k)
        = (∑ i, hyp.muGrid hG hodd i k) - (params.delta : ℂ) • (∑ i, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (params.n : ℂ)) • params.zeta := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [params.alpha_def, hmu]),
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
    rw [hαe, hd]; module
  -- `∑_i (δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}) = δ(∑ω_{ik}^σ − ∑ω_{i0}^σ) − (w₁n)ζ^{τ₁}`.
  have hsum_α : (∑ i, ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
        - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta))
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
          - ∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (params.n : ℂ)) • coh.tau1 params.zeta := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.smul_sum, Finset.sum_sub_distrib]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ),
        smul_smul]
  -- map the `M`-level identity through `τ` and substitute the three images.
  have hscaled : (params.delta : ℂ) • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta) := by
    have hkey := congrArg hyp.tau hMlevel
    rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul (R := ℂ)] at hkey
    rw [hkey, map_sub, htauμk, map_sum, Finset.sum_congr rfl (fun i _ => htauα i), hsum_α, hd]
    module
  -- cancel `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((params.delta : ℂ)
          • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)) := by
        rw [smul_smul, hδsq, one_smul]
    _ = (params.delta : ℂ) • ((params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta)) := by rw [hscaled]
    _ = (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.tau1 params.zeta := by
        rw [smul_smul, hδsq, one_smul]

open scoped FiniteInduce in
/-- **§10 (2.7) adjoint at the trivial character**: for an `A_0`-supported class function `φ` on `M`,
the Dade image `φ^τ = hyp.tau φ` has the same trivial-character multiplicity as `φ`,
`⟨φ^τ, 1_G⟩ = ⟨φ, 1_M⟩`.

The genuine §10 Dade isometry `hyp.tau` agrees on the supported subspace with the §4 Dade map
`hyp.dadeData.dade.dadeMap` (`dadeIntegralCharacterMap_apply_of_support`); the Peterfalvi (2.7) adjoint
formula `adjoint_formula` with `χ = 1_G` gives `⟨dadeMap ⟨φ,_⟩, 1_G⟩ = ⟨φ, ψ⟩`, where the coset
average `ψ = adjointAverageFun 1_G` is the constant `1` (`|H(a)|⁻¹·∑_{x ∈ H(a)} 1 = 1`), i.e. the
trivial character `1_M`.  This is the `a_{00} = ((μ_0 − ζ)^τ, 1_G) = (μ_0 − ζ, 1_M)` computation
underlying Peterfalvi (10.9). -/
theorem Hypothesis.tau_inner_trivial [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (trivialClassFunction G)
      = ClassFunction.inner φ (trivialClassFunction (↥M)) := by
  haveI := hyp.finiteG
  classical
  have hmem : φ ∈ ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M) :=
    (ClassFunction.mem_supportedSubmodule).mpr hφ
  -- `hyp.tau φ = dadeMap ⟨φ, supported⟩` on the supported subspace.
  have he : hyp.tau φ = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩ := by
    change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) φ
      = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  -- the coset average of `1_G` is the constant `1` (= `1_M`).
  have hψ : ∀ a : {a : G // a ∈ typePA0 M hyp.typeP},
      (trivialClassFunction (↥M)) ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩
        = OddOrder.Peterfalvi.S04.adjointAverageFun hyp.dadeData.dade (trivialClassFunction G)
            ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.adjointAverageFun, dif_pos a.2]
    simp only [trivialClassFunction_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  rw [he]
  exact OddOrder.Peterfalvi.S04.adjoint_formula hyp.dadeData.dade hyp.dadeData.dade.dadeMap
    (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)) hyp.hconj ⟨φ, hmem⟩ (trivialClassFunction G)
    (trivialClassFunction (↥M)) hψ

open scoped FiniteInduce in
/-- **§10 Dade isometry vanishes off the tame support `Ã(M) = dadeSupport`.**  For a class function
`φ` on `M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *vanishes* at any
`g ∉ Ã(M) = hyp.dadeData.dade.dadeSupport`.

The genuine §10 Dade isometry `hyp.tau` is `S07.dadeIntegralCharacterMap hyp.dadeData.dade …`; on the
supported subspace it agrees with the §4 Dade map `hyp.dadeData.dade.dadeMap`
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`).  This is the general "vanishes off `Ã(M)`" companion
of `dadeIntegralCharacterMap_apply_one_eq_zero` (the `g = 1` special case), and the `Ã(M)`-vanishing
step of (10.6)(b) (issue 1009, STEP 2). -/
theorem Hypothesis.tau_apply_eq_zero_of_not_mem_dadeSupport [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    hyp.tau φ g = 0 := by
  haveI := hyp.finiteG
  classical
  show OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) φ g = 0
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  exact (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)).map_eq_zero_of_not_mem_dadeSupport
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
      OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typePA0 M hyp.typeP) M) g hg

open scoped FiniteInduce in
/-- **§10 support of `μ_0 − ζ`** (Peterfalvi (10.6)(b), the `Ã(M)`-vanishing leg): the column-`0`
sum `μ_0 = ∑_i μ_{i0}` (an induced character of degree `w₁`, since each `μ_{i0}(1) = 1`) minus a
degree-`w₁` irreducible `ζ ∈ S` (induced from `M'`) is supported in `A_0(M)`.

Both `μ_0` and `ζ` are induced from the normal `M' = [M,M]`, hence vanish off `M'`
(`muGrid_column_sum_vanishes_off_derived`; induced-from-`M'` for `ζ`); and the degrees cancel,
`(μ_0 − ζ)(1) = w₁ − w₁ = 0` (`muGrid_zero_column_apply_one`), so the support lies in
`M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `muColumn_sub_conj_support`/`zeta_sub_conj_support`: it makes `μ_0 − ζ`
`A_0`-supported, so the Dade isometry `τ` vanishes on it off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`).  Together with the (10.6)(b) reduction identity
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`tau_muColumnZero_sub_zeta_eq`) it yields the pointwise
identity `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` off `Ã(M)`. -/
theorem Hypothesis.muColumnZero_sub_zeta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_0 z = ζ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK,
      hζvanish hzK, sub_zero]
  -- `z ≠ 1`: `(μ_0 − ζ)(1) = w₁ − w₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 2** (the `Ã(M)`-vanishing reduction): off the tame support
`Ã(M) = dadeSupport`, the coherent image `ζ^{τ₁}` agrees with the column-`0` σ-sum,
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` for `g ∉ hyp.dadeData.dade.dadeSupport`.

Combines the (10.6)(b) reduction identity `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}`
(`tau_muColumnZero_sub_zeta_eq`, STEP 1) with the vanishing of `τ(μ_0 − ζ)` off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`, since `μ_0 − ζ` is `A_0`-supported by
`muColumnZero_sub_zeta_support`).  This is STEP 2 of (10.6)(b) (issue 1009); the remaining STEP 3
(parity of `∑_i ω_{i0}^σ(g)` using `ω_{00}^σ = 1_G` and the conjugate-pairing of the `i > 0`
terms) then gives `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    coh.tau1 params.zeta g
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
  haveI := hyp.finiteG
  -- STEP 1: `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` as class functions on `G`.
  have hstep1 := hyp.tau_muColumnZero_sub_zeta_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj
  -- `μ_0 − ζ` is `A_0`-supported, so `τ(μ_0 − ζ)` vanishes off `Ã(M)`.
  have hsupp := hyp.muColumnZero_sub_zeta_support hG hG.odd hzS hz1
  have hvanish := hyp.tau_apply_eq_zero_of_not_mem_dadeSupport hsupp hg
  -- Evaluate the STEP 1 identity at `g` (`ClassFunction` is a `CoeFun`, not `DFunLike`).
  have heval : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta) g
      = ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          - coh.tau1 params.zeta) g :=
    congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) hstep1
  -- Cancel the vanishing left-hand side.
  rw [ClassFunction.sub_apply, hvanish] at heval
  linear_combination heval

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — integrality of the column-`0` σ-grid value** ((3.9)(c) on the
aligned grid): for `g : G` of order prime to `w₁`, each `ω_{i0}^σ(g)` is a rational integer.

The aligned grid is `ω_{i0}^σ = σ(ω(ξ_i))` for the transported linear character
`ξ_i = (omegaProdChar (w1CharEquiv i) χ₂).comp e` of `tic.W` (column-`0` dual `χ₂ = 1`).  As column
`0` is trivial, `ξ_i` factors through `W₁` (`omegaProdChar_one_right`), so `orderOf ξ_i ∣ |W₁| = w₁`;
since `(orderOf g)` is coprime to `w₁` it is coprime to `orderOf ξ_i`, and (3.9)(c)
(`exists_intCast_sigma_omega_apply`) gives the integer. -/
theorem Hypothesis.exists_intCast_alignedOmegaSigmaGrid_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {g : G}
    (hg : (orderOf g).Coprime hyp.w1) :
    ∃ n : ℤ, hyp.alignedOmegaSigmaGrid hG hodd i 0 g = (n : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ` of `tic.W`
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid i 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma; `ω = lin`).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd i 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial, so `ξ = (w1CharEquiv …).comp wFst ∘ e` factors through `W₁`.
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- `(w1CharEquiv …) ^ w₁ = 1` from `|Ŵ₁| = |W₁| = w₁` (Pontryagin self-duality).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hχ1pow : (h.w1CharEquiv (finCongr hcardW1.symm i)) ^ hyp.w1 = 1 := by
    have := pow_card_eq_one' (x := h.w1CharEquiv (finCongr hcardW1.symm i))
    rwa [hcardDual] at this
  -- column `0` trivial ⟹ `ξ` factors through `W₁` as `(w1CharEquiv …).comp wFst ∘ e`.
  have hξeq : ξ = ((h.w1CharEquiv (finCongr hcardW1.symm i)).comp
      h.sdiffTICyclicHypothesis.wFst).comp e.toMonoidHom := by
    have hpc : (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂)
        = (h.w1CharEquiv (finCongr hcardW1.symm i)).comp h.sdiffTICyclicHypothesis.wFst := by
      rw [hχ₂]
      exact h.sdiffTICyclicHypothesis.omegaProdChar_one_right _
    exact congrArg (fun f => f.comp e.toMonoidHom) hpc
  -- `ξ ^ w₁ = 1` pointwise.
  have hξpow : ξ ^ hyp.w1 = 1 := by
    refine MonoidHom.ext fun w => Units.val_injective ?_
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one, hξeq,
      MonoidHom.comp_apply, MonoidHom.comp_apply, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply,
      hχ1pow, MonoidHom.one_apply, Units.val_one]
  have hdvd : orderOf ξ ∣ hyp.w1 := orderOf_dvd_of_pow_eq_one hξpow
  have hcop : (orderOf g).Coprime (orderOf ξ) := hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ :=
    tic.exists_intCast_sigma_omega_apply rfl (hyp.canonicalFullDadeApp hG hodd) ξ hcop
  exact ⟨n, by rw [step1]; exact hn⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the principal grid value** ((4.4)/(3.2)(b)): the `(0,0)` entry
of the aligned σ-grid is the trivial character `1_G`, `ω_{00}^σ = 1_G`.

For `i = 0`, column `0`: the source `ξ_{00} = (omegaProdChar (w1CharEquiv 0) χ₂).comp e` is trivial —
`w1CharEquiv 0 = 1` (`w1CharEquiv_zero`), `χ₂ = 1` (column `0`), so `omegaProdChar 1 1 = 1`
(`omegaProdChar_one_one`) and `(1).comp e = 1`.  Then `tic.omega 1 = 1_{tic.W}` and
`1_{tic.W}^σ = 1_G` (`sigma_trivial`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_zero_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.alignedOmegaSigmaGrid hG hodd 0 0 = trivialClassFunction G := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)))
      χ₂).comp e.toMonoidHom
  -- `alignedOmegaSigmaGrid 0 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd 0 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- both indices trivial ⟹ `ξ = 1`.
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  have hχ1 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 1 := by
    rw [show (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 from by simp, h.w1CharEquiv_zero]
  have hξ1 : ξ = 1 := by
    have hpc : h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂ = 1 := by
      rw [hχ₂, hχ1]; exact h.sdiffTICyclicHypothesis.omegaProdChar_one_one
    show (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂).comp e.toMonoidHom = 1
    rw [hpc, MonoidHom.one_comp]
  -- `tic.omega 1 = 1_{tic.W}`, and `1_{tic.W}^σ = 1_G`.
  have homega1 : (tic.omega (1 : ↥tic.W →* ℂˣ) : ClassFunction ↥tic.W ℂ)
      = trivialClassFunction ↥tic.W := by ext w; simp
  rw [step1, hξ1, homega1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_trivial]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the row-conjugation involution** ((3.9)(a)/(4.9)(a) on the
aligned column-`0` grid): complex conjugation of `ω_{i0}^σ` is again a column-`0` grid value
`ω_{i'0}^σ`, where `i' = rowInv i` is the **row-inversion** index (`w1CharEquiv i' =
(w1CharEquiv i)⁻¹`); moreover `i' = i ↔ i = 0` (in the odd-order dual `Ŵ₁`, `χ⁻¹ = χ ⟺ χ = 1`), and
`i ↦ i'` is an involution.

`mapRingEquiv conj (ω_{i0}^σ) = sigma(galoisMap conj (ω(ξ_i))) = sigma(ω(ξ_i⁻¹))`
(`sigma_mapRingEquiv_comm` + `galoisMap_conj_omega`), and `ξ_i⁻¹ = ξ_{i'}` since
`omegaProdChar χ₁ χ₂` inverts coordinatewise (`omegaProdChar_inv`), `w1CharEquiv (rowInv i) =
(w1CharEquiv i)⁻¹` (`w1CharEquiv_rowInv`) and `χ₂⁻¹ = χ₂` (column `0` is trivial).  This is the
(3.9)(a) ingredient that pairs the `i > 0` terms of `∑_i ω_{i0}^σ(g)`. -/
theorem Hypothesis.exists_rowInv_alignedOmegaSigma_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.alignedOmegaSigmaGrid hG hodd i 0)
        = hyp.alignedOmegaSigmaGrid hG hodd i' 0
      ∧ (i' = i ↔ i = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hodd j' 0) → j' = i) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ_a` of `tic.W` for any row `a`
  let ξ : Fin hyp.w1 → (↥tic.W →* ℂˣ) := fun a =>
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid a 0 = σ(ω ξ_a)` for any row `a`.
  have step1 : ∀ a, hyp.alignedOmegaSigmaGrid hG hodd a 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ) := by
    intro a
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial: `χ₂ = 1` (so `χ₂⁻¹ = χ₂`).
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- the row-inversion translated index
  let i' : Fin hyp.w1 :=
    finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i))
  -- `finCongr` round-trip: `finCongr hcardW1.symm i' = rowInv (finCongr hcardW1.symm i)`.
  have hround : finCongr hcardW1.symm i'
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i) := by
    show finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)
    simp
  -- `χ₂⁻¹ = χ₂` (column `0` is trivial).
  have hχ₂inv : χ₂⁻¹ = χ₂ := by rw [hχ₂, inv_one]
  -- key: `mapRingEquiv conj (ω_{a0}^σ) = ω_{a'0}^σ` for a row `a` with translated index `a'`.
  have hconj : ∀ a : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.alignedOmegaSigmaGrid hG hodd a 0)
        = hyp.alignedOmegaSigmaGrid hG hodd
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) 0 := by
    intro a
    have hroundA : finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a) := by simp
    -- `ξ_a⁻¹ = ξ_{a'}`.
    have hξinv : (ξ a)⁻¹
        = ξ (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) := by
      -- the underlying `omegaProdChar` factors invert; `χ₂⁻¹ = χ₂`, row inverts via `rowInv`.
      have hprod : (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂)⁻¹
          = h.sdiffTICyclicHypothesis.omegaProdChar
              (h.w1CharEquiv (finCongr hcardW1.symm
                (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
                χ₂ := by
        rw [hroundA, OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv,
          OddOrder.Peterfalvi.S06.omegaProdChar_inv, hχ₂]
        congr 1
      show ((h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp e.toMonoidHom)⁻¹
        = (h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
              χ₂).comp e.toMonoidHom
      refine MonoidHom.ext fun w => Units.val_injective ?_
      rw [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← hprod,
        MonoidHom.inv_apply]
    rw [step1 a, step1 (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))),
      tic.sigma_mapRingEquiv_comm rfl (hyp.canonicalFullDadeApp hG hodd) _ _,
      OddOrder.Peterfalvi.S06.galoisMap_conj_omega, hξinv]
  -- oddness of the dual `Ŵ₁` (from `Odd |G|` via `W₁ ≤ M ≤ G` and Pontryagin).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hoddM : Odd (Nat.card ↥M) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card M)
  have hoddW1 : Odd (Nat.card ↥h.W1) :=
    Odd.of_dvd_nat hoddM (Subgroup.card_subgroup_dvd_card h.W1)
  -- in the odd-order dual, `χ⁻¹ = χ ⟹ χ = 1`.
  have hsq_one : ∀ χ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ⁻¹ = χ → χ = 1 := by
    intro χ hχ
    haveI : Finite ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Finite.of_fintype _
    have hx2 : χ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← hχ]; exact inv_mul_cancel χ
    have h2 : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hc : orderOf χ ∣ Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := orderOf_dvd_natCard χ
    have hcop : Nat.Coprime 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [Nat.coprime_two_left, hcardDual, ← hcardW1]; exact hoddW1
    have hg : orderOf χ ∣ Nat.gcd 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) :=
      Nat.dvd_gcd h2 hc
    rw [hcop.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  refine ⟨i', hconj i, ?_, ?_⟩
  · -- `i' = i ↔ i = 0`.
    constructor
    · intro hii
      have hceq : (h.w1CharEquiv (finCongr hcardW1.symm i))⁻¹
          = h.w1CharEquiv (finCongr hcardW1.symm i) := by
        rw [← OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv, ← hround, hii]
      have hx1 : h.w1CharEquiv (finCongr hcardW1.symm i) = 1 := hsq_one _ hceq
      have hz : finCongr hcardW1.symm i = 0 :=
        h.w1CharEquiv.injective (hx1.trans h.w1CharEquiv_zero.symm)
      have h0 : i = finCongr hcardW1 (0 : Fin (Nat.card h.W1)) := by rw [← hz]; simp
      rw [h0]; simp
    · intro hi0
      have hz : finCongr hcardW1.symm i = 0 := by rw [hi0]; simp
      show finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)) = i
      rw [hz]
      have hrow0 : OddOrder.Peterfalvi.S06.rowInv h (0 : Fin (Nat.card h.W1)) = 0 := by
        rw [OddOrder.Peterfalvi.S06.rowInv, h.w1CharEquiv_zero, inv_one]
        exact h.w1CharEquiv.symm_apply_eq.mpr h.w1CharEquiv_zero.symm
      rw [hrow0, hi0]; simp
  · -- involution: applying the construction to `i'` returns `i`.
    intro j' hj'
    have hkey := hconj i'
    rw [hj'] at hkey
    have hii : finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i')) = i := by
      rw [hround, OddOrder.Peterfalvi.S06.rowInv_rowInv]; simp
    rw [hii] at hkey
    -- `hkey : ω_{j'0}^σ = ω_{i0}^σ`.  Conclude `j' = i` via grid orthonormality.
    by_contra hne
    have hortho := hyp.alignedOmegaSigmaGrid_inner hG hodd j' i 0 0
    rw [hkey, hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun hc => hne hc.1)] at hortho
    exact one_ne_zero hortho

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the parity bound** (the (10.6)(b) target): off the tame support
`Ã(M)`, at a `g` of order prime to `w₁`, the coherent image `ζ^{τ₁}(g)` is an **odd integer**.

By STEP 2 (`zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport`),
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.  Each `ω_{i0}^σ(g)` is a rational integer `n_i`
(`exists_intCast_alignedOmegaSigmaGrid_zero_column`, (3.9)(c)), so `ζ^{τ₁}(g) = (∑_i n_i : ℤ)`.
The terms pair under the row-conjugation involution `i ↦ i'` (`exists_rowInv_alignedOmegaSigma_conj`,
(3.9)(a)): `n_{i'} = n_i` (conjugation fixes the real integer), and the unique fixed point `i = 0`
carries the principal value `n_0 = 1` (`alignedOmegaSigmaGrid_zero_zero`, `ω_{00}^σ = 1_G`).  Hence the
off-principal terms sum to an even integer and `∑_i n_i = 1 + even` is odd; in particular
`|ζ^{τ₁}(g)| ≥ 1`.  This closes (10.6)(b) (issue 1009). -/
theorem Hypothesis.zeta_tau1_norm_ge_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) (hgord : (orderOf g).Coprime hyp.w1) :
    ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m := by
  haveI := hyp.finiteG
  classical
  -- STEP 2: `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.
  have hstep2 := hyp.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport
    hG coh hmu hos hzS hz1 hzconj hδpm hδj hg
  -- push the application through the finite sum (CoeFun, not DFunLike).
  have hsumapply : (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
      = ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
        = ∑ i ∈ s, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  -- (3.9)(c): each `ω_{i0}^σ(g)` is a rational integer `n i`.
  have hint : ∀ i : Fin hyp.w1,
      ∃ n : ℤ, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n : ℂ) := fun i =>
    hyp.exists_intCast_alignedOmegaSigmaGrid_zero_column hG hG.odd i hgord
  let n : Fin hyp.w1 → ℤ := fun i => (hint i).choose
  have hn : ∀ i, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n i : ℂ) := fun i => (hint i).choose_spec
  -- `m := ∑ n i`, and `ζ^{τ₁}(g) = (m : ℂ)`.
  have hval : coh.tau1 params.zeta g = ((∑ i : Fin hyp.w1, n i : ℤ) : ℂ) := by
    rw [hstep2, hsumapply]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hn i)
  refine ⟨∑ i : Fin hyp.w1, n i, hval, ?_⟩
  -- the row-conjugation involution `ρ` ((3.9)(a)).
  have hB : ∀ a : Fin hyp.w1, ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
        = hyp.alignedOmegaSigmaGrid hG hG.odd i' 0
      ∧ (i' = a ↔ a = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hG.odd j' 0) → j' = a) := fun a =>
    hyp.exists_rowInv_alignedOmegaSigma_conj hG hG.odd a
  let ρ : Fin hyp.w1 → Fin hyp.w1 := fun a => (hB a).choose
  have hρconj : ∀ a, ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
      = hyp.alignedOmegaSigmaGrid hG hG.odd (ρ a) 0 := fun a => (hB a).choose_spec.1
  have hρfix : ∀ a, ρ a = a ↔ a = 0 := fun a => (hB a).choose_spec.2.1
  have hρinv : ∀ a, ρ (ρ a) = a := fun a => (hB a).choose_spec.2.2 (ρ (ρ a)) (hρconj (ρ a))
  -- the involution preserves `n`: `n (ρ a) = n a` (conjugation fixes the real integer).
  have hnρ : ∀ a, n (ρ a) = n a := by
    intro a
    have hc := congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) (hρconj a)
    simp only [ClassFunction.mapRingEquiv_apply] at hc
    rw [hn a, hn (ρ a), map_intCast] at hc
    exact_mod_cast hc.symm
  -- `n 0 = 1` (the principal value `ω_{00}^σ = 1_G`).
  have hn0 : n 0 = 1 := by
    have h00 := hyp.alignedOmegaSigmaGrid_zero_zero hG hG.odd
    have := hn 0
    rw [h00, trivialClassFunction_apply] at this
    exact_mod_cast this.symm
  -- off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {0}`).
  have heven : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i := by
    have hz : ((∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hnρ a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hρfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        have hca : ρ a = 0 := hcontra
        calc a = ρ (ρ a) := (hρinv a).symm
          _ = ρ 0 := by rw [hca]
          _ = 0 := (hρfix 0).mpr rfl
      · intro a _; exact hρinv a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- `∑ n i = n 0 + (even) = 1 + even` is odd.
  have hsplit : (∑ i : Fin hyp.w1, n i)
      = n 0 + ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i :=
    (Finset.add_sum_erase Finset.univ n (Finset.mem_univ 0)).symm
  rw [hsplit, hn0]
  rcases heven with ⟨c, hc⟩
  exact ⟨c, by rw [hc]; ring⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one.

Conjunct (a) (the summed isometry) is the genuine `muColumn_tau1_pin` (the §10 specialisation of
(5.8)).  Conjunct (b) (the (10.6)(b) parity bound) is now genuine and proven: off `Ã(M) = dadeSupport`,
at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an **odd integer** (`zeta_tau1_norm_ge_one`), hence
`|ζ^{τ₁}(g)| ≥ 1` — replacing the former opaque `zeta_tau1_norm_bound` placeholder field.  The
(10.3)/(10.5) carrier pins (`hmu`/`hos`/`hzS`/`hz1`/`hzconj`/`hδpm`/`hδj`) are discharged by the
constructed `params` (`w2_prime_and_parameter_independence`). -/
theorem tau1_values_and_norm_bound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (∀ (j : Fin hyp.w2), j ≠ 0 →
        coh.tau1 (∑ i : Fin hyp.w1, params.mu i j) =
          (params.delta : ℂ) • ∑ i : Fin hyp.w1, params.omegaSigma i j) ∧
      (∀ (g : G), g ∉ hyp.dadeData.dade.dadeSupport → (orderOf g).Coprime hyp.w1 →
          ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m) := by
  have hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1 := by
    intro jj hjj
    rw [← hmu, params.degree_independent 0 jj hjj]
    exact_mod_cast (by have := params.d_gt_one; omega : params.d ≠ 1)
  refine ⟨fun j hj0 => ?_, ?_⟩
  · -- (10.6)(a): the summed isometry `μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.
    rw [hmu, hos]
    exact hyp.muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  · -- (10.6)(b): off `Ã(M)`, at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an odd integer
    -- (`zeta_tau1_norm_ge_one`); in particular `|ζ^{τ₁}(g)| ≥ 1`.
    intro g hg hgord
    exact hyp.zeta_tau1_norm_ge_one hG coh hmu hos hzS hz1 hzconj hδpm hδj hg hgord


end OddOrder.Peterfalvi.S12
