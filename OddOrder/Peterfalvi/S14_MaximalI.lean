/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.Peterfalvi.S09_CertificateDischarge
import OddOrder.Peterfalvi.S07_CoherenceConstantDegree
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import OddOrder.GroupTheory.RepresentationTheory.CyclotomicCharacterCongruence
import Mathlib.RepresentationTheory.Irreducible

/-!
# Peterfalvi Section 14: Maximal Subgroups of Type I

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 14, pp. 69--74.

This section proves that every maximal subgroup of type I is a Frobenius group
with kernel `M_F`.  The proof first sets up the Dade isometry attached to a
type-I maximal subgroup, proves orthogonality and constancy properties for the
families `R(chi)`, and then excludes a minimal counterexample with a non-cyclic
Sylow subgroup in `M / M_F`.

The scaffold records the named endpoints (12.1)--(12.17).  The detailed
character decompositions, rho maps, and integer congruence calculations are kept
as proposition fields until the lower-level Dade/rho API is ready for this
maximal-subgroup layer.
-/

namespace OddOrder.Peterfalvi.S14
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (12.1): the type-I hypothesis -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1)**: setup for a maximal subgroup `L` of type I.

`G` is finite (carried as the instance field `finiteG`, the `S12`/`S15`
`FiniteInduce` pattern), so the *genuine* Dade isometry `tau`, the induced family
`Sset = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (`H = L_F`), and the support `A = A(L)`
are honest projections (`Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A`)
rather than unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis
for `A(L)` (supplied by `S10.dadeSupportHypotheses_typeI`), and `hconj` is its
`L`-conjugation invariance; together they build the Dade isometry relative to
`(A(L), L, G)` (Peterfalvi (12.1)). -/
structure Hypothesis (L : Subgroup G) where
  [finiteG : Finite G]
  maximal : L ∈ maximalSubgroups G
  typeI : TypeIData L
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData L (typeIA L typeI)
  hconj : dadeData.dade.HConjInvariant

namespace Hypothesis

/-- Peterfalvi's `H = L_F`. -/
def H {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  hyp.typeI.typeF.H

/-- Peterfalvi's `H'`, represented as an ambient subgroup. -/
def Hprime {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  derivedInG hyp.H

/-- Peterfalvi's ambient `A(L)` set from Definition (8.3). -/
def ambientA {L : Subgroup G} (hyp : Hypothesis L) : Set G :=
  typeIA L hyp.typeI

/-- Peterfalvi's support `A(L)` restricted to `L` (the `supportInSubgroup` of the
ambient `A(L)`), the genuine support of the Dade isometry, no longer an
unconstrained field. -/
def A {L : Subgroup G} (hyp : Hypothesis L) : Set ↥L :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's family `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` of (12.1),
`H = L_F`, induced via the canonical `ClassFunction.induce`.  No longer an
unconstrained field. -/
noncomputable def Sset {L : Subgroup G} (hyp : Hypothesis L) :
    Set (ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  { χ | ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      χ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) }

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The **filtration** `S(A) = {Ind_H^L θ | θ ≠ 1, A ⊆ Ker θ}` of the witness family `Sset`
(Peterfalvi (6.1)), indexed by subgroups `A ≤ L`.  `S(⊥) = Sset`, and the abstract Peterfalvi (6.3)
descent `six_three_of_six_two_oracle` runs on this filtration (with `SOf = SsubFiltration`,
`τ = tau`, `A0 = A`, kernel `H = L_F`).  Mirrors the Sibley `SibleyDadeHypothesis.SsubFiltration`
but over the witness's canonical `(L_F).subgroupOf L` kernel and Dade map. -/
noncomputable def SsubFiltration {L : Subgroup G} (hyp : Hypothesis L) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  { φ | ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      ((A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
          Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
      φ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) }

/-- `S(⊥) = Sset`: the kernel condition `⊥ ⊆ Ker θ` is vacuous (Peterfalvi's `S(1) = S`). -/
theorem SsubFiltration_bot {L : Subgroup G} (hyp : Hypothesis L) :
    hyp.SsubFiltration ⊥ = hyp.Sset := by
  ext φ
  simp only [SsubFiltration, Sset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ, hθ, -, hφ⟩; exact ⟨θ, hθ, hφ⟩
  · rintro ⟨θ, hθ, hφ⟩
    refine ⟨θ, hθ, ?_, hφ⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _

/-- Every member of a filtration level `S(A)` lies in the ambient family `Sset`. -/
theorem SsubFiltration_subset_Sset {L : Subgroup G} (hyp : Hypothesis L) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.Sset := by
  intro φ hφ
  simp only [SsubFiltration, Set.mem_setOf_eq] at hφ
  obtain ⟨θ, hθ, -, hφeq⟩ := hφ
  simp only [Sset, Set.mem_setOf_eq]
  exact ⟨θ, hθ, hφeq⟩

/-- The filtration is **antitone**: a larger kernel-constraint subgroup gives fewer members,
`A ≤ B → S(B) ⊆ S(A)` (Peterfalvi (6.1)). -/
theorem SsubFiltration_antitone {L : Subgroup G} (hyp : Hypothesis L) {A B : Subgroup ↥L}
    (hAB : A ≤ B) : hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  simp only [SsubFiltration, Set.mem_setOf_eq] at hφ ⊢
  obtain ⟨θ, hθ, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A(L), L, G)` of (12.1), pinned to
the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data `dadeData`.
No longer an unconstrained field. -/
noncomputable def tau {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Peterfalvi (7.1) `ρ`-machinery data for `(L, A(L))`** — the §7 foundation for the (12.16)
Dade calculation.  Built genuinely from the §10 Dade isometry carried by `hyp.dadeData`/`hyp.hconj`:
unlike the type-`P` `S12.Hypothesis.toHypothesis71`, the type-I support `A(L) = typeIA` is already the
set on which `dadeData` lives, so no restriction is needed — the Dade map, its `IsDadeMap`
certificate, and the `L`-equivariance transfer directly.  This `S09.Hypothesis71` is what lets the
§9 norm machinery — `chiRho_norm_sq_le` (7.2.b), `chiRho_integral_inequality` (7.3),
`family_inequality` (7.5), and `Hypothesis78.NormEstimates` (7.8.b) — apply to `L`. -/
noncomputable def toHypothesis71 {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (typeIA L hyp.typeI) L where
  hyp := hyp.dadeData.dade
  τ := (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.toDadeMap
  isDadeMap := (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeMap
  hConjInvariant := hyp.hconj

end Hypothesis

/-- Conjugation transports the centralizer of a singleton:
`g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)` (S14-local copy of the S12 helper; pure group theory). -/
private theorem conj_smul_centralizer_singleton (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group

/-- **Peterfalvi (8.14)/(8.15)**: the support kernel `R(x)` is `M`-conjugation equivariant
(S14-local copy of the S12 helper).  `supportKernel M M X (g x g⁻¹) = g · supportKernel M M X x`
for `g ∈ M` and `X` an `M`-invariant set. -/
private theorem supportKernel_conj_invariant {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    supportKernel M M X (g * x * g⁻¹) = MulAut.conj g • supportKernel M M X x := by
  have hMfix : MulAut.conj g • maxNilpotentNormalHall M = maxNilpotentNormalHall M :=
    conj_smul_eq_self_of_mem_normalizer
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hg)
  have hMself : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← hMself]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  have hescape : (g * x * g⁻¹ ∈ escapingCentralizerSet M X)
      ↔ (x ∈ escapingCentralizerSet M X) := by
    simp only [escapingCentralizerSet, Set.mem_setOf_eq, hmem, hcent]
  unfold supportKernel
  by_cases hx : x ∈ escapingCentralizerSet M X
  · rw [if_pos (hescape.mpr hx), if_pos hx, Subgroup.smul_inf, hMfix,
        conj_smul_centralizer_singleton]
  · rw [if_neg (fun h => hx (hescape.mp h)), if_neg hx, Subgroup.smul_bot]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1), construction from explicit type-I data**: a type-I maximal subgroup `L`
with a *given* `TypeIData` carries the (12.1) Hypothesis whose `typeI` field is exactly that data.
This refines `exists_typeI_hypothesis` by preserving the identity of the type-I witness, so callers
holding a `TypeIData` (e.g. the Frobenius structure of (12.10)) can recover it — and the associated
Frobenius decomposition of `H = L_F` — from the resulting `Hypothesis`.  The Dade isometry, induced
family, and support are the genuine `S07.dadeIntegralCharacterMap`, `Sset`, and `A(L)`; the only
inputs are the (8.15) Dade support data (`S10.dadeSupportHypotheses_typeI`) and the conjugation
invariance `hconj` of the support kernels (a (8.14)/(8.15) fact). -/
theorem hypothesis_of_typeIData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (data : TypeIData L) :
    ∃ hyp : Hypothesis L, hyp.typeI = data := by
  obtain ⟨dadeData⟩ :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeI hG hL data).1
  -- (8.14)/(8.15): the support kernels `R(a)` are `L`-conjugation invariant.
  have hconj : dadeData.dade.HConjInvariant := by
    intro a l
    simp only [dadeData.H_eq_supportKernel]
    refine supportKernel_conj_invariant l.2 ?_
    exact ⟨fun h => by simpa using dadeData.dade.L_normalizes_A l⁻¹ h,
      fun h => dadeData.dade.L_normalizes_A l h⟩
  exact ⟨{ maximal := hL, typeI := data, dadeData := dadeData, hconj := hconj }, rfl⟩

/-- **Peterfalvi (12.1), existence**: every type-I maximal subgroup `L` carries the (12.1)
Hypothesis.  Forgetful form of `hypothesis_of_typeIData`.  Mirrors
`S12.exists_hypothesis_of_typeIIIorIVorV`. -/
theorem exists_typeI_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (hType : IsTypeI L) :
    Nonempty (Hypothesis L) := by
  obtain ⟨data⟩ := hType
  obtain ⟨hyp, _⟩ := hypothesis_of_typeIData hG hL data
  exact ⟨hyp⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The type-I family `S = {Ind_H^L θ}` is closed under complex conjugation**
(Peterfalvi §12, the `χ̄ ∈ S` input to (12.2.b)): for `χ = Ind_H^L θ ∈ S` with
`θ ∈ Irr H`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_H^L θ̄` (`ClassFunction.induce_conj`),
and `θ̄` is again a non-trivial irreducible of `H = L_F`. -/
theorem Sset_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Sset := by
  classical
  intro φ hφ
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

/-! ## (12.2): character decomposition and Dade domain -/

/-- **Peterfalvi (12.2)**, genuine carrier: the constituent decomposition of `χ ∈ S`.
`S(χ) = constituents` is the (finite, nonempty) set of irreducible constituents of `χ`, all of
equal degree ((12.2.a)), each non-real (so `φ ≠ φ̄`) and supported in `A(L) ∪ {1}` (so the
differences `φ − φ̄` lie in the Dade domain `A(L)`, feeding (12.2.b) `R1`/`Rset`). -/
structure CharacterDecompositionData {L : Subgroup G} (hyp : Hypothesis L)
    (chi : ClassFunction ↥L ℂ) where
  chi_mem : chi ∈ hyp.Sset
  /-- `S(χ)`: the irreducible constituents of `χ`. -/
  constituents : Finset (IrreducibleCharacter ↥L)
  constituents_nonempty : constituents.Nonempty
  /-- (12.2.a): `χ` is the multiplicity-one sum of its constituents. -/
  decomp : chi = ∑ φ ∈ constituents, (φ : ClassFunction ↥L ℂ)
  /-- (12.2.a): the constituents share a common degree. -/
  equal_degree : ∀ φ ∈ constituents, ∀ φ' ∈ constituents,
    ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
  /-- Each constituent is non-real, so `φ ≠ φ̄` and `φ − φ̄ ≠ 0` ((12.2.b)). -/
  not_real : ∀ φ ∈ constituents, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)
  /-- (12.2.a): each constituent is supported in `A(L) ∪ {1}` (`H ⊄ Ker φ` (1.5.a), then (1.2)),
  so each difference `φ − φ̄` is supported in the Dade domain `A(L)`. -/
  supported : ∀ φ ∈ constituents, (φ : ClassFunction ↥L ℂ).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}

/-- **A commuting element of coprime order is a power of the product** — `g ∈ ⟨zg⟩` when `z`, `g`
commute with coprime orders.  `(zg)^{|z|} = g^{|z|}` (commuting, `z^{|z|}=1`), and `g ∈ ⟨g^{|z|}⟩`
since `gcd(|z|, |g|) = 1` (`mem_zpowers_pow_iff`); hence `g ∈ ⟨(zg)^{|z|}⟩ ≤ ⟨zg⟩`.  This is the
`π`-part step of Peterfalvi (8.2.c): once `(2.1)` conjugates `cg` to a *commuting* product `zg`
(`z ∈ C_H(g)`), `g` is a power of `zg`, so `g` centralizes whatever `zg` does. -/
theorem mem_zpowers_mul_of_commute_coprime {Γ : Type*} [Group Γ] {z g : Γ}
    (hzg : Commute z g) (hcop : Nat.Coprime (orderOf z) (orderOf g)) :
    g ∈ Subgroup.zpowers (z * g) := by
  have hpow : (z * g) ^ orderOf z = g ^ orderOf z := by
    rw [hzg.mul_pow, pow_orderOf_eq_one, one_mul]
  have hg : g ∈ Subgroup.zpowers (g ^ orderOf z) := mem_zpowers_pow_iff.mpr hcop
  rw [← hpow] at hg
  have hle : Subgroup.zpowers ((z * g) ^ orderOf z) ≤ Subgroup.zpowers (z * g) :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers (z * g)).pow_mem (Subgroup.mem_zpowers _) _)
  exact hle hg

/-- **Type-`F` class-fixing: an element of `U ∖ U₁` fixes only the identity `H`-class**
(the core of Peterfalvi (8.2.c)).  This is the type-`F` analogue of
`ConjugationBrauer.fixed_eq_one_of_not_mem_of_centralizer_le`, which uses the Frobenius condition
`C_G(h) ≤ H`; here the weaker type-`F` condition `U ⊓ C_G(x) ≤ U₁` (`TypeFData.centralizer_le_U1`)
suffices, at the cost of the coprime `(2.1)` step.  If `g ∈ U ∖ U₁` (`g` coprime to `H`, normalizing
`H`) fixes a class `⟦h⟧` (`h ≠ 1`), then some `c·g` centralizes `h` (`IsConj`); by (2.1)
(`exists_mem_centralizer_conj`) `c·g` is `H`-conjugate to `z·g` with `z ∈ C_H(g)`, so `z·g`
centralizes `w = yhy⁻¹ ≠ 1`; as `z` commutes with `g` coprimely, `g ∈ ⟨z·g⟩` centralizes `w`
(`mem_zpowers_mul_of_commute_coprime`), whence `g ∈ U ⊓ C_G(w) ≤ U₁` — contradiction. -/
theorem fixed_conjClass_eq_one_of_typeF {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [hHN : H.Normal] {g : Γ}
    (hcop : Nat.Coprime (orderOf g) (Nat.card ↥H)) (hgU : g ∈ U) (hgU1 : g ∉ U1)
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1)
    {C : ConjClasses ↥H}
    (hfix : ConjClasses.conjByPerm (G := Γ) (H := H) g C = C) :
    C = 1 := by
  classical
  have hnorm : ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun x hx => hHN.conj_mem x hx g
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  by_cases hh : h = 1
  · rw [hh, ConjClasses.one_eq_mk_one]
  exfalso
  have hmk : ConjClasses.mk (ClassFunction.conjByMulEquiv (G := Γ) (H := H) g h)
      = ConjClasses.mk h := by simpa [ConjClasses.conjByPerm_mk] using hfix
  have hisConj : IsConj (ClassFunction.conjByMulEquiv (G := Γ) (H := H) g h) h :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk
  obtain ⟨c, hc⟩ := isConj_iff.mp hisConj
  have hcG : (c : Γ) * (g * (h : Γ) * g⁻¹) * (c : Γ)⁻¹ = (h : Γ) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ClassFunction.conjByMulEquiv_apply]
      using congrArg Subtype.val hc
  have hxconj : ((c : Γ) * g) * (h : Γ) * (((c : Γ) * g)⁻¹) = (h : Γ) := by
    simpa [mul_assoc] using hcG
  have hxcent : (c : Γ) * g ∈ Subgroup.centralizer ({(h : Γ)} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul := congrArg (fun y : Γ => y * ((c : Γ) * g)) hxconj
    simpa [mul_assoc] using hmul
  -- (2.1): `c·g ∈ Hg` is `H`-conjugate to `z·g` with `z ∈ C_H(g)`.
  obtain ⟨z, hz, y, hy, hyz⟩ :=
    exists_mem_centralizer_conj (g := g) (H := H) hcop hnorm c.property
  have hzC : z ∈ Subgroup.centralizer ({g} : Set Γ) := (Subgroup.mem_inf.mp hz).2
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hz).1
  -- `w = y·h·y⁻¹ ∈ H`, `w ≠ 1`.
  set w : Γ := y * (h : Γ) * y⁻¹ with hwdef
  have hwH : w ∈ H := H.mul_mem (H.mul_mem hy (h.property)) (H.inv_mem hy)
  have hh1 : (h : Γ) ≠ 1 := fun hc1 => hh (Subtype.ext hc1)
  have hw1 : w ≠ 1 := by
    rw [hwdef]; intro hc1
    exact hh1 (by
      have := congrArg (fun t : Γ => y⁻¹ * t * y) hc1
      simpa [mul_assoc] using this)
  -- `z·g` centralizes `w`.
  have hzgw : z * g ∈ Subgroup.centralizer ({w} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hyz, hwdef]
    have hce := (Subgroup.mem_centralizer_singleton_iff).mp hxcent
    calc y * ((c : Γ) * g) * y⁻¹ * (y * (h : Γ) * y⁻¹)
        = y * (((c : Γ) * g) * (h : Γ)) * y⁻¹ := by group
      _ = y * ((h : Γ) * ((c : Γ) * g)) * y⁻¹ := by rw [hce]
      _ = y * (h : Γ) * y⁻¹ * (y * ((c : Γ) * g) * y⁻¹) := by group
  -- `z` commutes with `g` coprimely ⟹ `g ∈ ⟨z·g⟩` centralizes `w`.
  have hCommute : Commute z g :=
    Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hcopzg : Nat.Coprime (orderOf z) (orderOf g) := by
    have hzdvd : orderOf z ∣ Nat.card ↥H := by
      have := orderOf_dvd_natCard (⟨z, hzH⟩ : ↥H)
      simpa [orderOf_injective (H.subtype) H.subtype_injective ⟨z, hzH⟩] using this
    exact (Nat.Coprime.coprime_dvd_right hzdvd hcop).symm
  have hgzpow : g ∈ Subgroup.zpowers (z * g) := mem_zpowers_mul_of_commute_coprime hCommute hcopzg
  have hgw : g ∈ Subgroup.centralizer ({w} : Set Γ) :=
    (Subgroup.zpowers_le.mpr hzgw) hgzpow
  exact hgU1 (hcent w hwH hw1 (Subgroup.mem_inf.mpr ⟨hgU, hgw⟩))

/-- **Type-`F` fixed-class count is `1`** for `g ∈ U ∖ U₁`: the identity is the unique fixed
`H`-class (`fixed_conjClass_eq_one_of_typeF`), so `#{fixed classes} = 1`. -/
theorem card_fixedPoints_conjClassPerm_eq_one_of_typeF {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [H.Normal] {g : Γ}
    (hcop : Nat.Coprime (orderOf g) (Nat.card ↥H)) (hgU : g ∈ U) (hgU1 : g ∉ U1)
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := Γ) (H := H) g)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun C D => Subtype.ext ?_⟩,
    ⟨⟨1, ConjClasses.conjByPerm_one (G := Γ) (H := H) g⟩⟩⟩
  exact (fixed_conjClass_eq_one_of_typeF hcop hgU hgU1 hcent C.2).trans
    (fixed_conjClass_eq_one_of_typeF hcop hgU hgU1 hcent D.2).symm

/-- **Peterfalvi (8.2.c): `I(θ) ∩ U ⊆ U₁`** for a type-`F` group.  If `θ ∈ Irr H ∖ {1}` and
`g ∈ I(θ) ∩ U` but `g ∉ U₁`, then (`g` coprime to `H`) `g` fixes only the identity `H`-class
(`card_fixedPoints_conjClassPerm_eq_one_of_typeF`), so by Brauer's permutation lemma
(`fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one`) `g` fixes only the trivial character —
contradicting `g ∈ I(θ)`, `θ ≠ 1`.  Hence `g ∈ U₁`.  This is the inertia bound feeding the equal
degree of the constituents of `Ind_H^L θ` in the general type-I (12.2.a). -/
theorem typeF_inertia_inf_le_U1 {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [H.Normal]
    (hUHcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥H))
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1)
    (θ : IrreducibleCharacter ↥H) (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) ⊓ U ≤ U1 := by
  intro g hg
  have hgI := (Subgroup.mem_inf.mp hg).1
  have hgU := (Subgroup.mem_inf.mp hg).2
  by_contra hgU1
  have hcop : Nat.Coprime (orderOf g) (Nat.card ↥H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard U hgU) hUHcop
  have hcard1 := card_fixedPoints_conjClassPerm_eq_one_of_typeF hcop hgU hgU1 hcent
  have hfixθ : IrreducibleCharacter.conjByPerm (G := Γ) (H := H) g θ = θ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.conjByPerm_apply, IrreducibleCharacter.coe_conjBy]
    exact ClassFunction.mem_inertia.mp hgI
  exact hθ (fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one g hcard1 hfixθ)

/-- **Type-`F` induced-character constituent structure** (Peterfalvi (8.2.c) + (1.2)/(1.5.a) +
(1.7.c) + Clifford; a faithful §8 obligation — the deep content is type-`F` character theory living
in §8, not §12).  For a type-I maximal `L` and `χ = Ind_H^L θ ∈ S` (`θ ∈ Irr H ∖ {1}`), `χ` is the
multiplicity-one sum of a nonempty finite set of equal-degree, non-real irreducible constituents,
each supported in `A(L) ∪ {1}`.  Body = §8 type-`F` Clifford theory: (8.2.c) `I(θ) ∩ U ⊆ U₁` +
induced-degree (1.7.c) for the equal degree, `(Res_H φ, 1_H) = 0` (1.5.a) + (1.2) for the support. -/
theorem typeI_induced_char_constituents [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ S : Finset (IrreducibleCharacter ↥L), S.Nonempty ∧
      chi = ∑ φ ∈ S, (φ : ClassFunction ↥L ℂ) ∧
      (∀ φ ∈ S, ∀ φ' ∈ S, ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
        = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1) ∧
      (∀ φ ∈ S, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)) ∧
      (∀ φ ∈ S, (φ : ClassFunction ↥L ℂ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}) := by
  sorry

open scoped Classical in
/-- **Odd-order Frobenius: a nontrivial induced character is a single non-real irreducible supported
on the (normal) kernel.**  In a Frobenius group `Γ` of odd order with kernel `H`, for `θ ∈ Irr H`,
`θ ≠ 1`, the induced `Ind_H^Γ θ` is irreducible (`isIrreducibleCharacter_induce_of_frobeniusGroup`),
**non-real** (odd order, `not_isReal_of_ne_trivial_of_odd_card'`, `χ ≠ 1` via `⟨Ind θ, 1⟩ = 0`),
and supported on `H` (it vanishes off the **normal** `H`, `induceSum_eq_zero_of_not_conjugatesInto`).
Packaged as an **opaque** `ξ : Irr Γ` (with `↑ξ = Ind θ`) — stated with explicit `Fintype`/
`Invertible` binders (not the `FiniteInduce` scope) so the coset-sum coercion stays `whnf`-cheap.
Discharges the type-I (12.2.a) constituent structure trivially for a Frobenius `L`
(`frobenius_typeI_induced_char_constituents`). -/
theorem frobenius_induce_char_singleton {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [H.Normal] [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] (hodd : Odd (Nat.card Γ)) {W : Subgroup Γ}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup Γ H W)
    (θ : IrreducibleCharacter ↥H) (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    ∃ ξ : IrreducibleCharacter Γ,
      (ξ : ClassFunction Γ ℂ) = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∧
      ¬ ClassFunction.IsReal (ξ : ClassFunction Γ ℂ) ∧
      (ξ : ClassFunction Γ ℂ).support ⊆ (H : Set Γ) := by
  have hirr := isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ
  have hne_triv : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ :
      IrreducibleCharacter Γ) ≠ trivialIrreducibleCharacter Γ := by
    intro h
    have hrestrict : ClassFunction.restrict H
          (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ)
        = (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ) := by
      ext x
      simp [ClassFunction.restrict_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg hθ]
    have hcf : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
        = (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) h
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  refine ⟨⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩, rfl,
    not_isReal_of_ne_trivial_of_odd_card' hodd hne_triv, ?_⟩
  -- support: `Ind θ` vanishes off the normal `H`.
  intro x hx
  rw [ClassFunction.mem_support] at hx
  by_contra hxH
  refine hx ?_
  have hconj : (x : Γ) ∉ ClassFunction.conjugatesInto H := by
    rw [ClassFunction.mem_conjugatesInto]
    rintro ⟨y, hy⟩
    have hcm := ‹H.Normal›.conj_mem (y⁻¹ * x * y) hy y
    have he : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    exact hxH (he ▸ hcm)
  rw [ClassFunction.induce_apply, ← ClassFunction.induceSum_apply,
    ClassFunction.induceSum_eq_zero_of_not_conjugatesInto _ hconj, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (12.2.a) for a Frobenius type-I `L`** — the constituent decomposition is
**trivial**.  When `L` is a Frobenius group with kernel `H = L_F` (e.g. the witness `L` of (12.10),
`witness_L_frobenius`), every `χ = Ind_H^L θ ∈ S` (`θ ≠ 1`) is already **irreducible**, so its
constituent set is the singleton `{χ}`: decomposition, equal-degree, nonemptiness immediate;
non-realness from the odd order of `L`; support `H#` because `Ind θ` vanishes off the normal `H`.
This discharges `typeI_induced_char_constituents` **without (8.2.c)** for the Frobenius case — the
one the (12.16) witness-side `R(χ)`/(12.3)/(12.4) machinery actually consumes.  The heavy content is
in `frobenius_induce_char_singleton` (clean instances); here only the `H# ⊆ supportInSubgroup` bridge
and the singleton packaging remain. -/
theorem frobenius_typeI_induced_char_constituents [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ S : Finset (IrreducibleCharacter ↥L), S.Nonempty ∧
      chi = ∑ φ ∈ S, (φ : ClassFunction ↥L ℂ) ∧
      (∀ φ ∈ S, ∀ φ' ∈ S, ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
        = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1) ∧
      (∀ φ ∈ S, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)) ∧
      (∀ φ ∈ S, (φ : ClassFunction ↥L ℂ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}) := by
  classical
  obtain ⟨θ, hθ_ne, rfl⟩ := hchi
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨ξ, hξcoe, hξreal, hξsupp⟩ :=
    frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  refine ⟨{ξ}, Finset.singleton_nonempty _, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_singleton, hξcoe]
  · intro φ hφ φ' hφ'
    rw [Finset.mem_singleton] at hφ hφ'
    rw [hφ, hφ']
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    rw [hφ]; exact hξreal
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    rw [hφ]
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inr hx1
    · refine Or.inl ?_
      have hxK : x ∈ (hyp.typeI.typeF.H).subgroupOf L := SetLike.mem_coe.mp (hξsupp hx)
      exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hxK, hx1⟩

/-- **Peterfalvi (12.2.a)**: each `χ ∈ S` decomposes (multiplicity one) into irreducible
constituents of equal degree, each non-real and supported in `A(L) ∪ {1}`.  The §12 assembly:
unpack the type-`F` constituent structure (`typeI_induced_char_constituents`) into the genuine
`CharacterDecompositionData` carrier — whose R(χ) blocks of (12.2.b) then come from `R1`/`Rset`.  The deep type-`F` Clifford content ((8.2.c) inertia +
(1.7.c)/(1.5.a)/(1.2)) is isolated in the obligation, keeping this assembly `sorry`-free. -/
theorem character_decomposition_and_dade_domain [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi, data.chi_mem = hchi := by
  obtain ⟨S, hne, hdecomp, hdeg, hreal, hsupp⟩ := typeI_induced_char_constituents hyp hchi
  exact ⟨⟨hchi, S, hne, hdecomp, hdeg, hreal, hsupp⟩, rfl⟩

/-- **Peterfalvi (12.2.a) `CharacterDecompositionData` for a Frobenius type-I `L`** —
`character_decomposition_and_dade_domain` without the (8.2.c)-gated `typeI_induced_char_constituents`
obligation.  For a Frobenius `L` (kernel `H = L_F`) the constituent structure is the trivial
singleton `{χ}` (`frobenius_typeI_induced_char_constituents`), so the carrier is **sorry-free**.
This is the `data` the witness-`L` side of (12.16) needs (`ψ ∈ ℤ[R(χ_L)]` via (5.5), and the
`R(χ_L) ⊥ R(χ_M)` orthogonality of (12.3)); the witness `L` is Frobenius by (12.10)
(`witness_L_frobenius`), whose `hfrob` is cited under the signature contract. -/
theorem frobenius_character_decomposition_and_dade_domain [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi, data.chi_mem = hchi := by
  obtain ⟨S, hne, hdecomp, hdeg, hreal, hsupp⟩ :=
    frobenius_typeI_induced_char_constituents hG hyp hfrob hAH hchi
  exact ⟨⟨hchi, S, hne, hdecomp, hdeg, hreal, hsupp⟩, rfl⟩

/-! ## (12.2.b): the orthonormal Dade-image families `R₁(φ)` and `R(χ)` -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The constituent difference `φ̄ − φ` (`φ ∈ S(χ)`) is supported in the Dade domain
`A(L) = supportInSubgroup (A(L)) L`: `φ` is supported in `A(L) ∪ {1}` (`data.supported`), `φ̄` has
the same support (conjugation preserves it), and the value at `1` cancels (`φ̄(1) = φ(1)`, the
degree being a real natural number).  Feeds the difference-support constructor
`S07.dadeOrthonormalCharacterImageFamilyOfDiff` for the orthonormal block `R₁(φ)`. -/
theorem R1_diffsupp {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  haveI := hyp.finiteG
  have hsupp_eq : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)) x ≠ 0 := hx
  have hxsupp : x ∈ (φ : ClassFunction ↥L ℂ).support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases data.supported φ hφ hxsupp with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
    exact hx0 (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hd, star_natCast, sub_self])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the underlying difference image `{μ_φ, ν_φ, ε}` of `R₁(φ)`.**  The Dade
`CharacterDifferenceImage` of the constituent `φ ∈ S(χ)`: `(φ − φ̄)^τ = ε·(μ_φ − ν_φ)`.  `R1` is its
`toOrthonormalImage`; the raw `{μ_φ, ν_φ}` data is what the cross-`L` (4.1) orthogonality of (12.3)
consumes (`S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across`). -/
noncomputable def R1cdi {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    hyp.dadeData.dade hyp.hconj φ (data.not_real φ hφ) (R1_diffsupp data hφ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the orthonormal block `R₁(φ)`**: for a constituent `φ ∈ S(χ)`, the
orthonormal Dade-image family of `φ − φ̄`, "an orthonormal subset of `ℤ[Irr G]` of cardinality 2"
with `(φ − φ̄)^τ = ∑_{α ∈ R₁(φ)} α` (the `image_eq` field).  The `toOrthonormalImage` of the
difference image `R1cdi`.  This is the `imageFamily` the `CharacterPsiDecomposition` engine of
(12.4)/(12.5) consumes; its underlying `{μ, ν}` feeds the (12.3) cross-`L` orthogonality. -/
noncomputable def R1 {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  (R1cdi data hφ).toOrthonormalImage

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b)**: `R(χ) = ⋃_{φ ∈ S(χ)} R₁(φ)`, the union of the two-element orthonormal
Dade-image blocks `R₁(φ) = (R1 data hφ).imageSet` of the constituents.  A class function `ψ` is
"orthogonal to `R(χ)`" iff `⟨ψ, α⟩ = 0` for every `α ∈ R₁(φ)`, `φ ∈ S(χ)` ((12.4)/(12.5)). -/
noncomputable def Rset {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) : Set (ClassFunction G ℂ) :=
  haveI := hyp.finiteG
  {α | ∃ (φ : IrreducibleCharacter ↥L) (_hφ : φ ∈ data.constituents),
    α ∈ (R1 data _hφ).imageSet}

/-! ## (12.3)--(12.5): orthogonality and rho-constancy -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3), the geometric obligation** ((8.18.c) + (5.9) + Dade support).  For
non-conjugate type-I maximal subgroups `L₁, L₂` and constituents `φ₁ ∈ S(χ₁)`, `φ₂ ∈ S(χ₂)`, the
Dade difference-images `(φ₁−φ̄₁)^{τ₁}` and `(φ₂−φ̄₂)^{τ₂}` are orthogonal: their supports lie in the
disjoint thickened Dade domains `Ã(L₁)`, `Ã₁(L₂)` (Peterfalvi (8.18.c),
`S10.support_mutual_exclusion`).  A faithful §8/§10 obligation — the thickened-support theory and
its mutual-exclusion are §10 (lane-d/f) territory; (12.3) cites this as the geometric input to the
(4.1) assembly. -/
theorem nonconjugate_diffImage_inner_zero {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (_hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (_hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups `L₁, L₂`, the families
`R(χ₁) = Rset data1` and `R(χ₂) = Rset data2` are mutually orthogonal.

Proof: a member `α ∈ R(χ₁)` lies in `R₁(φ₁) = (R1cdi data1 hφ₁).toOrthonormalImage` for some
constituent `φ₁`, and likewise `β ∈ R₁(φ₂)`.  The cross-`L` (4.1) orthogonality
`toOrthonormalImage_inner_eq_zero_across` reduces `⟨α, β⟩ = 0` to the orthogonality of the signed
differences `⟨(φ₁−φ̄₁)^{τ₁}, (φ₂−φ̄₂)^{τ₂}⟩ = 0` (`image_eq_signedDifference`), which is the geometric
obligation `nonconjugate_diffImage_inner_zero` ((8.18.c): the supports lie in disjoint `Ã(L₁)`,
`Ã₁(L₂)`). -/
theorem nonconjugate_typeI_R_orthogonal {L1 L2 : Subgroup G} [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ∀ α ∈ Rset data1, ∀ β ∈ Rset data2, ClassFunction.inner α β = 0 := by
  intro α hαm β hβm
  obtain ⟨φ1, hφ1, hα⟩ := hαm
  obtain ⟨φ2, hφ2, hβ⟩ := hβm
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ1) (R1cdi data2 hφ2) ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ1),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference (R1cdi data2 hφ2)]
  exact nonconjugate_diffImage_inner_zero hyp1 hyp2 hnot_conj data1 hφ1 data2 hφ2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)/(12.5) input**: each member `χ = Ind_H^L θ` of `S` vanishes on `L − H`.
`H = L_F` is normal in `L` (`maxNilpotentNormalHall_subgroupOf_normal`, the Fitting subgroup `L_F`),
so the induced character is supported on `H` (`ClassFunction.induce_eq_zero_of_not_mem_normal`).  This
is the "the elements of `S` vanish on `L − H`" step of the constant-on-coset conclusions of
(12.4)/(12.5) (`ψ(xh) = β(xh) + γ(xh) = γ(x)`, the `β ∈ ℂ[S]` part vanishing off `H`). -/
theorem Sset_vanishes_off_H {L : Subgroup G} (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.Sset) {x : ↥L} (hxH : (x : G) ∉ hyp.H) : χ x = 0 := by
  haveI := hyp.finiteG
  obtain ⟨θ, _, hχ_eq⟩ := hχ
  haveI hnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  have hxmem : x ∉ (hyp.typeI.typeF.H).subgroupOf L :=
    fun hcon => hxH (Subgroup.mem_subgroupOf.mp hcon)
  rw [hχ_eq]
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hxmem

/-- **Difference-uniqueness for signed irreducible-character differences** (Peterfalvi §3, the
reconciliation core of (1.4)).  If two *signed* differences of distinct irreducible characters
coincide, `s • (a − b) = t • (c − d)` with `a ≠ b`, `c ≠ d` and a nonzero left scalar `s`, then the
unordered pairs agree, with the sign tracking the orientation: either `a = c, b = d, s = t`
(same orientation) or `a = d, b = c, s = −t` (reversed).

This is the lemma by which the per-constituent families `R₁(φ)` (built from `τ(φ̄ − φ)`) are
reconciled with the global signed family of (1.4) in pin (a) `constituent_diff_tau_mem_span`:
the two presentations of `τ(φ − φ̄)` as a signed difference must share their underlying irreducible
pair, so each `μ_φ` lands in `ℤ[R(χ)]`.

Proof: pairing the hypothesis on the *left* with the irreducible `a` (resp. `b`) and using
orthonormality `⟨χ, ψ⟩ = δ_{χ,ψ}` (`irreducibleCharacter_inner_eq_ite`; `ClassFunction.inner` is
ℂ-linear in the left slot) gives `s = t·([c=a] − [d=a])` and `−s = t·([c=b] − [d=b])`.  Since
`s ≠ 0`, exactly one of `c = a`, `d = a` holds (the two cases are the two orientations), and the
`b`-pairing pins the remaining equality. -/
theorem irreducibleCharacter_signed_difference_uniqueness [Finite G]
    {a b c d : IrreducibleCharacter G} (hab : a ≠ b) (hcd : c ≠ d)
    {s t : ℂ} (hs : s ≠ 0)
    (h : s • ((a : ClassFunction G ℂ) - (b : ClassFunction G ℂ))
        = t • ((c : ClassFunction G ℂ) - (d : ClassFunction G ℂ))) :
    (a = c ∧ b = d ∧ s = t) ∨ (a = d ∧ b = c ∧ s = -t) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hba : b ≠ a := fun he => hab he.symm
  -- Pair the equation on the left with an arbitrary irreducible `e`; orthonormality turns each
  -- coercion-inner into a Kronecker delta.
  have key : ∀ e : IrreducibleCharacter G,
      s * ((if a = e then (1 : ℂ) else 0) - (if b = e then 1 else 0))
        = t * ((if c = e then (1 : ℂ) else 0) - (if d = e then 1 else 0)) := by
    intro e
    have h2 := congrArg (fun f => ClassFunction.inner f (e : ClassFunction G ℂ)) h
    simpa only [ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
      irreducibleCharacter_inner_eq_ite] using h2
  -- Evaluate at `a`: `s = t·([c=a] − [d=a])`.
  have ka : s = t * ((if c = a then (1 : ℂ) else 0) - (if d = a then 1 else 0)) := by
    have hka := key a
    rwa [if_pos rfl, if_neg hba, sub_zero, mul_one] at hka
  -- Evaluate at `b`: `−s = t·([c=b] − [d=b])`.
  have kb : -s = t * ((if c = b then (1 : ℂ) else 0) - (if d = b then 1 else 0)) := by
    have hkb := key b
    rwa [if_neg hab, if_pos rfl, zero_sub, mul_neg_one] at hkb
  by_cases hca : c = a
  · -- Orientation A: `c = a`, hence `d ≠ a`, and `ka` collapses to `s = t`.
    have hda : d ≠ a := fun he => hcd (hca.trans he.symm)
    rw [if_pos hca, if_neg hda, sub_zero, mul_one] at ka
    have hcb : c ≠ b := fun he => hab (hca.symm.trans he)
    rw [if_neg hcb, zero_sub, mul_neg] at kb
    by_cases hdb : d = b
    · exact Or.inl ⟨hca.symm, hdb.symm, ka⟩
    · rw [if_neg hdb, mul_zero, neg_zero] at kb
      exact absurd (neg_eq_zero.mp kb) hs
  · by_cases hda : d = a
    · -- Orientation B: `c ≠ a`, `d = a`, and `ka` collapses to `s = −t`.
      rw [if_neg hca, if_pos hda, zero_sub, mul_neg_one] at ka
      have hdb : d ≠ b := fun he => hab (hda.symm.trans he)
      rw [if_neg hdb, sub_zero] at kb
      by_cases hcb : c = b
      · exact Or.inr ⟨hda.symm, hcb.symm, ka⟩
      · rw [if_neg hcb, mul_zero] at kb
        exact absurd (neg_eq_zero.mp kb) hs
    · -- Neither: `ka` forces `s = 0`, contradiction.
      rw [if_neg hca, if_neg hda, sub_zero, mul_zero] at ka
      exact absurd ka hs

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 3** (span membership): the two underlying irreducibles
`μ_φ, ν_φ` of the difference image `R1cdi data hφ` lie in `ℤ[R(χ)]`.  The orthonormal block
`R₁(φ).imageSet = {ε·μ_φ, −ε·ν_φ} ⊆ R(χ)` with `ε = ±1`, so `μ_φ = ε·(ε·μ_φ)` and
`ν_φ = (−ε)·(−ε·ν_φ)` are integer multiples of `R(χ)` members. -/
theorem R1cdi_muNu_mem_span_Rset {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (R1cdi data hφ).muClassFunction ∈ Submodule.span ℤ (Rset data) ∧
      (R1cdi data hφ).nuClassFunction ∈ Submodule.span ℤ (Rset data) := by
  haveI := hyp.finiteG
  classical
  have himg : (R1 data hφ).imageSet
      = ({(R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction,
          (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction} :
            Finset (ClassFunction G ℂ)) := rfl
  have hsq : (R1cdi data hφ).sign * (R1cdi data hφ).sign = 1 := (R1cdi data hφ).sign_mul_self
  have hμRset : (R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_self _ _⟩
  have hνRset : (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  refine ⟨?_, ?_⟩
  · have hμ : (R1cdi data hφ).muClassFunction
        = (R1cdi data hφ).sign • ((R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction) := by
      rw [smul_smul, hsq, one_smul]
    rw [hμ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hμRset)
  · have hν : (R1cdi data hφ).nuClassFunction
        = (-(R1cdi data hφ).sign) • ((-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction) := by
      rw [smul_smul, neg_mul_neg, hsq, one_smul]
    rw [hν]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hνRset)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 1** (global (1.4) coherence): the constituent set `S(χ)`
together with its complex conjugates forms a single coherent family under the Dade isometry `τ`.
There is a uniform sign `ε = ±1` and an injection `μ` of the conjugate-closed set
`T = S(χ) ∪ S(χ)‾` into `Irr G` with `τ(α − β) = ε·(μ α − μ β)` for all `α, β ∈ T`.

This is the §3 (1.4) keystone `isometry_difference_pair_structure` applied to the constant-degree
family `T` (every member supported in `A(L) ∪ {1}`, so member differences are `A(L)`-supported and
the three Dade-isometry hypotheses hold by `dadeIntegralCharacterMap_{mem_ZIrr_of_supported,
apply_one_eq_zero,inner_eq_on_supported_span}`). -/
theorem exists_uniform_image_of_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ∃ (ε : ℤ) (μ : IrreducibleCharacter ↥L → IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
      Set.InjOn μ ↑(data.constituents ∪
          data.constituents.image (IrreducibleCharacter.conjPerm ↥L)) ∧
      ∀ α ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
        ∀ β ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
          hyp.tau ((α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ))
            = ε • ((μ α : ClassFunction G ℂ) - (μ β : ClassFunction G ℂ)) := by
  haveI := hyp.finiteG
  classical
  set T := data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  obtain ⟨φref, hφref⟩ := data.constituents_nonempty
  -- (1) every member of `T` is supported in `A(L) ∪ {1}`.
  have hTsupp : ∀ x ∈ T, (x : ClassFunction ↥L ℂ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1} := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.supported x hx
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      have hconjsupp : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
        ext y; simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
      rw [hconjsupp]; exact data.supported φ hφ
  -- (2) every member of `T` has the reference degree `φref(1)`.
  have hTdeg : ∀ x ∈ T, ((x : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((φref : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.equal_degree x hx φref hφref
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
      rw [ClassFunction.conj_apply, hd, star_natCast, ← hd]
      exact data.equal_degree φ hφ φref hφref
  -- (3) enumerate `T` as a `Fin n` family.
  set n := T.card with hndef
  have hφrefT : φref ∈ T := Finset.mem_union_left _ hφref
  have hconjrefT : IrreducibleCharacter.conjPerm ↥L φref ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφref)
  have hrefne : φref ≠ IrreducibleCharacter.conjPerm ↥L φref := fun hcon =>
    data.not_real φref hφref ((IrreducibleCharacter.conjPerm_eq_self_iff φref).mp hcon.symm)
  have hn2 : 2 ≤ n := Finset.one_lt_card.mpr ⟨φref, hφrefT, _, hconjrefT, hrefne⟩
  haveI : NeZero n := ⟨by omega⟩
  set fam : Fin n → IrreducibleCharacter ↥L := fun i => (T.equivFin.symm i : IrreducibleCharacter ↥L)
    with hfamdef
  have hfam_mem : ∀ i, fam i ∈ T := fun i => (T.equivFin.symm i).2
  have hfam_inj : Function.Injective fam :=
    fun i j h => T.equivFin.symm.injective (Subtype.ext h)
  -- (4) each member difference `fam i − fam 0` is `A(L)`-supported.
  have hdiff_supp : ∀ i, (irreducibleCharacterDifference fam i).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro i y hy
    have hne1 : y ≠ 1 := by
      rintro rfl
      refine (ClassFunction.mem_support.mp hy) ?_
      show (fam i : ClassFunction ↥L ℂ) 1 - (fam 0 : ClassFunction ↥L ℂ) 1 = 0
      rw [hTdeg (fam i) (hfam_mem i), hTdeg (fam 0) (hfam_mem 0), sub_self]
    rcases ClassFunction.support_sub_subset _ _ hy with h | h
    · rcases hTsupp _ (hfam_mem i) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
    · rcases hTsupp _ (hfam_mem 0) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
  have hSsupp : ∀ s ∈ Set.range (irreducibleCharacterDifference fam),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    rintro s ⟨i, rfl⟩; exact hdiff_supp i
  -- (5) the three (1.4) hypotheses for the Dade isometry, via the supported-span lemmas.
  have hsame_deg : ∀ i, ((fam i : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((fam 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := fun i =>
    (hTdeg (fam i) (hfam_mem i)).trans (hTdeg (fam 0) (hfam_mem 0)).symm
  have hvirtual : IsometryDifferenceImagesAreVirtual hyp.tau fam := by
    intro i
    show hyp.tau (irreducibleCharacterDifference fam i) ∈ ZIrr G
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj (hdiff_supp i)
      (Submodule.sub_mem _ (fam i).mem_ZIrr (fam 0).mem_ZIrr)
  have hzero : IsometryDifferenceImagesVanishAtOne hyp.tau fam := by
    intro i
    show hyp.tau (irreducibleCharacterDifference fam i) (1 : G) = 0
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
      hyp.dadeData.dade hyp.hconj (hdiff_supp i)
  have hisom : ∀ i j, ClassFunction.inner (isometryDifferenceImage hyp.tau fam i)
      (isometryDifferenceImage hyp.tau fam j)
      = ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    show ClassFunction.inner (hyp.tau (irreducibleCharacterDifference fam i))
      (hyp.tau (irreducibleCharacterDifference fam j)) = _
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hSsupp (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.subset_span ⟨j, rfl⟩)
  -- (6) apply the (1.4) keystone.
  obtain ⟨sdf, himage⟩ :=
    isometry_difference_pair_structure hn2 fam hfam_inj hsame_deg hyp.tau hvirtual hzero hisom
  -- (7) read off `ε` and `μ`.
  refine ⟨sdf.sign, fun x => if hx : x ∈ T then sdf.mu (T.equivFin ⟨x, hx⟩) else sdf.mu 0,
    sdf.sign_eq, ?_, ?_⟩
  · -- InjOn
    intro x hx y hy hxy
    have hxT : x ∈ T := Finset.mem_coe.mp hx
    have hyT : y ∈ T := Finset.mem_coe.mp hy
    simp only [dif_pos hxT, dif_pos hyT] at hxy
    exact Subtype.ext_iff.mp (T.equivFin.injective (sdf.injective hxy))
  · -- the pair relation
    intro α hα β hβ
    have hαT : α ∈ T := hα
    have hβT : β ∈ T := hβ
    -- key: for `x ∈ T`, `τ(x − fam 0) = ε·(μ x − μ₀)`.
    have key : ∀ x (hx : x ∈ T), hyp.tau ((x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
        = sdf.sign • ((sdf.mu (T.equivFin ⟨x, hx⟩) : ClassFunction G ℂ)
            - (sdf.mu 0 : ClassFunction G ℂ)) := by
      intro x hx
      have hfx : fam (T.equivFin ⟨x, hx⟩) = x := by
        simp only [hfamdef, Equiv.symm_apply_apply]
      have hLHS : (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = irreducibleCharacterDifference fam (T.equivFin ⟨x, hx⟩) := by
        show (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = (fam (T.equivFin ⟨x, hx⟩) : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
        rw [hfx]
      rw [hLHS]
      change isometryDifferenceImage hyp.tau fam (T.equivFin ⟨x, hx⟩) = _
      rw [himage (T.equivFin ⟨x, hx⟩),
        SignedIrreducibleDifferenceFamily.signedDifference_apply,
        SignedIrreducibleDifferenceFamily.difference_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply]
    have hsub : (α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ)
        = ((α : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
          - ((β : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)) := by abel
    rw [hsub, map_sub, key α hαT, key β hβT, ← smul_sub]
    congr 1
    simp only [dif_pos hαT, dif_pos hβT]
    abel

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (a)** (coherence): for constituents `φ₁, φ₂ ∈ S(χ)`, the Dade image
`(φ₁ − φ₂)^τ` lies in `ℤ[R(χ)]`.

Proof (the (1.4) coherence content, now genuine): the conjugate-closed constituent set `T` is a
single coherent family under `τ` (`exists_uniform_image_of_constituents`), giving a uniform sign
`ε` and injection `μ : T → Irr G` with `τ(φ₁ − φ₂) = ε·(μ φ₁ − μ φ₂)`.  For each constituent `φ`,
the two presentations of `τ(φ − φ̄)` — the global `ε·(μ φ − μ φ̄)` and the per-`φ` block
`R₁(φ)`'s `ε_φ·(μ_φ − ν_φ)` (`R1cdi.image_eq`) — must share their irreducible pair
(`irreducibleCharacter_signed_difference_uniqueness`), so `μ φ ∈ {μ_φ, ν_φ} ⊆ ℤ[R(χ)]`
(`R1cdi_muNu_mem_span_Rset`).  Hence `μ φ₁, μ φ₂ ∈ ℤ[R(χ)]` and `τ(φ₁ − φ₂) ∈ ℤ[R(χ)]`. -/
theorem constituent_diff_tau_mem_span {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) ∈
      Submodule.span ℤ (Rset dχ) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨ε, μ, hε, hμinj, hμrel⟩ := exists_uniform_image_of_constituents hyp dχ
  set T := dχ.constituents ∪ dχ.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  -- reconciliation: every `μ φ` (for a constituent `φ`) lies in `ℤ[R(χ)]`.
  have hmu_mem : ∀ φ ∈ dχ.constituents, (μ φ : ClassFunction G ℂ) ∈ Submodule.span ℤ (Rset dχ) := by
    intro φ hφ
    have hφT : φ ∈ T := Finset.mem_union_left _ hφ
    have hconjT : IrreducibleCharacter.conjPerm ↥L φ ∈ T :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφ)
    set cdi := R1cdi dχ hφ with hcdi
    -- global vs per-`φ` presentation of `τ(φ − φ̄)`.
    have hglob := hμrel φ hφT (IrreducibleCharacter.conjPerm ↥L φ) hconjT
    rw [IrreducibleCharacter.conjPerm_apply_coe] at hglob
    have hcomb : ε • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = cdi.sign • ((cdi.muClassFunction) - (cdi.nuClassFunction)) :=
      hglob.symm.trans cdi.image_eq
    have hcombℂ : (ε : ℂ) • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = (cdi.sign : ℂ) • (((cdi.mu : ClassFunction G ℂ)) - ((cdi.nu : ClassFunction G ℂ))) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hcomb
    -- the two distinct-pair hypotheses.
    have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
      dχ.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
    have hab : μ φ ≠ μ (IrreducibleCharacter.conjPerm ↥L φ) := fun h =>
      hφne (hμinj (Finset.mem_coe.mpr hφT) (Finset.mem_coe.mpr hconjT) h)
    have hs : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
    rcases irreducibleCharacter_signed_difference_uniqueness hab cdi.distinct hs hcombℂ with
      ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).1
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).2
  -- assemble.
  have hφ₁T : φ₁ ∈ T := Finset.mem_union_left _ h₁
  have hφ₂T : φ₂ ∈ T := Finset.mem_union_left _ h₂
  rw [hμrel φ₁ hφ₁T φ₂ hφ₂T]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmu_mem φ₁ h₁) (hmu_mem φ₂ h₂))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5)** (`χ^{τ₁} ∈ ℤ[R(χ)]` for a coherent extension).  For the coherent
extension `coh` of the type-I family `S` of a `Hypothesis L`, and a non-real member `χ ∈ S`
(as an `IrreducibleCharacter`) whose difference `χ − χ̄` is supported in the Dade domain `A(L)`
and which is orthogonal to its conjugate (`⟨χ, χ̄⟩ = 0`), the Dade character `ψ = χ^{τ₁} =
coh.extension χ` lies in the integral span of the orthonormal image family
`R(χ) = dadeOrthonormalCharacterImageFamilyOfDiff … χ`.

This is the `ψ = 0` case of the (5.4) decomposition `(χ − ψ)^{τ₁} = X − Y`.  Taking the coherent
extension as the auxiliary isometry `τ₁`, its `ZIrr`-codomain (`extension_mem_ZIrr`, the
virtual-character property the general **unsupported** `X`-family `Ind θ` lacks — `χ(1) ≠ 0`)
supplies the single number-theoretic input to `CharacterPsiDecomposition.ofProjection`; then
`eq_sum_of_psi_eq_zero` forces `Y = 0`, so `χ^{τ₁} = X = ∑_{α ∈ E ⊆ R(χ)} α ∈ ℤ[R(χ)]`.  This is
the L-side `ψ ∈ ℤ[R(χ_L)]` which, combined with the (12.3) cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)` (`nonconjugate_typeI_R_orthogonal`), yields `ψ ⊥ R(χ_M)` — the `horth` input of
the (12.14) coset-constancy `psi_constant_on_xK`. -/
theorem coherent_extension_mem_span_imageFamily {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (χ : IrreducibleCharacter ↥L)
    (hχmem : (χ : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    coh.extension (χ : ClassFunction ↥L ℂ) ∈
      Submodule.span ℤ
        ((OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.dadeData.dade hyp.hconj χ hχreal hdiffsupp).imageSet :
          Set (ClassFunction G ℂ)) := by
  classical
  set imF := OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
    hyp.dadeData.dade hyp.hconj χ hχreal hdiffsupp with himF
  -- membership of `χ`, `χ̄`, and `χ − χ̄` in the coherent lattice `ℤ[S]`.
  have hχ_zSpan : (χ : ClassFunction ↥L ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχmem
  have hχbar_mem : (χ : ClassFunction ↥L ℂ).conj ∈ hyp.Sset :=
    (Sset_closedUnderConjugate hyp).conj_mem hχmem
  have hχbar_zSpan : (χ : ClassFunction ↥L ℂ).conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχbar_mem
  have hdiff_zSpan : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.sub_mem _ hχ_zSpan hχbar_zSpan
  -- `χ − χ̄` is supported in `A(L)` (sign flip of the given `χ̄ − χ` support).
  have hdiffsupp' : ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj).support ⊆
      hyp.A := by
    have heq : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj
        = -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) := by abel
    rw [heq, ClassFunction.support_neg]
    exact hdiffsupp
  -- the sublattice `ℤ[χ − χ̄, χ − 0]` sits inside `ℤ[S]`.
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥L)
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - 0} ≤
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    show Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hχ_zSpan
  -- build the (5.4) decomposition with `ψ = 0` and `τ₁ = coh.extension`, forcing `Y = 0`.
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0) imF coh.extension
        (fun φ ζ hφ hζ => coh.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (coh.extends_on_supported
          ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
          ⟨hdiff_zSpan, hdiffsupp'⟩)
        (by rw [sub_zero]; exact coh.extension_mem_ZIrr _ hχ_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        hχχbar)
  -- `coh.extension χ = χ^{τ₁} = X = ∑_{α ∈ E} α ∈ ℤ[R(χ)]`.
  have hgoal : coh.extension (χ : ClassFunction ↥L ℂ) = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα => Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) → (12.2.b), constituent form**: the coherent Dade image `χ^{τ₁} =
coh.extension φ` of a constituent `φ ∈ S(χ)` (`data.constituents`) that is itself a member of the
family `S` lies in `ℤ[R(χ)] = Submodule.span ℤ (Rset data)`.

The (5.5) image family `dadeOrthonormalCharacterImageFamilyOfDiff … φ` is *definitionally* the block
`R₁(φ) = R1 data hφ` — both are the `toOrthonormalImage` of the same
`dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj φ (data.not_real φ hφ)
(R1_diffsupp data hφ)` — which is a subfamily of `R(χ) = Rset data`, so
`coherent_extension_mem_span_imageFamily` lands in `ℤ[R(χ)]` after `span_mono`.  The orthogonality
`⟨φ, φ̄⟩ = 0` comes for free from `data.not_real φ hφ` (a non-real irreducible is orthogonal to its
conjugate).  This is the L-side `ψ ∈ ℤ[R(χ_L)]` for the (12.16) witness: the distinguished
`χ_L = Ind θ` is irreducible (Frobenius), so its unique constituent is itself, in `S`. -/
theorem coherent_extension_constituent_mem_span_Rset {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφmem : (φ : ClassFunction ↥L ℂ) ∈ hyp.Sset) :
    coh.extension (φ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ (Rset data) := by
  classical
  -- a non-real irreducible is orthogonal to its complex conjugate.
  have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
    data.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
  have hχχbar :
      ClassFunction.inner (φ : ClassFunction ↥L ℂ) (φ : ClassFunction ↥L ℂ).conj = 0 := by
    have h0 := irreducibleCharacter_inner_eq_ite φ (IrreducibleCharacter.conjPerm ↥L φ)
    rw [if_neg hφne] at h0
    rwa [IrreducibleCharacter.conjPerm_apply_coe] at h0
  -- (5.5): `coh.extension φ ∈ ℤ[R₁(φ)]`; and `R₁(φ) ⊆ R(χ) = Rset data`.
  have h55 := coherent_extension_mem_span_imageFamily hyp coh φ hφmem
    (data.not_real φ hφ) (R1_diffsupp data hφ) hχχbar
  refine Submodule.span_mono ?_ h55
  intro α hα
  exact ⟨φ, hφ, Finset.mem_coe.mp hα⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) + (12.3): the L-side Dade character `ψ = χ_L^{τ₁}` is orthogonal to
`R(χ_M)`.**  For two non-conjugate type-I maximal subgroups `L`, `M` and a constituent
`φ_L ∈ S(χ_L)` of the L-side family that is itself a member of `S` (the Frobenius witness case,
where `χ_L = Ind θ` is irreducible), the coherent Dade image `ψ = coh_L.extension φ_L` is orthogonal
to every element of `R(χ_M) = Rset data_M`.

Two ingredients combine: (5.5) `coherent_extension_constituent_mem_span_Rset` puts
`ψ ∈ ℤ[R(χ_L)]`, and (12.3) `nonconjugate_typeI_R_orthogonal` gives the cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)`; since `⟨·,·⟩` is conjugate-symmetric and additive, orthogonality of `ψ` to all
of `R(χ_M)` follows from `inner_eq_zero_of_mem_zSpan`.  This is precisely the per-`χ_M` piece of the
`horth` hypothesis that the (12.4)/(12.14) coset-constancy chain (`Sset_coeff_equal`,
`psi_constant_on_xK`) consumes: `ψ` restricted to the `M`-structure has equal coefficients across
`S(χ_M)`, forcing `ψ` constant on the `M_F`-cosets. -/
theorem coherent_extension_constituent_orthogonal_Rset_of_nonconjugate {L M : Subgroup G}
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp_L : Hypothesis L)
    (coh_L : OddOrder.Peterfalvi.S07.IsCoherent hyp_L.tau hyp_L.Sset hyp_L.A)
    {chi_L : ClassFunction ↥L ℂ} (data_L : CharacterDecompositionData hyp_L chi_L)
    {φ_L : IrreducibleCharacter ↥L} (hφ_L : φ_L ∈ data_L.constituents)
    (hφ_L_mem : (φ_L : ClassFunction ↥L ℂ) ∈ hyp_L.Sset)
    (hyp_M : Hypothesis M) (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L = M)
    {chi_M : ClassFunction ↥M ℂ} (data_M : CharacterDecompositionData hyp_M chi_M) :
    ∀ α ∈ Rset data_M,
      ClassFunction.inner (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) α = 0 := by
  -- (5.5): `ψ = coh_L.extension φ_L ∈ ℤ[R(χ_L)]`.
  have h55 := coherent_extension_constituent_mem_span_Rset hyp_L coh_L data_L hφ_L hφ_L_mem
  -- (12.3): `R(χ_L) ⊥ R(χ_M)`.
  have horth := nonconjugate_typeI_R_orthogonal hG hyp_L hyp_M hnot_conj data_L data_M
  intro α hα
  -- `α ⊥ R(χ_L)` (conjugate-swap of (12.3)), hence `α ⊥ ℤ[R(χ_L)] ∋ ψ`; conjugate back.
  have hαperp : ∀ β ∈ Rset data_L, ClassFunction.inner α β = 0 := by
    intro β hβ
    rw [inner_conj_symm β α, horth β hβ α hα, star_zero]
  have h0 : ClassFunction.inner α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hαperp h55
  rw [inner_conj_symm α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)), h0, star_zero]

open scoped Classical in
/-- **General TI-induction self-value** (Isaacs 7.x / Peterfalvi (3.2.c) value half), generalized
from `TICyclicHypothesis.induce_apply_eq_self_of_mem_V` to an arbitrary TI subset.  For a TI subset
`A` relative to `L` (`L ⊆ N_G(A)`, `A ⊆ L`, `IsTISubset A L`) and a class function `α` of `L`
supported in `A`, the induced class function `Ind_L^G α` agrees with `α` on `A`: only the `|L|`
conjugators `x ∈ L` contribute to the induction sum (the others land outside `A`, where `α` vanishes,
by the TI property), each with value `α(a)`.  This is **pin (b), step 1** — the value-half of the
"Dade map = Ind on the trivial-`H` part" bridge. -/
theorem induce_apply_eq_self_of_mem_tiSubset {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hAL : A ⊆ (L : Set G))
    (hnorm : ∀ x ∈ L, ∀ a ∈ A, x⁻¹ * a * x ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (α : ClassFunction ↥L ℂ)
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {a : G} (ha : a ∈ A) :
    ClassFunction.induce L α a = α ⟨a, hAL ha⟩ := by
  classical
  haveI : Fintype ↥L := Fintype.ofFinite _
  have haL : a ∈ L := hAL ha
  have hterm : ∀ x : G, ClassFunction.induceTerm L α x a
      = if x ∈ L then α ⟨a, haL⟩ else 0 := by
    intro x
    by_cases hx : x ∈ L
    · rw [if_pos hx]
      have haxL : x⁻¹ * a * x ∈ L := hAL (hnorm x hx a ha)
      rw [ClassFunction.induceTerm_of_mem _ haxL]
      have harg : (⟨x⁻¹ * a * x, haxL⟩ : ↥L)
          = ⟨x⁻¹, L.inv_mem hx⟩ * ⟨a, haL⟩ * ⟨x⁻¹, L.inv_mem hx⟩⁻¹ := by
        apply Subtype.ext; simp [inv_inv]
      rw [harg]
      exact α.conj_eq ⟨a, haL⟩ ⟨x⁻¹, L.inv_mem hx⟩
    · rw [if_neg hx]
      by_cases hax : x⁻¹ * a * x ∈ L
      · rw [ClassFunction.induceTerm_of_mem _ hax]
        have hnotA : x⁻¹ * a * x ∉ A := fun hV =>
          hx (by simpa using L.inv_mem (hTI x⁻¹ ⟨a, ha, by simpa using hV⟩))
        by_contra hne
        exact hnotA ((OddOrder.Peterfalvi.S04.mem_supportInSubgroup).mp
          (hαsupp (ClassFunction.mem_support.mpr hne)))
      · rw [ClassFunction.induceTerm_of_not_mem _ hax]
  rw [ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.univ.filter (· ∈ L)).card = Nat.card ↥L := by
    rw [Nat.card_eq_fintype_card]; exact (Fintype.card_subtype _).symm
  rw [hcard, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

open scoped Classical in
/-- **Peterfalvi (12.4) pin (b), step 2**: for a Dade hypothesis with all trivial stabilizers
`∀ a, H(a) = ⊥`, induction `Ind_L^G` (restricted to `CF(L, A)`) **is** the Dade map.  Generalizes
`TICyclicHypothesis.isDadeMap_inducedDadeMap`: the value half is the step-1 self-value
`induce_apply_eq_self_of_mem_tiSubset` (the coset condition collapses to `IsConj a g` since `h ∈ ⊥`),
the support half is `induce_eq_zero_of_not_conjugatesIntoSet` (induced functions vanish off the
`A`-conjugates, which are the Dade support when `H = ⊥`).  Via `IsDadeMap.unique` this pins the
abstract Dade map to `Ind_L^G` on `CF(L, A)`. -/
theorem isDadeMap_induce_of_forall_H_eq_bot {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hH : ∀ a, hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.IsDadeMap hyp
      (fun α => ClassFunction.induce L (α : ClassFunction ↥L ℂ)) where
  map_eq_of_isConj_hCoset := by
    intro α g a h hh hconj
    have hh1 : h = 1 := Subgroup.mem_bot.mp (by rw [← hH a]; exact hh)
    subst hh1
    have hga : IsConj a.1 g := by simpa using hconj
    show ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = _
    rw [← (ClassFunction.induce L (α : ClassFunction ↥L ℂ)).of_isConj hga]
    exact induce_apply_eq_self_of_mem_tiSubset hyp.subset_L
      (fun x hx a' ha' => by simpa using hyp.L_normalizes_A ⟨x⁻¹, L.inv_mem hx⟩ ha')
      (hyp.isTISubset_of_forall_H_eq_bot hH) _
      (ClassFunction.mem_supportedSubmodule.mp α.2) a.2
  map_eq_zero_of_not_mem_dadeSupport := by
    intro α g hg
    show ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = 0
    refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
      (ClassFunction.mem_supportedSubmodule.mp α.2) (fun hgin => hg ?_)
    rw [hyp.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot hH]
    obtain ⟨x, hx, hxV⟩ := hgin
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hxV
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨x⁻¹ * g * x, hxV, isConj_iff.mpr ⟨x, by group⟩⟩

/-- **Peterfalvi (12.4) pin (b), step 3** (restriction assembly): if a sub-support `A₁ ⊆ A` carries
only trivial Dade stabilizers (`(hyp.restrict …).H a = ⊥`), then on `A₁`-supported functions the
abstract Dade map of `hyp` **is** induction `Ind_L^G`.  The restricted hypothesis has `H = ⊥`, so its
Dade map is `Ind_L^G` (step 2 + `IsDadeMap.unique`); `Hypothesis.dadeMap_restrict_apply` identifies
it with `hyp.dadeMap` of the included function. -/
theorem dadeMap_eq_induce_of_supported_on_trivial_H {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) {A₁ : Set G} (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.restrict hA₁A hA₁norm).H a = ⊥)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A₁ L) :
    hyp.dadeMap (OddOrder.Peterfalvi.S04.SupportedClassFunctions.inclusion
        (G := G) (k := ℂ) (L := L) hA₁A α)
      = ClassFunction.induce L (α : ClassFunction ↥L ℂ) := by
  have h1 := OddOrder.Peterfalvi.S04.IsDadeMap.unique
    ((hyp.restrict hA₁A hA₁norm).isDadeMap_dadeMap (k := ℂ))
    (isDadeMap_induce_of_forall_H_eq_bot (hyp.restrict hA₁A hA₁norm) hH₁)
  rw [← hyp.dadeMap_restrict_apply hA₁A hA₁norm α]
  exact congrFun h1 α

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (b), type-I bridge**: for a type-I maximal `L`, on a class function `f`
supported in a trivial-`H` sub-support `A₁ ⊆ A(L)` (an `L`-invariant subset on which the type-I Dade
stabilizers vanish), the Dade isometry `τ` acts as induction `Ind_L^G`.  This instantiates the
general step-3 bridge `dadeMap_eq_induce_of_supported_on_trivial_H` at the type-I Dade map `hyp.tau`
(via `dadeIntegralCharacterMap_apply_of_support`, and `inclusion` to widen the support from `A₁`). -/
theorem typeI_tau_eq_induce_of_supported_trivial_H {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {A₁ : Set G} (hA₁A : A₁ ⊆ hyp.ambientA)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥)
    {f : ClassFunction ↥L ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ L) :
    hyp.tau f = ClassFunction.induce L f := by
  haveI := hyp.finiteG
  have hfA : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  have h1 : hyp.tau f = hyp.dadeData.dade.dadeMap (k := ℂ)
      ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hfA⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hfA
  rw [h1]
  -- `⟨f, hfA⟩` is defeq to `inclusion hA₁A ⟨f, hf⟩` (same carrier `f`), so step 3 applies directly.
  exact dadeMap_eq_induce_of_supported_on_trivial_H hyp.dadeData.dade hA₁A hA₁norm hH₁
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- The escaping-centralizer set `{a ∈ X : ¬ C_G(a) ≤ M}` is `M`-conjugation invariant when `X` is
(`C_G(gag⁻¹) = g·C_G(a)·g⁻¹` and `g ∈ M` normalizes `M`).  Extracted from the
`supportKernel_conj_invariant` calculation; the `L`-invariance of the trivial-`H` sub-support
`A(L) ∖ escaping` rests on this. -/
private theorem escaping_conj_mem_iff {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    g * x * g⁻¹ ∈ escapingCentralizerSet M X ↔ x ∈ escapingCentralizerSet M X := by
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg) :
      MulAut.conj g • M = M)]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  simp only [escapingCentralizerSet, Set.mem_setOf_eq, hmem, hcent]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the §8 support obligation** ([Is] 6.2 + (8.12.a)): for constituents
`φ₁, φ₂ ∈ S(χ)`, the difference `φ₁ − φ₂` is supported on the **non-escaping** part of `A(L)`,
`A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (= `A(L) − H^#`, exactly where the type-I Dade stabilizers vanish).
By [Is] 6.2 `Res_H φᵢ` is a conjugate-sum of `θ`, so `φᵢ` is supported on `A(L) ∪ {1}` with the
(8.12.a) restriction to the non-escaping part; the difference cancels the value at `1`.  A faithful
§8/[Is] obligation — the genuine cross-section content remaining in pin (b). -/
theorem constituent_diff_support_subset_nonescaping [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (hyp.ambientA \ escapingCentralizerSet L hyp.ambientA) L := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (b)** ([Is] 7.7 + (8.12.c) + [Is] 6.2): for constituents `φ₁, φ₂ ∈ S(χ)`,
the Dade isometry acts as induction on the difference, `(φ₁ − φ₂)^τ = Ind_L^G(φ₁ − φ₂)`.

Proof (now genuine, modulo the §8 support obligation): `φ₁ − φ₂` is supported on the non-escaping
part `A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (`constituent_diff_support_subset_nonescaping`), which is
`L`-invariant (`escaping_conj_mem_iff` + `A(L)` `L`-invariant) and carries only trivial Dade
stabilizers (`supportKernel = ⊥` off the escaping set, via `H_eq_supportKernel`).  On such a
trivial-`H` support the type-I Dade isometry coincides with `Ind_L^G`
(`typeI_tau_eq_induce_of_supported_trivial_H`, i.e. pin (b) steps 1–3 + the restriction assembly). -/
theorem constituent_diff_tau_eq_induce {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) =
      ClassFunction.induce L ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) := by
  have hmem : ∀ (l : L) (a : G), ((l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA ↔ a ∈ hyp.ambientA) := by
    intro l a
    refine ⟨fun h => ?_, fun h => hyp.dadeData.dade.L_normalizes_A l h⟩
    have h2 := hyp.dadeData.dade.L_normalizes_A l⁻¹ h
    simpa [Subgroup.coe_inv, mul_assoc] using h2
  have hA₁A : hyp.ambientA \ escapingCentralizerSet L hyp.ambientA ⊆ hyp.ambientA := Set.diff_subset
  have hA₁norm : ∀ (l : L) ⦃a : G⦄,
      a ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA →
      (l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA := by
    intro l a ha
    exact ⟨hyp.dadeData.dade.L_normalizes_A l ha.1,
      fun hesc => ha.2 ((escaping_conj_mem_iff l.2 (hmem l a)).mp hesc)⟩
  have hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H, hyp.dadeData.H_eq_supportKernel]
    show supportKernel L L hyp.ambientA a.1 = ⊥
    unfold supportKernel
    rw [if_neg a.2.2]
  exact typeI_tau_eq_induce_of_supported_trivial_H hyp hA₁A hA₁norm hH₁
    (constituent_diff_support_subset_nonescaping hyp dχ h₁ h₂)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), coherence → coefficient-equality bridge** (genuine).  If `ψ ⊥ R(χ)`, then
`Res_L ψ` has the *same* coefficient on every constituent of `χ`: `⟨Res_L ψ, φ₁⟩ = ⟨Res_L ψ, φ₂⟩`
for `φ₁, φ₂ ∈ S(χ)`.  Proof: `⟨Res_L ψ, φ₁ − φ₂⟩ = ⟨ψ, Ind_L^G(φ₁ − φ₂)⟩ = ⟨ψ, (φ₁ − φ₂)^τ⟩`
(Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry + pin (b)), and this is `0` because
`(φ₁ − φ₂)^τ ∈ ℤ[R(χ)]` (pin (a)) and `ψ ⊥ R(χ)` (`inner_eq_zero_of_mem_zSpan`).  This is the genuine
content by which `ψ ⊥ R(χ)` forces the `∪S(χ)`-part of `Res_L ψ` to be `β = ∑_χ c_χ·χ ∈ ℂ[S]`. -/
theorem Sset_coeff_equal {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {psi : ClassFunction G ℂ} (horth : ∀ α ∈ Rset dχ, ClassFunction.inner psi α = 0)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.inner (ClassFunction.restrict L psi) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₂ : ClassFunction ↥L ℂ) := by
  haveI := hyp.finiteG
  set f : ClassFunction ↥L ℂ :=
    (φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ) with hf
  -- `⟨ψ, τ f⟩ = 0`: `τ f ∈ ℤ[R(χ)]` (pin a) and `ψ ⊥ R(χ)`.
  have hψτ : ClassFunction.inner psi (hyp.tau f) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan horth
      (constituent_diff_tau_mem_span hyp dχ h₁ h₂)
  -- `⟨f, Res_L ψ⟩ = ⟨Ind_L^G f, ψ⟩ = ⟨τ f, ψ⟩ = star⟨ψ, τ f⟩ = 0`.
  have hfres : ClassFunction.inner f (ClassFunction.restrict L psi) = 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict L f psi,
      ← constituent_diff_tau_eq_induce hyp dχ h₁ h₂,
      inner_conj_symm psi (hyp.tau f), hψτ, star_zero]
  -- `⟨Res_L ψ, f⟩ = star⟨f, Res_L ψ⟩ = 0`, then split the difference.
  have hresf : ClassFunction.inner (ClassFunction.restrict L psi) f = 0 := by
    rw [inner_conj_symm f (ClassFunction.restrict L psi), hfres, star_zero]
  rw [hf, ClassFunction.inner_sub_right] at hresf
  exact sub_eq_zero.mp hresf

/-- Evaluation of a finite sum of class functions at a point (the eval map is additive). -/
private theorem classFunction_sum_apply {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) (g : H) : (∑ i ∈ s, F i) g = ∑ i ∈ s, (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

/-- The "`H ⊆ ker φ`" predicate: the Fitting subgroup `H = L_F` lies in the character kernel of the
irreducible character `φ` of `L`.  The `γ`-components of `Res_L ψ` in (12.4) are exactly those `φ`
with `InHKernel`; they are constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`). -/
def InHKernel {L : Subgroup G} (hyp : Hypothesis L) (φ : IrreducibleCharacter ↥L) : Prop :=
  ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) ⊆
    OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the off-kernel direction** (genuine): every constituent `φ ∈ S(χ)` of a
member `χ = Ind_H^L θ ∈ S` (`θ ≠ 1_H`) is off-kernel, `H ⊄ ker φ`.  If `H ⊆ ker φ` then `Res_H φ` is
constant `= φ(1)` on `H` (`= φ(1)·1_H`), so by Frobenius `⟨χ, φ⟩ = ⟨θ, Res_H φ⟩ = star(φ(1))·⟨θ, 1_H⟩
= 0` (`θ ≠ 1_H`); but `φ` a constituent of `χ` gives `⟨χ, φ⟩ = 1`.  This is the `⊇` inclusion
`S(χ) ⊆ {φ : H ⊄ ker φ}` of the partition `exists_offKernel_constituent_partition`. -/
theorem constituents_not_inHKernel {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hχ : chi ∈ hyp.Sset) (dχ : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ dχ.constituents) : ¬ InHKernel hyp φ := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := hχ
  intro hker
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  -- `Res_K φ = φ(1) · 1_K` (since `H ⊆ ker φ`, `φ` is constant `= φ(1)` on `K`).
  have hrestrict : ClassFunction.restrict K (φ : ClassFunction ↥L ℂ)
      = OddOrder.Peterfalvi.S03.characterDegree (φ : ClassFunction ↥L ℂ) •
        (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    ext k
    rw [ClassFunction.restrict_apply, ClassFunction.smul_apply]
    have hmem : (↑k : ↥L) ∈ OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ) :=
      hker k.2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
    simp only [hmem, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply, mul_one]
  -- `⟨χ, φ⟩ = ⟨θ, Res_K φ⟩ = star(φ(1)) · ⟨θ, 1_K⟩ = 0` (`θ ≠ 1_K`).
  have hzero : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 0 := by
    rw [hchi_eq, ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
      OddOrder.RepresentationTheory.inner_smul_right, irreducibleCharacter_inner, if_neg hθ_ne,
      mul_zero]
  -- `⟨χ, φ⟩ = 1` (multiplicity-one constituent), contradiction.
  have hone : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 1 := by
    rw [dχ.decomp, inner_sum_left,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg hne]),
      irreducibleCharacter_inner, if_pos rfl]
  rw [hone] at hzero
  exact one_ne_zero hzero

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the capturing direction** (genuine): every off-kernel irreducible `φ`
(`H ⊄ ker φ`) is a constituent of some `χ ∈ S`.  By `exists_constituent_not_subset_characterKernel`
([Is] 6.5 / constituent transitivity), `Res_H φ` has a constituent `θ ≠ 1_H`; then `χ := Ind_H^L θ ∈ S`
and `⟨φ, χ⟩ = ⟨Res_H φ, θ⟩ ≠ 0` (Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry), so
`φ ∈ S(χ)`.  This is the `⊆` inclusion `{φ : H ⊄ ker φ} ⊆ ⋃ S(χ)` of the partition
`exists_offKernel_constituent_partition`. -/
theorem not_inHKernel_imp_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} (hφ : ¬ InHKernel hyp φ) :
    ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hlo, hθker⟩ :=
    exists_constituent_not_subset_characterKernel
      (le_refl ((hyp.typeI.typeF.H).subgroupOf L)) φ hφ
  -- `θ ≠ 1`: else `K = K.subgroupOf K ⊆ ker θ = univ`, contradicting `hθker`.
  have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rintro rfl
    exact hθker (by
      simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction, Set.subset_univ])
  -- `θ` is a genuine constituent of `Res_K φ`.
  have hlo' : ClassFunction.inner
      (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ≠ 0 := by
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  -- `⟨φ, Ind_K θ⟩ = ⟨Res_K φ, θ⟩ ≠ 0` (Frobenius + conjugate symmetry).
  have hinner_ne : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    exact hlo'
  by_contra hnotin
  apply hinner_ne
  rw [(data _ ⟨θ, hθ_ne, rfl⟩).decomp, inner_sum_right]
  refine Finset.sum_eq_zero fun φ' hφ' => ?_
  have hne : φ ≠ φ' := by rintro rfl; exact hnotin hφ'
  rw [irreducibleCharacter_inner, if_neg hne]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Pin (c') partition characterization** (genuine, both directions): the off-kernel irreducibles
`{φ : H ⊄ ker φ}` are *exactly* the constituents of the `S`-members, `⋃_{χ ∈ S} S(χ)`.  `⊆` is the
capturing direction `not_inHKernel_imp_mem_constituents`; `⊇` is `constituents_not_inHKernel`.  This
is the set-equality underlying the `biUnion` of `exists_offKernel_constituent_partition`; the residual
of that pin is now only the **disjointness** (φ in `S(χ) ∩ S(χ')` ⟹ χ = χ', via Clifford single-orbit
`RestrictionConstituentsSingleOrbit.exists_conj` + `induce_conjBy_eq`) and the `parts`-`Finset`
construction. -/
theorem not_inHKernel_iff {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} :
    ¬ InHKernel hyp φ ↔
      ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents :=
  ⟨not_inHKernel_imp_mem_constituents hyp data,
    fun ⟨χ, hχ, hmem⟩ => constituents_not_inHKernel hyp hχ (data χ hχ) hmem⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), disjointness** (genuine, Clifford single-orbit): a `φ` that is a
constituent of both `χ, χ' ∈ S` forces `χ = χ'`.  Writing `χ = Ind_H^L θ`, `χ' = Ind_H^L θ'`, both
witnesses `θ, θ'` lie under `φ` (`⟨Res_H φ, θ⟩ = ⟨φ, χ⟩ ≠ 0`, Frobenius); by Clifford single-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible` + `.exists_conj`) they are `L`-conjugate,
`conjBy g θ = θ'`, so `Ind θ = Ind θ'` (`induce_conjBy_eq`, Peterfalvi (1.5.a)).  This is the
`PairwiseDisjoint` content of `exists_offKernel_constituent_partition`. -/
theorem constituents_eq_of_mem {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    (dχ : CharacterDecompositionData hyp χ) (dχ' : CharacterDecompositionData hyp χ')
    {φ : IrreducibleCharacter ↥L} (hmem : φ ∈ dχ.constituents) (hmem' : φ ∈ dχ'.constituents) :
    χ = χ' := by
  haveI := hyp.finiteG
  classical
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hχ'
  -- `θ`, `θ'` lie under `φ`: `⟨Res_K φ, η⟩ = ⟨φ, Ind_K η⟩ = 1 ≠ 0` for a constituent.
  have key : ∀ (η : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
      (dη : CharacterDecompositionData hyp
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)))
      (_ : φ ∈ dη.constituents),
      IrreducibleCharacter.LiesOver ((hyp.typeI.typeF.H).subgroupOf L) φ η := by
    intro η dη hη
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def]
    have hval : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)) = 1 := by
      rw [dη.decomp, inner_sum_right,
        Finset.sum_eq_single_of_mem φ hη (fun φ' _ hne => by
          rw [irreducibleCharacter_inner, if_neg (Ne.symm hne)]),
        irreducibleCharacter_inner, if_pos rfl]
    have hrel : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ))
        = ClassFunction.inner
          (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
          (η : ClassFunction _ ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        ClassFunction.inner_induce_eq_inner_restrict,
        OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    rw [← hrel, hval]; exact one_ne_zero
  obtain ⟨g, hg⟩ :=
    (restrictionConstituentsSingleOrbit_of_isIrreducible φ).exists_conj
      (key θ dχ hmem) (key θ' dχ' hmem')
  rw [← hg]
  exact (ClassFunction.induce_conjBy_eq (H := (hyp.typeI.typeF.H).subgroupOf L) g
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)).symm

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (c)** ([Is] 6.2 capturing + (1.5.a)/(1.2)): the off-kernel irreducible
characters `{φ : H ⊄ ker φ}` partition into the constituent-sets `S(χ)`, `χ ∈ S`.  By [Is] 6.2,
`H ⊄ ker φ ⟹ Res_H φ` has a non-trivial constituent `θ`, so `φ ∈ S(Ind_H^L θ)`; the orbit `θ`
determines `χ = Ind θ` uniquely ((1.5.a)/(1.2)), so the `S(χ)` are pairwise disjoint and cover the
off-kernel irreducibles.  This is the genuine cross-section content (the [Is] 6.2 partition); the
`β`-vanishing regroup `Sset_offKernel_vanishes_off_H` is proved from it. -/
theorem exists_offKernel_constituent_partition {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) :
    ∃ parts : Finset {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset},
      Finset.univ.filter (fun φ => ¬ InHKernel hyp φ) =
        parts.biUnion (fun χ => (data χ.1 χ.2).constituents) ∧
      (↑parts : Set {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset}).PairwiseDisjoint
        (fun χ => (data χ.1 χ.2).constituents) := by
  haveI := hyp.finiteG
  classical
  by_cases hne : (Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).Nonempty
  · -- The off-kernel filter is nonempty, so `S` is nonempty; build the capturing map.
    obtain ⟨φ0, hφ0⟩ := hne
    rw [Finset.mem_filter] at hφ0
    obtain ⟨χ0, hχ0, -⟩ := not_inHKernel_imp_mem_constituents hyp data hφ0.2
    haveI : Nonempty {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} := ⟨⟨χ0, hχ0⟩⟩
    let cap : IrreducibleCharacter ↥L → {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} :=
      fun φ => if h : ¬ InHKernel hyp φ then
        ⟨(not_inHKernel_imp_mem_constituents hyp data h).choose,
         (not_inHKernel_imp_mem_constituents hyp data h).choose_spec.choose⟩
      else Classical.arbitrary _
    refine ⟨(Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).image cap, ?_, ?_⟩
    · ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hφ
        refine ⟨cap φ, ⟨φ, hφ, rfl⟩, ?_⟩
        have hcapφ : cap φ = ⟨(not_inHKernel_imp_mem_constituents hyp data hφ).choose,
            (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose⟩ := dif_pos hφ
        rw [hcapφ]
        exact (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose_spec
      · rintro ⟨χs, ⟨φ', _, rfl⟩, hmem⟩
        exact constituents_not_inHKernel hyp (cap φ').2 (data (cap φ').1 (cap φ').2) hmem
    · intro χs _ χs' _ hne_s
      simp only [Function.onFun, Finset.disjoint_left]
      intro φ hmem hmem'
      exact hne_s (Subtype.ext (constituents_eq_of_mem hyp χs.2 χs'.2
        (data χs.1 χs.2) (data χs'.1 χs'.2) hmem hmem'))
  · -- The off-kernel filter is empty; the empty partition works.
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨∅, by rw [hne, Finset.biUnion_empty], by
      rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩


open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the off-kernel regroup** (genuine, from the [Is] 6.2 partition pin): the
off-kernel Fourier part `β = ∑_{φ : H ⊄ ker φ} ⟨Res_L ψ, φ⟩·φ` of `Res_L ψ` vanishes on `L − H`.
Regroup the off-kernel irreducibles by the partition into `S(χ)`
(`exists_offKernel_constituent_partition`); on each `S(χ)` the coefficient `⟨Res_L ψ, φ⟩` is constant
(`Sset_coeff_equal`, from `ψ ⊥ R(χ)`), so the `S(χ)`-block is `c_χ·∑_{φ ∈ S(χ)} φ = c_χ·χ`
(`decomp`), which vanishes at `g ∈ L − H` (`Sset_vanishes_off_H`). -/
theorem Sset_offKernel_vanishes_off_H {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {g : ↥L} (hg : (g : G) ∉ hyp.H) :
    (∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
      ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g = 0 := by
  obtain ⟨parts, hpart, hdisj⟩ := exists_offKernel_constituent_partition hyp data
  rw [classFunction_sum_apply, hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun χ _ => ?_
  -- The `S(χ)`-block: `∑_{φ ∈ S(χ)} ⟨Res_L ψ, φ⟩ · φ(g) = c_χ · χ(g) = 0`.
  obtain ⟨φ₀, hφ₀⟩ := (data χ.1 χ.2).constituents_nonempty
  have hblock : ∑ φ ∈ (data χ.1 χ.2).constituents,
      (ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₀ : ClassFunction ↥L ℂ) *
        ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply,
      Sset_coeff_equal hyp (data χ.1 χ.2) (horth χ.1 χ.2) hφ hφ₀]
  have hdecomp : ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g = χ.1 g := by
    rw [← classFunction_sum_apply, ← (data χ.1 χ.2).decomp]
  rw [hblock, hdecomp, Sset_vanishes_off_H hyp χ.2 hg, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)**: a class function `ψ` orthogonal to every type-I family `R(χ)` (`χ ∈ S`) is
constant on each coset `xH` with `x ∈ L − H`.

Proof: write `Res_L ψ = γ + β` by the Fourier expansion (`sum_inner_irreducibleCharacter_smul`),
splitting `Irr L` into `{H ⊆ ker φ}` (= `γ`) and `{H ⊄ ker φ}` (= `β`).  The kernel part `γ` is
constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`, each `φ` with `H ⊆ ker φ`); the
off-kernel part `β` vanishes on `L − H` (`Sset_offKernel_vanishes_off_H`: by [Is] 6.2 + the
coefficient bridge `Sset_coeff_equal`, `β ∈ ℂ[S]` vanishes off `H`).  Hence
`ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`. -/
theorem orthogonal_character_constant_on_coset {L : Subgroup G} [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  haveI := hyp.finiteG
  classical
  intro h hh
  have hhL : h ∈ L := hyp.typeI.typeF.H_le hh
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  set hL : ↥L := ⟨h, hhL⟩ with hhLdef
  set gf : ClassFunction ↥L ℂ := ClassFunction.restrict L psi with hgf
  -- Fourier split of `Res_L ψ = γ + β`.
  set γ : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hγ
  set β : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hβ
  have hsplit : gf = γ + β := by
    rw [hγ, hβ, Finset.sum_filter_add_sum_filter_not]
    exact (sum_inner_irreducibleCharacter_smul gf).symm
  -- `hL` lies in `H` (as a subgroup of `L`).
  have hLmem : hL ∈ ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) :=
    Subgroup.mem_subgroupOf.mpr hh
  -- `γ` is constant on the `H`-coset `xL · hL`.
  have hγconst : γ (xL * hL) = γ xL := by
    rw [hγ, classFunction_sum_apply, classFunction_sum_apply]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply,
      apply_mul_eq_of_mem_characterKernel φ.isIrreducible
        ((Finset.mem_filter.mp hφ).2 hLmem) xL]
  -- `β` vanishes on `L − H` (off-kernel part is in `ℂ[S]`).
  have hxhH : x * h ∉ hyp.H := fun hcon => hxH (by
    have hmem : x * h * h⁻¹ ∈ hyp.H := mul_mem hcon (inv_mem hh)
    rwa [mul_inv_cancel_right] at hmem)
  have hβxh : β (xL * hL) = 0 := by
    rw [hβ]
    exact Sset_offKernel_vanishes_off_H hyp data horth (g := xL * hL)
      (by rw [Subgroup.coe_mul]; exact hxhH)
  have hβx : β xL = 0 := by
    rw [hβ]; exact Sset_offKernel_vanishes_off_H hyp data horth (g := xL) hxH
  -- Assemble: `ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`.
  have key : gf (xL * hL) = gf xL := by
    simp only [hsplit, ClassFunction.add_apply, hγconst, hβxh, hβx, add_zero]
  have hgxh : gf (xL * hL) = psi (x * h) := by
    rw [hgf, ClassFunction.restrict_apply, Subgroup.coe_mul]
  have hgx : gf xL = psi x := by rw [hgf, ClassFunction.restrict_apply]
  rw [← hgxh, ← hgx]; exact key

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5)**: after the rho-reduction, a class function `ψ` orthogonal
to every type-I family `R(χ)` is constant on `H − H'`.  The orthogonality hypothesis
is the genuine `⟨ψ, α⟩ = 0` for `α ∈ R(χ)`, no longer an opaque field. -/
theorem rho_constant_on_H_minus_Hprime {L : Subgroup G} [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0) :
    ∀ h : G, h ∈ hyp.H → h ∉ hyp.Hprime → psi h = psi 1 := by
  sorry

/-! ## (12.6)--(12.7): type-I Frobenius structure -/

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Transporting a §4 Dade datum along an equality of its support set preserves the Dade isometry
`dadeIntegralCharacterMap`.**  The isometry's codomain `IntegralCharacterMap ↥L G` does not mention
the support `A`, so rewriting `A` to `A'` in the datum leaves the map unchanged (`subst` + `rfl`).
This lets the (6.8) `SibleyDadeHypothesis` (Dade datum on `sharpImage H`) carry *exactly* the (12.1)
isometry `hyp.tau` (Dade datum on `A(L)`) after the ambient identification `sharpImage H = A(L)` —
the map is an *arbitrary* linear extension off the supported lattice
(`dadeIntegralCharacterMap_apply_of_support`), so only the identical datum (transported), not a
re-construction via `of_isTISubset`, reproduces `hyp.tau`. -/
theorem hconj_transport_ambient {L : Subgroup G} [Fintype G] {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : dade.HConjInvariant) :
    (hEq ▸ dade : OddOrder.Peterfalvi.S04.Hypothesis G A' L).HConjInvariant := by
  subst hEq; exact hconj

theorem dadeIntegralCharacterMap_transport_ambient {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : dade.HConjInvariant)
    (hconj' : (hEq ▸ dade : OddOrder.Peterfalvi.S04.Hypothesis G A' L).HConjInvariant) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hEq ▸ dade)
        ((hEq ▸ dade).fullDadeIsometryData hconj')
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
        (dade.fullDadeIsometryData hconj) := by
  subst hEq; rfl

/-- **The centralizer-support of `N^#` collapses to `N^#` for a Frobenius `L` with kernel `N`.**
The (12.1) type-I Dade support is `A(L) = centralizerSupport (N^#) L`; when `L` is a Frobenius group
with kernel `N` (`N.subgroupOf L`), the extra centralizer condition is vacuous — a `y` centralizing
a nontrivial `x ∈ N` lands in the kernel `N` (`IsFrobeniusGroup.centralizer_kernel_le`), so the
support is just `N^#`.  This is the **non-circular** upstream twin of the §16
`centralizerSupport_sharpSubgroup_eq_of_frobenius`: it takes the Frobenius structure as a hypothesis
(supplied for the (12.16) witness by (12.10) `witness_L_frobenius`) rather than routing through the
final (12.7), so it is available before the minimal-counterexample machinery. -/
theorem centralizerSupport_sharp_eq_of_frobenius [Finite G] {M N : Subgroup G} {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Ambient match for the (6.8) Sibley setup**: the `H^#`-image `sharpImage (H.subgroupOf L)` of
the Fitting kernel (`H = L_F`), pushed back to `G`, is exactly the type-I Dade support
`A(L) = typeIA L`.  Here `A(L) = centralizerSupport (H^#) L` (`typeIA` def) collapses to `H^#` for
the **Frobenius** `L` (`centralizerSupport_sharp_eq_of_frobenius`, non-circular from `hfrob`), and
`(H.subgroupOf L).map L.subtype = H ⊓ L = H` (`subgroupOf_map_subtype`, `H ≤ L`) matches the two
`H^#` descriptions.  This is the ambient identification that lets the (6.8) `SibleyDadeHypothesis`
(Dade datum on `sharpImage H`) reuse the (12.1) datum `hyp.dadeData.dade` (on `A(L)`), preserving
the isometry `hyp.tau` exactly. -/
theorem sharpImage_H_subgroupOf_eq_typeIA [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) = typeIA L hyp.typeI := by
  have hmap : (hyp.H.subgroupOf L).map L.subtype = hyp.typeI.typeF.H := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hyp.typeI.typeF.H_le
  rw [show typeIA L hyp.typeI
        = OddOrder.GroupTheory.centralizerSupport
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L from rfl,
    centralizerSupport_sharp_eq_of_frobenius (N := hyp.typeI.typeF.H) hfrob hyp.typeI.typeF.H_le]
  simp only [OddOrder.Peterfalvi.S08.sharpImage, OddOrder.GroupTheory.sharpSubgroup, hmap]

/-- **Structural input for Peterfalvi (12.6) — TI-kernel Frobenius case (6.8)(c1).**

For the (6.8) case-(c1) route, `L` is Frobenius **and** `H^#` is a TI-subset of `G`
(Peterfalvi (6.8)(a) requires *both*: being Frobenius is (c1), but the ambient TI-ness is a
separate hypothesis).  Under TI, the §4 Dade datum's local subgroups vanish
(`dade.H a = ⊥`), which is exactly the `SibleyDadeHypothesis.dade_H_eq_bot` field, so a
`SibleyTarget` is available.

**Note (2026-07-01, issue 2032):** the earlier `_hfrob`-only signature was *unsound* — the (12.16)
witness `L` is Frobenius but its `H^#` is **not** TI in `G` (Peterfalvi (12.10): "By (12.9), `H^#` is
not a TI-subset of `G`"), so `dade_H_eq_bot` fails there.  The `_hTI` hypothesis restores soundness;
the witness (non-TI) is handled by the case-(b)/(c) routes of `frobenius_typeI_coherent`, not by this
TI-only carrier. -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
      (Subgroup.normalizer (hyp.typeI.typeF.H : Set G))) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := sorry

/-- **Lattice-relative `xFamily_inner`** — the (5.7) `X`-family orthonormality `⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩`
(`Xⱼ = β − τ(χ₀ − χⱼ)`) **without a global isometry**.  `S07.xFamily_inner` (S07:472) uses the
isometry only on the supported differences `χ₀ − χⱼ` (S07:487); this variant takes exactly that
lattice-relative fact `hdiff`, so it applies to the Feit–Thompson **Dade** map (which is *not* a
global `IsIntegralIsometry` — `dim CF(L) > dim CF(G)` — but *is* isometric on the `A(L)`-supported
differences).  Identical proof, sourcing the difference inner product from `hdiff`.  This is the one
place the (5.7) equal-degree coherence used the global isometry (issue 9001), so it is the load-bearing
step for a Dade-compatible `frobenius_typeI_coherent_of_abelianKernel`. -/
theorem xFamily_inner_dade {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {n : ℕ} [NeZero n]
    (χ : Fin n → ClassFunction ↥L ℂ) (β : ClassFunction G ℂ)
    (hdiff : ∀ i j, ClassFunction.inner (τ (χ 0 - χ i)) (τ (χ 0 - χ j))
      = ClassFunction.inner (χ 0 - χ i) (χ 0 - χ j))
    (hββ : ClassFunction.inner β β = 1)
    (hB : ∀ j, ClassFunction.inner β (τ (χ 0 - χ j)) = 1 - ClassFunction.inner (χ 0) (χ j))
    (i j : Fin n) :
    ClassFunction.inner (β - τ (χ 0 - χ i)) (β - τ (χ 0 - χ j))
      = ClassFunction.inner (χ i) (χ j) := by
  have hχ00 : ClassFunction.inner (χ 0) (χ 0) = 1 := by
    have h := hB 0; rw [sub_self, map_zero, ClassFunction.inner_zero_right] at h
    linear_combination h
  have hai : ClassFunction.inner (τ (χ 0 - χ i)) β = 1 - ClassFunction.inner (χ i) (χ 0) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hB i, star_sub, star_one,
      ← OddOrder.RepresentationTheory.inner_conj_symm]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hββ, hB j, hai, hdiff i j, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hχ00]
  ring

/-- **Peterfalvi (12.1) support `A(L) = H^#` from a Frobenius witness** — the Frobenius-parameterized
core of `typeIA_eq_sharp` (below), factored out so the (12.6) case-(b) coherence assembly can cite it
with the `hfrob` it already has (the full `typeIA_eq_sharp` derives `hfrob` from `typeI_frobenius`,
which is defined later).  Since `L` is Frobenius with kernel `H`, the centralizer of any `x ∈ H^#`
lies in `H` (`IsFrobeniusGroup.centralizer_kernel_le`), so the `A(L)`-support (`centralizerSupport`
of `H^#`) is exactly `H^#`. -/
theorem Hypothesis.typeIA_eq_sharp_of_frobenius [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  show OddOrder.GroupTheory.centralizerSupport
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L
    = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyL, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxL : x ∈ L := hyp.typeI.typeF.H_le hxN
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      hfrob.centralizer_kernel_le _ hxsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hyp.typeI.typeF.H_le hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are irreducible characters of `L`** — the crux of the (12.6)
case-(b) reduction: for a Frobenius `L` with kernel `H`, `Ind_H^L θ` (`θ ≠ 1`) is irreducible
(`isIrreducibleCharacter_induce_of_frobeniusGroup`).  This feeds the unit-norm, orthogonality, and
`ZIrr`-membership inputs of `coherent_of_constant_degree`. -/
theorem Sset_isIrreducibleCharacter [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    IsIrreducibleCharacter χ := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hfrob θ hθ_ne

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` has no real characters** ((5.2) input for case (b)/(12.6)).  Each
member is a Frobenius-induced irreducible (`frobenius_induce_char_singleton`), non-real by the odd
order of `L` (`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem Sset_hasNoRealCharacters [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Sset := by
  classical
  intro χ hχ
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨ξ, hξcoe, hξreal, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  rw [← hξcoe]; exact hξreal

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` is pairwise orthogonal** ((5.2) input for case (b)/(12.6)).  Each
member is an irreducible character of `L` (Frobenius induction), so two distinct members are
orthogonal by row orthogonality (`irreducibleCharacter_inner_eq_ite`). -/
theorem Sset_pairwiseOrthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal hyp.Sset := by
  classical
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  intro χ ψ hχ hψ hne
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ hψ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hψ
  obtain ⟨ξ, hξcoe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  obtain ⟨ξ', hξ'coe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ' hθ'_ne
  rw [← hξcoe, ← hξ'coe, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  exact hne (by rw [← hξcoe, ← hξ'coe, h])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are unit-norm** (the `hirr` input of (5.7)/(12.6) case (b)).
Each `Ind_H^L θ` (`θ ≠ 1`) is a Frobenius-induced irreducible, so `‖Ind_H^L θ‖² = 1`
(`inner_self_induce_eq_one_of_frobeniusGroup`, the inertia-`H` norm computation). -/
theorem Sset_inner_self_eq_one [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner χ χ = 1 := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact inner_self_induce_eq_one_of_frobeniusGroup hfrob θ hθ_ne

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members share the degree `[L:H]`** (the `hconst`/`hdeg0` input of
(5.7)/(12.6) case (b)).  With `H = L_F` abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear
(`θ(1) = 1`, `IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative`; commutativity transfers
to `H.subgroupOf L` by the `subgroupOf_isMulCommutative` instance), so
`(Ind_H^L θ)(1) = [L:H]·θ(1) = [L:H]` (`induce_apply_one`). -/
theorem Sset_apply_one_eq_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  haveI : IsMulCommutative ↥hyp.typeI.typeF.H := hab
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  rw [ClassFunction.induce_apply_one, θ.isIrreducible.apply_one_eq_one_of_isMulCommutative, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is constant-degree** (the (5.7) input for `hcoh` of the (6.5.c) engine, without
assuming `H` abelian).  Every member of `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is `Ind_K^L θ` with
`⁅K,K⁆ ⊆ Ker θ`; then `θ` factors through the abelian `K/⁅K,K⁆`, so `θ(1) = 1`
(`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`) and `Ind θ (1) = |L:K|`.
This is Peterfalvi's `η_j(1) = |W₁|` for the `Y = S(H′)` family — the subfamily replacement for the
case-(b) `Sset_apply_one_eq_index` (which needs all of `H` abelian). -/
theorem SsubFiltration_commutator_apply_one_eq_index [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, _hθ_ne, hker, rfl⟩ := hχ
  have hθ1 : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) 1 = 1 := by
    haveI : IsMulCommutative (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥((hyp.typeI.typeF.H).subgroupOf L)))
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) θ ?_
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self ((hyp.typeI.typeF.H).subgroupOf L)]
    exact hker
  rw [ClassFunction.induce_apply_one, hθ1, mul_one]

open OddOrder.Peterfalvi.S09.Cert in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences are `A(L)`-supported** (the `hsuppdiff` input of (5.7)/(12.6) case
(b), and the support that lets the Dade isometry apply — `tau_isometry_diff`).  Two members
`a, b ∈ S = {Ind_H^L θ}` both vanish off `H` (`Sset_vanishes_off_H`) and share the degree `[L:H]`
(`Sset_apply_one_eq_index`), so `a − b` vanishes off `H` and at `1`, i.e. is supported in
`A(L) = H^# = supportInSubgroup (H \ {1}) L`. -/
theorem Sset_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp ha h, Sset_vanishes_off_H hyp hb h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A member's conjugate-difference `χ̄ − χ` is `A(L)`-supported** (any `χ ∈ S`, no constant-degree
needed) — the per-member support field of the (5.6) family enumeration (h56).  Off `H` both `χ` and
`χ̄` vanish (`Sset_vanishes_off_H`); at `1`, `χ̄(1) = χ(1)` because `χ(1)` is a (real) natural degree
(`χ` irreducible), so `χ̄ − χ` is supported on `H^# = A(L)`. -/
theorem Sset_conjDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (χ.conj - χ) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h]; simp
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    obtain ⟨n, -, hn1, -⟩ :=
      (Sset_isIrreducibleCharacter hyp hfrob hχ).exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast, sub_self]
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Orthonormal enumeration of a coherent `S₁ ⊆ S`** — the witness analogue of the Sibley
`exists_sMemberOrthonormalFamily`, the family-enumeration input of the (5.6) break bound (h56).
Members of `S₁` are irreducible (`Sset_isIrreducibleCharacter`), so `exists_finEnum_irreducible`
lists them as `χmem : Fin k → Irr L`; the per-member fields are the witness `Sset` facts (no-real,
`Sset_conjDiff_supported`, pairwise/self orthonormality), `hS₁conj` supplies `χ̄ ∈ S₁`. -/
theorem Sset_exists_orthonormalFamily [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ :=
    OddOrder.Peterfalvi.S08.exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact Sset_hasNoRealCharacters hyp hodd hfrob (hS₁sub (hmemS1 j))
  · intro j
    exact Sset_conjDiff_supported hyp hfrob hAH (hS₁sub (hmemS1 j))
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    have hχS := hS₁sub (hmemS1 j)
    have hne : (χmem j : ClassFunction ↥L ℂ) ≠ (χmem j : ClassFunction ↥L ℂ).conj :=
      fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχS) h.symm
    exact Sset_pairwiseOrthogonal hyp hodd hfrob hχS (Sset_closedUnderConjugate hyp hχS) hne
  · intro i j
    rw [OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A member's degree is `d·|L:K|`** (`d = θ(1)` the source degree) — the integer degree-ratio
input of the (5.6) degree data (h56).  `χ = Ind_K^L θ` has `χ(1) = |L:K|·θ(1)` (`induce_apply_one`),
`θ(1)` a positive natural (`θ` irreducible). -/
theorem Sset_charValue_one_eq_mul_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ d : ℕ, 0 < d ∧
      (χ : ↥L → ℂ) 1 = (d : ℂ) * (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, -, rfl⟩ := hχ
  obtain ⟨d, hd0, hd1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  refine ⟨d, hd0, ?_⟩
  rw [ClassFunction.induce_apply_one, hd1]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A scaled difference `χ − m·χ′` is `A(L)`-supported** when `χ(1) = m·χ′(1)` (any `χ, χ′ ∈ S`) —
the per-member scaled-difference support of the (5.6) degree data (h56).  Off `H` both vanish
(`Sset_vanishes_off_H`); at `1` the degree relation makes it vanish; so it is supported on
`H^# = A(L)`. -/
theorem Sset_scaledDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset) {m : ℕ}
    (hdeg : (χ : ↥L → ℂ) 1 = (m : ℂ) * (χ' : ↥L → ℂ) 1) :
    (χ - m • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  rw [show (m • χ' : ClassFunction ↥L ℂ) = (m : ℂ) • χ' from
    (Nat.cast_smul_eq_nsmul ℂ m χ').symm]
  intro x hx
  have hx0 : (χ - (m : ℂ) • χ') x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h, Sset_vanishes_off_H hyp hχ' h]; ring
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    rw [hdeg]; ring
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

/-- **Degree data for an enumerated `S`-family** — the witness analogue of the Sibley
`exists_sMemberDegreeData`, the integer-degree-ratio input of the (5.6) break bound (h56).  Against a
minimal-degree anchor `χmem i₁` of degree `|L:K|`, each member has an integer ratio
`deg j = χmem j(1)/|L:K|` (`Sset_charValue_one_eq_mul_index`), `deg i₁ = 1`, and the scaled
difference `χmem j − deg j·χmem i₁` is `A(L)`-supported (`Sset_scaledDiff_supported`). -/
theorem Sset_exists_degreeData [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) := by
  choose deg hdeg_pos hdeg_eq using fun j => Sset_charValue_one_eq_mul_index hyp (hmemS j)
  have hdeg_eq' : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := fun j => by
    rw [hdeg_eq j, hanchordeg]
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq', fun j =>
    Sset_scaledDiff_supported hyp hfrob hAH (hmemS j) (hmemS i₁) (hdeg_eq' j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hidx_ne : (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg1 : (deg i₁ : ℂ) = 1 := mul_right_cancel₀ hidx_ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Break-pair fields for `{ψ, ψ̄}`** — the witness analogue of the Sibley `sBreakPair_fields`, the
per-`ψ` inputs the (5.6) bound `coherentDegreeSumBound_of_not_coherent` consumes (in its argument
order): non-realness, conjugate-difference support, the `{ψ, ψ̄}` orthonormality, and the
orthogonality of `ψ`, `ψ̄` to every member of `S₁` (distinct irreducibles, since `ψ, ψ̄ ∉ S₁`). -/
theorem Sset_breakPair_fields [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
    (ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∧
    ClassFunction.inner ψ ψ = 1 ∧
    ClassFunction.inner ψ.conj ψ.conj = 1 ∧
    ClassFunction.inner ψ ψ.conj = 0 ∧
    ClassFunction.inner ψ.conj ψ = 0 ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ x = 0) ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ.conj x = 0) := by
  have hψconjS := Sset_closedUnderConjugate hyp hψS
  have hne : ψ ≠ ψ.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hψS) h.symm
  refine ⟨Sset_hasNoRealCharacters hyp hodd hfrob hψS,
    Sset_conjDiff_supported hyp hfrob hAH hψS,
    Sset_inner_self_eq_one hyp hfrob hψS,
    Sset_inner_self_eq_one hyp hfrob hψconjS,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψS hψconjS hne,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψconjS hψS (fun h => hne h.symm), ?_, ?_⟩
  · intro x hx
    have hxne : ψ ≠ x := by rintro rfl; exact hψnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ, Sset_isIrreducibleCharacter hyp hfrob hψS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite
  · intro x hx
    have hxne : ψ.conj ≠ x := by rintro rfl; exact hψcnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ.conj, Sset_isIrreducibleCharacter hyp hfrob hψconjS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (6.2) member-family degree-sum bound over the witness `τ`** — the witness analogue
of the Sibley `sMember_degreeSumBound_of_not_coherent`, feeding the (5.6) core
`coherentDegreeSumBound_of_not_coherent` (over `hyp.dadeData.dade`, the same Dade datum as
`hyp.tau`).  Assembled from the six witness member-family helpers + the abstract §7 generation
bridges.  If `S₁` (coherent, containing a degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then
`∑ⱼ degⱼ² ≤ 2a` where `χmemⱼ(1) = degⱼ·χ₁(1)`, `ψ(1) = a·χ₁(1)`. -/
theorem Sset_degreeSumBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1, hmemconjortho,
      hmemortho⟩ := Sset_exists_orthonormalFamily hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by rw [hi₁eq]; exact hχ₁deg
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    Sset_exists_degreeData hyp hfrob hAH hmemS hanchordeg
  obtain ⟨hrealψ, hdiffsuppψ, hψψ, hψbarψbar, hψψbar, hψbarψ, hψ_S1, hψbar_S1⟩ :=
    Sset_breakPair_fields hyp hodd hfrob hAH hψS hS₁sub hψnotS1 hψcnotS1
  obtain ⟨a, _ha_pos, hψratio0⟩ := Sset_charValue_one_eq_mul_index hyp hψS
  have hψratio : ψ 1 = (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by rw [hψratio0, ← hanchordeg]
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    Sset_scaledDiff_supported hyp hfrob hAH hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hdiffasuppψ
      (Submodule.sub_mem _ (IrreducibleCharacter.mem_ZIrr ⟨ψ, hψirr⟩)
        (nsmul_mem (IrreducibleCharacter.mem_ZIrr (χmem i₁)) a))
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSumBound_of_not_coherent
    hyp.dadeData.dade hyp.hconj hS₁coh ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ
    hψ_S1 hψbar_S1 (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (6.2) member-family degree-square bound** (real form, witness `τ`) — rescales
`Sset_degreeSumBound_of_not_coherent`'s `∑ⱼ degⱼ² ≤ 2a` by the anchor degree `χ₁(1)` into the
character-degree-square sum `∑ⱼ (χⱼ(1).re)² ≤ 2·ψ(1).re·χ₁(1).re`.  Mirror of the Sibley
`sMember_degreeSqReBound_of_not_coherent`. -/
theorem Sset_degreeSqReBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    Sset_degreeSumBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j; rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

/-- **The witness kernel `K = (L_F).subgroupOf L` is normal in `↥L`** — `L_F = maxNilpotentNormalHall L`
whose `subgroupOf L` is normal (`maxNilpotentNormalHall_subgroupOf_normal`).  Needed by the (6.2) B2
degree-sum identity and the (6.5) engine's `hHnorm`. -/
theorem typeF_H_subgroupOf_normal [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
  rw [hyp.typeI.typeF.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) B2 — the `S(A)` degree-square identity** (witness form).  Mirror of the Sibley
`sum_re_sq_induce_kernelFilter_eq`: over the witness kernel `K = (L_F).subgroupOf L`, the filtered
induced family `{Ind_K^L θ | A ⊆ Ker θ, θ ≠ 1}` has degree-square sum `|L:K|·(|K:A| − 1)`, via the
abstract B2 `sum_div_normSq_induce_kernelFilter_eq` and that each member is irreducible (`‖·‖² = 1`,
`χ(1)` a real natural). -/
theorem Sset_sum_re_sq_induce_kernelFilter_eq [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) := by
  haveI := hyp.finiteG
  haveI : ((hyp.typeI.typeF.H).subgroupOf L).Normal := typeF_H_subgroupOf_normal hyp
  have hB2 := OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq (G := ↥L)
    (H := (hyp.typeI.typeF.H).subgroupOf L) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) :=
      (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset := by
      simp only [Hypothesis.Sset, Set.mem_setOf_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := Sset_isIrreducibleCharacter hyp hfrob hχS
    have hinner : ClassFunction.inner
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ))
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) = 1 := by
      simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
        (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) per-step index bound** (witness form) — if `S(A) ⊆ S₁` (coherent, with a
degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then `|K:A| − 1 ≤ 2·ψ(1).re`.  The `S(A)`
degree-square sum `|L:K|·(|K:A|−1)` (B2, `Sset_sum_re_sq_induce_kernelFilter_eq`) is bounded by the
full enumerated `S₁`-family sum, which the (5.6) bound `Sset_degreeSqReBound_of_not_coherent` caps by
`2·ψ(1).re·χ₁(1).re`; dividing by `χ₁(1).re = |L:K|`.  Mirror of `sMember_index_le_two_psi`. -/
theorem Sset_index_le_two_psi [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    (Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    Sset_degreeSqReBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := Sset_sum_re_sq_induce_kernelFilter_eq hyp hfrob (A := A)
  set SA := (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction)
    with hSAdef
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    apply hSA_S1
    simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq]
    exact ⟨θ, hne, hker, rfl⟩
  have hchain : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by
    calc (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
          ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
            A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := hchain
      _ = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`Sset` is finite** — a subset of the (finite) range of `θ ↦ Ind_K^L θ`. -/
theorem Sset_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) : hyp.Sset.Finite := by
  haveI := hyp.finiteG
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  have hsub : hyp.Sset ⊆ Set.range
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
    rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
  exact (Set.finite_range _).subset hsub

/-- **Every filtration level `S(A)` is finite** (subset of the finite `Sset`) — the finiteness input
of `exists_coherentBreakPair` (h56). -/
theorem SsubFiltration_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  (Sset_finite hyp).subset hyp.SsubFiltration_subset_Sset

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every filtration level `S(A)` is closed under conjugation** (kernel preserved by
`characterKernel_conj`) — the conjugation-closure input of `exists_coherentBreakPair` (h56).  General
`A` version of `SsubFiltration_commutator_closedUnderConjugate`. -/
theorem SsubFiltration_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (A : Subgroup ↥L) : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  classical
  intro χ hχ
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **`S(H′)` member differences are `A(L)`-supported** — the `hab`-free subfamily analogue of
`Sset_diff_supported` for the (6.5.c) `hcoh`.  Members of `S(⁅K,K⁆)` vanish off `H` (as `Sset`
members, `Sset_vanishes_off_H`) and share the constant degree `|L:K|` at `1`
(`SsubFiltration_commutator_apply_one_eq_index`, replacing the case-(b) `Sset_apply_one_eq_index`
that needs `H` abelian), so their difference is supported on `H^# = A(L)`. -/
theorem SsubFiltration_commutator_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have haS : a ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset ha
  have hbS : b ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset hb
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp haS h, Sset_vanishes_off_H hyp hbS h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
          SsubFiltration_commutator_apply_one_eq_index hyp hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S(H′)`** — the `tau_isometry_diff` field of
the subfamily `S07.Hypothesis` (`hab`-free), mirroring `Sset_tau_isometry_diff` via
`SsubFiltration_commutator_diff_supported`. -/
theorem SsubFiltration_commutator_tau_isometry_diff [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hc : c ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hd : d ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact SsubFiltration_commutator_diff_supported hyp hAH ha hb
    · exact SsubFiltration_commutator_diff_supported hyp hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S`** — the `tau_isometry_diff` field of the
lattice-relative `S07.Hypothesis` (issue 9001).  For members `a, b, c, d ∈ S`, both differences are
`A(L)`-supported (`Sset_diff_supported`), so the genuine §10 Dade isometry preserves their inner
product (`dadeIntegralCharacterMap_inner_eq_on_supported_span`).  No global isometry is used. -/
theorem Sset_tau_isometry_diff [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset)
    (hc : c ∈ hyp.Sset) (hd : d ∈ hyp.Sset) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Sset_diff_supported hyp hab hAH ha hb
    · exact Sset_diff_supported hyp hab hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences map into `ℤ[Irr G]`** — the `hZIrr` input of
`coherent_of_constant_degree`.  Each member is irreducible (`Sset_isIrreducibleCharacter`), so
`a − b ∈ ℤ[Irr L]`, and it is `A(L)`-supported (`Sset_diff_supported`), so the Dade image is a
virtual character of `G` (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`). -/
theorem Sset_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj (Sset_diff_supported hyp hab hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr ⟨a, Sset_isIrreducibleCharacter hyp hfrob ha⟩)
    (IrreducibleCharacter.mem_ZIrr ⟨b, Sset_isIrreducibleCharacter hyp hfrob hb⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.d) difference image for a witness member** — the `difference_image` field of the
`S07.Hypothesis`.  Each `χ ∈ S` is a non-real irreducible (`Sset_isIrreducibleCharacter`,
`Sset_hasNoRealCharacters`) whose conjugate-difference `χ̄ − χ` is `A(L)`-supported
(`Sset_diff_supported`), so the genuine Dade map sends `χ − χ̄` to a signed difference of two
irreducibles of `G` (`dadeCharacterDifferenceImageOfDiff`). -/
noncomputable def Sset_differenceImage [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob hχ⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob hχ)
    (Sset_diff_supported hyp hab hAH (Sset_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.e) orthogonality of witness difference images** — the
`difference_images_orthogonal` field.  For members `φ, χ ∈ S` with `⟨φ,χ⟩ = ⟨φ,χ̄⟩ = 0`, the signed
Dade images `(φ−φ̄)^τ`, `(χ−χ̄)^τ` are orthogonal: the conjugate-differences are `A(L)`-supported, so
the Dade isometry (`Sset_tau_isometry_diff`) reduces the pairing to the source
`⟨φ−φ̄, χ−χ̄⟩`, which expands to the four cross terms — all zero by orthogonality and irreducibility
(`Sset_pairwiseOrthogonal`, `Sset_inner_self_eq_one`). -/
theorem Sset_differenceImages_orthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Sset) (hχ : χ ∈ hyp.Sset)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (Sset_differenceImage hyp hodd hfrob hab hAH hφ).Orthogonal
      (Sset_differenceImage hyp hodd hfrob hab hAH hχ) := by
  have hφc := Sset_closedUnderConjugate hyp hφ
  have hχc := Sset_closedUnderConjugate hyp hχ
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (Sset_differenceImage hyp hodd hfrob hab hAH hφ).image_conjugateDifference,
      ← (Sset_differenceImage hyp hodd hfrob hab hAH hχ).image_conjugateDifference]
  show ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [Sset_tau_isometry_diff hyp hab hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφ] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχ] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχ hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχc hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is closed under conjugation** — the `conjugate_closed` field for the subfamily
`S07.Hypothesis`.  Mirrors `Sset_closedUnderConjugate` (`χ.conj = Ind_K^L θ̄`, `θ̄ ≠ 1`), with the
extra `S(H′)`-kernel condition preserved because `Ker θ̄ = Ker θ` (`characterKernel_conj`). -/
theorem SsubFiltration_commutator_closedUnderConjugate [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    χ.conj ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` member differences map into `ℤ[Irr G]`** — the `hZIrr` input for the subfamily
`coherent_of_constant_degree`.  `hab`-free mirror of `Sset_tau_diff_mem_ZIrr` via
`SsubFiltration_commutator_diff_supported`; irreducibility is inherited from `Sset`. -/
theorem SsubFiltration_commutator_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj (SsubFiltration_commutator_diff_supported hyp hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr
      ⟨a, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset ha)⟩)
    (IrreducibleCharacter.mem_ZIrr
      ⟨b, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hb)⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.d) difference image for an `S(H′)` member** — the `difference_image` field, `hab`-free
mirror of `Sset_differenceImage` via `SsubFiltration_commutator_diff_supported` and the subfamily
conjugation-closure. -/
noncomputable def SsubFiltration_commutator_differenceImage [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hχ)⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ))
    (SsubFiltration_commutator_diff_supported hyp hAH
      (SsubFiltration_commutator_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) orthogonality of `S(H′)` difference images** — the `difference_images_orthogonal`
field, `hab`-free mirror of `Sset_differenceImages_orthogonal`. -/
theorem SsubFiltration_commutator_differenceImages_orthogonal [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).Orthogonal
      (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ) := by
  have hφc := SsubFiltration_commutator_closedUnderConjugate hyp hφ
  have hχc := SsubFiltration_commutator_closedUnderConjugate hyp hχ
  have hφS := hyp.SsubFiltration_subset_Sset hφ
  have hχS := hyp.SsubFiltration_subset_Sset hχ
  have hφcS := hyp.SsubFiltration_subset_Sset hφc
  have hχcS := hyp.SsubFiltration_subset_Sset hχc
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).image_conjugateDifference,
      ← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ).image_conjugateDifference]
  show ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [SsubFiltration_commutator_tau_isometry_diff hyp hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφS] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχS] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχS hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχcS hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (b): abelian rank-2 kernel → equal-degree coherence (5.7).**
When `H = L_F` is abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear, so every member
`Ind_H^L θ ∈ S` has the same degree `[L:H]`; `S` is then coherent by (5.7).  The witness
`S07.Hypothesis hyp.Sset hyp.A` is assembled from the ten witness lemmas above (all seven §5.2 fields
plus the `coherent_of_constant_degree` inputs), and the coherence is produced by the now
lattice-relative `coherent_of_constant_degree` (issue 9001, no global isometry needed).  Nonemptiness
of `S` (`hcard`) comes from the nontrivial abelian kernel `H` having a nontrivial irreducible `θ`,
whose induced pair `{Ind θ, Ind θ̄}` is two distinct non-real members. -/
theorem frobenius_typeI_coherent_of_abelianKernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob' : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (hab' : IsMulCommutative ↥hyp.typeI.typeF.H ∧ rank ↥hyp.typeI.typeF.H = 2) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  obtain ⟨C, hfrob⟩ := hfrob'
  have hab := hab'.1
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    hyp.typeIA_eq_sharp_of_frobenius hfrob
  -- `S` is finite: a subset of the (finite) range of `θ ↦ Ind_H^L θ`.
  have hSfin : hyp.Sset.Finite := by
    haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩
      refine ⟨θ, ?_⟩
      rfl
    exact (Set.finite_range _).subset hsub
  -- the abelian kernel is nontrivial, so it has a nontrivial irreducible `θ`.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (ConjClasses ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq]; exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨θ, hθ⟩ := exists_ne (trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction with hχ0
  have hχ0S : χ0 ∈ hyp.Sset := by
    simp only [hχ0, Hypothesis.Sset, Set.mem_setOf_eq]
    refine ⟨θ, hθ, ?_⟩
    rfl
  have hχ0cS : χ0.conj ∈ hyp.Sset := Sset_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχ0S) h.symm
  have hcard : 2 ≤ hyp.Sset.ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ hyp.Sset.ncard :=
          Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  -- assemble the §5.2 hypothesis and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ _ _ ha hb hc hd => Sset_tau_isometry_diff hyp hab hAH ha hb hc hd
      conjugate_closed := Sset_closedUnderConjugate hyp
      no_real_characters := Sset_hasNoRealCharacters hyp hodd hfrob
      pairwise_orthogonal := Sset_pairwiseOrthogonal hyp hodd hfrob
      difference_image := fun _ hχ => Sset_differenceImage hyp hodd hfrob hab hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        Sset_differenceImages_orthogonal hyp hodd hfrob hab hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob hζ
  · exact fun a ha b hb => Sset_tau_diff_mem_ZIrr hyp hfrob hab hAH ha hb
  · exact fun a ha b hb => by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb]
  · exact fun a ha => by
      rw [Sset_apply_one_eq_index hyp hab ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => Sset_diff_supported hyp hab hAH ha hb

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.RepresentationTheory in
/-- **`S(H′)` is coherent** — the `hcoh` input of the (6.5.c) engine
`nonempty_coherent_SOf_bot_of_index_dvd`.  `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is a
constant-degree family of degree `|L:K|` (`SsubFiltration_commutator_apply_one_eq_index`), coherent
by (5.7).  All seven §5.2 fields hold `hab`-free (the subfamily lemmas above); `2 ≤ |S(H′)|` because
the nontrivial abelianization `K/⁅K,K⁆` (`K` nilpotent nontrivial) has a nontrivial character whose
inflation `θ0` gives a member `Ind θ0` and its (distinct) conjugate. -/
theorem SsubFiltration_commutator_coherent [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    [Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsubFiltration ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
      hyp.A) := by
  classical
  haveI := hyp.finiteG
  -- `S(H′) ⊆ Sset` is finite.
  have hSsetfin : hyp.Sset.Finite := by
    haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
    exact (Set.finite_range _).subset hsub
  have hSfin : (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).Finite :=
    hSsetfin.subset hyp.SsubFiltration_subset_Sset
  -- `K` is nontrivial.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  -- `K/⁅K,K⁆` is nontrivial (`K` nilpotent nontrivial is not perfect).
  have hcomm_lt : commutator ↥((hyp.typeI.typeF.H).subgroupOf L) < ⊤ :=
    IsSolvable.commutator_lt_top_of_nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L)
  haveI : Nontrivial (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) := by
    rw [QuotientGroup.nontrivial_iff]; exact hcomm_lt.ne
  -- a nontrivial character of the abelianization, inflated to a member `θ0` of `S(H′)`.
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (ConjClasses (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  haveI : Nontrivial (IrreducibleCharacter (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq]
          exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨χbar, hχbar⟩ := exists_ne (trivialIrreducibleCharacter
    (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸ commutator ↥((hyp.typeI.typeF.H).subgroupOf L)))
  have hθ0ne : inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
      ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := fun h =>
    hχbar (inflate_injective (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
      (h.trans (inflate_trivial (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))).symm))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    ((inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar).toClassFunction) with hχ0def
  have hχ0S : χ0 ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
    simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq]
    refine ⟨inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar, hθ0ne, ?_, rfl⟩
    rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
    exact subset_characterKernel_inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
  have hχ0cS := SsubFiltration_commutator_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h =>
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ0S)) h.symm
  have hcard : 2 ≤ (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ _ := Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ _ _ ha hb hc hd =>
        SsubFiltration_commutator_tau_isometry_diff hyp hAH ha hb hc hd
      conjugate_closed := fun _ hχ => SsubFiltration_commutator_closedUnderConjugate hyp hχ
      no_real_characters := fun _ hχ =>
        Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ)
      pairwise_orthogonal := fun _ _ hφ hχ hne =>
        Sset_pairwiseOrthogonal hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hφ)
          (hyp.SsubFiltration_subset_Sset hχ) hne
      difference_image := fun _ hχ =>
        SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        SsubFiltration_commutator_differenceImages_orthogonal hyp hodd hfrob hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob (hyp.SsubFiltration_subset_Sset hζ)
  · exact fun a ha b hb => SsubFiltration_commutator_tau_diff_mem_ZIrr hyp hfrob hAH ha hb
  · exact fun a ha b hb => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
        SsubFiltration_commutator_apply_one_eq_index hyp hb]
  · exact fun a ha => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => SsubFiltration_commutator_diff_supported hyp hAH ha hb

/-- **The witness kernel `K = (L_F).subgroupOf L` is nilpotent** — the `[IsNilpotent ↥K]` input of
`SsubFiltration_commutator_coherent` (and the (6.5) engine).  `L_F = maxNilpotentNormalHall L` is
nilpotent (`maxNilpotentNormalHall_isNilpotent`), and `K ≃* L_F` (`subgroupOfEquivOfLe`, `L_F ≤ L`)
transfers nilpotency. -/
theorem typeF_H_subgroupOf_isNilpotent [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L) := by
  haveI := hyp.finiteG
  haveI : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (c): cyclic-quotient kernel → (6.5.c) coherence.**
Def (8.3) case (c): `H` is a `p`-group and `|L/H|` divides `p − 1` (via (8.2.a)/(8.3.c)); `S` is
coherent by (6.5.c).  (Gap: the (6.5.c) coherence producer for `|L/H| ∣ p−1` is not yet in the
coherence library — see issue 2032 / hub issue 9001.) -/
theorem frobenius_typeI_coherent_of_cyclicQuotient [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hexp : (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors →
        Monoid.exponent hyp.typeI.typeF.U ∣ p - 1) ∧
      ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors ∧
        IsCyclic ↥(OddOrder.GroupTheory.opiCoreInG {p}ᶜ hyp.typeI.typeF.H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6)**: if `L` is Frobenius with kernel `H = L_F`, then `S` is coherent.

The textbook proof **case-splits** on the type-I trichotomy `Definition (8.3)` (carried by
`hyp.typeI.alternative`): (a) `H^#` TI in `G` → (6.8) (`sibleyTarget_frobI`); (b) `H` abelian rank 2
→ equal-degree (5.7) (`frobenius_typeI_coherent_of_abelianKernel`); (c) `|L/H| ∣ p−1` → (6.5.c)
(`frobenius_typeI_coherent_of_cyclicQuotient`).  The (12.16) witness lands in case (b) or (c)
(Peterfalvi (12.10): its `H^#` is *not* TI), so the (6.8) route alone is insufficient — the earlier
single-`sibleyTarget_frobI` proof was unsound (issue 2032).  This assembly carries no `sorry` of its
own; the per-case gaps are isolated in the three delegated lemmas. -/
theorem frobenius_typeI_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hfrob hTI)
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp hfrob hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp hfrob hexp

/-- **Frobenius realization bridge for type `F`** (the (8.2.b) consumer behind (12.10)/(12.16)).
A type-`F` maximal `M` whose complement `U` is a **Z-group** (every Sylow subgroup cyclic) is a
Frobenius group with kernel `M_F`.  By `IsZGroup.exponent_eq_card`, `|U| = exp(U)`, so Peterfalvi
(8.2.b) (`S10.typeF_frobenius_of_card_eq_exponent`) applies.  `sorry`-free + axiom-clean. -/
theorem typeF_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hZ : _root_.IsZGroup ↥data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  haveI := hZ
  exact OddOrder.Peterfalvi.S10.typeF_frobenius_of_card_eq_exponent data
    (_root_.IsZGroup.exponent_eq_card (G := ↥data.U)).symm

/-- **Frobenius realization bridge for type I** (the `kernel = M_F` form consumed by (12.10)).
A type-I maximal `M` whose complement `U = M/M_F` is a **Z-group** is a Frobenius group with kernel
`M_F = typeF.H`.  Wraps `typeF_frobenius_of_isZGroup_complement` on `data.typeF`. -/
theorem typeI_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeIData M) (hZ : _root_.IsZGroup ↥data.typeF.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) :=
  typeF_frobenius_of_isZGroup_complement data.typeF hZ

/-! The headline **(12.7)** (`typeI_frobenius`: every type-I maximal is a Frobenius group with
kernel `M_F`) is proved at the end of this section, after the minimal-counterexample machinery
(12.8)–(12.16) on which it depends: the `π = ∅` case is the easy direction
`typeI_frobenius_of_pi_empty`, and `π = ∅` itself (`pi_empty`) is the content of (12.16). -/

/-! ## (12.8)--(12.12): minimal counterexample analysis -/

/-- **Peterfalvi (12.8), the prime set `π`**: `q ∈ π` when some type-`I` maximal subgroup `M'`
has a **noncyclic Sylow `q`-subgroup in `M' / M'_F`**.  Encoded by a Sylow `q`-subgroup `P ≤ M'`
(`q`-group with `q ∤ [M' : P]`) that is noncyclic and satisfies `q ∣ [M' : M'_F]` — so `P` is not
contained in `M'_F` and its image in `M'/M'_F` is a noncyclic Sylow `q`-subgroup. -/
def InPi (q : ℕ) : Prop :=
  ∃ M' : Subgroup G, M' ∈ maximalSubgroups G ∧ IsTypeI M' ∧
    ∃ P : Subgroup G, P ≤ M' ∧ IsPGroup q ↥P ∧ ¬ q ∣ P.relIndex M' ∧
      ¬ IsCyclic ↥P ∧ q ∣ (maxNilpotentNormalHall M').relIndex M'

/-- **Peterfalvi (12.7), the `π = ∅` case** (the first sentence of the proof of (12.16)): if the
prime set `π` of (12.8) is empty, every type-I maximal `M` is a Frobenius group with kernel `M_F`.

`M_F = H` is a normal Hall subgroup (8.11), so its complement `U` has `|U| = [M : M_F]` coprime
to `|M_F|`; hence every Sylow `q`-subgroup `P` of `U` has full `q`-order in `M`.  Were `P`
noncyclic, its `M`-image `P.map U.subtype` would be a noncyclic Sylow `q`-subgroup of `M` with
`q ∣ [M : M_F]`, i.e. `q ∈ π` — contradicting `π = ∅`.  So `U` is a Z-group and the bridge
`typeI_frobenius_of_isZGroup_complement` applies.  Its only gap is the (8.11) Hall input. -/
theorem typeI_frobenius_of_pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hpi : ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) := by
  classical
  refine typeI_frobenius_of_isZGroup_complement data ?_
  set H := data.typeF.H with hHdef
  set U := data.typeF.U with hUdef
  have hUM : U ≤ M := data.typeF.U_le
  -- `[M : H] = |U|` (complement) and `|M| = |H| * |U|`.
  have hrel : H.relIndex M = Nat.card ↥U := by
    rw [Subgroup.relIndex, data.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hMcard : Nat.card ↥M = Nat.card ↥H * Nat.card ↥U := by
    rw [← (H.subgroupOf M).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv,
      ← Subgroup.relIndex, hrel]
  -- `H = M_F` is Hall in `G` (8.11), so `|H|` is coprime to `[M : H] = |U|`.
  have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hM
    (tau := PeterfalviType.I) ⟨data⟩).1
  rw [← data.typeF.H_eq] at hHall
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥U) :=
    hHall.coprime_index.coprime_dvd_right
      (hrel ▸ Subgroup.relIndex_dvd_index_of_le data.typeF.H_le)
  -- Every Sylow `q`-subgroup `P` of `U` is cyclic.
  refine ⟨fun q hq P => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hnc
  -- `P ≠ ⊥`, so `q ∣ |U|`, and `|H|` has no `q`.
  have hPcard : Nat.card ↥(P : Subgroup ↥U) = q ^ (Nat.card ↥U).factorization q :=
    P.card_eq_multiplicity
  have hPne : (P : Subgroup ↥U) ≠ ⊥ := fun h => hnc (h ▸ inferInstance)
  have hfacU_pos : 0 < (Nat.card ↥U).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥U).factorization q) with h0 | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hPcard, h0, pow_zero])) hPne
    · exact h
  have hqU : q ∣ Nat.card ↥U := Nat.dvd_of_factorization_pos hfacU_pos.ne'
  have hHfac0 : (Nat.card ↥H).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_right hqU).symm)
  have hMfac : (Nat.card ↥M).factorization q = (Nat.card ↥U).factorization q := by
    rw [hMcard, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
      (Nat.card_pos (α := ↥U)).ne', Finsupp.add_apply, hHfac0, zero_add]
  -- `Pm = P.map U.subtype`: a noncyclic `q`-subgroup of `M` of full `q`-order.
  set Pm := (P : Subgroup ↥U).map U.subtype with hPmdef
  have hPmM : Pm ≤ M := (Subgroup.map_subtype_le _).trans hUM
  have hPmcard : Nat.card ↥Pm = q ^ (Nat.card ↥M).factorization q := by
    rw [hPmdef, Subgroup.card_map_of_injective U.subtype_injective, hPcard, hMfac]
  have hPmsub : Nat.card ↥(Pm.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmM).toEquiv, hPmcard]
  have hPmP : IsPGroup q ↥Pm := (IsPGroup.iff_card).mpr ⟨_, hPmcard⟩
  refine hpi q hq ⟨M, hM, ⟨data⟩, Pm, hPmM, hPmP, ?_, ?_, ?_⟩
  · -- `¬ q ∣ Pm.relIndex M`: `Pm` has the full `q`-part of `|M|`.
    rw [Subgroup.relIndex]
    intro hdvd
    have hsplit : (Nat.card ↥M).factorization q
        = (Nat.card ↥(Pm.subgroupOf M)).factorization q
          + ((Pm.subgroupOf M).index).factorization q := by
      conv_lhs => rw [← (Pm.subgroupOf M).card_mul_index]
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥(Pm.subgroupOf M))).ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply]
    rw [hPmsub, hq.factorization_pow, Finsupp.single_eq_same] at hsplit
    exact absurd (Nat.Prime.factorization_pos_of_dvd hq Subgroup.index_ne_zero_of_finite hdvd)
      (by omega)
  · -- `¬ IsCyclic ↥Pm`: `Pm ≃* P` and `P` is noncyclic.
    intro hc
    haveI := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.surjective)
  · -- `q ∣ (maxNilpotentNormalHall M).relIndex M = [M : H] = |U|`.
    rw [← data.typeF.H_eq, hrel]; exact hqU

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7).

`M` is a type-`I` maximal subgroup whose Fitting kernel is `K = M_F` (`K' = [K, K]`), and `P₀`
is a Sylow `p`-subgroup of `M` that is noncyclic with `p ∣ [M : M_F]` (so the image of `P₀` in
`M/M_F` is a noncyclic Sylow `p`-subgroup, i.e. `p ∈ π`); `p` is the smallest element of `π`. -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInG K
  P0_le_M : P0 ≤ M
  /-- `P₀` is a `p`-group… -/
  P0_pGroup : IsPGroup p ↥P0
  /-- …and a Sylow `p`-subgroup of `M` (`p ∤ [M : P₀]`). -/
  P0_sylow : ¬ p ∣ P0.relIndex M
  /-- The Sylow `p`-subgroup of `M/M_F` is noncyclic (so `P₀` is noncyclic). -/
  P0_noncyclic : ¬ IsCyclic ↥P0
  /-- …and `p ∣ [M : M_F]` (so `P₀ ⊄ M_F`; together with the Hall property this gives `p ∤ |M_F|`). -/
  p_dvd_index : p ∣ K.relIndex M
  /-- `p` is the smallest prime in `π`. -/
  minimal_p : ∀ q : ℕ, q.Prime → InPi (G := G) q → p ≤ q

/-- **Peterfalvi (12.8), existence of the minimal counterexample.**  If the prime set `π` of
(12.8) is nonempty, its least element `p = Nat.find` yields a `CounterexampleHypothesis`: the
`InPi` witness for `p` supplies a type-`I` maximal `M'` with a noncyclic Sylow `p`-subgroup `P₀`
that has `p ∣ [M' : M'_F]`, and `Nat.find_min'` records that `p` is the smallest prime in `π`.

This is the well-ordering step that opens the minimal-counterexample analysis of (12.7); it is
`§8`-free and unconditional (its only input is `InPi` for some prime). -/
theorem exists_counterexampleHypothesis [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (h : ∃ q : ℕ, q.Prime ∧ InPi (G := G) q) :
    Nonempty (CounterexampleHypothesis (G := G)) := by
  classical
  obtain ⟨hp_prime, M', hM', hM'I, P, hPle, hPpg, hPsyl, hPnc, hqdvd⟩ := Nat.find_spec h
  exact ⟨{
    p := Nat.find h
    p_prime := hp_prime
    M := M'
    K := maxNilpotentNormalHall M'
    Kprime := derivedInG (maxNilpotentNormalHall M')
    P0 := P
    M_maximal := hM'
    M_typeI := hM'I
    K_eq_MF := rfl
    Kprime_eq := rfl
    P0_le_M := hPle
    P0_pGroup := hPpg
    P0_sylow := hPsyl
    P0_noncyclic := hPnc
    p_dvd_index := hqdvd
    minimal_p := fun q hq hqInPi => Nat.find_min' h ⟨hq, hqInPi⟩ }⟩

/-- The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully.

`L` is the second maximal subgroup with `P₀ ⊆ L_s` (`L_s = mainSubgroup L L_type`); `x` is the
order-`p` element of `Ω₁(P₀)^#` whose centralizer in `K = M_F` escapes `K'`, controls `N_G(⟨x⟩)`,
and escapes `L`. -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  /-- Peterfalvi's type attached to `L` (so `L_s = mainSubgroup L L_type`). -/
  L_type : PeterfalviType
  L_hasType : HasPeterfalviType L_type L
  /-- `P₀ ⊆ L_s`. -/
  P0_le_Ls : ctr.P0 ≤ mainSubgroup L L_type
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  /-- `x ∈ Ω₁(P₀)^#`: `x` has order dividing `p`. -/
  x_mem_omega1 : x ^ ctr.p = 1
  /-- `C_K(x) ⊄ K'` (equivalently `C_{K/K'}(x) ≠ 1`). -/
  CKx_not_le_Kprime : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)
  /-- `N_G(⟨x⟩) ⊆ M`. -/
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  /-- `C_G(x) ⊄ L`. -/
  centralizer_x_not_le_L : ¬ (Subgroup.centralizer ({x} : Set G) ≤ L)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Group-theoretic core of Peterfalvi (12.9)** (fully general, `§8`-independent).

If a **noncyclic abelian** group `A` acts **coprimely** on a finite group `K` whose
abelianization is nontrivial (`[K, K] ≠ K`), then some **nontrivial** `a ∈ A` has a fixed
subgroup `C_K(a)` that is *not* contained in the derived subgroup `[K, K]`.

This is the abstract content of the centralizer step of (12.9): there Peterfalvi takes
`A = Ω₁(P₀)` (elementary abelian of rank `2`, hence noncyclic) acting by conjugation on
`K = M_F`, with `[K, K] = K'`, and concludes `∃ x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`
(equivalently `C_{K/K'}(x) ≠ 1`).

Proof.  `[K, K]` is characteristic, hence `A`-invariant, so `A` acts on the quotient
`K / [K, K]`.  By **BG Proposition 1.16(1)** (Isaacs 6.21,
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) applied to that quotient action,
`K / [K, K] = ⟨ C_{K/[K,K]}(a) ∣ a ≠ 1 ⟩`.  Since `K / [K, K]` is nontrivial, some
`a ≠ 1` has `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset lifts, by the coprime fixed-point
lifting (**Isaacs Cor 3.28**, `coprime_fixedPoints_quotient`), to an element of `C_K(a)`
outside `[K, K]`. -/
theorem exists_ne_one_actionFixedBy_not_le_commutator
    {A K : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hCop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hSolv : IsSolvable A ∨ IsSolvable K) (hNC : ¬ IsCyclic A)
    (hK' : commutator K ≠ ⊤) :
    ∃ a : A, a ≠ 1 ∧ ¬ (Ch06.actionFixedBy φ a ≤ commutator K) := by
  classical
  -- `[K, K]` is characteristic, hence `A`-invariant; let `ψ` be the induced quotient action.
  have hN_inv : Ch03.IsAInvariant φ (commutator K) := Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  -- Coprimality on the quotient: `|K / [K,K]|` divides `|K|`.
  have hCopQ : Nat.Coprime (Nat.card A) (Nat.card (K ⧸ commutator K)) :=
    hCop.coprime_dvd_right (commutator K).card_quotient_dvd_card
  -- BG 1.16(1) on the quotient action: the nontrivial fixed-point closure is everything.
  have htop : Ch06.nontrivialActionFixedByClosure ψ = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic' ψ hCopQ hNC
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a, a ≠ 1 → C_K(a) ≤ [K, K]`.  Show the quotient closure is `⊥`.
  have hquot_bot : Ch06.nontrivialActionFixedByClosure ψ ≤ ⊥ := by
    rw [Ch06.nontrivialActionFixedByClosure_le_iff]
    intro a ha q hq
    -- `q ∈ C_{K/K'}(a)`: `q` is fixed by every element of `⟨a⟩`.
    have hq_zp : q ∈ Ch06.actionFixedPoints ψ (Subgroup.zpowers a) := by
      rw [← Ch06.actionFixedBy_eq_actionFixedPoints_zpowers]; exact hq
    -- Lift `q = mk' g` and assemble the coset-fixed hypothesis on `⟨a⟩`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) q
    have hg_fix : ∀ b : ↥(Subgroup.zpowers a), ∃ n ∈ commutator K, φ (b : A) g = g * n := by
      intro b
      have hb := (Ch06.mem_actionFixedPoints.mp hq_zp) b
      rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
      exact ⟨g⁻¹ * φ (b : A) g, by simpa using (commutator K).inv_mem hb, by group⟩
    -- Coprime fixed-point lifting (Isaacs Cor 3.28) on the cyclic group `⟨a⟩`.
    have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card K) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hSolv' : IsSolvable ↥(Subgroup.zpowers a) ∨ IsSolvable K := by
      rcases hSolv with hA | hK
      · haveI := hA; exact Or.inl inferInstance
      · exact Or.inr hK
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      Ch04.coprime_fixedPoints_quotient hCop' hSolv'
        (Ch03.IsAInvariant.of_characteristic (φ.comp (Subgroup.zpowers a).subtype)) hg_fix
    -- `c` is fixed by `a`, hence `c ∈ C_K(a) ≤ [K, K]` by `hcon`.
    have hca : φ a c = c := hc_fix ⟨a, Subgroup.mem_zpowers a⟩
    have hc_mem : c ∈ commutator K := hcon a ha (Ch06.mem_actionFixedBy.mpr hca)
    -- Then `g = c * n⁻¹ ∈ [K, K]`, so the coset `q = mk' g` is trivial.
    have hg_mem : g ∈ commutator K := by
      have : g = c * n⁻¹ := by rw [hcn]; group
      rw [this]; exact (commutator K).mul_mem hc_mem ((commutator K).inv_mem hn)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg_mem
  -- `⊤ ≤ ⊥` forces `K / [K, K]` trivial, i.e. `[K, K] = ⊤`, contradicting `hK'`.
  have hbot : (⊤ : Subgroup (K ⧸ commutator K)) = ⊥ := le_bot_iff.mp (htop ▸ hquot_bot)
  apply hK'
  rw [Subgroup.eq_top_iff']
  intro k
  have hk1 : QuotientGroup.mk' (commutator K) k ∈ (⊥ : Subgroup (K ⧸ commutator K)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact hk1

/-- **Conjugation form of the (12.9) centralizer core** (ambient subgroups, directly the
form consumed by (12.9)).  If a **noncyclic abelian** subgroup `A ≤ G` normalizes a finite
subgroup `K` of **coprime** order whose abelianization is nontrivial (`⁅K, K⁆ ≠ K`), then
some `x ∈ A`, `x ≠ 1`, has `C_K(x) = C_G(x) ⊓ K` **not** contained in `⁅K, K⁆`.

Specialization of `exists_ne_one_actionFixedBy_not_le_commutator` to the conjugation action
`A → MulAut K` (`Subgroup.normalizerMonoidHom`): the abstract fixed subgroup `C_K(a)` becomes
`C_G(a) ⊓ K` and `commutator ↥K` maps to `⁅K, K⁆` under `K.subtype`. -/
theorem exists_mem_centralizer_inf_not_le_commutator
    {A K : Subgroup G} [Finite ↥A] [IsMulCommutative ↥A] [Finite ↥K]
    (hAK : A ≤ Subgroup.normalizer K) (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K))
    (hSolv : IsSolvable ↥A ∨ IsSolvable ↥K) (hNC : ¬ IsCyclic ↥A) (hK' : ⁅K, K⁆ ≠ K) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 ∧ ¬ (Subgroup.centralizer {x} ⊓ K ≤ ⁅K, K⁆) := by
  classical
  -- The conjugation action `φ : A → MulAut K` and the `K.subtype`-image of `[↥K, ↥K]`.
  set φ : ↥A →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hAK)
    with hφ
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hg; exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, htop_map]
  -- `[↥K, ↥K] ≠ ⊤`: else its `K.subtype`-image would be `⁅K, K⁆ = K`.
  have hKtop : commutator ↥K ≠ ⊤ := by
    intro h; exact hK' (by rw [← hmap, h, htop_map])
  obtain ⟨a, ha_ne, hnle⟩ :=
    exists_ne_one_actionFixedBy_not_le_commutator φ hCop hSolv hNC hKtop
  -- Translate the abstract conclusion to ambient subgroups.
  obtain ⟨n, hn_fix, hn_out⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨(a : G), a.2, fun h => ha_ne (Subtype.ext h), SetLike.not_le_iff_exists.mpr
    ⟨(n : G), ?_, ?_⟩⟩
  · -- `n ∈ C_G(a) ⊓ K`: `a` conjugates `n` to itself, and `n ∈ K`.
    rw [Ch06.mem_actionFixedBy] at hn_fix
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      congrArg (Subtype.val) hn_fix
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, n.2⟩
    rintro y rfl
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `n ∉ ⁅K, K⁆`: else `n ∈ [↥K, ↥K]`, contradicting `hn_out`.
    rw [← hmap]
    intro hmem
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hmem
    exact hn_out (by rw [show n = m from Subtype.ext hmn.symm]; exact hm)

/-- **Peterfalvi (12.9), the order-`p` centralizer witness** (the genuine, `§8`-free heart of
(12.9)).  Given the counterexample data with `P₀` abelian, coprime to `K = M_F`, normalizing `K`,
and `K` not perfect, there is an element `x ∈ Ω₁(P₀)^#` (order dividing `p`) with `C_K(x) ⊄ K'`.

Proof: apply the centralizer core `exists_mem_centralizer_inf_not_le_commutator` to the abelian
noncyclic `P₀` acting by conjugation on `K`, yielding `y ∈ P₀^#` with `C_K(y) ⊄ K'`; then pass to
the order-`p` power `x = y ^ (|y| / p)` — its centralizer contains `C_K(y)`, so still escapes `K'`. -/
theorem exists_orderP_centralizer_witness [Finite G]
    (ctr : CounterexampleHypothesis (G := G))
    (habelian : IsMulCommutative ↥ctr.P0)
    (hcoprime : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K))
    (hP0_norm : ctr.P0 ≤ Subgroup.normalizer ctr.K)
    (hKperfect : ⁅ctr.K, ctr.K⁆ ≠ ctr.K) :
    ∃ x : G, x ∈ ctr.P0 ∧ x ≠ 1 ∧ x ^ ctr.p = 1 ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI := habelian
  haveI : Group.IsNilpotent ↥ctr.P0 := ctr.P0_pGroup.isNilpotent
  -- `K' = ⁅K, K⁆`.
  have hKprime : ctr.Kprime = ⁅ctr.K, ctr.K⁆ :=
    ctr.Kprime_eq.trans (Subgroup.map_subtype_commutator ctr.K)
  -- Centralizer core (A = P₀, abelian noncyclic, coprime, normalizing K, K not perfect).
  obtain ⟨y, hyP0, hy_ne, hy_cent⟩ :=
    exists_mem_centralizer_inf_not_le_commutator (A := ctr.P0) (K := ctr.K)
      hP0_norm hcoprime (Or.inl inferInstance) ctr.P0_noncyclic hKperfect
  -- `y` has `p`-power order `p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ctr.P0_pGroup) ⟨y, hyP0⟩
  have hoy : orderOf y = ctr.p ^ k :=
    (orderOf_injective ctr.P0.subtype ctr.P0.subtype_injective ⟨y, hyP0⟩).trans hk
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hoy; exact absurd hoy hy_ne
    · exact h
  have hp_dvd : ctr.p ∣ orderOf y := hoy ▸ dvd_pow_self ctr.p (by omega)
  have hord_pos : 0 < orderOf y := hoy ▸ pow_pos ctr.p_prime.pos k
  -- The order-`p` power `x = y ^ (|y| / p)`.
  set n := orderOf y / ctr.p with hn
  have hnp : n * ctr.p = orderOf y := Nat.div_mul_cancel hp_dvd
  have hn_pos : 0 < n := by
    rw [hn]; exact Nat.div_pos (Nat.le_of_dvd hord_pos hp_dvd) ctr.p_prime.pos
  have hn_lt : n < orderOf y := by
    rw [hn]; exact Nat.div_lt_self hord_pos ctr.p_prime.one_lt
  refine ⟨y ^ n, ctr.P0.pow_mem hyP0 n, ?_, ?_, ?_⟩
  · -- `y ^ n ≠ 1`: else `|y| ∣ n < |y|`, impossible.
    rw [Ne, ← orderOf_dvd_iff_pow_eq_one]
    exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  · -- `(y ^ n) ^ p = y ^ (n * p) = y ^ |y| = 1`.
    rw [← pow_mul, hnp, pow_orderOf_eq_one]
  · -- `C_K(y ^ n) ⊇ C_K(y) ⊄ K'`.
    rw [hKprime]
    intro hle
    apply hy_cent
    refine le_trans (inf_le_inf_right ctr.K ?_) hle
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro z rfl
    exact Commute.pow_left (hg y rfl) n

/-- **Peterfalvi (12.9), the `(κ ∪ σ)ᶜ`-Hall complement obligation** — the precise BG §16
(Proposition 16.1) bridge behind `(8.12.a)`.  For the type-`I` minimal-counterexample `M`, the
Sylow `p`-subgroup `P₀` (with `p ∣ [M : M_F]`, hence `p ∤ |M_F|` as `M_F` is Hall) lies in a
`(κ(M) ∪ σ(M))ᶜ`-Hall subgroup `U ≤ M`.

*Why this is the gate (and not `(8.12.a)` itself).*  BG Theorem B(1)
(`theoremB_U_sylow_abelian_rank_le_two`, already **proved** in the repo) says every Sylow of such
a `U` is abelian of rank `≤ 2`; the only missing input is producing the complement `U`.  The
type-`I` complement of `M_F` is `π(M_F)ᶜ`-Hall (immediate from `M_F` being a normal Hall
subgroup), and Proposition 16.1's type-`I` classification (`κ(M) = ∅` and `M_F = M_σ`)
identifies `π(M_F)ᶜ` with `(κ ∪ σ)ᶜ`.

**Proof (issue 2016).**  Write `M = ctr.M`, `p = ctr.p`.  Proposition 16.1 (clause (a)) gives
`κ(M) = ∅` for the type-`I` `M`, and (clause (f)) gives `M_F = M_σ`.  Since `M_F` is `π(M_F)`-Hall
in `M` (`maxNilpotentNormalHall_isHall`) and `p ∣ [M : M_F]`, we have `p ∤ |M_F| = |M_σ|`.  As
`M_σ` is `σ(M)`-Hall in `G` (`S10.isHall_Msigma_Malpha`), `p ∤ |M_σ|` forces `p ∉ σ(M)` (else
`p` would divide the `σ`-part `|M_σ|` of `|G|`).  With `κ(M) = ∅` this gives `p ∈ (κ ∪ σ)ᶜ`, so
the `p`-group `P₀` is a `(κ ∪ σ)ᶜ`-subgroup of the solvable `M` and Hall's theorem D
(`Ch03.hall_D`) places it in a `(κ ∪ σ)ᶜ`-Hall subgroup `U` of `M`.  The only `§16`-gated inputs
are the cited Proposition 16.1 type-`I` clauses (lane-f frontier, issue 8015). -/
theorem exists_sigmaKappaCompl_hall_ge_P0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ U : Subgroup G, ctr.P0 ≤ U ∧ U ≤ ctr.M ∧
      Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ)
        (U.subgroupOf ctr.M) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI hMsolv : IsSolvable ↥ctr.M := hG.solvable_of_mem_maximalSubgroups ctr.M_maximal
  -- κ(M) = ∅ (Type I ⟹ Type F, Prop 16.1 clause (a)).
  have hκ : OddOrder.BG.Ch4.S14.kappa ctr.M = ∅ :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).1.mp ctr.M_typeI
  -- M_F = M_σ (Prop 16.1 clause (f)).
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  -- `p ∤ |M_F|`: `M_F` is `π(M_F)`-Hall in `M` and `p ∣ [M : M_F]`.
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  -- `p ∣ |G|` (`p ∣ [M : M_F] ∣ |M| ∣ |G|`).
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  -- `p ∉ σ(M)`: `M_σ` is `σ(M)`-Hall in `G`, and `p ∤ |M_σ|` with `p ∣ |G| = |M_σ|·[G:M_σ]`.
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  have hp_not_sigma : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
    intro hpσ
    refine hp_not_dvd_Mσ ?_
    have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
        * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
      rw [Subgroup.card_mul_index]; exact hp_dvd_G
    rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
    · exact h
    · exact absurd hpσ (hσHall.index_no_pi ctr.p
        (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))
  -- `p ∈ (κ ∪ σ)ᶜ`.
  have hp_compl : ctr.p ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M
      ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hκ ▸ Set.notMem_empty ctr.p, hp_not_sigma⟩
  -- Every prime divisor of `|P₀|` (a `p`-power) is `p ∈ (κ ∪ σ)ᶜ`; place `P₀` via Hall D.
  have hcond : ∀ q ∈ (Nat.card ↥(ctr.P0.subgroupOf ctr.M)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ctr.P0_pGroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv, hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hp_compl
  obtain ⟨V, hVhall, hPV⟩ := Ch03.hall_D (G := ↥ctr.M) hcond
  refine ⟨V.map ctr.M.subtype, ?_, Subgroup.map_subtype_le V, ?_⟩
  · rw [show ctr.P0 = (ctr.P0.subgroupOf ctr.M).map ctr.M.subtype from
      (Subgroup.map_subgroupOf_eq_of_le ctr.P0_le_M).symm]
    exact Subgroup.map_mono hPV
  · have hUeq : (V.map ctr.M.subtype).subgroupOf ctr.M = V :=
      Subgroup.comap_map_eq_self_of_injective ctr.M.subtype_injective V
    rw [hUeq]; exact hVhall

/-- **Peterfalvi (12.9), the rank-two structure for `P₀`** = `(8.12.a)`.

Every Sylow subgroup of the type-`I` complement `U` (`M = M_F ⋊ U`) is abelian of rank `≤ 2`
(BG **Theorem B(1)**, `theoremB_U_sylow_abelian_rank_le_two`, **proved**); applied to the Sylow
`p`-subgroup `P₀ ≤ U` and combined with `P₀` noncyclic (Hypothesis `(12.8)`, `ctr.P0_noncyclic`,
giving `2 ≤ rank P₀` via `two_le_rank_of_noncyclic_pSubgroup`), this forces `P₀` abelian of rank
exactly `2`.

The substantive content (Theorem B(1) + the rank lower bound) is therefore **wired and
load-bearing**; the only remaining gap is the `(κ ∪ σ)ᶜ`-Hall complement obligation
`exists_sigmaKappaCompl_hall_ge_P0` (the BG §16 / Proposition 16.1 bridge, lane-f).

(The other structural inputs `P₀` coprime to `K`, `P₀ ≤ N_G(K)`, `⁅K, K⁆ ≠ K` are discharged in
`exists_rankTwoWitness` from `(8.11)` [`M_F` Hall] and `M_F ◁ M` nilpotent + nontrivial.) -/
theorem counterexample_P0_K_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨U, hP0U, hUM, hU⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  obtain ⟨hrank_le, habelian⟩ :=
    OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two hG ctr.M_maximal hUM hU
      ctr.p ctr.p_prime ctr.P0 hP0U ctr.P0_pGroup
  exact ⟨habelian, le_antisymm hrank_le
    (OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup ctr.P0_noncyclic)⟩

/-- A `p`-Hall subgroup `H` (its order having only `p`-primary divisors among `π = π(|H|)`) with
`p ∣ |H|` contains a Sylow `p`-subgroup of the ambient group `G`.

A Sylow `p`-subgroup `R` of `↥H` maps to a subgroup `R.map H.subtype ≤ H` of `G` of the same
order `p ^ v_p(|H|)`.  Since `H` is Hall, `p ∤ [G : H]`, so `v_p(|H|) = v_p(|G|)`; hence
`R.map H.subtype` is a Sylow `p`-subgroup of `G` contained in `H`. -/
theorem exists_sylow_le_of_hall [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H) (hp : p ∣ Nat.card ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  -- A Sylow `p`-subgroup `R` of `↥H`.
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥H))
  -- The `p`-multiplicity of `|H|` equals that of `|G|`, because `H` is Hall and `p ∣ |H|`.
  have hfact : (Nat.card ↥H).factorization p = (Nat.card G).factorization p := by
    have hcop : Nat.Coprime (Nat.card ↥H) H.index := hHall.coprime_index
    have hp_notdvd : ¬ p ∣ H.index :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hp)
    have hidx0 : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_notdvd
    have hsplit : (Nat.card G).factorization p =
        (Nat.card ↥H).factorization p + H.index.factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
        Subgroup.index_ne_zero_of_finite]
      rfl
    rw [hsplit, hidx0, add_zero]
  -- `R.map H.subtype` is a `p ^ v_p(|G|)`-subgroup of `G`, i.e. a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(R : Subgroup ↥H) = p ^ (Nat.card G).factorization p := by
    rw [R.card_eq_multiplicity, hfact]
  have hcardQ : Nat.card ↥((R : Subgroup ↥H).map H.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardR]
  exact ⟨Sylow.ofCard ((R : Subgroup ↥H).map H.subtype) hcardQ,
    by rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi (12.9), existence of the second maximal `L`** — a §8 obligation
(`(8.17.a)` `bgTheoremE_cover_data`: `p ∈ π(G)` is covered by some `π((M_i)_s)`, giving a maximal
`L` with `p ∣ |L_s|`; then `(8.11)`/`L_s ⊇ Sylow_p(G)` and Sylow conjugation place `P₀ ⊆ L_s`). -/
theorem exists_second_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ (L : Subgroup G) (Lt : PeterfalviType), L ∈ maximalSubgroups G ∧ L ≠ ctr.M ∧
      HasPeterfalviType Lt L ∧ ctr.P0 ≤ mainSubgroup L Lt := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∈ π(G)`: `p ∣ [M : M_F] ∣ |M| ∣ |G|`.
  have hp_in_G : ctr.p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨ctr.p_prime, ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ctr.p_dvd_index (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card ctr.M))
    exact Subgroup.relIndex_dvd_card (H := ctr.K) (K := ctr.M)
  -- `p ∤ |M_F| = |K|`: `(8.11)` makes `M_F` Hall, and `p ∣ [M : M_F] ∣ [G : M_F]`.
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hpK : ¬ ctr.p ∣ Nat.card ↥ctr.K := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    exact ctr.p_prime.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm)
  -- BG Theorem E cover data: `p ∈ π((M_i)_s)` for some representative `M_i = L₀`.  Repackage the
  -- representative as genuine local variables `L₀, Lt` (so we may later `cases` on the type label).
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨i, hi⟩ := (data.primeFactors_cover ctr.p ctr.p_prime).mp hp_in_G
  obtain ⟨L₀, Lt, hL₀max, hL₀typed, hi'⟩ :
      ∃ (L₀ : Subgroup G) (Lt : PeterfalviType), L₀ ∈ maximalSubgroups G ∧
        HasPeterfalviType Lt L₀ ∧
        ctr.p ∈ (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors :=
    ⟨data.reps i, data.tau i, data.maximal i, data.typed i, hi⟩
  have hp_Ls : ctr.p ∣ Nat.card ↥(mainSubgroup L₀ Lt) := (Nat.mem_primeFactors.mp hi').2.1
  -- `(8.11)`: `(L₀)_s` is Hall, hence contains a Sylow `p`-subgroup `Q` of `G`.
  have hLsHall : Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors
      (mainSubgroup L₀ Lt) :=
    (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hL₀max hL₀typed).2
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_hall hLsHall hp_Ls
  -- A Sylow `p`-subgroup `Q'` of `G` over `P₀`, then conjugate `Q` to `Q'`.
  obtain ⟨Q', hQ'le⟩ := ctr.P0_pGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  -- `P₀ ≤ Q' = ↑(g • Q) = conj g • ↑Q ≤ conj g • (L₀)_s`.
  have hP0_le : ctr.P0 ≤ MulAut.conj g • mainSubgroup L₀ Lt := by
    refine hQ'le.trans ?_
    have hQ'eq : (Q' : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [hQ'eq]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQle
  -- Assemble: `L = conj g • L₀`, type `Lt`, with `P₀ ⊆ (conj g • L₀)_s`.
  refine ⟨MulAut.conj g • L₀, Lt, mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL₀max)), ?_,
    hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed, ?_⟩
  · -- `conj g • L₀ ≠ M`: else `M` has type `Lt`; if `Lt = I` then `p ∣ |K|` (false), else `M` is
    -- both type I and non-I (false).
    rintro hEq
    have hMtype : HasPeterfalviType Lt ctr.M :=
      hEq ▸ hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed
    -- transport the divisibility `p ∣ |(L₀)_s|` to `p ∣ |M_s|`.
    have hp_Ms : ctr.p ∣ Nat.card ↥(mainSubgroup ctr.M Lt) := by
      have hcard : Nat.card ↥(mainSubgroup ctr.M Lt) = Nat.card ↥(mainSubgroup L₀ Lt) := by
        rw [← hEq, ← mainSubgroup_pointwise_smul, card_pointwise_smul]
      rw [hcard]; exact hp_Ls
    -- `ctr.M` has type `Lt` and type I.  Type `I` forces `p ∣ |K|` (false); any non-I label
    -- makes `ctr.M` non-I, contradicting type I via `not_isTypeI_of_isTypeNonI`.
    have hMnotNonI : ¬ IsTypeNonI ctr.M := fun h =>
      OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG ctr.M_maximal h ctr.M_typeI
    cases Lt with
    | I => exact hpK (by rw [ctr.K_eq_MF]; exact hp_Ms)
    | II => exact hMnotNonI (Or.inl hMtype)
    | III => exact hMnotNonI (Or.inr (Or.inl hMtype))
    | IV => exact hMnotNonI (Or.inr (Or.inr (Or.inl hMtype)))
    | V => exact hMnotNonI (Or.inr (Or.inr (Or.inr hMtype)))
  · -- `P₀ ⊆ mainSubgroup (conj g • L₀) Lt`.
    rw [← mainSubgroup_pointwise_smul]; exact hP0_le

/-- **Peterfalvi (12.9), centralizer control** — **discharged** from `(8.12.b)`
(`typeI_or_typeII_centralizer_unique`) + `G` simple.

Applying `(8.12.b)` with `U = M` and `X = {x}` (`x ∈ M^#`, and `C_K(x) ⊄ K'` gives
`M_F ⊓ C_G(x) ≠ 1`) yields `C_G(x) ≤ M` together with `IsUniquelyMaximal (C_G(x))` — `M` is the
*unique* maximal subgroup over `C_G(x)`.  Hence: `N_G(⟨x⟩) ⊇ C_G(x)` is a proper subgroup
(`⟨x⟩` is a proper nontrivial subgroup of the nonabelian simple `G`, so not normal), so it lies
in a maximal subgroup over `C_G(x)`, which must be `M`; and any maximal `L ≠ M` cannot contain
`C_G(x)`. -/
theorem centralizer_control_of_CKx [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ ctr.M)
    {Lt : PeterfalviType} (hLt : HasPeterfalviType Lt L) (hPL : ctr.P0 ≤ mainSubgroup L Lt)
    {x : G} (hx : x ∈ ctr.P0) (hxne : x ≠ 1)
    (hCKx : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)) :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ≤ L) := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  have hMcoatom : IsCoatom ctr.M := ctr.M_maximal
  have hLcoatom : IsCoatom L := hL
  have hxM : x ∈ ctr.M := ctr.P0_le_M hx
  -- `M_F ⊓ C_G(x) ≠ ⊥` from `C_K(x) ⊄ K'`.
  have hCKne : maxNilpotentNormalHall ctr.M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot; apply hCKx; rw [ctr.K_eq_MF, inf_comm, hbot]; exact bot_le
  have hxsharp : ({x} : Set G) ⊆ sharpSubgroup ctr.M := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨hxM, fun h => hxne (Set.mem_singleton_iff.mp h)⟩
  -- (8.12.b): `C_G(x) ≤ M` and uniquely maximal.
  obtain ⟨hCxleM, huniq⟩ := OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique hG
    ctr.M_maximal (Or.inl ctr.M_typeI) (le_refl ctr.M) ({x} : Set G) (Set.singleton_nonempty x)
    hxsharp hCKne
  refine ⟨?_, fun hCxleL => hLM (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hLcoatom hCxleL).symm⟩
  -- `N_G(⟨x⟩) ⊆ M`.
  have hCx_le_Nx : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure]; exact Subgroup.centralizer_le_normalizer _
  have hcl_le_M : Subgroup.closure ({x} : Set G) ≤ ctr.M := Subgroup.closure_le _ |>.mpr (by
    simpa using hxM)
  have hNx_lt : Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
    · exact hxne (by simpa [hb] using Subgroup.subset_closure (Set.mem_singleton x))
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hcl_le_M))
  obtain ⟨N, hNco, hNx_le_N⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNx_lt
  exact hNx_le_N.trans (le_of_eq
    (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hNco (hCx_le_Nx.trans hNx_le_N)).symm)

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup.

Honest assembly: the structural inputs `(8.12.a)`/`(8.11)` (`counterexample_P0_K_structure`) give
`P₀` abelian of rank `2`, coprime to `K`, normalizing `K`, with `K` not perfect; the genuine
`§8`-free `exists_orderP_centralizer_witness` then produces the order-`p` element `x` with
`C_K(x) ⊄ K'`; `(8.17.a)` (`exists_second_maximal`) supplies `L`; and `(8.12.b)`
(`centralizer_control_of_CKx`) the centralizer conditions. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr) := by
  obtain ⟨hab, hrank⟩ := counterexample_P0_K_structure hG ctr
  refine ⟨hab, hrank, ?_⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `P₀` coprime to `K`: `(8.11)` makes `M_F` Hall (`p ∤ |M_F|` from `p ∣ [M : M_F] ∣ [G : M_F]`).
  have hcop : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K) := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    have hcop_p : Nat.Coprime ctr.p (Nat.card ↥ctr.K) :=
      Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn]; exact hcop_p.pow_left n
  -- `P₀ ≤ N_G(K)` from `M_F ◁ M` (`maxNilpotentNormalHall_le_normalizer`).
  have hnorm : ctr.P0 ≤ Subgroup.normalizer ctr.K := by
    rw [ctr.K_eq_MF]
    exact ctr.P0_le_M.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M)
  -- `⁅K, K⁆ ≠ K`: `K = M_F` is nilpotent and nontrivial, hence not perfect.
  have hperf : ⁅ctr.K, ctr.K⁆ ≠ ctr.K := by
    obtain ⟨tiData⟩ := ctr.M_typeI
    have hKH : ctr.K = tiData.typeF.H := ctr.K_eq_MF.trans tiData.typeF.H_eq.symm
    haveI : Nontrivial ↥ctr.K :=
      ctr.K.nontrivial_iff_ne_bot.mpr (hKH ▸ tiData.typeF.H_nontrivial)
    haveI : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hlt : commutator ↥ctr.K < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ctr.K)
    intro hEq
    have htop_map : (⊤ : Subgroup ↥ctr.K).map ctr.K.subtype = ctr.K := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    exact hlt.ne (Subgroup.map_injective ctr.K.subtype_injective
      (by rw [Subgroup.map_subtype_commutator, hEq, htop_map]))
  obtain ⟨x, hxP0, hxne, hxp, hCKx⟩ := exists_orderP_centralizer_witness ctr hab hcop hnorm hperf
  obtain ⟨L, Lt, hLmax, hLne, hLt, hPL⟩ := exists_second_maximal hG ctr
  obtain ⟨hNx, hCx⟩ := centralizer_control_of_CKx hG ctr hLmax hLne hLt hPL hxP0 hxne hCKx
  exact ⟨{ L := L, L_maximal := hLmax, L_type := Lt, L_hasType := hLt, P0_le_Ls := hPL,
           x := x, x_mem_P0 := hxP0, x_ne_one := hxne, x_mem_omega1 := hxp,
           CKx_not_le_Kprime := hCKx, normalizer_closure_x_le_M := hNx,
           centralizer_x_not_le_L := hCx }⟩

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is
Frobenius with kernel `L_F`. -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  sorry

/-- **Peterfalvi (12.1) for the witness subgroup `L`, with its Frobenius witness**: the second
maximal subgroup `L` of (12.9) carries the (12.1) Hypothesis together with an explicit Frobenius
decomposition of its kernel `H = L_F`.  Since `L` is type I (Frobenius, by (12.10)
`witness_L_frobenius`), `hypothesis_of_typeIData` applied to the recovered `TypeIData` yields the
Hypothesis whose `typeI` is that very data, so the Frobenius group structure `frob.frobenius`
transfers to `hyp.H`.  This Frobenius witness is the structural input to coherence (12.6). -/
theorem witness_L_hypothesis_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (hyp.H.subgroupOf data.L) C := by
  obtain ⟨frob, _⟩ := witness_L_frobenius hG data
  obtain ⟨hyp, hhyp⟩ := hypothesis_of_typeIData hG data.L_maximal frob.typeI
  refine ⟨hyp, frob.complement, ?_⟩
  have hH : hyp.H = frob.typeI.typeF.H := by
    rw [show hyp.H = hyp.typeI.typeF.H from rfl, hhyp]
  rw [hH]
  exact frob.frobenius

/-- **Peterfalvi (12.1) Hypothesis for the witness subgroup `L`** (forgetful form of
`witness_L_hypothesis_frobenius`). -/
theorem witness_L_hypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nonempty (Hypothesis data.L) := by
  obtain ⟨hyp, _⟩ := witness_L_hypothesis_frobenius hG data
  exact ⟨hyp⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) for the witness subgroup `L`**: the type-I family `S` of `L` is coherent.
Combines the Hypothesis + Frobenius witness of `witness_L_hypothesis_frobenius` with the (12.6)
Frobenius-case coherence `frobenius_typeI_coherent`.  This is the coherence input "`S` coherent" of
the (12.16) Dade calculation — it feeds the `(7.8.b)` norm bound `hB` of `CounterexampleDadeData`
via the §7 `Hypothesis78`/`NormEstimates`. -/
theorem witness_L_coherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  obtain ⟨hyp, C, hC⟩ := witness_L_hypothesis_frobenius hG data
  exact ⟨hyp, frobenius_typeI_coherent hG hyp ⟨C, hC⟩⟩

/-- **Peterfalvi (12.11)**: `M inter L` complements `K` in `M` and lies in the
Fitting kernel `H` of the witness subgroup `L`. -/
theorem intersection_complement_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  sorry

/-- **(12.12) Case A core.**  A finite group `E` acting faithfully on a one-dimensional
`𝔽_p`-space `V` is cyclic, with `|E| ∣ |V| - 1 = p - 1`.  This is the reducible / rank-one case
of Peterfalvi (12.12): `End_{𝔽_p}(V) ≅ 𝔽_p` (every endomorphism of a line is a homothety), so
`E ↪ End(V)ˣ ≅ (ℤ/p)ˣ`, a cyclic group of order `p - 1`. -/
theorem isCyclic_and_card_dvd_of_faithful_one_dim
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `End_{𝔽_p}(V) ≅ 𝔽_p` via `algebraMap` (bijective in dimension one: every endo is `c • id`).
  have hsurj : Function.Surjective (algebraMap (ZMod p) (Module.End (ZMod p) V)) := by
    intro u
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) V)) :=
    (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective
  let eRing : ZMod p ≃+* Module.End (ZMod p) V := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  -- `E ↪ End(V)ˣ ≃ (ℤ/p)ˣ`.
  let φ : E →* (ZMod p)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).symm.toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hfaith
    have h1 : (MonoidHom.toHomUnits ρ) a = (MonoidHom.toHomUnits ρ) b :=
      (Units.mapEquiv eRing.toMulEquiv).symm.injective (by simpa [φ] using hab)
    simpa using congrArg (Units.val) h1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : IsCyclic φ.range := inferInstance
  have hcardV : Nat.card V = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, pow_one, Nat.card_eq_fintype_card,
      ZMod.card]
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
      (MonoidHom.ofInjective hφinj).symm.surjective, ?_⟩
  rw [hcardV]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

/-- **(12.12) irreducible-case core.**  An odd-order group `E` acting faithfully and
irreducibly on a two-dimensional `𝔽_p`-space `V` (with `p ∤ |E|`) is cyclic, with
`|E| ∣ |V| - 1 = p² - 1`.  This is the rank-two irreducible case of Peterfalvi (12.12):
BG Theorem 2.6(a) (`odd_two_dim_abelian`) abelianizes `E`, and the commutativity-free Singer
mechanism (`isCyclic_and_card_dvd_of_faithful_irreducible_comm`) then realizes `E` inside the
units of the Singer field `𝔽_p[E] ⧸ I ≅ 𝔽_{p²}`. -/
theorem isCyclic_and_card_dvd_of_odd_two_dim_irreducible
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- BG 2.6(a): a faithful odd two-dimensional representation has abelian image.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  -- Give `V` the `𝔽_p[E]`-module structure of the representation *directly* (this is
  -- definitionally `ρ.asModule`'s instance, but stated on `V` so that instance synthesis does
  -- not choke on the `ρ.asModule` notation — which it does once `IsIrreducible ρ` is around).
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  exact isCyclic_and_card_dvd_of_faithful_irreducible_comm (M := V) hcomm hfaith'

/-- **(12.12) `p + 1` refinement, irreducible case.**  An odd-order group `E` (`p ∤ |E|`) acting
faithfully and irreducibly on a two-dimensional `𝔽_p`-space `V`, with **no nontrivial element
acting as an `𝔽_p`-scalar** (`hnonscalar`), is cyclic with `|E| ∣ p + 1`.

This is the rank-two refinement of Peterfalvi (12.12): the plain irreducible core
(`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`) only bounds `|E| ∣ p² - 1`.  The Singer
realization places `E` inside the cyclic group `𝔽_{p²}ˣ` (order `p² - 1`), where the non-scalar
hypothesis makes it meet the scalar subgroup `𝔽_pˣ` (order `p - 1`) trivially, so
`coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar` gives `Coprime |E| (p - 1)`.  Together
with `|E| ∣ p² - 1 = (p - 1)(p + 1)`, coprimality to the first factor forces `|E| ∣ p + 1`. -/
theorem isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E)
    (hnonscalar : ∀ e : E, (∃ n : ℕ, ∀ x : V, ρ e x = n • x) → e = 1) :
    IsCyclic E ∧ Nat.card E ∣ p + 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `|E| ∣ p² - 1` and cyclicity from the irreducible core.
  obtain ⟨hcyc, hdvd_sq⟩ :=
    isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  have hcardV : Nat.card V = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, Nat.card_eq_fintype_card, ZMod.card]
  rw [hcardV] at hdvd_sq
  -- Singer non-scalar core ⟹ `Coprime |E| (p - 1)`.  Reuse the `𝔽ₚ[E]`-module setup of the core.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  have hns' : ∀ e : E,
      (∃ n : ℕ, ∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = n • x) → e = 1 := by
    rintro e ⟨n, hn⟩
    exact hnonscalar e ⟨n, fun x => by rw [← hsmul e x]; exact hn x⟩
  have hcop : Nat.Coprime (Nat.card E) (p - 1) :=
    OddOrder.RepresentationTheory.coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar
      hcomm hfaith' hns'
  -- `|E| ∣ (p - 1)(p + 1) = p² - 1` and `Coprime |E| (p - 1)` force `|E| ∣ p + 1`.
  have hpq : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := (Fact.out (p := p.Prime)).two_le; omega⟩
    show (n + 1) * (n + 3) = (n + 2) ^ 2 - 1
    have hexp : (n + 2) ^ 2 = (n + 1) * (n + 3) + 1 := by ring
    omega
  rw [← hpq] at hdvd_sq
  exact hcop.dvd_of_dvd_mul_left hdvd_sq

/-- **(12.12) rep-theory core (combined).**  A finite odd-order group `E` (`p ∤ |E|`) acting
**fixed-point-freely** (no nonzero vector is fixed by a nontrivial element) on an `𝔽_p`-space `V`
of dimension `1` or `2` is **cyclic**, with `|E| ∣ |V| - 1`.  Dispatches the two (12.12) cores:
dim 1 (or dim 2 with an `E`-invariant line) ⟹ Case A (`isCyclic_and_card_dvd_of_faithful_one_dim`);
dim 2 irreducible ⟹ Case B (`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`).  The FPF
hypothesis makes `E` faithful on every nonzero invariant subspace. -/
theorem isCyclic_and_card_dvd_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- Step 1: the FPF hypothesis makes `ρ` faithful.
  -- `V` is nontrivial because `finrank V ≥ 1`, so it has a nonzero vector; a nontrivial element in
  -- the kernel would fix that vector, contradicting `hfpf`.
  haveI hVnt : Nontrivial V := by
    rcases hdim with h | h
    · exact Module.nontrivial_of_finrank_eq_succ h
    · exact Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [h])
  have hfaith : Function.Injective ρ := by
    intro a b hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (hfpf (b⁻¹ * a) hba v ?_)
    rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rcases hdim with hd1 | hd2
  · -- dim 1: Case A.
    exact isCyclic_and_card_dvd_of_faithful_one_dim ρ hfaith hd1
  · -- dim 2.
    by_cases hirr : Representation.IsIrreducible ρ
    · -- irreducible: Case B.
      exact isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hd2 hp_ndvd
    · -- reducible: a proper nonzero invariant line `W` exists; apply Case A to `W.toRepresentation`,
      -- then lift `|E| ∣ p - 1` to `|E| ∣ p² - 1` via `p - 1 ∣ p² - 1`.
      -- `¬ IsSimpleOrder` plus nontriviality (`⊥ ≠ ⊤` since `V` is nontrivial) yields a proper
      -- nonzero subrepresentation `W`.
      have hbnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
        bot_ne_top (congrArg Subrepresentation.toSubmodule h)
      haveI : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
      have hnotall : ¬ ∀ W : Subrepresentation ρ, W = ⊥ ∨ W = ⊤ := fun H =>
        hirr { eq_bot_or_eq_top := H }
      push_neg at hnotall
      obtain ⟨W, hWbot, hWtop⟩ := hnotall
      -- `W` is a proper nonzero subrepresentation; its submodule has `finrank = 1`.
      have hWsub_bot : W.toSubmodule ≠ ⊥ := fun h =>
        hWbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      have hWsub_top : W.toSubmodule ≠ ⊤ := fun h =>
        hWtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      haveI : Finite ↥W.toSubmodule := Subtype.finite
      haveI : Module.Finite (ZMod p) ↥W.toSubmodule := Module.Finite.of_finite
      have hpos : 0 < Module.finrank (ZMod p) ↥W.toSubmodule := by
        have := Submodule.finrank_lt_finrank_of_lt (s := (⊥ : Submodule (ZMod p) V))
          (t := W.toSubmodule) (lt_of_le_of_ne bot_le (Ne.symm hWsub_bot))
        simpa using this
      have hlt : Module.finrank (ZMod p) ↥W.toSubmodule < Module.finrank (ZMod p) V :=
        Submodule.finrank_lt hWsub_top
      have hWdim : Module.finrank (ZMod p) ↥W.toSubmodule = 1 := by
        rw [hd2] at hlt; omega
      -- faithfulness of `W.toRepresentation` from `hfpf` restricted to `W`.
      have hfaithW : Function.Injective W.toRepresentation := by
        intro a b hab
        by_contra hne
        have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
        -- every element of `W` is fixed by `ρ (b⁻¹ a)`, hence is `0` by `hfpf`; so `W = ⊥`.
        apply hWsub_bot
        rw [Submodule.eq_bot_iff]
        intro w hw
        have hfix : W.toRepresentation (b⁻¹ * a) ⟨w, hw⟩ = ⟨w, hw⟩ := by
          rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
            inv_mul_cancel, map_one, Module.End.one_apply]
        have hfixV : ρ (b⁻¹ * a) w = w := by
          have := congrArg Subtype.val hfix
          simpa [Subrepresentation.toRepresentation, LinearMap.restrict_coe_apply] using this
        exact hfpf (b⁻¹ * a) hba w hfixV
      -- Case A on `W.toRepresentation` gives `IsCyclic E ∧ |E| ∣ p - 1`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_faithful_one_dim W.toRepresentation hfaithW hWdim
      refine ⟨hcyc, ?_⟩
      -- `Nat.card ↥W.toSubmodule = p`, `Nat.card V = p²`.
      have hcardW : Nat.card ↥W.toSubmodule = p := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hWdim, pow_one, Nat.card_eq_fintype_card,
          ZMod.card]
      have hcardV : Nat.card V = p ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
      rw [hcardW] at hdvd
      rw [hcardV]
      -- `|E| ∣ p - 1 ∣ p² - 1`, via `p² - 1 = (p - 1) * (p + 1)`.
      refine hdvd.trans ?_
      have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      refine ⟨k + 2, ?_⟩
      have hsq : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
      rw [hsq, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form).**  A finite odd-order group
`E` (`p ∤ |E|`) acting **fixed-point-freely** on an elementary abelian `p`-group `M` — encoded by
a `ZMod p`-module structure on `Additive M` — of `𝔽_p`-dimension `1` or `2` is **cyclic**, with
`|E| ∣ |M| - 1`.

This lifts `isCyclic_and_card_dvd_of_fpf_dim_le_two` from an abstract `Representation` to a
`MulDistribMulAction` (via `Representation.ofDistribMulAction`), which is the form that a
conjugation action of `E` on an elementary abelian subgroup supplies. -/
theorem isCyclic_and_card_dvd_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The fixed-point-free hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    -- `e • v = Additive.ofMul (e • v.toMul)` definitionally; pass to the multiplicative action.
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  exact ⟨hcyc, by rwa [Nat.card_congr (Additive.toMul (α := M))] at hdvd⟩

/-- **(12.12) rep-theory bridge (conjugation form).**  Let a finite group `E` normalize an
elementary abelian `p`-subgroup `T` of order `p` or `p²` of `G`, with `|E|` odd and coprime to `p`,
and let `E` act **fixed-point-freely on `T` by conjugation** (no nontrivial element of `T` is fixed
by a nontrivial element of `E`).  Then `E` is **cyclic** and `|E|` divides `p - 1` or `p² - 1`.

This is the `§8`-free structural core of Peterfalvi (12.12): there `T = Ω₁(Z(O_p(H)))` is the
rank `≤ 2` elementary abelian subgroup and `E` the Frobenius complement of `L`, acting FPF on `T`
by (12.10).  The `p + 1` refinement of (12.12) is separate (it consumes (12.9)/(12.11)). -/
theorem isCyclic_and_card_dvd_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p ^ 2 - 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpf' : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_of_fpf_mulDistribMulAction hodd hp_ndvd hdim hfpf'
  refine ⟨hcyc, ?_⟩
  rcases hT_card with h | h
  · exact Or.inl (by rwa [h] at hdvd)
  · exact Or.inr (by rwa [h] at hdvd)

/-- **Peterfalvi (12.12)**: the Frobenius complement in the witness subgroup is
cyclic, with order dividing `p - 1` or `p + 1`. -/
theorem complement_cyclic_order_dvd [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (frob : TypeIFrobeniusData L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  sorry

/-! ## (12.13)--(12.16): Dade notation and contradiction -/

/-- **Peterfalvi (12.13)**: notation for the final Dade calculation in the
minimal counterexample. -/
structure DadeNotation {L : Subgroup G} (hyp : Hypothesis L) where
  e : ℕ
  e_eq_index : Prop
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  chi : ClassFunction ↥L ℂ
  chi_mem : chi ∈ hyp.Sset
  chi_degree_eq_e : chi 1 = (e : ℂ)
  psi : ClassFunction G ℂ
  psi_eq_tau1_chi : psi = tau1 chi
  rhoFormula : Prop
  rhoMFormula : Prop

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13), the Dade calculation realized from coherence**: given the (12.6) coherent
extension of `L`'s family `S` (`S07.IsCoherent`, supplied by `witness_L_coherent`) and a distinguished
character `χ ∈ S` of degree `e`, the (12.13) `DadeNotation` is realized with `τ₁ =` the coherent
extension and `ψ = χ^{τ₁} = extension χ`.

This wires the coherent isometric extension into the `ψ`-construction backbone of (12.16): the
former opaque `tau1`/`psi` are now the genuine `coh.extension` and its value on `χ`.  The remaining
input is the *selection* of the distinguished `χ` — a minimal-degree `Ind_H^L θ` with `θ` a
nontrivial linear character of `H = L_F`, so `χ(1) = [L:H] = e` — together with the (12.12) degree
bounds on `e`.  (`e_eq_index`/`rhoFormula`/`rhoMFormula` remain the structure's carried `Prop`s.) -/
noncomputable def dadeNotation_of_coherence {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset) (e : ℕ) (hdeg : χ 1 = (e : ℂ)) :
    DadeNotation hyp where
  e := e
  e_eq_index := e = (hyp.H.subgroupOf L).index
  tau1 := coh.extension
  chi := χ
  chi_mem := hχ
  chi_degree_eq_e := hdeg
  psi := coh.extension χ
  psi_eq_tau1_chi := rfl
  rhoFormula := True
  rhoMFormula := True

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13), the distinguished character**: the family `S` of `L` contains a member of
minimal degree `[L : H]` (`H = L_F`), namely `Ind_H^L θ` for `θ` a nontrivial **linear** character
of `H`.  Such `θ` exists because `H = L_F` is a nontrivial nilpotent group, so its commutator is
proper (`H` is not perfect); `exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`
then supplies a nontrivial degree-one `θ`, and `induce_apply_one` gives the induced degree
`[L:H]·θ(1) = [L:H]`.  This is the distinguished `χ ∈ S` with `χ(1) = e = [L:H]` of the (12.13)/(12.16)
Dade calculation — the input to `dadeNotation_of_coherence`. -/
theorem exists_distinguished_char {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    ∃ χ ∈ hyp.Sset, χ (1 : ↥L) = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  have hHL : hyp.typeI.typeF.H ≤ L := hyp.typeI.typeF.H_le
  have e : ↥((hyp.typeI.typeF.H).subgroupOf L) ≃* ↥(hyp.typeI.typeF.H) :=
    Subgroup.subgroupOfEquivOfLe hHL
  haveI : Nontrivial ↥(hyp.typeI.typeF.H) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.H_nontrivial
  haveI : Group.IsNilpotent ↥(hyp.typeI.typeF.H) :=
    hyp.typeI.typeF.H_eq ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) := e.toEquiv.nontrivial
  haveI : IsSolvable ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hcomm : commutator ↥((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial _).ne
  obtain ⟨θ, hθ_ne, hθ_deg⟩ :=
    OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top
      hcomm
  have hmem : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset :=
    ⟨θ, hθ_ne, rfl⟩
  refine ⟨_, hmem, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ_deg, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The placed induced family for the witness `L`** (§12→§7 bridge, the `θ`/`ind1H` shape
`hypothesis78OfDade` consumes).  Applies `exists_placed_induced_family` to the distinguished
`χ = Ind θ_lin ∈ S` of `exists_distinguished_char` (`θ_lin` nontrivial linear, so `χ ≠ Ind 1_K` by
`induce_ne_trivialChar_induce`): the distinguished char lands at index `0` with induced degree
`[L:K]` (`= e`), the trivial char `1_K` lands at some `ind1H ≠ 0`, and the family is
injective/covering.  `K = (L_F).subgroupOf L` is normal in `L` (`maxNilpotentNormalHall_..._normal`).
This is the family input to the witness-`L` `Hypothesis78`. -/
theorem exists_witness_placed_family {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    ∃ (n : ℕ) (θ : Fin (n + 1) → IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
      (ind1H : Fin (n + 1)),
      ind1H ≠ 0 ∧
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ 0 : ClassFunction _ ℂ) (1 : ↥L) = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) ∧
      θ ind1H = trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      Function.Injective (fun i => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ i : ClassFunction _ ℂ)) ∧
      ∀ φ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
        ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction _ ℂ) ∈
          Set.range (fun i => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
            (θ i : ClassFunction _ ℂ)) := by
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨χ, hχ, hdeg⟩ := exists_distinguished_char hyp
  obtain ⟨θlin, hθ_ne, hχ_eq⟩ := hχ
  obtain ⟨n, θ, ind1H, hind, h0, htriv, hinj, hcov⟩ :=
    OddOrder.Peterfalvi.S09.Cert.exists_placed_induced_family ((hyp.typeI.typeF.H).subgroupOf L) χ
      ⟨θlin, hχ_eq.symm⟩
      (hχ_eq ▸ OddOrder.Peterfalvi.S09.Cert.induce_ne_trivialChar_induce
        ((hyp.typeI.typeF.H).subgroupOf L) θlin hθ_ne)
  exact ⟨n, θ, ind1H, hind, by rw [h0]; exact hdeg, htriv, hinj, hcov⟩

/-- **Peterfalvi (12.13)/(12.16), the degree lower bound `e ≥ 3`**: the distinguished degree
`e = [L:H]` (`H = L_F`) of a type-I `Hypothesis` is at least `3`.  It equals the order of the
Frobenius complement `U` (`H` complements `U` in `L`, `typeF.complement`), which is **nontrivial**
(`typeF.U_nontrivial`) and of **odd** order (a subgroup of the odd-order `G`); an odd integer `> 1`
is `≥ 3`.  This discharges the `he : 3 ≤ e` field of `CounterexampleDadeData`. -/
theorem three_le_index {L : Subgroup G} [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis L) :
    3 ≤ ((hyp.typeI.typeF.H).subgroupOf L).index := by
  -- `[L : H] = |U|` via the complement `H ⋊ U = L`.
  have hUle : hyp.typeI.typeF.U ≤ L := hyp.typeI.typeF.U_le
  have hidx_eq : ((hyp.typeI.typeF.H).subgroupOf L).index = Nat.card ↥(hyp.typeI.typeF.U) := by
    rw [hyp.typeI.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv]
  -- `|U| > 1` (nontrivial) and `|U|` odd (divides `|G|` odd), so `|U| ≥ 3`.
  haveI : Nontrivial ↥(hyp.typeI.typeF.U) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.U_nontrivial
  have hgt1 : 1 < ((hyp.typeI.typeF.H).subgroupOf L).index := by
    rw [hidx_eq]; exact Finite.one_lt_card
  have hodd : Odd ((hyp.typeI.typeF.H).subgroupOf L).index := by
    have hdvd : ((hyp.typeI.typeF.H).subgroupOf L).index ∣ Nat.card G :=
      (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L)
    rcases Nat.even_or_odd ((hyp.typeI.typeF.H).subgroupOf L).index with hev | ho
    · exfalso
      obtain ⟨d, hd⟩ := hG.odd
      obtain ⟨m, hm⟩ := hev.two_dvd.trans hdvd
      omega
    · exact ho
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Peterfalvi (12.11)/(12.16), the index bound `|M| ≤ |K|·|H|`** (`H = L_F`): from the (12.11)
complement structure (`M ∩ L` complements `K` in `M`, and `M ∩ L ≤ L_F`), the order of `M`
factors as `|M| = |K|·|M ∩ L| ≤ |K|·|L_F|`.  This discharges the `hM` field of
`CounterexampleDadeData` (cites the (12.11) `intersection_complement_structure`). -/
theorem card_M_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nat.card ↥ctr.M ≤ Nat.card ↥ctr.K * Nat.card ↥(maxNilpotentNormalHall data.L) := by
  obtain ⟨hcompl, hsub⟩ := intersection_complement_structure hG data
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `|M| = |K| · |M ∩ L|` from the complement `K ⋊ (M ∩ L) = M`.
  have h1 : Nat.card ↥(ctr.K.subgroupOf ctr.M) * (ctr.K.subgroupOf ctr.M).index = Nat.card ↥ctr.M :=
    Subgroup.card_mul_index _
  have h2 : (ctr.K.subgroupOf ctr.M).index = Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) :=
    hcompl.symm.index_eq_card
  have h3 : Nat.card ↥(ctr.K.subgroupOf ctr.M) = Nat.card ↥ctr.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have h4 : Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) = Nat.card ↥(ctr.M ⊓ data.L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hMeq : Nat.card ↥ctr.M = Nat.card ↥ctr.K * Nat.card ↥(ctr.M ⊓ data.L) := by
    rw [← h3, ← h4, ← h2, h1]
  -- `|M ∩ L| ≤ |L_F|` since `M ∩ L ≤ L_F`.
  have hle : Nat.card ↥(ctr.M ⊓ data.L) ≤ Nat.card ↥(maxNilpotentNormalHall data.L) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hsub)
  rw [hMeq]
  exact Nat.mul_le_mul_left _ hle

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13) for the witness subgroup `L`**: the second maximal `L` of (12.9) carries a
full (12.13) `DadeNotation` — the realized `ψ = χ^{τ₁}` of the (12.16) Dade calculation.

Assembles the foundation chain: `witness_L_coherent` supplies the (12.6) coherent extension of `L`'s
family `S`, `exists_distinguished_char` selects the distinguished `χ ∈ S` of degree `[L:H]`, and
`dadeNotation_of_coherence` realizes the (12.13) notation with `τ₁ = ` the coherent extension and
`ψ = χ^{τ₁}`.  This is the `ψ`-data of `CounterexampleDadeData`; what remains for the (12.16)
contradiction is the value/norm content — (12.14)/(12.15) for `h_const`/`h_psig_int`, the (12.12)
degree bounds, and the `ρ`/`ρM` norm bounds `hA`/`hB`/`hC`. -/
theorem exists_witness_dadeNotation [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ dade : DadeNotation hyp, dade.psi ∈ ZIrr G := by
  obtain ⟨hyp, ⟨coh⟩⟩ := witness_L_coherent hG data
  obtain ⟨χ, hχ, hdeg⟩ := exists_distinguished_char hyp
  refine ⟨hyp, dadeNotation_of_coherence hyp coh χ hχ
    ((hyp.typeI.typeF.H).subgroupOf data.L).index hdeg, ?_⟩
  -- `dade.psi = coh.extension χ` and `χ ∈ S ⊆ ℤ[S]`, so the coherent extension lands in `ℤ[Irr G]`.
  exact coh.extension_mem_ZIrr χ (Submodule.subset_span hχ)

/-- **Peterfalvi (12.14)**: the character `psi` is constant on the coset `xK`. -/
theorem psi_constant_on_xK [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (hyp : Hypothesis L) (witness : RankTwoWitnessData ctr)
    (dade : DadeNotation hyp) :
    ∀ g : G, g ∈ ctr.K → dade.psi (witness.x * g) = dade.psi witness.x := by
  sorry

/-- **Peterfalvi (12.15)**: the rho image is unchanged on `K#`, constant on
`K - K'`, and has integer values there. -/
theorem rhoM_integer_values [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    {hyp : Hypothesis L} (dade : DadeNotation hyp) :
    dade.rhoMFormula ∧
      (∀ g : G, g ∈ ctr.K → g ∉ ctr.Kprime → ∃ z : ℤ, dade.psi g = (z : ℂ)) := by
  sorry

/-- **Peterfalvi (12.16), the (1.10) congruence core**: the cyclotomic-congruence chain of the
(12.16) contradiction.  Given the minimal-counterexample data — a virtual character `ψ ∈ ℤ[Irr G]`,
an order-`p` element `x` and a commuting `g` — together with the facts supplied by the surrounding
§12 machinery (`ψ` constant on the coset, `ψ(xg) = ψ(x)`, by (12.14); `ψ(x) ≡ e (mod 1-ε)`, from the
Dade value relation and (1.10.a) applied to `χ`; and `ψ(g) = mval ∈ ℤ`, by (12.15)), Peterfalvi
(1.10.a) (`exists_integral_apply_sub_of_commute`) and (1.10.b) (`int_dvd_of_one_sub_primRoot_dvd`)
yield `ψ(g) ≡ e (mod p)`, i.e. `p ∣ (mval - e)`.

This isolates the `(1.10)`-using arithmetic of (12.16) (now fully discharged); the remaining
contradiction is the norm/degree inequality (`2e ≤ p+1` of (12.12) together with (12.15)). -/
theorem psi_int_congr_e_mod_p [Finite G] {p : ℕ} (hp : p.Prime) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G}
    (hx : x ^ p = 1) (hxg : Commute x g) {e mval : ℤ}
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ)) :
    (p : ℤ) ∣ (mval - e) := by
  obtain ⟨z, hz, hzeq⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hp.pos hε hψ hx hxg
  obtain ⟨w, hw, hweq⟩ := h_psix
  apply OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hp hε (hw.sub hz)
  have h1 : ψ x - ψ g = (1 - ε) * z := by rw [← h_const]; exact hzeq
  rw [h_psig_int] at h1
  push_cast
  linear_combination hweq - h1

/-- **Peterfalvi (12.16), the magnitude step**: an integer `mval ≡ e (mod p)` with `1 ≤ e` and
`2e ≤ p+1` (the degree bound (12.12)) satisfies `|mval| ≥ e - 1`.  Indeed the integers `≡ e (mod p)`
nearest `0` are `e` (distance `e`) and `e - p` (distance `p - e ≥ e - 1`, by `2e ≤ p+1`), so every
such value has `|·| ≥ min(e, p-e) ≥ e - 1`. -/
theorem abs_ge_e_sub_one {p : ℕ} (hppos : 0 < p) {e mval : ℤ} (he : 1 ≤ e)
    (h2e : 2 * e ≤ (p : ℤ) + 1) (hdvd : (p : ℤ) ∣ (mval - e)) :
    e - 1 ≤ |mval| := by
  obtain ⟨k, hk⟩ := hdvd
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hppos
  by_cases hk' : 0 ≤ k
  · have hpk : 0 ≤ (p : ℤ) * k := mul_nonneg hpZ.le hk'
    rw [abs_of_nonneg (by omega)]; omega
  · have hk1 : k ≤ -1 := by omega
    have hpk : (p : ℤ) * k ≤ -(p : ℤ) := by nlinarith [mul_le_mul_of_nonneg_left hk1 hpZ.le]
    rw [abs_of_nonpos (by omega)]; omega

/-- **Peterfalvi (12.16), the value-magnitude conclusion**: chaining the `(1.10)` congruence core
(`psi_int_congr_e_mod_p`) with the degree bound `2e ≤ p+1` of (12.12) gives `|ψ(g)| ≥ e - 1` — the
lower bound on `|ψ(g)|` feeding the final norm inequality of (12.16). -/
theorem abs_psi_g_ge_e_sub_one [Finite G] {p : ℕ} (hp : p.Prime) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G}
    (hx : x ^ p = 1) (hxg : Commute x g) {e mval : ℤ} (he : 1 ≤ e)
    (h2e : 2 * e ≤ (p : ℤ) + 1)
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ)) :
    e - 1 ≤ |mval| :=
  abs_ge_e_sub_one hp.pos he h2e
    (psi_int_congr_e_mod_p hp hε hψ hx hxg h_const h_psix h_psig_int)

/-- **Peterfalvi (12.16), the index/degree contradiction** (the heart of the final inequality): the
reduced inequality `(|K| - |K'|)(e-1)² < e·|K|` together with `4·|K'| ≤ |K|` (i.e. `[K:K'] ≥ 4`,
forced by the fixed-point-free order-`p` action of (8.1.c)) and `e ≥ 3` is contradictory.  Indeed
`|K| - |K'| ≥ (3/4)|K|`, so `(3/4)(e-1)² < e`, i.e. `3(e-1)² < 4e`, i.e. `(3e-1)(e-3) < 0` — false
for `e ≥ 3`.  This is the `e/(e-1)² ≤ 3/4 < 1 - |K'|/|K|` step of (12.16). -/
theorem index_ratio_contradiction {e kK kKp : ℝ} (he : 3 ≤ e) (hkKp : 0 < kKp)
    (hidx : 4 * kKp ≤ kK) (hineq : (kK - kKp) * (e - 1) ^ 2 < e * kK) : False := by
  have hkK : 0 < kK := by linarith
  nlinarith [hineq, mul_nonneg (show (0:ℝ) ≤ kK / 4 - kKp by linarith) (sq_nonneg (e - 1)),
    mul_nonneg hkK.le (mul_nonneg (show (0:ℝ) ≤ e - 3 by linarith)
      (show (0:ℝ) ≤ 3 * e - 1 by linarith))]

/-- **Peterfalvi (12.16), the (12.11) reduction**: the final norm inequality
`((|K|-|K'|)/|M|)(e-1)² + 1 - e/|H| < 1` together with `|M| ≤ |K|·|H|` of (12.11) reduces to
`(|K|-|K'|)(e-1)² < e·|K|` (clear `|M|`, `|H|`, then bound `|M|` above). -/
theorem norm_ineq_reduce {e kK kKp kM kH : ℝ} (hkM : 0 < kM) (hkH : 0 < kH)
    (he1 : 0 ≤ e) (hM : kM ≤ kK * kH)
    (hnorm : ((kK - kKp) / kM) * (e - 1) ^ 2 + 1 - e / kH < 1) :
    (kK - kKp) * (e - 1) ^ 2 < e * kK := by
  have h1 : (kK - kKp) * (e - 1) ^ 2 / kM < e / kH := by
    have e1 : (kK - kKp) * (e - 1) ^ 2 / kM = ((kK - kKp) / kM) * (e - 1) ^ 2 := by ring
    rw [e1]; linarith [hnorm]
  rw [div_lt_div_iff₀ hkM hkH] at h1
  have h2 : e * kM ≤ e * (kK * kH) := mul_le_mul_of_nonneg_left hM he1
  have h3 : (kK - kKp) * (e - 1) ^ 2 * kH < e * kK * kH := by nlinarith [h1, h2]
  exact lt_of_mul_lt_mul_right h3 hkH.le

/-- **Peterfalvi (12.16), the closing contradiction** (norm-inequality endgame): given the final
norm bound `((|K|-|K'|)/|M|)(e-1)² + 1 - e/|H| < 1` (from (7.3)/(7.8.b)/(8.17) with `|ψ(g)| ≥ e-1`),
the index bound `|M| ≤ |K|·|H|` of (12.11), the degree bound `e ≥ 3`, and the fixed-point-free
`[K:K'] ≥ 4` of (8.1.c), the minimal counterexample is impossible.  Combines `norm_ineq_reduce`
with `index_ratio_contradiction`. -/
theorem counterexample_closing {e kK kKp kM kH : ℝ} (he : 3 ≤ e) (hkKp : 0 < kKp)
    (hkM : 0 < kM) (hkH : 0 < kH) (hidx : 4 * kKp ≤ kK) (hM : kM ≤ kK * kH)
    (hnorm : ((kK - kKp) / kM) * (e - 1) ^ 2 + 1 - e / kH < 1) : False :=
  index_ratio_contradiction he hkKp hidx (norm_ineq_reduce hkM hkH (by linarith) hM hnorm)

/-- **Peterfalvi (12.16), the middle (norm-bound) glue**: from `|ψ(g)| ≥ e-1` and the three §7/§8
norm bounds — `A`: `‖ψ^{ρM}‖² ≥ (|K-K'|/|M|)|ψ(g)|²` (from (12.15)), `B`: `‖ψ^ρ‖² ≥ 1 - e/|H|`
((7.8.b)), `C`: `‖ψ^{ρM}‖² + ‖ψ^ρ‖² < 1` ((7.3) with (8.17)) — the norm conclusion
`(|K-K'|/|M|)(e-1)² + 1 - e/|H| < 1` follows (`|ψ(g)|² = mval² ≥ (e-1)²`, then linear). -/
theorem norm_conclusion_glue {e mval : ℤ} {kK kKp kM kH normRhoM normRho : ℝ}
    (he : 3 ≤ e) (hkKp : 0 < kKp) (hkM : 0 < kM) (hidx : 4 * kKp ≤ kK)
    (hmag : (e : ℝ) - 1 ≤ |(mval : ℝ)|)
    (hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM)
    (hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho)
    (hC : normRhoM + normRho < 1) :
    (kK - kKp) / kM * ((e : ℝ) - 1) ^ 2 + 1 - (e : ℝ) / kH < 1 := by
  have hsq : ((e : ℝ) - 1) ^ 2 ≤ (mval : ℝ) ^ 2 := by
    have heR : (3 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    nlinarith [hmag, sq_abs (mval : ℝ), abs_nonneg (mval : ℝ)]
  have hpos : 0 ≤ (kK - kKp) / kM := div_nonneg (by linarith) hkM.le
  have hA' : (kK - kKp) / kM * ((e : ℝ) - 1) ^ 2 ≤ normRhoM :=
    le_trans (mul_le_mul_of_nonneg_left hsq hpos) hA
  linarith [hA', hB, hC]

/-- **Peterfalvi (12.16), the full assembly** (the entire argument, parameterized on its gated
upstream): the minimal counterexample is impossible.  Combines the `(1.10)` congruence/magnitude
start (`abs_psi_g_ge_e_sub_one`: `|ψ(g)| ≥ e-1`), the §7/§8 norm-bound middle (`norm_conclusion_glue`
from the three bounds `hA`/`hB`/`hC`), and the index/degree endgame (`counterexample_closing`).

Every hypothesis is a fact supplied by §7/§8/§12: `h_const` = (12.14), `h_psix` = Dade value relation
with (1.10.a) on `χ`, `h_psig_int` = (12.15), `h2e` = (12.12); `hA` = (12.15)+`|ψ(g)|`, `hB` = (7.8.b),
`hC` = (7.3)+(8.17); `hM` = (12.11), `hidx` = fpf `[K:K'] ≥ 4` of (8.1.c).  The remaining work to close
`counterexample_contradiction` is exactly the construction of these — the §7 `ρ`/`ρM` machinery. -/
theorem counterexample_contradiction_of_facts [Finite G]
    {p : ℕ} (hp : p.Prime) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G} (hx : x ^ p = 1) (hxg : Commute x g)
    {e mval : ℤ} (he : 3 ≤ e) (h2e : 2 * e ≤ (p : ℤ) + 1)
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ))
    {kK kKp kM kH normRhoM normRho : ℝ}
    (hkKp : 0 < kKp) (hkM : 0 < kM) (hkH : 0 < kH)
    (hidx : 4 * kKp ≤ kK) (hM : kM ≤ kK * kH)
    (hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM)
    (hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho)
    (hC : normRhoM + normRho < 1) :
    False := by
  have hmagZ : (e - 1 : ℤ) ≤ |mval| :=
    abs_psi_g_ge_e_sub_one hp hε hψ hx hxg (by linarith) h2e h_const h_psix h_psig_int
  have hmag : (e : ℝ) - 1 ≤ |(mval : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hmagZ
  have heR : (3 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  exact counterexample_closing heR hkKp hkM hkH hidx hM
    (norm_conclusion_glue he hkKp hkM hidx hmag hA hB hC)

/-- **Peterfalvi (12.12) → (12.16) numerical bridge**: the (12.12) conclusion `e ∣ p+1` together
with `e` odd (odd order) gives the bound `2e ≤ p+1` cited by (12.16).  Since `p` is odd, `2 ∣ p+1`;
as `gcd(2,e)=1`, `2e ∣ p+1`, hence `2e ≤ p+1`.  (`e ≤ (p+1)/2` in the textbook.) -/
theorem two_mul_le_succ_of_odd_dvd {e p : ℕ} (hp : Odd p) (he : Odd e)
    (hdvd : e ∣ (p + 1)) : 2 * e ≤ p + 1 :=
  Nat.le_of_dvd (by omega) (he.coprime_two_left.mul_dvd_of_dvd_of_dvd (hp.add_one).two_dvd hdvd)

/-- **Peterfalvi (8.1.c) → (12.16) numerical bridge**: a fixed-point-free order-`p` action on
`K/K'` forces `p ∣ ([K:K'] - 1)`; with `[K:K'] > 1` and `p ≥ 3` this gives `[K:K'] ≥ 4`, the index
bound contradicting `[K:K'] < 4` in the (12.16) endgame. -/
theorem four_le_of_dvd_sub_one {p n : ℕ} (hp : 3 ≤ p) (hn : 1 < n) (hdvd : p ∣ (n - 1)) :
    4 ≤ n := by
  have : p ≤ n - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **Peterfalvi (12.9), the centralizer witness extraction**: the rank-two witness datum records
`¬(C_G(x) ⊓ K ≤ K')`, which directly yields an element `g ∈ C_K(x)` with `g ∉ K'` — the `g`
commuting with `x` used throughout the (12.16) argument.  (Pure `SetLike` extraction, ungated.) -/
theorem exists_witness_g {ctr : CounterexampleHypothesis (G := G)}
    (witness : RankTwoWitnessData ctr) :
    ∃ g : G, Commute witness.x g ∧ g ∈ ctr.K ∧ g ∉ ctr.Kprime := by
  obtain ⟨g, hgA, hgB⟩ := SetLike.not_le_iff_exists.mp witness.CKx_not_le_Kprime
  rw [Subgroup.mem_inf] at hgA
  exact ⟨g, Subgroup.mem_centralizer_iff.mp hgA.1 witness.x (Set.mem_singleton _), hgA.2, hgB⟩

/-- **Peterfalvi (12.13)–(12.16), the character/norm contract** packaging every fact that the
numerical endgame `counterexample_contradiction_of_facts` consumes.  Bundling them here isolates the
deep §7/§12 content — the Dade calculation `ψ = χ^{τ₁}` of (12.13), the coset/value facts
(12.14)/(12.15), and the `ρ`/`ρM` integral inequalities (7.3)/(7.8.b) — into a single
faithfully-typed obligation, leaving the (12.16) capstone `counterexample_contradiction` a
`sorry`-free assembly.

Field map to the textbook (`H = L_F`, the Fitting kernel of the witness subgroup `L`):
* `ε`/`hε` — a primitive `p`-th root of unity (the cyclotomic base of (1.10));
* `ψ`/`hψ` — the virtual character `ψ = χ^{τ₁}` of (12.13) (`ZIrr` membership = it is a
  ℤ-combination of irreducibles, from the Dade isometry image);
* `e` — the common degree `χ(1) = e` of the coherent family `S` ((12.6)); `he`/`h2e` = (12.12);
* `h_const` = (12.14) (`ψ` constant on the coset `xK`); `h_psix` = (1.10.a) applied to `χ`;
  `h_psig_int` = (12.15) (`ψ(g) ∈ ℤ`);
* `kK`/`kKp`/`kM`/`kH` = `|K|`/`|K'|`/`|M|`/`|H|`; `hidx` = (8.1.c), `hM` = (12.11);
* `hA` = (12.15) norm relation for `ρM`, `hB` = (7.8.b) for `ρ`, `hC` = (7.3)+(8.17). -/
structure CounterexampleDadeData {ctr : CounterexampleHypothesis (G := G)}
    (witness : RankTwoWitnessData ctr) (g : G) where
  ε : ℂ
  hε : IsPrimitiveRoot ε ctr.p
  ψ : ClassFunction G ℂ
  hψ : ψ ∈ ZIrr G
  e : ℤ
  mval : ℤ
  he : 3 ≤ e
  h2e : 2 * e ≤ (ctr.p : ℤ) + 1
  h_const : ψ (witness.x * g) = ψ witness.x
  h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ witness.x - (e : ℂ) = (1 - ε) * w
  h_psig_int : ψ g = (mval : ℂ)
  kK : ℝ
  kKp : ℝ
  kM : ℝ
  kH : ℝ
  normRhoM : ℝ
  normRho : ℝ
  hkKp : 0 < kKp
  hkM : 0 < kM
  hkH : 0 < kH
  hidx : 4 * kKp ≤ kK
  hM : kM ≤ kK * kH
  hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM
  hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho
  hC : normRhoM + normRho < 1

/-- **Peterfalvi (12.13)–(12.15) + (7.3)/(7.8.b)**, the construction of the character/norm contract
of (12.16).  Given the rank-two witness of (12.9) and a commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`), the §7/§12 machinery produces the Dade calculation `ψ = χ^{τ₁}` and its
associated `ρ`/`ρM` norm bounds.

This is the remaining deep obligation of (12.16): build a `Hypothesis L` for the witness subgroup
`L` (type I by (12.10) `witness_L_frobenius`), the Dade isometry `τ₁` and coherent family `S`
((12.6)), the `DadeNotation` of (12.13), then discharge each field via the existing §12 theorems —
`psi_constant_on_xK` (12.14), `rhoM_integer_values` (12.15), `intersection_complement_structure`
(12.11) — and the §7 `chiRho` norm estimates (`S09.NormEstimates`, `chiRho_integral_inequality`).
Bottoms out on (12.6)/(12.10)/(12.11) (cited via signature contract). -/
theorem exists_counterexample_dade_data [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (ctr : CounterexampleHypothesis (G := G))
    (witness : RankTwoWitnessData ctr) {g : G}
    (_hg_comm : Commute witness.x g) (_hgK : g ∈ ctr.K) (_hgK' : g ∉ ctr.Kprime) :
    Nonempty (CounterexampleDadeData witness g) :=
  sorry

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible.

The rank-two witness of (12.9) (`exists_rankTwoWitness`) and the commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`) are extracted unconditionally; the deep §7/§12 character calculation is bundled
into `exists_counterexample_dade_data`; the contradiction then follows from the numerical endgame
`counterexample_contradiction_of_facts`. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  obtain ⟨_, _, ⟨witness⟩⟩ := exists_rankTwoWitness hG ctr
  obtain ⟨g, hg_comm, hgK, hgK'⟩ := exists_witness_g witness
  obtain ⟨d⟩ := exists_counterexample_dade_data hG ctr witness hg_comm hgK hgK'
  exact counterexample_contradiction_of_facts ctr.p_prime d.hε d.hψ witness.x_mem_omega1 hg_comm
    d.he d.h2e d.h_const d.h_psix d.h_psig_int d.hkKp d.hkM d.hkH d.hidx d.hM d.hA d.hB d.hC

/-- **Peterfalvi (12.7), `π = ∅`** (the headline consequence of (12.16)): no prime lies in the
set `π` of (12.8).  Were `π` nonempty, (12.8) (`exists_counterexampleHypothesis`) would build a
minimal counterexample, contradicting (12.16) (`counterexample_contradiction`). -/
theorem pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q := by
  by_contra h
  push_neg at h
  obtain ⟨ctr⟩ := exists_counterexampleHypothesis hG h
  exact counterexample_contradiction hG ctr

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with kernel `M_F`.

Since `π = ∅` by (12.16) (`pi_empty`), the easy direction `typeI_frobenius_of_pi_empty` applies
and gives the Frobenius decomposition with kernel `M_F = typeF.H` and complement `typeF.U`.  (The
`kernel_eq_MF` carrier is vacuous here: the `frobenius` field already names `typeF.H = M_F` as the
kernel, so the identification holds definitionally.) -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  obtain ⟨data⟩ := hType
  exact ⟨{ typeI := data
           complement := data.typeF.U.subgroupOf M
           kernel_eq_MF := True
           kernel_eq_MF_holds := trivial
           frobenius := typeI_frobenius_of_pi_empty hG (pi_empty hG) hM data }, trivial⟩

/-- **The type-I Dade support is `H#`** (Peterfalvi (8.3)/(12.1) for the witness subgroup `L`).
`typeIA L = centralizerSupport (H#) L` collapses to `H# = (H : Set G) \ {1}` (`H = L_F`): the
Frobenius structure of `L` (from (12.7) `typeI_frobenius`) makes the centralizer condition vacuous
on `H#` (`IsFrobeniusGroup.centralizer_kernel_le`).  This supplies the `A = H#` shape that
`S09.Cert.hypothesis78OfDade` needs (the `hAH` argument of the §12→§7 Dade bridge).

Re-derives the `centralizerSupport = sharp` argument of
`S16.centralizerSupport_sharpSubgroup_eq_of_frobenius` — which lives downstream of `S14` and so
cannot be cited here; a hub dedup hoisting that pure-group-theory fact to a shared file (e.g.
`MaximalSubgroupType`) is tracked in issue 1013. -/
theorem Hypothesis.typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  obtain ⟨fdata, _⟩ := typeI_frobenius hG hyp.maximal ⟨hyp.typeI⟩
  have hKf : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ fdata.frobenius)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8)/(12.16), the witness `Hypothesis78`**: the second maximal subgroup `L` of
(12.9) carries the full §7 (7.8) structure — the `ρ`-machinery `Hypothesis71`, the distinguished
induced family `{ζ_i = Ind θ_i}`, the coherent extension `ν`, and the (7.8.a) coherence agreement.

Assembles `hypothesis78OfDade` from three genuine ingredients for the witness `L`:
* the (12.6) coherence `witness_L_coherent` supplies the extension `ν = coh.extension`, whose
  `IsCoherent.extension_inner_eq`/`extends_on_supported` give the `nu_isometry` (via
  `coherence_extension_inner_eq_on_family`) and the (7.8.a) agreement (via
  `coherence_hagree_dadeMap`);
* the placed family `exists_witness_placed_family` supplies the `Fin (n+1)`-indexed `θ` with the
  distinguished character at index `0` (`Ind (θ 0)(1) = [L:H] = e`) and the trivial character `1_H`
  at `ind1H ≠ 0`, injective and covering;
* the (12.1) support `A(L) = H#` (`typeIA_eq_sharp`) and the degree coefficients `d_i = θ_i(1)`
  (`induce_apply_one`), with the difference support `ψ_i = ζ_i − d_i ζ_0 ⊆ H#` from
  `induce_diff_support`.

This is the (7.8) hypothesis to which Peterfalvi's (7.8.b) norm bound `hB` of
`CounterexampleDadeData` applies (via `zetaNuRhoNormSqGeOfDade`). -/
theorem witness_L_hypothesis78 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      Nonempty (OddOrder.Peterfalvi.S09.Hypothesis78 G (typeIA data.L hyp.typeI) data.L) := by
  classical
  obtain ⟨hyp, ⟨coh⟩⟩ := witness_L_coherent hG data
  refine ⟨hyp, ?_⟩
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- (12.1): the type-I support `A(L)` is `H#`.
  have hAH : typeIA data.L hyp.typeI = (hyp.typeI.typeF.H : Set G) \ {1} :=
    Hypothesis.typeIA_eq_sharp hG hyp
  -- `H = L_F` is `L`-conjugation invariant (from the `subgroupOf`-normality).
  have hHnorm : ∀ (l : ↥data.L) {h : G}, h ∈ hyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ hyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ data.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥data.L) ∈ (hyp.typeI.typeF.H).subgroupOf data.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- The placed induced family for `L`.
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ := exists_witness_placed_family hyp
  -- Every non-trivial member `Ind θ_i` (`i ≠ ind1H`) lies in the coherent family `S`.
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        ∈ hyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  -- Degree coefficients `d_i = θ_i(1)`.
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L)) := fun _ => rfl
  -- `ζ_i(1) = d_i · ζ_0(1)`.
  have hdeg : ∀ i, ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥data.L)
      = d i * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  -- `ζ_0(1) = ζ_{ind1H}(1)` (both `[L:H]`).
  have hdeg_match : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L)
      = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥data.L) := by
    rw [hdeg0, htriv]
    change (((hyp.typeI.typeF.H).subgroupOf data.L).index : ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L)) (1 : ↥data.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  -- `ψ_i = ζ_i − d_i ζ_0` is supported on `A(L) = H#`.
  have psi_support : ∀ i, (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA data.L hyp.typeI) data.L := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hx.1, hx.2⟩
  -- Assemble the `Hypothesis78` via `hypothesis78OfDade`.
  refine ⟨hypothesis78OfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension ?_ ?_⟩
  · -- `nu_isometry`: the coherent extension is isometric on the family members.
    intro i j hi hj
    exact coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  · -- `hagree`: the (7.8.a) coherence agreement `τ ψ_i = ν ζ_i − d_i ν ζ_0`.
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)

open scoped Classical in
/-- **Odd-order Frobenius: a nontrivial induced irreducible is orthogonal to its complex
conjugate.**  In a Frobenius group `Γ` of odd order with kernel `H`, for `θ ∈ Irr H`, `θ ≠ 1`,
the induced `Ind_H^Γ θ` is irreducible (`isIrreducibleCharacter_induce_of_frobeniusGroup`) and
nontrivial (`⟨Ind θ, 1_Γ⟩ = ⟨θ, 1_H⟩ = 0 ≠ 1`), hence — `Γ` odd — **not real**
(`not_isReal_of_ne_trivial_of_odd_card'`): `(Ind θ)‾ = Ind θ̄ ≠ Ind θ`.  Distinct irreducibles are
orthogonal, so `⟨Ind θ, Ind θ̄⟩ = 0`.  This is the `⟨ζ_0, ζ̄_0⟩ = 0` input for the §7 (7.8.a)
`⊥ 1_G` argument (`witness_L_hzeta0nu`).  Stated with **explicit** `Fintype`/`Invertible` binders
(not the `FiniteInduce` scope) so the `induce`/`inner` coercions stay `whnf`-cheap. -/
theorem inner_induce_conj_eq_zero_of_frobenius_of_odd {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [H.Normal] [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] (hodd : Odd (Nat.card Γ)) {W : Subgroup Γ}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup Γ H W)
    (θ : IrreducibleCharacter ↥H) (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (ClassFunction.induce H ((θ : ClassFunction ↥H ℂ).conj)) = 0 := by
  -- `θ̄` is again a nontrivial irreducible character of `H`.
  have hθbar_ne : (⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩ :
      IrreducibleCharacter ↥H) ≠ trivialIrreducibleCharacter ↥H := by
    intro h
    apply hθ
    have hcoe : (θ : ClassFunction ↥H ℂ).conj = trivialClassFunction ↥H := by
      have h2 := congrArg (fun c : IrreducibleCharacter ↥H => (c : ClassFunction ↥H ℂ)) h
      simpa using h2
    apply Subtype.ext
    show (θ : ClassFunction ↥H ℂ) = trivialClassFunction ↥H
    rw [← ClassFunction.conj_conj (θ : ClassFunction ↥H ℂ), hcoe]
    exact trivialClassFunction_isReal
  have hirr := isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ
  have hirr' := isIrreducibleCharacter_induce_of_frobeniusGroup hF
    (⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥H) hθbar_ne
  -- `Ind θ` is nontrivial: `⟨Ind θ, 1_Γ⟩ = ⟨θ, 1_H⟩ = 0`, but `⟨1_Γ, 1_Γ⟩ = 1`.
  have hne_triv : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ :
      IrreducibleCharacter Γ) ≠ trivialIrreducibleCharacter Γ := by
    intro h
    have hrestrict : ClassFunction.restrict H
          (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ)
        = (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ) := by
      ext x
      simp [ClassFunction.restrict_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg hθ]
    have hcf : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
        = (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) h
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  -- Odd order ⟹ `Ind θ` not real ⟹ `(Ind θ)‾ ≠ Ind θ`.
  have hnotreal := not_isReal_of_ne_trivial_of_odd_card' hodd hne_triv
  have hconj_eq : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      = ClassFunction.induce H ((θ : ClassFunction ↥H ℂ).conj) :=
    ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)
  have hne : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      ≠ ClassFunction.induce H ((θ : ClassFunction ↥H ℂ).conj) :=
    fun heq => hnotreal (hconj_eq.trans heq.symm)
  -- Distinct irreducibles are orthogonal.
  have hii := irreducibleCharacter_inner_eq_ite
    (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ : IrreducibleCharacter Γ)
    ⟨ClassFunction.induce H ((θ : ClassFunction ↥H ℂ).conj), hirr'⟩
  rwa [if_neg (fun h => hne (congrArg (fun c : IrreducibleCharacter Γ =>
    (c : ClassFunction Γ ℂ)) h))] at hii

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8.a) for the witness `L`: `⟨ζ_0^ν, 1_G⟩ = 0`** (`hzeta0nu`, the last input to
the (7.8.b) bound `hB`).  The abstract `IsCoherent` does not carry orthogonality to `1_G`, but it
is recovered from the **complex conjugate** `ζ̄_0 = Ind θ̄_0 ∈ S` (`Sset_closedUnderConjugate`) — a
second member of the *same degree*, distinct from `ζ_0` because `L` has odd order (no nontrivial
real irreducible, `not_isReal_of_ne_trivial_of_odd_card'`).  `coherence_extension_orthogonal_constOne`
then forces `⟨ν ζ_0, 1_G⟩ = 0`.  Holds for **any** nontrivial `θ_0` (degree-`e`/linearity unused). -/
theorem witness_L_hzeta0nu [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (θ0 : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
    (hθ0 : θ0 ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
    ClassFunction.inner
        (coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0 := by
  classical
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  -- The complex conjugate character `θ̄_0` is again nontrivial irreducible.  Introduce it
  -- **opaquely** (via `obtain`, not `let`), carrying only its coercion `↑θ̄_0 = (↑θ_0)‾`: a `let`
  -- gets its coercion re-unfolded inside every `induce` coset sum, blowing the `whnf` budget.
  obtain ⟨θ0', hθ0'coe⟩ :
      ∃ t : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
        (t : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
          = (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj :=
    ⟨⟨(θ0 : ClassFunction _ ℂ).conj, θ0.isIrreducible.conj⟩, rfl⟩
  have hθ0' : θ0' ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    intro h
    apply hθ0
    have hcoe : (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      rw [← hθ0'coe]
      have h2 := congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
      simpa using h2
    apply Subtype.ext
    show (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  -- The two members `ζ_0 = Ind θ_0`, `ζ̄_0 = Ind θ̄_0 ∈ S`.
  have hmem0 : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ0 : ClassFunction _ ℂ) ∈ hyp.Sset := ⟨θ0, hθ0, rfl⟩
  have hmem0' : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ0' : ClassFunction _ ℂ) ∈ hyp.Sset := ⟨θ0', hθ0', rfl⟩
  -- Norms `= 1` (Frobenius), orthogonality to `1_L`, irreducibility.
  have hnorm0 := inner_self_induce_eq_one_of_frobeniusGroup hfrob θ0 hθ0
  have hnorm0' := inner_self_induce_eq_one_of_frobeniusGroup hfrob θ0' hθ0'
  have h1_0 := inner_induce_constOne_eq_zero ((hyp.typeI.typeF.H).subgroupOf L) θ0 hθ0
  have h1_0' := inner_induce_constOne_eq_zero ((hyp.typeI.typeF.H).subgroupOf L) θ0' hθ0'
  -- `⟨ζ_0, ζ̄_0⟩ = 0` (odd-order Frobenius: `ζ_0` non-real), from the reusable general helper
  -- (`hθ0'coe : ↑θ̄_0 = (↑θ_0)‾` reindexes it to `θ_0'`).
  have horth : ClassFunction.inner
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0 : ClassFunction _ ℂ))
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)) = 0 := by
    rw [hθ0'coe]
    exact inner_induce_conj_eq_zero_of_frobenius_of_odd hodd hfrob θ0 hθ0
  -- The equal-degree difference is `A(L) = H#`-supported.
  have hAH : typeIA L hyp.typeI = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    Hypothesis.typeIA_eq_sharp hG hyp
  have hdeg' : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)
        (1 : ↥L)
      = 1 * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0 : ClassFunction _ ℂ)
        (1 : ↥L) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨n, -, hn⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ0
    rw [hn, star_natCast]
  have hsupp : (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)
      - ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ0 : ClassFunction _ ℂ)).support ⊆ hyp.A := by
    have hds := induce_diff_support (K := (hyp.typeI.typeF.H).subgroupOf L) θ0' θ0 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hxd.1, hxd.2⟩
  -- The Dade `⊥ 1_G` transport and `ℂ`-linearity of `τ = hyp.tau`.
  have htau1 : ∀ φ : ClassFunction ↥L ℂ, φ.support ⊆ hyp.A →
      ClassFunction.inner (hyp.tau φ) (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne L) := by
    intro φ hφ
    rw [show hyp.tau φ = hyp.dadeData.dade.dadeMap
        ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ]
    exact inner_tau_supported_constOne hyp.toHypothesis71
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥L ℂ), hyp.tau (c • x) = c • hyp.tau x :=
    dadeIntegralCharacterMap_smul_complex hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
  exact coherence_extension_orthogonal_constOne coh hτ_smul htau1 hmem0 hmem0'
    hnorm0 hnorm0' horth hsupp h1_0 h1_0'

/-- **Peterfalvi (7.8.b)/(12.12) size condition for an odd-order Frobenius group**: if a finite
Frobenius group has kernel `N` and complement `A` both of **odd** order, with `N ≠ ⊥`, then
`2|A| + 1 ≤ |N|` (equivalently `e ≤ (h-1)/2`, the `smallIndex` hypothesis of the §7 `(7.8.b)` norm
bound).  The complement `A` acts freely on `N#`, so `|A| ∣ |N| - 1` (`card_kernel_modEq_one`,
Isaacs 6.1); as `|N|` is odd, `|N| - 1` is even, and an odd divisor of an even number is at most
half of it, so `|N| - 1 ≥ 2|A|`.  This is the `2e_i + 1 ≤ h_i` shape consumed by
`localSmallIndex_of_family_cardinalities` for the witness `L` of (12.16).  (General Frobenius fact,
hoistable to `Ch06`.) -/
theorem frobenius_two_mul_card_complement_add_one_le_card_kernel {Γ : Type*} [Group Γ] [Finite Γ]
    {N A : Subgroup Γ} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup Γ N A)
    (hNodd : Odd (Nat.card ↥N)) (hAodd : Odd (Nat.card ↥A)) (hNnt : N ≠ ⊥) :
    2 * Nat.card ↥A + 1 ≤ Nat.card ↥N := by
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNnt
  have hN1 : 1 < Nat.card ↥N := Finite.one_lt_card
  -- `|A| ∣ |N| - 1` from `|N| ≡ 1 [MOD |A|]` (Isaacs 6.1).
  obtain ⟨m, hm⟩ : Nat.card ↥A ∣ Nat.card ↥N - 1 :=
    (Nat.modEq_iff_dvd' hN1.le).mp hFrob.card_kernel_modEq_one.symm
  -- `|N| - 1` is even (`|N|` odd), `|A|` is odd, so the cofactor `m` is even.
  have hNm1_even : Even (Nat.card ↥N - 1) := Nat.Odd.sub_odd hNodd odd_one
  have hm_even : Even m := by
    rcases (Nat.even_mul.mp (hm ▸ hNm1_even)) with hA | hm
    · exact absurd hA (Nat.not_even_iff_odd.mpr hAodd)
    · exact hm
  -- `m ≠ 0` (else `|N| = 1`), so `m ≥ 2`; hence `|N| - 1 = |A|·m ≥ 2|A|`.
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact hp
  have hm2 : 2 ≤ m := Nat.le_of_dvd hm_pos hm_even.two_dvd
  have hge : Nat.card ↥A * 2 ≤ Nat.card ↥A * m := Nat.mul_le_mul_left _ hm2
  omega

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8.b)/(12.16) `hB` for the witness `L`**: the second maximal subgroup `L` of
(12.9) satisfies the `(7.8.b)` norm lower bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²`
(`= CounterexampleDadeData.hB`), where `e = [L:H]` (`complementIndex`), `h = |H|` (`kernelOrder`),
`ζ_0 = Ind θ_0` the distinguished coherent-family member.  Assembles the witness `Hypothesis78`
(as in `witness_L_hypothesis78`) and feeds the concrete §7 producer `zetaNuRhoNormSqGeOfDade`,
supplying its four genuine `(7.8)` inputs: `hzeta0nu` (`ζ_0^ν ⊥ 1_G`, `witness_L_hzeta0nu`),
`hζ0norm` (`‖ζ_0‖² = 1`, Frobenius), `a`/`ha` (`(β, ζ_0^ν) + 1 ∈ ℤ`, `exists_betaDecomp_a`), and
`hsmall` (`2e + 1 ≤ h`, `frobenius_two_mul_card_complement_add_one_le_card_kernel`).  This realizes
the §7 hard-floor consumption for (12.16): the (7.8.b) `hB` field is now constructible. -/
theorem witness_L_zeta_bound [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      ∃ H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G (typeIA data.L hyp.typeI) data.L,
        (1 : ℝ) - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤ H78.zetaNuRhoNormSq := by
  classical
  obtain ⟨hyp, C, hC⟩ := witness_L_hypothesis_frobenius hG data
  obtain ⟨coh⟩ := frobenius_typeI_coherent hG hyp ⟨C, hC⟩
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- `hC`'s kernel is written with the `hyp.H` accessor; register the normality in that form too.
  haveI : (hyp.H.subgroupOf data.L).Normal := hKnormal
  have hAH : typeIA data.L hyp.typeI = (hyp.typeI.typeF.H : Set G) \ {1} :=
    Hypothesis.typeIA_eq_sharp hG hyp
  have hHnorm : ∀ (l : ↥data.L) {h : G}, h ∈ hyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ hyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ data.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥data.L) ∈ (hyp.typeI.typeF.H).subgroupOf data.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ := exists_witness_placed_family hyp
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        ∈ hyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  -- `θ_0 ≠ 1` (else `θ_0 = θ_{ind1H}` by `htriv`, so `0 = ind1H` by `hinj`, contra `hind1H`).
  have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf data.L) := by
    intro h
    refine hind1H (hinj ?_).symm
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [h, htriv]
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L)) := fun _ => rfl
  have hdeg : ∀ i, ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥data.L)
      = d i * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  have hdeg_match : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L)
      = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥data.L) := by
    rw [hdeg0, htriv]
    change (((hyp.typeI.typeF.H).subgroupOf data.L).index : ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L)) (1 : ↥data.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  have psi_support : ∀ i, (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA data.L hyp.typeI) data.L := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hx.1, hx.2⟩
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.extension
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)))
          (coh.extension
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ j : ClassFunction _ ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      hyp.toHypothesis71.τ ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ i : ClassFunction _ ℂ))
          - d i • coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ 0 : ClassFunction _ ℂ)) := by
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)
  -- The concrete witness `Hypothesis78`.
  set H78 := hypothesis78OfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension hnu_isometry hagree with hH78def
  -- (7.8) input `a`: `(β, ζ_0^ν) + 1 ∈ ℤ`.
  obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
    (Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
    (coh.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
  -- (7.8.b) `smallIndex`: `2e + 1 ≤ h`, from the Frobenius size bound.
  have hodd : Odd (Nat.card ↥data.L) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.L)
  have hKodd : Odd (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hCodd : Odd (Nat.card ↥C) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card C)
  have hKcard : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) = Nat.card hyp.typeI.typeF.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hKnt : ((hyp.typeI.typeF.H).subgroupOf data.L) ≠ ⊥ := by
    haveI : Nontrivial ↥hyp.typeI.typeF.H :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.H_nontrivial
    haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf data.L) :=
      (Subgroup.subgroupOfEquivOfLe hHL).toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hcompl : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) * Nat.card ↥C
      = Nat.card ↥data.L := hC.isComplement.card_mul_card
  have hsmall : H78.smallIndex := by
    have hfrob := frobenius_two_mul_card_complement_add_one_le_card_kernel hC hKodd hCodd hKnt
    show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
    have hke : H78.kernelOrder = Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) := by
      rw [hKcard]; rfl
    have hce : H78.complementIndex = Nat.card ↥C := by
      show Nat.card ↥data.L / Nat.card hyp.typeI.typeF.H = Nat.card ↥C
      rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
    rw [hke, hce]; exact hfrob
  refine ⟨hyp, H78, ?_⟩
  exact zetaNuRhoNormSqGeOfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension hnu_isometry hagree
    (witness_L_hzeta0nu hG hyp hC coh (θ 0) hθ0_ne)
    (inner_self_induce_eq_one_of_frobeniusGroup hC (θ 0) hθ0_ne) a ha hsmall

/-! ## (12.17): forcing case (b) of Theorem (8.8) — the all-type-I non-existence argument

Peterfalvi (12.17) shows that case (a) of Theorem (8.8) — *every* maximal subgroup of `G` being of
type I — is impossible.  The argument assembles the type-I maximals into a Frobenius family in the
sense of (7.10) (`S09.FrobeniusFamily`) and derives the contradiction from (7.11)
(`S09.not_trivial_G0`).  Combined with the (8.8) dichotomy (`theorem88_dichotomy`, BG §16), this
forces the case-(b) pairing data `Theorem88CaseBData`, which the Feit–Thompson endgame consumes.

The genuinely group-theoretic content of the family — the Frobenius structure (from (12.7)) and the
self-normalizing identity `L = N_G(L_F)` — is proved here.  The remaining §8/§10 covering inputs
(TI sharp-sets via (8.13.c1), coprime kernels and the `G#` cover via (8.17)) are isolated in the
faithful carrier `TypeICovering`. -/

section Theorem1217

variable [Finite G]

/-- **Normalizer bridge for Peterfalvi (12.17)**: a maximal subgroup `L` of a minimal simple group
of odd order is the normalizer of its maximal nilpotent normal Hall subgroup `L_F`, as soon as
`L_F ≠ ⊥`.

`L ≤ N_G(L_F)` is `maxNilpotentNormalHall_le_normalizer`.  If `N_G(L_F) = ⊤` then `L_F ⊴ G`, so by
simplicity `L_F = ⊥` or `⊤`; both are excluded (`L_F ≠ ⊥` by hypothesis, `L_F ≤ L < ⊤`).  Hence
`L ≤ N_G(L_F) < ⊤`, and `L` being a coatom upgrades the containment to equality. -/
theorem maximalSubgroup_eq_normalizer_maxNilpotentNormalHall
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hne : maxNilpotentNormalHall L ≠ ⊥) :
    L = Subgroup.normalizer (maxNilpotentNormalHall L : Set G) := by
  have hco : IsCoatom L := hL
  have hLleN : L ≤ Subgroup.normalizer (maxNilpotentNormalHall L : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L
  refine le_antisymm hLleN ?_
  rcases hLleN.lt_or_eq with hlt | heq
  · -- `L < N_G(L_F)` would force `N_G(L_F) = ⊤`, making `L_F ⊴ G`, which simplicity excludes.
    exfalso
    have hNtop : Subgroup.normalizer (maxNilpotentNormalHall L : Set G) = ⊤ := hco.2 _ hlt
    haveI hHnormal : (maxNilpotentNormalHall L).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall L) hHnormal with hb | ht
    · exact hne hb
    · have hle : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
      rw [ht] at hle
      exact hco.1 (top_le_iff.mp hle)
  · exact heq.ge

/-- **§8/§10 covering inputs to Peterfalvi (12.17)** — the all-type-I case of Theorem (8.8).

When every maximal subgroup of `G` is of type I, the §8 covering theory (BG Theorem E, (8.17), and
the escaping-centralizer control (8.13.c1)) supplies a finite family of conjugacy-class
representatives `reps i` whose maximal nilpotent normal Hall subgroups `(reps i)_F`:
* number at least two (`two_le`);
* have TI sharp-sets `((reps i)_F)#` (`isTI`, via (8.13.c1)+(2.3));
* are pairwise of coprime order (`coprime`, via the (8.17) prime partition);
* cover `G#` up to conjugacy (`covers`, the (8.17.a) type-I covering).

These are exactly the inputs the (12.17) argument feeds to (7.11), beyond the genuinely
group-theoretic family facts (Frobenius structure, `reps i = N_G((reps i)_F)`) discharged in
`not_all_maximal_typeI`. -/
structure TypeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) where
  /-- Number of conjugacy classes of maximal subgroups. -/
  k : ℕ
  /-- Conjugacy-class representatives of the maximal subgroups. -/
  reps : Fin k → Subgroup G
  /-- Each representative is maximal. -/
  reps_maximal : ∀ i, reps i ∈ maximalSubgroups G
  /-- (7.10): at least two members. -/
  two_le : 2 ≤ k
  /-- (8.13.c1)+(2.3): each kernel sharp-set is a TI-subset. -/
  isTI : ∀ i, IsTISubset ((maxNilpotentNormalHall (reps i) : Set G) \ {1}) (reps i)
  /-- (8.17): the kernels have pairwise-coprime order. -/
  coprime : ∀ ⦃i j⦄, i ≠ j →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (reps i)))
      (Nat.card ↥(maxNilpotentNormalHall (reps j)))
  /-- (8.17.a): the conjugates of the kernels cover every nonidentity element. -/
  covers : ∀ x : G, x ≠ 1 →
    ∃ i, ∃ g : G, g * x * g⁻¹ ∈ (maxNilpotentNormalHall (reps i) : Set G) \ {1}

omit [Finite G] in
/-- **§8 thickening kernel containment.**  The subgroup `R(x) = supportKernel L M X x` of
Peterfalvi (8.14) is always contained in `L_F = maxNilpotentNormalHall L`: on the
escaping-centralizer set it is `L_F ⊓ C_G(x) ≤ L_F`, and elsewhere it is `⊥`. -/
theorem supportKernel_le_maxNilpotentNormalHall (L M : Subgroup G) (X : Set G) (x : G) :
    supportKernel L M X x ≤ maxNilpotentNormalHall L := by
  classical
  unfold supportKernel
  split
  · exact inf_le_left
  · exact bot_le

/-- **The type-I thickened cover lands in `L_F`-conjugates.**  If a support set `X` is contained in
`L_F = maxNilpotentNormalHall L`, then every element of the thickened support
`⋃_{z ∈ X} (z R(z))^G` (`thickenedSupport L M X`) is conjugate to an element of `L_F`: the coset
factor `z ∈ X ⊆ L_F` and the kernel factor `r ∈ R(z) ⊆ L_F`
(`supportKernel_le_maxNilpotentNormalHall`) multiply into `L_F`, which `𝒞_G` saturates.

This is the structural heart of the (12.17) type-I covering: the thickening `R(z)` never escapes
`L_F`, so the `A_1(L) = (L_F)#` cover by thickened sets is, up to conjugacy, a cover by `L_F`. -/
theorem thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall
    {L M : Subgroup G} {X : Set G} (hX : X ⊆ (maxNilpotentNormalHall L : Set G)) :
    thickenedSupport L M X ⊆ conjClassSet (maxNilpotentNormalHall L : Set G) := by
  rintro y ⟨z, hz, hyz⟩
  obtain ⟨w, hw, g, hgwy⟩ := hyz
  obtain ⟨r, hr, hzrw⟩ := hw
  have hzMF : z ∈ maxNilpotentNormalHall L := hX hz
  have hrMF : r ∈ maxNilpotentNormalHall L :=
    supportKernel_le_maxNilpotentNormalHall L M X z (SetLike.mem_coe.mp hr)
  have hwMF : w ∈ maxNilpotentNormalHall L := hzrw ▸ mul_mem hzMF hrMF
  exact ⟨w, SetLike.mem_coe.mpr hwMF, g, hgwy⟩

/-- **Peterfalvi (8.17)/(8.13.c1), all-type-I case**: the §8 covering inputs of (12.17) exist.

Built as an honest reduction from BG Theorem E (`S10.bgTheoremE_cover_data`): in the all-type-I case
every representative `M_i` has `data.tau i = .I` (type exclusivity, `not_isTypeI_of_isTypeNonI`), so
`mainSubgroup (M_i) (τ_i) = (M_i)_F`.  The `reps`/`reps_maximal` plumbing, `coprime` (the (8.17)
prime-factor partition is disjoint, hence the kernels are coprime), `two_le` (a single class would
make `|G#| = (|M_s|-1)|G:M| < |G|-1 = |G#|`), and `covers` (the thickened cover lands in
`(M_i)_F`-conjugates, `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`) are all
discharged.  Two upstream facts remain isolated as residual sorries: `isTI`, the escaping-centralizer
control (8.13.c1)+(2.3) making each kernel sharp-set a TI-subset; and the selection of the type-I
cover branch under `hall`, the (8.8.a) dichotomy (BG §16, parallel to `theorem88_dichotomy`). -/
theorem exists_typeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by
  classical
  -- `BGTheoremECoverData.ι : Type*` is universe-polymorphic; pin the index type to `Type 0`.
  obtain ⟨data, hcover⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  haveI : Fintype data.ι := data.finite_index
  -- **Every representative is type I**, so `data.tau i = .I` and hence
  -- `mainSubgroup (M_i) (τ_i) = (M_i)_F`.  Type exclusivity is
  -- `not_isTypeI_of_isTypeNonI` (BG §16): a type-`P` (= non-type-I) maximal is not type I.
  have hMF : ∀ i, mainSubgroup (data.reps i) (data.tau i)
      = maxNilpotentNormalHall (data.reps i) := by
    intro i
    have hI : IsTypeI (data.reps i) := hall _ (data.maximal i)
    have htau := data.typed i
    have htauI : data.tau i = PeterfalviType.I := by
      by_contra hne
      have hNonI : IsTypeNonI (data.reps i) := by
        cases hc : data.tau i with
        | I => exact absurd hc hne
        | II => rw [hc] at htau; exact Or.inl htau
        | III => rw [hc] at htau; exact Or.inr (Or.inl htau)
        | IV => rw [hc] at htau; exact Or.inr (Or.inr (Or.inl htau))
        | V => rw [hc] at htau; exact Or.inr (Or.inr (Or.inr htau))
      exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG (data.maximal i) hNonI hI
    simp only [htauI, mainSubgroup]
  -- The `Fin k`-indexing of the representatives (`e : data.ι ≃ Fin k`).
  set e := Fintype.equivFin data.ι with he
  rcases hcover with hTypeI | hNonTypeI
  · -- **(8.8.a) type-I cover branch.**
    refine ⟨{
      k := Fintype.card data.ι
      reps := fun j => data.reps (e.symm j)
      reps_maximal := fun j => data.maximal (e.symm j)
      two_le := ?_
      isTI := ?_
      coprime := ?_
      covers := ?_ }⟩
    · -- **`two_le`** (discharged): at least two conjugacy classes of maximal subgroups (7.10).
      -- A single class would force `|G#| = |thickenedA1(M)| = (|M_s| - 1)|G : M|`; but
      -- `(|M_s| - 1)|G : M| ≤ (|M| - 1)|G : M| = |G| - |G : M| ≤ |G| - 2 < |G| - 1 = |G#|`, and an
      -- empty class would force `|G#| = 0`, both impossible.  No counting of disjoint unions is
      -- needed: a one-element index makes the cover `⋃ᵢ thickenedA1(Mᵢ)` equal to a single
      -- `thickenedA1(M)`, whose cardinality is strictly below `|G#|`.
      haveI : Nontrivial G := hG.simple.toNontrivial
      by_contra hlt
      rw [Nat.not_le] at hlt
      have hcard01 : Fintype.card data.ι = 0 ∨ Fintype.card data.ι = 1 := by omega
      rcases hcard01 with h0 | h1
      · -- empty index: the cover is empty, but `G#` contains a nonidentity element.
        rw [Fintype.card_eq_zero_iff] at h0
        have hempty : (⋃ i, data.cover i) = ∅ :=
          Set.iUnion_of_empty _
        rw [← hTypeI.cover_nonidentity] at hempty
        obtain ⟨b, hb⟩ := exists_ne (1 : G)
        have hbmem : b ∈ sharpSubgroup (⊤ : Subgroup G) := by
          simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_diff, Set.mem_univ, true_and,
            Set.mem_singleton_iff]
          exact hb
        rw [hempty] at hbmem
        exact hbmem.elim
      · -- one class: `⋃ᵢ thickenedA1(Mᵢ) = thickenedA1(M)`, of cardinality `< |G#|`.
        obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
        have hunion : (⋃ i, data.cover i) = data.cover i₀ := by
          ext x
          simp only [Set.mem_iUnion]
          exact ⟨fun ⟨i, hi⟩ => by rwa [hi₀ i] at hi, fun hx => ⟨i₀, hx⟩⟩
        rw [← hTypeI.cover_nonidentity] at hunion
        have hcard_eq : Nat.card ↥(data.cover i₀) = Nat.card G - 1 := by
          rw [Nat.card_coe_set_eq, ← hunion]
          show ((↑(⊤ : Subgroup G) : Set G) \ {1}).ncard = Nat.card G - 1
          rw [Subgroup.coe_top, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
        rw [data.cover_card i₀] at hcard_eq
        -- Arithmetic contradiction.
        have hmain_le : mainSubgroup (data.reps i₀) (data.tau i₀) ≤ data.reps i₀ :=
          (hMF i₀).le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (data.reps i₀))
        have ham : Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀))
            ≤ Nat.card ↥(data.reps i₀) := Subgroup.card_le_of_le hmain_le
        have hidx0 : (data.reps i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hidx1 : (data.reps i₀).index ≠ 1 :=
          fun h => (data.maximal i₀).1 (Subgroup.index_eq_one.mp h)
        have hidx : 2 ≤ (data.reps i₀).index := by omega
        have hmidx : Nat.card ↥(data.reps i₀) * (data.reps i₀).index = Nat.card G :=
          Subgroup.card_mul_index (data.reps i₀)
        have hm_pos : 0 < Nat.card ↥(data.reps i₀) := Nat.card_pos
        have hG2 : 2 ≤ Nat.card G :=
          le_trans hidx (hmidx ▸ Nat.le_mul_of_pos_left (data.reps i₀).index hm_pos)
        have hb1 : (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
            * (data.reps i₀).index
            ≤ (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ham 1)
        have hrhs : (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index
            = Nat.card G - (data.reps i₀).index := by rw [Nat.sub_one_mul, hmidx]
        rw [hrhs] at hb1
        -- `hcard_eq : P = |G| - 1`, `hb1 : P ≤ |G| - idx`, `idx ≥ 2`, `|G| ≥ 2` ⟹ `False`.
        set P := (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
          * (data.reps i₀).index with hP
        omega
    · -- `isTI`: each kernel sharp-set `((M_i)_F)#` is a TI-subset, by (8.13.c1)+(2.3).
      -- Escaping-centralizer §8 residual.
      intro j
      sorry
    · -- **`coprime`** (discharged): the kernels have pairwise-coprime order because the (8.17)
      -- partition makes their prime-factor sets disjoint.
      intro j j' hjj'
      have hne : e.symm j ≠ e.symm j' := fun h => hjj' (e.symm.injective h)
      have hdisj := data.primeFactors_disjoint (e.symm j) (e.symm j') hne
      simp only [hMF] at hdisj
      have hcard1 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j))) ≠ 0 :=
        Nat.card_pos.ne'
      have hcard2 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j'))) ≠ 0 :=
        Nat.card_pos.ne'
      exact (Nat.disjoint_primeFactors hcard1 hcard2).mp hdisj
    · -- **`covers`** (discharged): the faithful BG cover `𝒞_G(M̃_i)` lands in the conjugates of the
      -- kernel sharp-set `((M_i)_F)#` (`BGTheoremETypeICovering.cover_subset_kernels`; in the
      -- all-type-I case `R(x) = 1`, so `M̃_i = (M_i)_σ# = (M_i)_F#`).  Combined with the (8.17.a)
      -- cover `cover_nonidentity`, every nonidentity `x` is conjugate into some `(M_i)_F#`.
      intro x hx1
      have hxsharp : x ∈ sharpSubgroup (⊤ : Subgroup G) := by
        simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_diff, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        exact hx1
      rw [hTypeI.cover_nonidentity] at hxsharp
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxsharp
      obtain ⟨t, htMF, g, hgtx⟩ := hTypeI.cover_subset_kernels i hxi
      refine ⟨e i, g⁻¹, ?_⟩
      have hreps : data.reps (e.symm (e i)) = data.reps i := by rw [Equiv.symm_apply_apply]
      have hconj : g⁻¹ * x * (g⁻¹)⁻¹ = t := by rw [inv_inv, ← hgtx]; group
      rw [hreps, hconj]
      exact htMF
  · -- **(8.8.b) non-type-I cover branch**: ruled out when every maximal subgroup is type I.
    -- This is the all-type-I case of the (8.8) dichotomy (`theorem88_dichotomy`); under `hall`
    -- BG Theorem E returns the type-I cover, never the two-exceptional-subgroup case (the
    -- exceptional `W` of `hNonTypeI` is the normalizer of a non-type-I maximal).  Isolating that
    -- is the BG §16 (8.8.a) residual.
    exfalso
    sorry

/-- **Peterfalvi (12.17), non-existence half**: in a minimal simple group of odd order, not every
maximal subgroup is of type I.

*Proof.*  Assume otherwise.  The §8 covering theory (`exists_typeICovering`) provides the family of
conjugacy-class representatives `reps i` of the maximal subgroups, whose kernels `(reps i)_F` are
pairwise-coprime TI-subsets covering `G#`.  Each `reps i` is a Frobenius group with kernel
`(reps i)_F` by (12.7) (`typeI_frobenius`) and equals its own `N_G((reps i)_F)`
(`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`), so these data assemble into a Frobenius
family in the sense of (7.10) (`S09.FrobeniusFamily`).  The covering makes `G₀ = {1}`, contradicting
(7.11) (`S09.not_trivial_G0`). -/
theorem not_all_maximal_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) := by
  intro hall
  obtain ⟨cov⟩ := exists_typeICovering hG hall
  let F : OddOrder.Peterfalvi.S09.FrobeniusFamily G cov.k :=
    { L := cov.reps
      H := fun i => maxNilpotentNormalHall (cov.reps i)
      two_le := cov.two_le
      kernel_le := fun i => OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (cov.reps i)
      isFrobenius := fun i => by
        obtain ⟨fd, -⟩ := typeI_frobenius hG (cov.reps_maximal i) (hall _ (cov.reps_maximal i))
        refine ⟨fd.complement, ?_⟩
        rw [← fd.typeI.typeF.H_eq]
        exact fd.frobenius
      normalizer_eq := fun i =>
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG (cov.reps_maximal i) (by
          obtain ⟨td⟩ := hall _ (cov.reps_maximal i)
          rw [← td.typeF.H_eq]
          exact td.typeF.H_nontrivial)
      isTI := cov.isTI
      coprime_kernel := cov.coprime }
  have hG0 : F.G0 = {(1 : G)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨F.one_mem_G0, fun x hx => ?_⟩
    by_contra hx1
    obtain ⟨i, g, hg⟩ := cov.covers x hx1
    exact (F.mem_G0_iff.mp hx) i ⟨g, hg⟩
  exact OddOrder.Peterfalvi.S09.not_trivial_G0 F hG.odd hG0

end Theorem1217

/-! ## (12.17) → (8.8): the case-(b) dichotomy -/

/-- **Type-`P` ⟹ non-Type-I** (Proposition 16.1(b)(c)(d)): a type-`P` maximal subgroup of a minimal
simple group of odd order is one of the Types II–V.  Split `κ(M)` against `π(M) - σ(M)`: equal gives
`P₁`, which is Type V (`M_F = M_σ`) or Type III/IV (`M_F ≠ M_σ`); unequal gives `P₂` = Type II.  This
is the local `typeP_imp_nonI` of BG Theorem I's dichotomy proof, isolated here for
`theorem88_dichotomy`. -/
private theorem isTypeNonI_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP N) : IsTypeNonI N := by
  obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
  by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
  · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
    by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
    · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
    · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
      · exact Or.inr (Or.inl hIII)
      · exact Or.inr (Or.inr (Or.inl hIV))
  · exact Or.inl (hbII.mpr ⟨hP, hk⟩)

/-- **Theorem (8.8) dichotomy** (BG §16): for a minimal simple group of odd order, either every
maximal subgroup is of type I, or the case-(b) pairing data `Theorem88CaseBData` exists.

*Proof.*  If some maximal `S` is not type I, then it is type `P` (Proposition 16.1(a): `TypeI ⟺
TypeF`, and `TypeF ⟺ κ(S) = ∅`).  BG Theorem 14.7 duality (`typeP_duality`) applied to `S` with a
`κ(S)`-Hall subgroup `K` produces the complement `S = S' ⋊ K` (first conjunct), the dual maximal
`T = M*`, the cyclic factor `W = K ⊔ K*`, the type-II witness, and the `κ(M*)`-Hall `K*`.  Applying
the duality again at `M*` gives the second complement `T = T' ⋊ K*`.  The `κ`-Hall complement `K`
plays the role of the case-(b) factor `W₁` (both `K` and the type-`P` `W₁` complement `S'`, Peterfalvi
(8.8.b1)).  Cites the merged BG §16 `typeP_duality` and `proposition_type_classification`; the
remaining hard content lives in their (issue-8015) residuals. -/
theorem theorem88_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  classical
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · exact Or.inl hall
  · refine Or.inr ?_
    push_neg at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
    -- `S` not type I ⟹ `S` type `P` (Prop 16.1(a): `TypeI ⟺ TypeF`, `TypeF ⟺ κ(S) = ∅`).
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP S := by
      have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).1
      have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF S := fun hF => hSnotI (hiff.mpr hF)
      rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- A `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- BG Theorem 14.7 duality at `S`: `S = S' ⋊ K` (`hScompl`), the dual `M*`, its data.
    obtain ⟨hScompl, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
    -- Apply duality again at `M*` with its `κ`-Hall `K*`: `M* = (M*)' ⋊ K*` (`hTcompl`).
    obtain ⟨hTcompl, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq
    exact ⟨{
      S := S, T := Mstar, W1 := K, W2 := Kstar, W := K ⊔ Kstar
      S_maximal := hS, T_maximal := hMstarMem
      S_ne_T := by
        intro hST
        rw [hST] at hSnconjMstar
        exact hSnconjMstar (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
      W_eq := rfl, W_cyclic := hcyc
      S_nonI := isTypeNonI_of_isTypeP hG hS hSP
      T_nonI := isTypeNonI_of_isTypeP hG hMstarMem hMstarP
      one_typeII := hP2disj.imp
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr h)
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr h)
      W1_le_S := Subgroup.map_subtype_le K'
      W2_le_T := hKstarMstar
      S_compl := hScompl
      T_compl := hTcompl }⟩

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible, so the case-(b)
data of (8.8) exists.  Immediate from the (8.8) dichotomy (`theorem88_dichotomy`) and the
non-existence half `not_all_maximal_typeI`. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) :=
  (theorem88_dichotomy hG).resolve_left (not_all_maximal_typeI hG)

end OddOrder.Peterfalvi.S14

#print axioms OddOrder.Peterfalvi.S14.frobenius_typeI_induced_char_constituents
#print axioms OddOrder.Peterfalvi.S14.fixed_conjClass_eq_one_of_typeF
#print axioms OddOrder.Peterfalvi.S14.coherent_extension_mem_span_imageFamily
#print axioms OddOrder.Peterfalvi.S14.coherent_extension_constituent_mem_span_Rset
-- `coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` is sorry-free in its own body
-- but transitively cites `nonconjugate_typeI_R_orthogonal` (12.3), whose geometric obligation
-- `nonconjugate_diffImage_inner_zero` (8.18.c, §10 thickened-support) is the one remaining sorry;
-- so it is intentionally *not* in the axiom-clean block above (would show `sorryAx`).
