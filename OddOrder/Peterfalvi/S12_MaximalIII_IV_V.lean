/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV

/-!
# Peterfalvi Section 12: Maximal Subgroups of Types III, IV, and V

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
  obtain ⟨ptype, hptype⟩ : ∃ ptype : PeterfalviType, HasPeterfalviType ptype M := by
    rcases hType with h | h | h
    · exact ⟨.III, h⟩
    · exact ⟨.IV, h⟩
    · exact ⟨.V, h⟩
  obtain ⟨dadeData⟩ :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeP hG hM data hptype).1
  -- (8.14)/(8.15): the support kernels `R(a)` are `L`-conjugation invariant.
  have hconj : dadeData.dade.HConjInvariant := by
    sorry
  refine ⟨?_⟩
  exact
    { maximal := hM
      typeP := data
      type_alt := hType
      dadeData := dadeData
      hconj := hconj }

/-! ## (10.2)--(10.4): basic character parameters and coherent extension -/

/-- The character parameters obtained in Peterfalvi (10.2)--(10.3).

The fields `degree_independent`, `delta_independent`, and `n_formula` name the
arithmetic conclusions whose detailed proofs come from (4.5.a) and the
automorphism calculation around (3.9). -/
structure CharacterParameters {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_S : zeta ∈ hyp.Sset
  zeta_irreducible : Prop
  zeta_irreducible_holds : zeta_irreducible
  d : ℕ
  delta : ℤ
  n : ℕ
  w2_prime : hyp.w2.Prime
  d_gt_one : 1 < d
  degree_independent : Prop
  degree_independent_holds : degree_independent
  delta_independent : Prop
  delta_independent_holds : delta_independent
  n_formula : Prop
  n_formula_holds : n_formula
  mu : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  omegaSigma : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ
  alpha : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  alpha_formula : Prop
  alpha_formula_holds : alpha_formula
  alpha_tau_formula : Prop
  mu_tau1_formula : Prop
  zeta_tau1_norm_bound : Prop
  orthogonality_w1_lt_w2 : Prop
  typeV_parameter_formula : Prop
  typeV_coherence_formula : Prop

/-- **Peterfalvi (10.4)**: the coherent-extension hypothesis for the family of
characters in (10.1). -/
structure CoherentHypothesis {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (params : CharacterParameters hyp) where
  coherent_S : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1_extends_tau_on_S : Prop
  tau1_extends_tau_on_S_holds : tau1_extends_tau_on_S

/-- **Peterfalvi (10.2)**: the family `S` contains an irreducible character
`zeta` of degree `w_1`. -/
theorem exists_zeta_degree_w1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.zeta ∈ hyp.Sset ∧ params.zeta_irreducible ∧
        params.zeta 1 = ((hyp.w1 : ℕ) : ℂ) := by
  sorry

/-- **Peterfalvi (10.3)**: `w_2` is prime and the parameters `d`, `delta`, and
`n = (d - delta) / w_1` are well-defined and independent of the indices. -/
theorem w2_prime_and_parameter_independence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      hyp.w2.Prime ∧ 1 < params.d ∧ params.degree_independent ∧
        params.delta_independent ∧ params.n_formula := by
  sorry

/-! ## (10.5)--(10.6): Dade-isometry calculations -/

/-- **Peterfalvi (10.5)**: the virtual characters `alpha_ij` are supported on
`A_0(M)`, and under the coherent extension they have the stated Dade image. -/
theorem alpha_support_and_image [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    (∀ i j, (params.alpha i j).support ⊆ hyp.A0) ∧ params.alpha_tau_formula := by
  sorry

/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one. -/
theorem tau1_values_and_norm_bound [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    params.mu_tau1_formula ∧ params.zeta_tau1_norm_bound := by
  sorry

/-! ## (10.7)--(10.8): Type II derived Frobenius and non-coherence -/

/-- A carrier for the conclusion of Peterfalvi (10.7): `[S,S]` is a Frobenius
group with kernel `S_F`. -/
structure DerivedFrobeniusData (S : Subgroup G) where
  kernel : Subgroup ↥(derivedInG S)
  complement : Subgroup ↥(derivedInG S)
  kernel_is_SF : Prop
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S) kernel complement

/-- **Peterfalvi (10.7)**: if `S` is a maximal subgroup of type II, then
`[S,S]` is Frobenius with kernel `S_F`. -/
theorem typeII_derived_frobenius [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSType : IsTypeII S) :
    ∃ data : DerivedFrobeniusData S, data.kernel_is_SF := by
  sorry

/-- **Peterfalvi (10.8)**: under Hypothesis (10.1), the character family `S` is
not coherent. -/
theorem S_not_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

/-! ## (10.9)--(10.11): the Type V elimination and the case-B remark -/

/-- **Peterfalvi (10.9)**: when `w_1 < w_2`, the residual character in
`(mu_0 - zeta)^tau` is orthogonal to `(Irr W)^sigma`. -/
theorem orthogonality_of_w1_lt_w2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} (params : CharacterParameters hyp)
    (hw : hyp.w1 < hyp.w2) :
    params.orthogonality_w1_lt_w2 := by
  sorry

/-- **Peterfalvi (10.10.1)--(10.10.4)**: if Hypothesis (10.1) holds with `M`
of type V, then the Type V parameter calculation forces `S` to be coherent. -/
theorem typeV_forces_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} (hV : IsTypeV M) (params : CharacterParameters hyp) :
    params.typeV_parameter_formula ∧ params.typeV_coherence_formula ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (10.10)**: `G` has no maximal subgroup of type V.

By (10.8) (`S_not_coherent`) the family `S` of any type-III/IV/V maximal is not
coherent; but a type-V maximal forces `S` to be coherent by (10.10.1)–(10.10.4)
(`typeV_forces_coherence`).  These now refer to the *genuine* Dade isometry,
induced family, and support carried by the faithful (10.1) `Hypothesis` (built by
`exists_hypothesis_of_typeIIIorIVorV`), so the contradiction is honest. -/
theorem no_typeV_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M := by
  rintro ⟨M, hMmax, hMV⟩
  obtain ⟨hyp⟩ := exists_hypothesis_of_typeIIIorIVorV hG hMmax (Or.inr (Or.inr hMV))
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  exact S_not_coherent hG hyp (typeV_forces_coherence hG hMV params).2.2

/-- The case-(b) data in Peterfalvi (8.8), used in the remark (10.11). -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T

/-- **Peterfalvi (10.11), first assertion**: in case (b) of Theorem (8.8), the
orders of `W_1` and `W_2` are prime. -/
theorem theorem88_caseB_prime_orders [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseB : Theorem88CaseBData G) :
    (Nat.card ↥caseB.W1).Prime ∧ (Nat.card ↥caseB.W2).Prime := by
  sorry

/-- **Peterfalvi (10.11), Type II assertion**: for a type-II maximal subgroup,
the §11 family `S(H_0 C')` specializes to a coherent set. -/
theorem typeII_section11_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent chars.tau chars.S chars.H0CprimeSupport) := by
  exact ⟨OddOrder.Peterfalvi.S11.coherent_H0C_commutator chars⟩

end OddOrder.Peterfalvi.S12
