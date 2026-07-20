/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_PivotCoherence
import OddOrder.Peterfalvi.S11_NineElevenBridgeBase
import OddOrder.Peterfalvi.S10_SubcoherentTypeP
import OddOrder.Peterfalvi.S11_MaximalII_III_IV.ThetaCountAssembly
import OddOrder.Peterfalvi.S11_NineElevenCoherence
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

/-!
# The (9.9.b) dichotomy, the `R`-family dispatch, and case (9.7.b) — §9 level

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8 (8.15.3) and §9 (9.5), pp. 47-51 (issue 1045).

Peterfalvi gets the base coherence used by (9.11) from **(8.15.3)**: the family `𝒮` of §9 is a
conjugation-closed set of induced characters to which Hypothesis (5.2) applies, and (5.7)
(`S07.coherent_subset_of_constant_degree`) then makes any constant-degree subfamily coherent.
The repo instead routed that through the §10 μ-grid engine
(`S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`), which is what tied the (9.11) chain to
the §10/§11 packaging and hence to types III/IV.

This file supplies the missing link — that §9's family is a subfamily of the (8.15.3) one:

* §9 (9.5) family: `𝒮(Y) = {Ind_{HU}^M χ | χ ∈ Irr(HU), H ⊄ Ker χ, Y ⊆ Ker χ}` (`S11.sOf`);
* (8.15.3) family: `{Ind_{M'}^M θ | θ ∈ Irr M', M_σ ⊄ Ker θ}` (`S10.inducedNonKernelFamily`).

They induce from the *same* subgroup, since `HU = M'` (`huSub_eq_derivedInG_subgroupOf`,
Peterfalvi (9.2)); and §9's filter is the *stronger* one, since `M_F ≤ M_σ`
(`BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`) makes `M_F ⊄ Ker χ` imply `M_σ ⊄ Ker χ`.

⚠ In types III/IV, `M_s = M'`, so (8.15.3)'s filter degenerates to `θ ≠ 1` and §9's family is
strictly narrower; the containment still runs the direction we need.

⚠ **Why a separate leaf**: `S10_SubcoherentTypeP` (where `inducedNonKernelFamily` lives) and
`S11_MaximalII_III_IV.*` (where `sOf` lives) are *sibling* modules — neither imports the other.
Putting the bridge in the §8 file would make an §8 module import §9, reintroducing exactly the
layering inversion that issues 1045/1046 removed.
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]
/-- **Peterfalvi (9.9.b), member form** (§6 level, no transport): a reducible induced character
from `h46.K` is a certain-type column sum.

This is the content the §9 caseB `R`-family dispatch needs, isolated so that **no coercion between
`↥h46.K` and `↥(huSub data)` appears** — everything stays inside `h46.K`.  An earlier attempt stated
it over `sOf data Y` directly and tried to move the source character across
`h46.K = huSub data`; that rewrite is not type-correct (the motive mentions
`IrreducibleCharacter ↥_a` *and* `chiRestrict χ₂ = χ`, both dependent on the subgroup).  Splitting
it this way keeps the dependent step transport-free and leaves the §9 identification to the
Set-valued level, where the `▸` idiom does work (cf. `sOf_subset_inducedNonKernelFamily`).

The §13 analogue is `S13.caseB_sOf_member_dichotomy`, whose conclusion is phrased in the §10 μ-grid;
the book builds these members from (4.7) and Theorem (4.5), both §6, so the `columnSum` form here is
the faithful one. -/
theorem induce_columnSum_of_not_irreducible {M : Subgroup G} {A : Set G} [Finite G] [Fintype G]
    [Fintype ↥M]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] [Invertible (Nat.card ↥h46.K : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥h46.K)
    (hχne : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥h46.K)
    (hred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce h46.K (χ : ClassFunction ↥h46.K ℂ))) :
    ∃ χ₂ ≠ 1, ClassFunction.induce h46.K (χ : ClassFunction ↥h46.K ℂ)
      = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
  obtain ⟨χ₂, hχ₂⟩ := (h46.induce_not_isIrreducible_iff χ).mp hred
  refine ⟨χ₂, ?_, ?_⟩
  · -- `χ₂ = 1` would make the source trivial (`chiRestrict_one_eq_trivial`)
    rintro rfl
    rw [h46.chiRestrict_one_eq_trivial] at hχ₂
    exact hχne hχ₂.symm
  · rw [← hχ₂, OddOrder.Peterfalvi.S06.columnSum_def]
    exact h46.induce_restrict_certainType_eq χ₂

/-- **Transporting an induction source across an equality of induction subgroups.**  For `K = K'`
an irreducible `K'`-character has an irreducible `K`-counterpart with the *same* induction, and the
two are trivial together.

The equality is discharged by `subst` (both subgroups are variables here), which is exactly why the
lemma is stated in this generality rather than at `h46.K = huSub data`: there `h46.K` is a
projection, so `subst` does not apply and a direct `▸` on the dependent character type breaks the
motive (cf. the docstring of `induce_columnSum_of_not_irreducible`).  The residual `Invertible`
mismatch after `subst` is propositional (`Subsingleton`), the same wrinkle
`induceHU_eq_induce` handles. -/
theorem exists_induce_eq_of_subgroup_eq {L : Type*} [Group L] [Fintype L] {K K' : Subgroup L}
    (hKK' : K = K') [Invertible (Nat.card ↥K : ℂ)] [Invertible (Nat.card ↥K' : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K') :
    ∃ χ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (χ' : ClassFunction ↥K ℂ)
          = ClassFunction.induce K' (χ : ClassFunction ↥K' ℂ) ∧
        (χ' = OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K ↔
          χ = OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K') := by
  subst hKK'
  refine ⟨χ, ?_, Iff.rfl⟩
  convert rfl using 2
  exact Subsingleton.elim (α := Invertible (Nat.card ↥K : ℂ)) _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.9.b) at §9 level**: a *reducible* member of `𝒮(Y)` is a nontrivial certain-type
column sum `μ_{χ₂}` of Hypothesis (4.6).

This is the §9 replacement for `S13.caseB_sOf_member_dichotomy`, whose conclusion is stated in the
§10 μ-grid (`hyp.base.muColumnChar`) and therefore drags the whole §10/§11 packaging — and with it
the type III/IV restriction — into the caseB `R`-family dispatch.  The book has no such detour: it
builds the reducible members from (4.7) and Theorem (4.5), both §6 results, which is exactly the
`S06.columnSum` form produced here.  (§10 converts §6-columns to μ-grid columns and `certainTypeR`
converts them back, so the packaging route is a round trip; issue 1045.)

The `𝒮`-side source is nontrivial because `𝒳` demands `H ⊄ Ker χ` while the trivial character has
kernel everything, and `hKeq` moves it into the (4.6) world where
`induce_columnSum_of_not_irreducible` applies.  Callers get `hKeq` from
`huSub_eq_derivedInG_subgroupOf` together with the `K`-field of the (4.6) producer
(`S10.typePACore_toHypothesis46_core`). -/
theorem sOf_columnSum_of_not_irreducible [Finite G] {M : Subgroup G} {A : Set G}
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) {Y : Subgroup G} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data Y) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ χ₂ ≠ 1, φ = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
  obtain ⟨χ, hχ, rfl⟩ := hφ
  -- `χ ≠ 1`: the trivial character's kernel is everything, contradicting `H ⊄ Ker χ` (`𝒳`).
  have hχne : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥(huSub data) := by
    intro htriv
    apply hχ.1
    rw [htriv]
    simp only [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  obtain ⟨χ', hind, htriviff⟩ := exists_induce_eq_of_subgroup_eq hKeq χ
  have hred' : ¬ IsIrreducibleCharacter
      (ClassFunction.induce h46.K (χ' : ClassFunction ↥h46.K ℂ)) := by
    rw [hind, ← induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ)]
    exact hred
  obtain ⟨χ₂, hχ₂ne, heq⟩ :=
    induce_columnSum_of_not_irreducible h46 χ' (fun h => hχne (htriviff.mp h)) hred'
  exact ⟨χ₂, hχ₂ne,
    (induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ)).trans (hind.symm.trans heq)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The certain-type `R`-family transported to a member equal to its column.**  For `η = μ_{χ₂}`
with `χ₂ ≠ 1`, this is `S06.certainTypeR` restated at `η`.

Only the `image_eq` field mentions the member, so `imageSet`/`mem_ZIrr`/`orthonormal` are reused
verbatim and `.imageSet` is *definitionally* `certainTypeR`'s — the form the (5.2.e)
cross-orthogonality lemmas consume.  Keeping `χ₂` and `hηeq` as parameters (rather than choosing
them inside) is what makes the `η`-rewrite in `image_eq` type-correct: were `χ₂` obtained by
`Classical.choose` from an existential over `η`, the `imageSet` in the motive would itself depend on
`η`. -/
noncomputable def columnRFamily {M : Subgroup G} {A : Set G} [Finite G]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {η : ClassFunction ↥M ℂ} (hηeq : η = OddOrder.Peterfalvi.S06.columnSum h46 χ₂) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) η where
  imageSet := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet
  mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).mem_ZIrr
  orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).orthonormal
  image_eq := by
    rw [hηeq]
    exact (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).image_eq

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member orthonormal `R`-family over `𝒮(Y)`, at §9 level** — the raw (5.2.d) datum feeding
the norm-general (5.7) engine `S07.uniform_degree_coherence_of_families` in case (9.7.b) of (9.11).

Every member of `𝒮(Y)` is either irreducible or, by (9.9.b)
(`sOf_columnSum_of_not_irreducible`), a nontrivial certain-type column `μ_{χ₂}`; the `R`-family is
dispatched accordingly:

* **irreducible `η`** — the 2-element signed Dade family
  `S07.dadeOrthonormalCharacterImageFamilyOfDiff` (`τ(η − η̄) = ε·(μ − ν)`), whose no-realness and
  `A₀`-supported difference come from the `⊥`-kernel world-bridge
  (`sOf_subset_inducedKernelFamily_bot`) rather than from a `S13.Hypothesis`;
* **column `η = μ_{χ₂}`** — the `2q`-element certain-type family `S06.certainTypeR`.

This is the §9 replacement for `S13.caseB_sOf_memberRFamily`.  The two differ only in where the
reducible branch gets its column: the §13 version reads a μ-grid index `k : Fin hyp.base.w2` off the
§10 packaging (which is what confined it to types III/IV), while here it is the §6 column `χ₂` that
`certainTypeR` consumes anyway.  **No type hypothesis appears on this route.**

⚠ `τ` is *not* a free parameter here (unlike case (9.7.a)'s `caseA_coherent_sOf_cprime_of_refuter`):
`certainTypeR` produces its family over `dadeIntegralCharacterMap h46.dade0 h46.tau`, so the
conclusion is pinned to it, and the irreducible branch — which lands on
`h46.dade0.fullDadeIsometryData hconj` — is matched to it by `htau`.  For the intended producer
`S10.typePACore_toHypothesis46_core`, which stores `tau := dade0.fullDadeIsometryData hconj`
verbatim, `htau` is `rfl`.

⚠ The family is assembled field-by-field rather than by transporting along `htau` / `η = μ_{χ₂}`,
so that `.imageSet` is *definitionally* the underlying constructor's — the form in which the (5.2.e)
cross-orthogonality lemmas consume it (same reason as in the §13 version). -/
noncomputable def sOf_memberRFamily [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) η := by
  classical
  -- `M' ⊴ M`; in the §13 version this instance arrived through the packaging's import closure.
  haveI := derivedInG_subgroupOf_normal M
  have hηIKF0 := sOf_subset_inducedKernelFamily_bot hG hM data Y hη
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible member: the signed Dade image family, matched to `h46.tau` by `htau`
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hηIKF0
    exact
      { imageSet := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).imageSet
        mem_ZIrr := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).mem_ZIrr
        orthonormal := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).orthonormal
        image_eq := by
          rw [htau]
          exact (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).image_eq }
  · -- reducible member: (9.9.b) gives the column `χ₂ ≠ 1`, and `certainTypeR` its `2q`-family
    exact columnRFamily h46 (sOf_columnSum_of_not_irreducible data h46 hKeq hη hirr).choose_spec.1
      (sOf_columnSum_of_not_irreducible data h46 hKeq hη hirr).choose_spec.2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`sOf_memberRFamily` reduction, irreducible case**: for an irreducible member the dispatched
family *is* `S07.dadeOrthonormalCharacterImageFamilyOfDiff` (imageSet form).  The realness and
support proofs are existential — they are proof-irrelevant inputs to a proof-independent
`imageSet` — so the (5.2.e) lemmas apply after rewriting. -/
theorem sOf_memberRFamily_imageSet_of_irr [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M),
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hr hs).imageSet := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hηIKF0 := sOf_subset_inducedKernelFamily_bot hG hM data Y hη
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hηIKF0, ?_⟩
  unfold sOf_memberRFamily
  rw [dif_pos hirr]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`sOf_memberRFamily` reduction, column case**: for a reducible member the dispatched family
*is* `S06.certainTypeR` at the (9.9.b) column `χ₂` (imageSet form), exposed together with the
membership equation `η = μ_{χ₂}` — which is what supplies the `≠`-side conditions of the μ×μ and
μ×irr cross-orthogonality. -/
theorem sOf_memberRFamily_imageSet_of_col [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (hχ₂ : χ₂ ≠ 1),
      η = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∧
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet := by
  classical
  have hex := sOf_columnSum_of_not_irreducible data h46 hKeq hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold sOf_memberRFamily
  rw [dif_neg hcol]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Dade image of an `A₁`-supported function vanishes on the exceptional set `V`**, at
Hypothesis (4.6) generality.

`V ⊆ A₀` — the exceptional elements *are* Dade base points — so the explicit (2.5) evaluation
(`dadeValue_eq` at `a = v`, `h = 1`) reduces `α^τ(v)` to `α(v)`, which vanishes as soon as `α` is
supported on some set `A₁` that `V` avoids.

This is the (4.6)-level form of `S13.tau_apply_eq_zero_of_mem_typePV`, which fixes
`A₁ = A(M) = (M')^#` and reads the avoidance off `typePData_typePV_not_mem_derived`.  Keeping `A₁`
separate from the (4.6) ambient `A` matters: the members of `𝒮(Y)` have `(M')^#`-supported
differences, and for a type-uniform `A(M)` (i.e. `typePACore`) that is *strictly larger* than `A`,
so the §13 phrasing would not transfer. -/
theorem dadeICM_apply_eq_zero_of_avoidV [Finite G] {M : Subgroup G} {A : Set G}
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) h46.dade0)
    {α : ClassFunction ↥M ℂ}
    (hαA0 : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {A₁ : Set G} (hαA₁ : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ M)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) (hvA₁ : v ∉ A₁) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 tau α v = 0 := by
  classical
  have hvV : v ∈ h46.tic.V := by rw [h46.tic_V]; exact hv
  have hvA0 : v ∈ A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V :=
    Or.inr ⟨v, hvV, 1, M.one_mem, by group⟩
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 _ hαA0,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    h46.dade0.dadeValue_eq _ (a := ⟨v, hvA0⟩) (Subgroup.one_mem _) (by rw [mul_one])]
  by_contra hne
  exact hvA₁ (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
    (hαA₁ (ClassFunction.mem_support.mpr hne)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families over `𝒮(Y)`, at §9 level** — the
`hRorth` input of the norm-general (5.7) engine.

For members `φ, ξ` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the families `R(φ) ⊥ R(ξ)`: a `2×2` case split on
the member dichotomy.

* **irr × irr** — `S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`; the two extra scalars
  `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` are `star`-conjugates of `⟨φ, ξ̄⟩`, `⟨φ, ξ⟩`;
* **irr × column** / **column × irr** —
  `S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV` (irr-on-left via an
  `inner_conj_symm` swap), whose anchor is `dadeICM_apply_eq_zero_of_avoidV` at `A₁ = M'`;
* **column × column** — `S06.certainTypeR_imageSet_orthogonal_certainTypeR`, whose `χ₂ ≠ χ₂'` and
  `χ₂ ≠ χ₂'⁻¹` side conditions come from `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`: equality would force
  `φ = ξ` (resp. `φ = ξ̄` by `columnSum_conj_eq`) and the self-norm `w₁ ≠ 0`.

The §13 analogue is `S13.caseB_sOf_memberRFamily_orthogonal`.  The only genuinely ambient input
here is `hVsub`: the exceptional set `V` avoids `M'` (at the intended instantiation, exactly
`S10.typePData_typePV_not_mem_derived`).  **No type hypothesis appears.** -/
theorem sOf_memberRFamily_orthogonal [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {Y : Subgroup G} {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data Y) (hξ : ξ ∈ sOf data Y)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hφ).Orthogonal
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hξ) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  -- member differences are `M'`-supported (the `A₁` of the anchor), on top of being `A₀`-supported
  have hMderiv : ∀ {ζ : ClassFunction ↥M ℂ}, ζ ∈ sOf data Y →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        ((derivedInG M : Set G)) M) := fun {ζ} hζ =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      (fun _ hx _ => Subgroup.mem_subgroupOf.mp hx)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hζ)
  -- the anchor of the mixed stratum: `(ζ − ζ̄)^τ` vanishes on the exceptional `V`
  have hanchor : ∀ {ζ : ClassFunction ↥M ℂ}, ζ ∈ sOf data Y →
      ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (ζ - ζ.conj) v = 0 := by
    intro ζ hζ v hv
    have hflip : (ζ - ζ.conj : ClassFunction ↥M ℂ) = -(ζ.conj - ζ) := by abel
    refine dadeICM_apply_eq_zero_of_avoidV h46 _ ?_ ?_ hv (hVsub v hv)
    · rw [hflip, ClassFunction.support_neg]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp
        (sOf_subset_inducedKernelFamily_bot hG hM data Y hζ)
    · rw [hflip, ClassFunction.support_neg]
      exact hMderiv hζ
  have hw1ne : (Nat.card h46.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
      h46.dade0 hconj (x := ⟨φ, hφirr⟩) (χ := ⟨ξ, hξirr⟩) hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar
      α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨χ₂, hχ₂, -, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
      h46 hχ₂ (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      h46.dade0 hconj ⟨φ, hφirr⟩ hrφ hsφ (hanchor hφ) β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨χ₂, hχ₂, -, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
      h46 hχ₂ (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      h46.dade0 hconj ⟨ξ, hξirr⟩ hrξ hsξ (hanchor hξ) α hα β hβ
  · -- column × column
    obtain ⟨χ₂, hχ₂, hφcol, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨χ₂', hχ₂', hξcol, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    -- `χ₂ ≠ χ₂'`: else `φ = ξ` and `⟨φ, φ⟩ = w₁ ≠ 0` contradicts `h1`
    have hne1 : χ₂ ≠ χ₂' := by
      intro heq
      rw [hφcol, hξcol, heq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    -- `χ₂ ≠ χ₂'⁻¹`: else `φ = ξ̄` and `⟨φ, ξ̄⟩ = w₁ ≠ 0` contradicts `h2`
    have hne2 : χ₂ ≠ χ₂'⁻¹ := by
      intro heq
      rw [hφcol, hξcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq, heq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46 hχ₂ hχ₂'
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂').symm hne1 hne2 α hα β hβ

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every member of `𝒮(Y)` has natural-number self-norm** — `1` for an irreducible, `w₁` for a
(9.9.b) column `μ_{χ₂}` (`columnFamily_mu_sum_inner` on the diagonal).  This is the `hN` input of
the norm-general (5.7) engine, and the one place where being *norm-general* rather than
all-irreducible is visible. -/
theorem sOf_member_inner_self_natCast [Finite G] {M : Subgroup G} {A : Set G}
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y) :
    ∃ n : ℕ, ClassFunction.inner η η = (n : ℂ) := by
  classical
  by_cases hirr : IsIrreducibleCharacter η
  · exact ⟨1, by rw [hirr.inner_self_eq_one, Nat.cast_one]⟩
  · obtain ⟨χ₂, -, hcol⟩ := sOf_columnSum_of_not_irreducible data h46 hKeq hη hirr
    exact ⟨Nat.card h46.W1, by
      rw [hcol, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), case (9.7.b), at §9 level**: a uniform-degree `𝒮(Y)` is coherent on
`A₀(M)`.

The book's case (b) is two citations — "By (9.9.a) and (5.7), `𝒮(H₀C′)` is coherent" — and this is
that sentence: (9.9.a) supplies the uniform degree `d = qu` (the parameter `hunif`, discharged by
the type-free `S11.caseB_degree_qu`), and the norm-general (5.7) engine
`S07.uniform_degree_coherence_of_families` does the rest.  The engine is the norm-general one
because (9.9.b) puts *reducible* members (the columns `μ_j`) in `𝒮(H₀C′)`, so the all-irreducible
(5.7) wrapper does not apply — this is exactly why the `R`-family dispatch above was needed.

The §13 analogue is `S13.caseB_coherent_sOf_H0Cprime`, which anchors on a §10 μ-grid column
(`hyp.base.muColumnChar`) obtained through (11.7) `H₀ = 1` — available only in types III/IV.  Here
the pivot `η₁` is an explicit parameter: the book gets it from (9.9.b)'s count of reducible members,
which is genuine upstream content and is honest to expose rather than to re-derive from packaging
(the same pattern as the `2 ≤ ncard` parameter of `S15.Hypothesis.sSetIrrDeg_coherent`).

**No type hypothesis appears on this route.** -/
theorem sOf_caseB_coherent [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {Y : Subgroup G} (d : ℕ)
    (hunif : ∀ φ ∈ sOf data Y, ((φ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ)) (hd0 : d ≠ 0)
    {η₁ : ClassFunction ↥M ℂ} (hη₁ : η₁ ∈ sOf data Y) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) (sOf data Y)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ sOf data Y →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data Y hx
  -- every member difference is `A₀`-supported: pass through the pivot `η₁`
  have hsuppdiff : ∀ a ∈ sOf data Y, ∀ b ∈ sOf data Y,
      ((a - b : ClassFunction ↥M ℂ)).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    intro a ha b hb
    have ha1 := sOf_anchor_diff_support hG hM data Y hKsupp d hunif hη₁ ha
    have hb1 := sOf_anchor_diff_support hG hM data Y hKsupp d hunif hη₁ hb
    rw [show (a - b : ClassFunction ↥M ℂ) = (a - η₁) - (b - η₁) by abel]
    exact (ClassFunction.support_sub_subset _ _).trans (Set.union_subset ha1 hb1)
  have hnr : ∀ a ∈ sOf data Y, a ≠ (a : ClassFunction ↥M ℂ).conj := fun a ha h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _ (hIKF ha) h.symm
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families (sOf_finite data Y) hη₁
    (fun η hη => sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hη)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal (hIKF ha) (hIKF hb) hab)
    (sOf_closedUnderConjugate data Y) hnr
    (sOf_member_inner_self_natCast data h46 hKeq hη₁)
    (fun {φ ψ} hφ hψ => ?_) (fun a ha b hb => ?_) hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      sOf_memberRFamily_orthogonal hG hM data h46 hKeq hconj htau hKsupp hVsub hφ hξ h1 h2)
    (fun a ha => (hunif a ha).trans (hunif _ hη₁).symm)
    (by rw [hunif _ hη₁]; exact Nat.cast_ne_zero.mpr hd0)
    (fun h => absurd (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h) (fun hmem =>
      (OddOrder.Peterfalvi.S04.mem_sharp.mp (h46.dade0.subset_sharp hmem)).2 rfl))
    (sOf_closedUnderConjugate data Y hη₁) (Ne.symm (hnr _ hη₁))
  · -- `hiso`: the Dade lift is an isometry on `A₀`-supported functions
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0 hconj
      (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
      (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ)
  · -- `hZdiff`: supported differences of virtual characters have virtual images
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported h46.dade0 hconj
      (hsuppdiff a ha b hb)
      (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF ha))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hb)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11) in case (9.7.b)**: `𝒮(H₀C′)` is coherent, with the uniform degree supplied
by **(9.9.a)** — the book's "By (9.9.a) and (5.7)" verbatim.

Specializes `sOf_caseB_coherent` to the caseB Clifford datum: (9.9.a)
(`S11.caseB_degree_qu`, itself type-free) gives every member degree `qu`, and `qu ≠ 0` since `q` is
a subgroup order and `u` is odd.

Only the pivot `η₁` remains as a parameter.  The book takes it from **(9.9.b)** — `𝒮(H₀)` contains
exactly `p−1` reducible members `μ_j`, all lying in `𝒮(H₀C) ⊆ 𝒮(H₀C′)` — which is genuine upstream
content, not something to reconstruct from packaging (the §13 route reaches it only through (11.7)
`H₀ = 1`, i.e. types III/IV). -/
theorem caseB_coherent_sOf_cprime [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {η₁ : ClassFunction ↥M ℂ} (hη₁ : η₁ ∈ sOf data (chief.H0 ⊔ chars.Cprime)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (sOf data (chief.H0 ⊔ chars.Cprime))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :=
  sOf_caseB_coherent hG hM data h46 hKeq hconj htau hKsupp hVsub (data.q * chars.u)
    (caseB_degree_qu hG chars caseB)
    (mul_ne_zero Nat.card_pos.ne' (u_odd hG chars).pos.ne') hη₁

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A `𝒮(Y)`-member and its conjugate have the same degree.**

Members are inductions of irreducible characters, so `φ(1) = [M:M']·θ(1)` is a natural number
(`inducedKernelFamily_apply_one` + `exists_natDegree_charValue_one_dvd_card`) and conjugation fixes
it (`star` of a natural cast).

This is what makes the `A(M)`-descent below **branch-independent**: the (4.7) estimate
`inducedNonKernelFamily_diff_support` only needs the two degrees to agree, and `φ̄(1) = φ(1)` holds
for *every* member — no uniform-degree hypothesis required. -/
theorem sOf_conj_apply_one [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G)
    {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y) :
    ((η : ClassFunction ↥M ℂ).conj : ↥M → ℂ) 1 = (η : ↥M → ℂ) 1 := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  obtain ⟨θ, -, -, hη1⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_apply_one
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hη)
  obtain ⟨n, -, hn, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  have hnat : (η : ↥M → ℂ) 1 = ((((derivedInG M).subgroupOf M).index * n : ℕ) : ℂ) := by
    rw [hη1, hn]; push_cast; ring
  rw [ClassFunction.conj_apply, hnat]
  exact star_natCast _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Case (9.7.b) coherence, moved down to the `A(M)`-isometry** — the form (9.5) actually asks
for.

Hypothesis (9.5) says "τ the Dade isometry with respect to `(A(M), M, G)`", while `certainTypeR`
— hence `sOf_caseB_coherent` — produces its families for the *enlarged* `(4.6.e)` isometry on
`A₀ = A ∪ V^M`.  The book does not distinguish them because the `A`-Dade datum **is** the
restriction of the `A₀` one; in Lean that restriction has to be crossed explicitly, and this is the
crossing:

* `isCoherent_of_supportedSpan_le` shrinks the support `A₀ ⇝ A` (the containment is plain
  monotonicity, `A ⊆ A₀`), needing a nonzero `A`-supported witness in `ℤ[𝒮(Y)]`;
* `IsCoherent.congrMap` retargets the map, the two agreeing on `A`-supported functions by
  `S08.dadeIntegralCharacterMap_restrict_eq_of_support`.

The witness is `η̄ − η` for any member `η`: nonzero because a group of odd order has no real
characters, and `A`-supported by the (4.7) estimate `S10.inducedNonKernelFamily_diff_support`
through the (8.15.3) bridge — *not* merely `A₀`-supported.  That (4.7) sharpening is exactly what
makes the descent possible.

⚠ Note this runs the *opposite* way to the §13 use of `isCoherent_of_supportedSpan_le`
(`S13.certainTypeSet_isCoherent_A0`, which enlarges `A ⇝ A₀`); there the family is the certain-type
column set, here it is `𝒮(Y)`, and the target is the book's `A(M)`. -/
noncomputable def sOf_coherent_restrict [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    (h46c : OddOrder.Peterfalvi.S06.Hypothesis46Core A M)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    {Y : Subgroup G}
    (hKeq : h46c.K = (derivedInG M).subgroupOf M)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46c.subH)
    {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) (sOf data Y)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (h46.dade0.restrict Set.subset_union_left hAnorm)
        (h46.tau.restrict Set.subset_union_left hAnorm))
      (sOf data Y) (OddOrder.Peterfalvi.S04.supportInSubgroup A M) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  -- the conjugate difference of a member: `A`-supported by (4.7), nonzero by odd order
  have hmemNK : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ sOf data Y →
      x ∈ OddOrder.Peterfalvi.S10.inducedNonKernelFamily h46c.K h46c.subH := fun {_} hx =>
    OddOrder.Peterfalvi.S10.inducedNonKernelFamily_mono hHle
      (hKeq ▸ sOf_subset_inducedNonKernelFamily hG hM data Y hx)
  have hηc : (η : ClassFunction ↥M ℂ).conj ∈ sOf data Y :=
    sOf_closedUnderConjugate data Y hη
  have hwitsupp : ((η : ClassFunction ↥M ℂ).conj - η).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A M :=
    OddOrder.Peterfalvi.S10.inducedNonKernelFamily_diff_support h46c (hmemNK hηc) (hmemNK hη)
      (sOf_conj_apply_one hG hM data Y hη)
  have hwitne : ((η : ClassFunction ↥M ℂ).conj - η) ≠ 0 := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hη) (sub_eq_zero.mp h)
  refine (OddOrder.Peterfalvi.S07.isCoherent_of_supportedSpan_le hcoh
    (fun _ hφ => OddOrder.Peterfalvi.S07.zSupportedSpan_mono_right
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left) hφ)
    ⟨_, ⟨Submodule.sub_mem _ (Submodule.subset_span hηc) (Submodule.subset_span hη),
      hwitsupp⟩, hwitne⟩).congrMap (fun φ hφ => ?_)
  exact (OddOrder.Peterfalvi.S08.dadeIntegralCharacterMap_restrict_eq_of_support
    h46.dade0 h46.tau Set.subset_union_left hAnorm hφ.2).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮(H₀C′) ≠ ∅`** — the pivot of the (9.11) case (9.7.b) engine, from **(9.9.b)**.

The book's (9.9.b) says `𝒮(H₀)` *and* `𝒮(H₀C)` each contain exactly `p − 1` reducible characters
`μ_j`; since `C′ = [C,C] ≤ C`, the family `𝒮(H₀C)` sits inside `𝒮(H₀C′)` (`sOf_antitone`), so those
`μ_j` are members here too — and `p − 1 > 0` because `p` is prime.

Note the count is taken at `H₀C`, not `H₀`: the reducibles of `𝒮(H₀)` need not lie in the *smaller*
`𝒮(H₀C′)`, which is exactly why the book states (9.9.b) for both carriers.  The §13 route reaches
the same pivot through the §10 μ-grid and (11.7) `H₀ = 1`, hence only in types III/IV
(issue 1045). -/
theorem sOf_cprime_nonempty [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data} :
    (sOf data (chief.H0 ⊔ cprimeSub data chief)).Nonempty := by
  have hne : {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
      ¬ IsIrreducibleCharacter φ}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [reducible_count_sOf_H0supC hG chief]
    have := chief.p_prime.one_lt
    omega
  obtain ⟨φ, hφ, -⟩ := hne
  exact ⟨φ, sOf_antitone data (sup_le_sup_left (cprimeSub_le_C data chief) chief.H0) hφ⟩

/-! ### (5.5) for coherent extensions and the `coherent_ortho` cross-orthogonality -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) for a coherent subfamily of `𝒮(Y)`, at §9 level** (Coq
`mem_coherent_sum_subseq`, `PFsection5.v:957`) — the §9 form of
`S13.coherent_extension_eq_sum_memberRFamily`.

A coherent extension of `T ⊆ 𝒮(Y)` evaluates a member `ψ` (whose conjugate is also in `T`) as a
partial sum `∑_{α ∈ E} α` over the dispatched `R(ψ)`-family `sOf_memberRFamily`.  This is
`CharacterPsiDecomposition.ofProjection` at `ψ = 0` — the auxiliary isometry is the coherent
extension itself (isometric on `ℤ[T]`, agreeing with `τ` on the supported `ψ − ψ̄`) — closed by
`eq_sum_of_psi_eq_zero`.

The §13 version derives `ψ ≠ ψ̄` and the supportedness of `ψ − ψ̄` from the packaging's
`hyp.base.mderivSharp_subset_A0`; here they come from `hKsupp` and odd order, so **no type
hypothesis appears**. -/
theorem sOf_coherent_extension_eq_sum_memberRFamily [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {T : Set (ClassFunction ↥M ℂ)} (hTsub : T ⊆ sOf data Y)
    (c' : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) T
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M))
    {ψ : ClassFunction ↥M ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hψsOf := hTsub hψT
  have hψcsOf := hTsub hψcT
  have hψbot := sOf_subset_inducedKernelFamily_bot hG hM data Y hψsOf
  have hψcbot := sOf_subset_inducedKernelFamily_bot hG hM data Y hψcsOf
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : ψ ≠ ψ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (⊥ : Subgroup ↥M) hψbot h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hψbot hψcbot hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    rw [show (ψ - ψ.conj : ClassFunction ↥M ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hψbot
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥M ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hψsOf) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Cross-orthogonality of coherent images, at §9 level** (Coq `coherent_ortho`,
`PFsection5.v:986`) — the §9 form of `S13.coherent_extension_cross_orthogonal`.

For coherent subfamilies `T₁, T₂ ⊆ 𝒮(Y)` and members `ψ ∈ T₁`, `λ ∈ T₂` with `ψ ∉ {λ, λ̄}`
(so `⟨ψ, λ⟩ = ⟨ψ, λ̄⟩ = 0` by the family's pairwise orthogonality), the coherent images are
orthogonal: both are partial `R`-family sums by (5.5), and the `R`-families are cross-orthogonal
by (5.2.e) (`sOf_memberRFamily_orthogonal`).  **No type hypothesis appears.** -/
theorem sOf_coherent_extension_cross_orthogonal [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {Y : Subgroup G} {T₁ T₂ : Set (ClassFunction ↥M ℂ)}
    (hT₁sub : T₁ ⊆ sOf data Y) (hT₂sub : T₂ ⊆ sOf data Y)
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) T₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M))
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) T₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M))
    {ψ lam : ClassFunction ↥M ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have h1 : ClassFunction.inner ψ lam = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (sOf_subset_inducedKernelFamily_bot hG hM data Y (hT₁sub hψT))
      (sOf_subset_inducedKernelFamily_bot hG hM data Y (hT₂sub hlamT)) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (sOf_subset_inducedKernelFamily_bot hG hM data Y (hT₁sub hψT))
      (sOf_subset_inducedKernelFamily_bot hG hM data Y (hT₂sub hlamcT)) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ := sOf_coherent_extension_eq_sum_memberRFamily hG hM data h46
    hKeq hconj htau hKsupp hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ := sOf_coherent_extension_eq_sum_memberRFamily hG hM data h46
    hKeq hconj htau hKsupp hT₂sub c₂ hlamT hlamcT
  have horth := sOf_memberRFamily_orthogonal hG hM data h46 hKeq hconj htau hKsupp hVsub
    (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

end OddOrder.Peterfalvi.S11
