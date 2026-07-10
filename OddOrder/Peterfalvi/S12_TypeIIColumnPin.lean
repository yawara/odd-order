/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_TypeIIFrobenius
import OddOrder.Peterfalvi.S05_SigmaTrichotomy

/-!
# Peterfalvi (5.8) for the type-II `S`-side column: the `ν^{τ₂}` pin

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §5, (5.8);
Coq mirror `coherent_prDade_TIred` (`PFsection5.v:1371`).

For the (10.7) `T2 = {λ, λ̄, ν, ν̄}` family coherent over the `S`-side `A₀(S)`-Dade isometry
(`typeII_T2_coherent`), this file pins the coherent image of the reducible column
`ν = μ_{χ₂} = columnSum χ₂`: `ν^{τ₂}` is a **signed full grid column**,
`ν^{τ₂} = δ·∑_i ω_{χ₂,i}^σ` or `ν^{τ₂} = −δ·∑_i ω_{χ₂⁻¹,i}^σ` — the dichotomy of Coq's
(5.8), which suffices for the (10.7) cross-isometry package (the row/sign are packaged
existentially there).

The route (frontier note `notes/peterfalvi/s10_7_derived_frobenius.md`, update¹⁰):

1. **(5.5)** (`typeII_T2_extension_columnSum_eq_sum`, `…_lam_eq_single`): the coherent
   extension's values are subsums of the per-member `R`-families —
   `ν^{τ₂} = ∑_{α ∈ E} α` with `E ⊆ R(ν)`, `|E| = w₁`, and `λ^{τ₂} = ±(single Dade
   constituent)` (`|E'| = ‖λ‖² = 1`) — via `CharacterPsiDecomposition.ofProjection` +
   `eq_sum_of_psi_eq_zero`, mirroring the `M`-side `exists_muColumn_tau1_eq_sum_R`.
2. **`V`-vanishing**: `λ^{τ₂}` is orthogonal to the whole `σ`-grid (the (5.2.e) key brick),
   hence vanishes on `V`; the `zeta1`-trick (`zeta1 = λ(1)·ν − ν(1)·λ`, an `A(S)`-supported
   difference whose Dade image vanishes on `V` by the (8.16) base-point anchor) then
   transfers the vanishing to `ν^{τ₂}`.
3. **Endgame**: the landed (5.8) `σ`-coefficient machine
   `eq_smul_chiFam_column_of_vanishOnV` (S05) turns the two-column `{0, ±δ}` coefficient
   grid of `ν^{τ₂}` (from step 1) plus the `V`-vanishing (step 2), `‖ν^{τ₂}‖² = w₁` and
   Parseval into the full-column dichotomy.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

section ColumnPin

open OddOrder.BG.Ch3.S10

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the reducible `T2`-column `ν = μ_{χ₂}`** (mirror of the `M`-side
`Hypothesis.exists_muColumn_tau1_eq_sum_R`): the coherent extension of the (10.7) `T2`-family
sends `columnSum χ₂` to a subsum `∑_{α ∈ E} α` of its `R`-family `certainTypeR`, with
`|E| = ‖μ_{χ₂}‖² = w₁`.

Assembled from `CharacterPsiDecomposition.ofProjection` at `ψ = 0` (the `R`-family is the
landed `certainTypeR`; the lattice-relative isometry, `τ_S`-agreement on the `A₀(S)`-supported
`ν − ν̄`, and `ℤIrr`-membership are the `IsCoherent` fields; `⟨ν, ν̄⟩ = 0` is the cross-column
Gram entry) and `eq_sum_of_psi_eq_zero`. -/
theorem typeII_T2_extension_columnSum_eq_sum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    {χ₂ : ((typeIIHypothesis46 hG hSmax hSII data.typeP).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data.typeP).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data.typeP).W2)) →* ℂˣ}
    (hχ₂ne : χ₂ ≠ 1)
    (hkeq : nu = OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂) :
    ∃ E ⊆ (OddOrder.Peterfalvi.S06.certainTypeR
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).imageSet,
      c.extension nu = ∑ α ∈ E, α ∧
        (E.card : ℂ) = (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1 : ℂ) := by
  classical
  subst hkeq
  -- membership and support bookkeeping for `ν, ν̄ ∈ T2` (`ν` is now the column sum)
  have hνT2 : OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
      ∈ ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
        : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hνcT2 : (OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj
      ∈ ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
        : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  -- `⟨ν, ν̄⟩ = 0`: the cross-column Gram entry `χ₂ ≠ χ₂⁻¹`
  have hχχbar : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂)
      (OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne).symm]
  -- `ν − ν̄` is `ℤ[T2]` and `A₀(S)`-supported
  have hsuppmem : (OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
      - (OddOrder.Peterfalvi.S06.columnSum
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
          : Set (ClassFunction ↥S ℂ))
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
            ∪ conjClassSetIn S (typePV S data.typeP)) S) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hνT2)
      (Submodule.subset_span hνcT2), ?_⟩
    refine (diff_support_subset_of_support_subset_union_one (hT2supp _ hνT2)
      (hT2supp _ hνcT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one _ hνcT2, hT2one _ hνT2]
  -- the lattice-relative isometry on `zSpan {ν − ν̄, ν − 0}`
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      {OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
        - (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂ - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan
        ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
          : Set (ClassFunction ↥S ℂ)) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hνT2)
        (Submodule.subset_span hνcT2)
    · rw [sub_zero]; exact Submodule.subset_span hνT2
  -- assemble the (5.4) decomposition and apply (5.5)
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      (OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂) 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
      (OddOrder.Peterfalvi.S06.certainTypeR
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm)
      c.extension
      (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (c.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact c.extension_mem_ZIrr _ (Submodule.subset_span hνT2))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  have hDt : D.tau1 = c.extension := rfl
  obtain ⟨-, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  rw [hDt] at hτ1
  refine ⟨E, hEsub, by rw [← hEsum]; exact hτ1, ?_⟩
  rw [hEcard, OddOrder.Peterfalvi.S06.columnSum_def,
    OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the irreducible `T2`-member `λ`**: the coherent extension sends `λ`
to a **single** signed Dade constituent — `λ^{τ₂} = α` for some `α ∈ R(λ)`
(`|E| = ‖λ‖² = 1`).  Same `ofProjection` assembly as the column case, with the 2-element Dade
`R(λ)` and `⟨λ, λ̄⟩ = 0` from distinctness of the conjugate pair (odd order). -/
theorem typeII_T2_extension_lam_eq_single [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)) :
    ∃ (hr : ¬ ClassFunction.IsReal lam)
      (hs : (lam.conj - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)
      (α : ClassFunction G ℂ),
      α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
        ⟨lam, hlam_irr⟩ hr hs).imageSet ∧
      c.extension lam = α := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  have hlamT2 : lam ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert _ _
  have hlamcT2 : lam.conj ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  have hlamIKF : lam ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) (Y.subgroupOf S) :=
    typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  -- realness and difference-support of `λ`
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hs : (lam.conj - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S := by
    refine (diff_support_subset_of_support_subset_union_one (hT2supp lam.conj hlamcT2)
      (hT2supp lam hlamT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one lam.conj hlamcT2, hT2one lam hlamT2]
  -- `⟨λ, λ̄⟩ = 0`: distinct irreducibles (`λ ≠ λ̄` in odd order)
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hχχbar : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  -- `λ − λ̄ ∈ ℤ[T2, A₀]` and the span bound
  have hsuppmem : (lam - lam.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hlamT2)
      (Submodule.subset_span hlamcT2), ?_⟩
    refine (diff_support_subset_of_support_subset_union_one (hT2supp lam hlamT2)
      (hT2supp lam.conj hlamcT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one lam.conj hlamcT2, hT2one lam hlamT2]
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥S) {lam - lam.conj, lam - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan
        ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hlamT2)
        (Submodule.subset_span hlamcT2)
    · rw [sub_zero]; exact Submodule.subset_span hlamT2
  -- assemble and apply (5.5); `|E| = ‖λ‖² = 1` forces a singleton
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau) lam 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
        ⟨lam, hlam_irr⟩ hr hs)
      c.extension
      (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (c.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact c.extension_mem_ZIrr lam (Submodule.subset_span hlamT2))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  have hDt : D.tau1 = c.extension := rfl
  obtain ⟨-, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  rw [hDt] at hτ1
  have hlamnorm : ClassFunction.inner lam lam = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam, hlam_irr⟩
    rwa [if_pos rfl] at h
  have hE1 : E.card = 1 := by
    have : (E.card : ℂ) = 1 := by rw [hEcard, hlamnorm]
    exact_mod_cast this
  obtain ⟨α, hα⟩ := Finset.card_eq_one.mp hE1
  refine ⟨hr, hs, α, hEsub (by rw [hα]; exact Finset.mem_singleton_self α), ?_⟩
  rw [hτ1, hEsum, hα, Finset.sum_singleton]

set_option maxHeartbeats 800000 in
open scoped Classical FiniteInduce in
/-- **The `R(λ)`-members are orthogonal to the whole `σ`-grid** (Peterfalvi (5.3.b) for the
type-II `S`-side; standalone form of the key brick inside
`typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff`, quantified over *every* grid column
`χ₂'`): each Dade constituent `β` of `(χ − χ̄)^{τ_S}` satisfies `⟨β, ω_{χ₂',i}^σ⟩ = 0`.

With the (5.5) singleton form `λ^{τ₂} ∈ R(λ)` this makes `λ^{τ₂}` orthogonal to the whole
grid — the input of the (3.2.e) `V`-vanishing of `λ^{τ₂}` in the (5.8) `ν`-pin. -/
theorem typeII_dadeOfDiff_member_inner_omegaSigma_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    (χ : IrreducibleCharacter ↥S)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥S ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    (hdiffsuppχ : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data)) S)
    {β : ClassFunction G ℂ}
    (hβ : β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)
      χ hrealχ hdiffsuppχ).imageSet)
    (χ₂' : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
      ((typeIIHypothesis46 hG hSmax hSII data).W1 ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ)
    (i : Fin (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)) :
    ClassFunction.inner β
      (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma
        (typeIIHypothesis46 hG hSmax hSII data) χ₂' i) = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W2
    omega
  -- core disjointness brick (as in the landed cross lemma)
  have key : ∀ {c c' : ℂ} {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G →
      ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
        (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma
          (typeIIHypothesis46 hG hSmax hSII data) χ₂' i) = 0 := by
    intro c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact OddOrder.Peterfalvi.S08.inner_smul_chiFam_eq_zero_of_diff_vanishOnV
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (typeIIHypothesis46 hG hSmax hSII data))
      hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish hmin _
  -- `(χ − χ̄)^{τ_S}` vanishes on `V` (the type-II anchor)
  have hsuppsub : (((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
    rw [show (χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj =
        -((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  have htauvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data).dade0 (typeIIHypothesis46 hG hSmax hSII data).tau
        ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data hsuppsub hv
  -- capture the two-element `R(χ)` abstractly and split the membership
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIHypothesis46 hG hSmax hSII data).dade0
          ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)))
        (χ : ClassFunction ↥S ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            (typeIIHypothesis46 hG hSmax hSII data).dade0
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data) χ hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIHypothesis46 hG hSmax hSII data).dade0
      ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data))
      ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hvanishμν : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · rw [show cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction from
      (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm]
    exact key hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν
  · rw [show (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction by
      rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]]
    exact key hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ

end ColumnPin

end OddOrder.Peterfalvi.S12
