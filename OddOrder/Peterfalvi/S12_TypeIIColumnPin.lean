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

end ColumnPin

end OddOrder.Peterfalvi.S12
