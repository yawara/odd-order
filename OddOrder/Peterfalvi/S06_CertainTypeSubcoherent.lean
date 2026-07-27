/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeCoherence
import OddOrder.Peterfalvi.S06_CertainTypeSupport
import OddOrder.Peterfalvi.S08_CrossOrthogonality
import OddOrder.Peterfalvi.S08_InducedKernelFamily

/-!
# Peterfalvi (5.3)(b): subcoherence of an induction family over Hypothesis (4.6)

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§5, p. 26, Theorem (5.3)(b).

> **(5.3)(b)** Assume Hypothesis (4.6), (5.2.a) and that
> `𝒮 ⊆ {Ind_H^L θ | θ ∈ Irr H, H ⊄ Ker θ}`.  Then **Hypothesis (5.2) holds**, with the isometry
> `τ` of (5.2) being the restriction to `ℤ[𝒮, L^#]` of the isometry `τ` of Hypothesis (4.6).

The book's proof splits the (5.2.d) clause `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α` by reducibility of the
member `χ = Ind_K^L θ`:

* `χ` **irreducible** — the two-element image of (5.3)(a), `R(χ) = {ε·μ, −ε·ν}`;
* `χ` **reducible** — by (4.4)+(4.5) the source `θ` is one of the certain-type columns
  `θ = χ_j` (`chiRestrict χ₂`), so `χ = μ_j` is a column sum and (4.9) supplies the `2w₁`-element
  family `R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ | 0 ≤ i < w₁}`.

This file builds the **reducible branch** at the Hypothesis (4.6) level (issue 0159): the
classification `induce_not_isIrreducible_iff` identifies the source as a nontrivial column, and
`certainTypeR` then supplies the image family.  Note that `certainTypeR`'s degree side condition
`hdeg` is discharged *unconditionally* here by `columnSum_inv_apply_one` (the conjugate column has
the same degree), so the reducible branch needs no hypothesis beyond `θ ≠ 1_K` and reducibility.

Being able to state (5.2.d) with a variable-size `R(χ)` at all is what
`S07.GeneralHypothesis` (issue 0157) added; the fixed two-element `S07.Hypothesis` record cannot
hold the `2w₁`-element reducible family.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`; issue 0159.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-! ### The reducible members of the induction family are the nontrivial columns -/

/-- **Peterfalvi (5.3)(b), reducible-source classification** (the (4.4)+(4.5) input of the
(5.2.d) case split).  A nontrivial `θ ∈ Irr(K)` whose induction `Ind_K^L θ` is *reducible* is one
of the certain-type columns `χ_j = chiRestrict χ₂` with `χ₂ ≠ 1`, and then `Ind_K^L θ` is the
column character `μ_j = columnSum χ₂`.

`induce_not_isIrreducible_iff` ((4.5.b)) produces the column `χ₂`; it is nontrivial because the
trivial column restricts to `1_K` (`chiRestrict_one_eq_trivial`, the (4.4) anchor), which `θ ≠ 1_K`
excludes; and `induce_restrict_certainType_eq` ((4.5.a)) evaluates the induction as the column
sum. -/
theorem exists_ne_one_induce_eq_columnSum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥h.K} (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hred : ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))) :
    ∃ χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ) = columnSum h χ₂ := by
  obtain ⟨χ₂, hχ₂⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  refine ⟨χ₂, ?_, ?_⟩
  · rintro rfl
    exact hθ (hχ₂ ▸ h.chiRestrict_one_eq_trivial)
  · rw [← hχ₂, h.coe_chiRestrict, h.induce_restrict_certainType_eq, columnSum_def]

/-! ### The reducible branch of (5.2.d) -/

/-- **Peterfalvi (5.3)(b), the reducible `R(χ)`** (issue 0159).  For a nontrivial column
`χ₂ ≠ 1`, any character `φ` equal to the column sum `μ_j = columnSum χ₂` carries the (4.9)
orthonormal difference-image family `R(μ_j)` of clause (5.2.d).

This is `certainTypeR` transported along `hφ : φ = columnSum h χ₂`, with the degree side condition
supplied for free: `certainTypeR` asks for `μ_j(1) = μ̄_j(1)`, which is
`columnSum_inv_apply_one` (the conjugate column `μ_{j⁻¹}` has the same degree, being the complex
conjugate of a sum of positive integers).  Only `image_eq` mentions `φ`, so the transport keeps
`imageSet` definitionally the `certainTypeR` one — which matters because the (5.2.e)
cross-orthogonality lemmas (`certainTypeR_imageSet_orthogonal_certainTypeR`) are stated on
`imageSet`. -/
noncomputable def columnR (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ = columnSum h χ₂) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau) φ where
  imageSet := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet
  mem_ZIrr := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).mem_ZIrr
  orthonormal := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).orthonormal
  image_eq := by
    rw [hφ]
    exact (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).image_eq

/-- The reducible branch is pinned by its column: since `columnSum` is injective
(`columnSum_injective`), any two presentations `φ = μ_j = μ_k` of the same member give the same
family, so `columnR` is well defined on the member alone. -/
theorem columnR_imageSet_congr (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ = columnSum h χ₂) (hφ' : φ = columnSum h χ₂') :
    (columnR h hχ₂ hφ).imageSet = (columnR h hχ₂' hφ').imageSet := by
  obtain rfl : χ₂ = χ₂' := columnSum_injective h (hφ ▸ hφ')
  rfl

@[simp] theorem columnR_imageSet (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ = columnSum h χ₂) :
    (columnR h hχ₂ hφ).imageSet
      = (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet :=
  rfl

/-! ### (5.2.d): the difference image of an induction-family member -/

section /- (5.2.d): irreducible / reducible dispatch (Peterfalvi (5.3)(b), p. 26) -/

variable (h : Hypothesis46 A L)

open scoped Classical in
/-- **Peterfalvi (5.3)(b), clause (5.2.d)**: the difference image `R(χ)` of a member
`χ = Ind_K^L θ` of the induction family (`θ ∈ Irr K`, `θ ≠ 1_K`).

The book's case split, verbatim:

* `χ` **irreducible** — `R(χ) = {ε·μ, −ε·ν}` is the two-element (5.3)(a) image, produced by the
  Dade difference datum `dadeOrthonormalCharacterImageFamilyOfDiff`;
* `χ` **reducible** — by (4.4)+(4.5) the source is a nontrivial column
  (`exists_ne_one_induce_eq_columnSum`) and (4.9) supplies the `2w₁`-element `R(μ_j)`
  (`columnR`).

Both branches are pinned by the member `χ` alone, *not* by the presentation `θ`: the irreducible
one mentions only `χ` (and proofs, which are irrelevant), the reducible one only its column,
which `columnSum_injective` determines (`columnR_imageSet_congr`).  That is what
`inducedR_imageSet_of_irreducible` / `inducedR_imageSet_of_not_irreducible` record, and it is all
the (5.2.e) clause needs — `OrthonormalCharacterImageFamily.Orthogonal` is stated on
`imageSet`. -/
noncomputable def inducedR [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ : ClassFunction ↥L ℂ} {θ : IrreducibleCharacter ↥h.K}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hχθ : χ = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))
    (hreal : ¬ ClassFunction.IsReal χ)
    (hdiffsupp : (χ.conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau) χ :=
  if hirr : IsIrreducibleCharacter χ then
    S07.dadeOrthonormalCharacterImageFamilyOfDiff h.dade0
      (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) hreal hdiffsupp
  else
    columnR h (exists_ne_one_induce_eq_columnSum h hθ (hχθ ▸ hirr)).choose_spec.1
      (hχθ.trans (exists_ne_one_induce_eq_columnSum h hθ (hχθ ▸ hirr)).choose_spec.2)

open scoped Classical in
/-- The **irreducible branch** of `inducedR`: `R(χ)` is the two-element (5.3)(a) Dade image, which
depends on the member `χ` only. -/
theorem inducedR_imageSet_of_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ : ClassFunction ↥L ℂ} {θ : IrreducibleCharacter ↥h.K}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hχθ : χ = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))
    (hreal : ¬ ClassFunction.IsReal χ)
    (hdiffsupp : (χ.conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    (hirr : IsIrreducibleCharacter χ) :
    (inducedR h hθ hχθ hreal hdiffsupp).imageSet
      = (S07.dadeOrthonormalCharacterImageFamilyOfDiff h.dade0
          (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) hreal hdiffsupp).imageSet := by
  rw [inducedR, dif_pos hirr]

open scoped Classical in
/-- The **reducible branch** of `inducedR`: `R(χ) = R(μ_j)` is the (4.9) column family.  Stated
for an *arbitrary* presentation `χ = columnSum χ₂`, unique by `columnSum_injective`. -/
theorem inducedR_imageSet_of_not_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ : ClassFunction ↥L ℂ} {θ : IrreducibleCharacter ↥h.K}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hχθ : χ = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))
    (hreal : ¬ ClassFunction.IsReal χ)
    (hdiffsupp : (χ.conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    (hirr : ¬ IsIrreducibleCharacter χ)
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hcol : χ = columnSum h χ₂) :
    (inducedR h hθ hχθ hreal hdiffsupp).imageSet
      = (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet := by
  rw [inducedR, dif_neg hirr]
  exact columnR_imageSet_congr h _ hχ₂ _ hcol

end
/-! ### (5.3)(b): Hypothesis (5.2) for an induction family -/

section /- (5.3)(b): the capstone (Peterfalvi, p. 26) -/

variable (h : Hypothesis46 A L)

/-- The `A₀ = A ∪ V^L` support set of the (4.6) Dade datum `h.dade0`, in which the (5.2.b)
isometry and the (5.2.d) difference supports live. -/
abbrev supportSet : Set ↥L :=
  OddOrder.Peterfalvi.S04.supportInSubgroup
    (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L

/-- **Reducible members of the induction family are columns** (the membership form of
`exists_ne_one_induce_eq_columnSum`). -/
theorem exists_column_of_mem_of_not_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily h.K ⊥)
    (hirr : ¬ IsIrreducibleCharacter χ) :
    ∃ χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ₂ ≠ 1 ∧ χ = columnSum h χ₂ := by
  obtain ⟨θ, hθ, -, rfl⟩ := hχ
  exact exists_ne_one_induce_eq_columnSum h hθ hirr

variable {S : Set (ClassFunction ↥L ℂ)}

open scoped Classical in
/-- **Peterfalvi (5.3)(b), clause (5.2.d) on a family**: the difference image of a member of
`𝒮 ⊆ {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1_K}`, obtained by feeding `inducedR` the presentation carried
by the family membership.  Which presentation is picked is immaterial —
`memberR_imageSet_of_irreducible` / `memberR_imageSet_of_not_irreducible` read the `imageSet` off
the member alone. -/
noncomputable def memberR [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (hSsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily h.K ⊥)
    (hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hdiffsupp : ∀ ⦃χ : ClassFunction ↥L ℂ⦄, χ ∈ S →
      (χ.conj - χ).support ⊆ supportSet h)
    ⦃χ : ClassFunction ↥L ℂ⦄ (hχ : χ ∈ S) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau) χ :=
  inducedR h (hSsub hχ).choose_spec.1 (hSsub hχ).choose_spec.2.2 (hnoreal hχ) (hdiffsupp hχ)

open scoped Classical in
theorem memberR_imageSet_of_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (hSsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily h.K ⊥)
    (hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hdiffsupp : ∀ ⦃χ : ClassFunction ↥L ℂ⦄, χ ∈ S →
      (χ.conj - χ).support ⊆ supportSet h)
    ⦃χ : ClassFunction ↥L ℂ⦄ (hχ : χ ∈ S) (hirr : IsIrreducibleCharacter χ) :
    (memberR h hSsub hnoreal hdiffsupp hχ).imageSet
      = (S07.dadeOrthonormalCharacterImageFamilyOfDiff h.dade0
          (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) (hnoreal hχ) (hdiffsupp hχ)).imageSet :=
  inducedR_imageSet_of_irreducible h _ _ _ _ hirr

open scoped Classical in
theorem memberR_imageSet_of_not_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (hSsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily h.K ⊥)
    (hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hdiffsupp : ∀ ⦃χ : ClassFunction ↥L ℂ⦄, χ ∈ S →
      (χ.conj - χ).support ⊆ supportSet h)
    ⦃χ : ClassFunction ↥L ℂ⦄ (hχ : χ ∈ S) (hirr : ¬ IsIrreducibleCharacter χ)
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hcol : χ = columnSum h χ₂) :
    (memberR h hSsub hnoreal hdiffsupp hχ).imageSet
      = (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet :=
  inducedR_imageSet_of_not_irreducible h _ _ _ _ hirr hχ₂ hcol

open scoped Classical in
/-- **Peterfalvi (5.3)(b)** (p. 26): Hypothesis (5.2) holds for a family of induced characters.

> Assume Hypothesis (4.6), (5.2.a) and that `𝒮 ⊆ {Ind_H^L θ | θ ∈ Irr H, H ⊄ Ker θ}`.  Then
> Hypothesis (5.2) holds, with the isometry `τ` of (5.2) being the restriction to `ℤ[𝒮, L^#]` of
> the isometry `τ` of Hypothesis (4.6).

Field by field:

* **(5.2.b)** `tau` is the (4.6) Dade isometry `dadeIntegralCharacterMap h.dade0 h.tau`, and the
  restriction to `ℤ[𝒮, A₀]` is an isometry *unconditionally* —
  `dadeIntegralCharacterMap_inner_eq_of_supported` needs only the supportedness half of
  `zSupportedSpan` membership, no hypothesis on `𝒮`.
* **(5.2.a)** `conjugate_closed`, `no_real_characters` are the book's standing assumption.
* **(5.2.c)** `pairwise_orthogonal` — the book derives this from (1.5.c); here it is a hypothesis,
  matching the (5.3)(a) assembler `S07.irrSubcoherent`.
* **(5.2.d)** `memberR`: irreducible members get the two-element (5.3)(a) Dade image, reducible
  ones the `2w₁`-element column family `R(μ_j)` of (4.9).  This is the clause that needs
  `GeneralHypothesis` rather than `S07.Hypothesis`: the two-element record cannot hold `R(μ_j)`.
* **(5.2.e)** the four strata of cross-orthogonality, each already available at (4.6) generality:
  irreducible × irreducible `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`, the two mixed
  ones `certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV` (and its swap), and
  reducible × reducible `certainTypeR_imageSet_orthogonal_certainTypeR`.  The reducible × reducible
  side conditions — the columns of `φ` and `χ` being distinct and non-inverse — are read off the
  Gram matrix from the two orthogonality hypotheses (`ne_of_columnSum_inner_eq_zero`).

The one genuine input beyond (5.2.a)/(5.2.c) is `hvanish`, the **anchor**: `(χ − χ̄)^τ` vanishes on
the exceptional set `V` of `ticVdiff h` for irreducible members.  This is where the book's
`NC((φ − φ̄)^τ) ≤ 2` + (3.8) argument enters; the repo isolates it as the single ambient input of
the mixed (5.2.e) stratum (see `S08_CrossOrthogonality`, whose three call sites each discharge it
by their own route). -/
noncomputable def toGeneralHypothesis [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (hSsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily h.K ⊥)
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S)
    (hdiffsupp : ∀ ⦃χ : ClassFunction ↥L ℂ⦄, χ ∈ S →
      (χ.conj - χ).support ⊆ supportSet h)
    (hvanish : ∀ ⦃χ : ClassFunction ↥L ℂ⦄, χ ∈ S → IsIrreducibleCharacter χ →
      ∀ v ∈ (ticVdiff h).V,
        S07.dadeIntegralCharacterMap h.dade0 h.tau (χ - χ.conj) v = 0) :
    S07.GeneralHypothesis (L := ↥L) (G := G) S (supportSet h) where
  tau := S07.dadeIntegralCharacterMap h.dade0 h.tau
  tau_isometry_diff := fun {_φ _ψ} hφ hψ =>
    S07.dadeIntegralCharacterMap_inner_eq_of_supported h.dade0 hφ.2 hψ.2
  conjugate_closed := hconj
  no_real_characters := hnoreal
  pairwise_orthogonal := hortho
  difference_image := memberR h hSsub hnoreal hdiffsupp
  difference_images_orthogonal := by
    intro φ χ hφ hχ h1 h2 α hα β hβ
    -- the two conjugated orthogonalities `⟨φ̄, χ⟩ = ⟨φ̄, χ̄⟩ = 0`
    have h3 : ClassFunction.inner φ.conj χ = 0 := by
      have hcc := OddOrder.RepresentationTheory.inner_conj_conj φ χ.conj
      rw [ClassFunction.conj_conj] at hcc
      rw [hcc, h2, star_zero]
    have h4 : ClassFunction.inner φ.conj χ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_conj, h1, star_zero]
    by_cases hφirr : IsIrreducibleCharacter φ
    · by_cases hχirr : IsIrreducibleCharacter χ
      · -- irreducible × irreducible
        rw [memberR_imageSet_of_irreducible h hSsub hnoreal hdiffsupp hφ hφirr] at hα
        rw [memberR_imageSet_of_irreducible h hSsub hnoreal hdiffsupp hχ hχirr] at hβ
        exact OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
          h.dade0 (x := ⟨φ, hφirr⟩) (χ := ⟨χ, hχirr⟩)
          (hnoreal hφ) (hdiffsupp hφ) (hnoreal hχ) (hdiffsupp hχ) h1 h2 h3 h4 α hα β hβ
      · -- irreducible × reducible
        obtain ⟨χ₂', hne', hcol'⟩ := exists_column_of_mem_of_not_irreducible h (hSsub hχ) hχirr
        rw [memberR_imageSet_of_irreducible h hSsub hnoreal hdiffsupp hφ hφirr] at hα
        rw [memberR_imageSet_of_not_irreducible h hSsub hnoreal hdiffsupp hχ hχirr hne' hcol']
          at hβ
        exact OddOrder.Peterfalvi.S08.dadeOfDiff_imageSet_orthogonal_certainTypeR_of_vanishOnV
          h hne' (columnSum_inv_apply_one h χ₂').symm h.dade0 ⟨φ, hφirr⟩
          (hnoreal hφ) (hdiffsupp hφ) (hvanish hφ hφirr) α hα β hβ
    · obtain ⟨χ₂, hne, hcol⟩ := exists_column_of_mem_of_not_irreducible h (hSsub hφ) hφirr
      by_cases hχirr : IsIrreducibleCharacter χ
      · -- reducible × irreducible
        rw [memberR_imageSet_of_not_irreducible h hSsub hnoreal hdiffsupp hφ hφirr hne hcol] at hα
        rw [memberR_imageSet_of_irreducible h hSsub hnoreal hdiffsupp hχ hχirr] at hβ
        exact OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
          h hne (columnSum_inv_apply_one h χ₂).symm h.dade0 ⟨χ, hχirr⟩
          (hnoreal hχ) (hdiffsupp hχ) (hvanish hχ hχirr) α hα β hβ
      · -- reducible × reducible: read the column disjointness off the Gram matrix
        obtain ⟨χ₂', hne', hcol'⟩ := exists_column_of_mem_of_not_irreducible h (hSsub hχ) hχirr
        rw [memberR_imageSet_of_not_irreducible h hSsub hnoreal hdiffsupp hφ hφirr hne hcol] at hα
        rw [memberR_imageSet_of_not_irreducible h hSsub hnoreal hdiffsupp hχ hχirr hne' hcol']
          at hβ
        have hd1 : χ₂ ≠ χ₂' :=
          ne_of_columnSum_inner_eq_zero h (by rw [← hcol, ← hcol']; exact h1)
        have hd2 : χ₂ ≠ χ₂'⁻¹ :=
          ne_of_columnSum_inner_eq_zero h (by
            rw [← hcol, ← columnSum_conj_eq, ← hcol']; exact h2)
        exact certainTypeR_imageSet_orthogonal_certainTypeR h hne hne'
          (columnSum_inv_apply_one h χ₂).symm (columnSum_inv_apply_one h χ₂').symm
          hd1 hd2 α hα β hβ

end

end OddOrder.Peterfalvi.S06
