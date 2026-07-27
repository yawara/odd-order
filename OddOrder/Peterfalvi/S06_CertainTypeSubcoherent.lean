/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeCoherence
import OddOrder.Peterfalvi.S06_CertainTypeSupport

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

/-! ### The (5.2.d) dispatcher on the induction family -/

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

Both branches are pinned by the member alone: the irreducible one depends only on `χ` (and
proofs), the reducible one only through its column, which `columnSum_injective` determines
(`columnR_imageSet_congr`).  The `imageSet` of each branch is read off by
`inducedR_imageSet_of_irreducible` / `inducedR_imageSet_of_not_irreducible`, which is all the
(5.2.e) clause needs (`Orthogonal` is stated on `imageSet`). -/
noncomputable def inducedR [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {θ : IrreducibleCharacter ↥h.K} (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)))
    (hdiffsupp : ((ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).conj
        - ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau)
      (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)) :=
  if hirr : IsIrreducibleCharacter (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)) then
    S07.dadeOrthonormalCharacterImageFamilyOfDiff h.dade0
      (⟨ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ), hirr⟩ : IrreducibleCharacter ↥L)
      hreal hdiffsupp
  else
    columnR h (exists_ne_one_induce_eq_columnSum h hθ hirr).choose_spec.1
      (exists_ne_one_induce_eq_columnSum h hθ hirr).choose_spec.2

open scoped Classical in
/-- The **irreducible branch** of `inducedR`: `R(χ)` is the two-element (5.3)(a) Dade image. -/
theorem inducedR_imageSet_of_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {θ : IrreducibleCharacter ↥h.K} (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)))
    (hdiffsupp : ((ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).conj
        - ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    (hirr : IsIrreducibleCharacter (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))) :
    (inducedR h hθ hreal hdiffsupp).imageSet
      = (S07.dadeOrthonormalCharacterImageFamilyOfDiff h.dade0
          (⟨ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ), hirr⟩ : IrreducibleCharacter ↥L)
          hreal hdiffsupp).imageSet := by
  rw [inducedR, dif_pos hirr]

open scoped Classical in
/-- The **reducible branch** of `inducedR`: `R(χ) = R(μ_j)` is the (4.9) column family of the
column `χ₂` presenting `χ` as `μ_j`.  Stated for an *arbitrary* presentation `χ = columnSum χ₂`,
which `columnSum_injective` shows is unique (`columnR_imageSet_congr`). -/
theorem inducedR_imageSet_of_not_irreducible [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {θ : IrreducibleCharacter ↥h.K} (hθ : θ ≠ trivialIrreducibleCharacter ↥h.K)
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)))
    (hdiffsupp : ((ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).conj
        - ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    (hirr : ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)))
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hcol : ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ) = columnSum h χ₂) :
    (inducedR h hθ hreal hdiffsupp).imageSet
      = (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet := by
  rw [inducedR, dif_neg hirr]
  exact columnR_imageSet_congr h _ hχ₂ _ hcol

end

end OddOrder.Peterfalvi.S06
