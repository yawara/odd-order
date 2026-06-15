/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence2

/-!
# Peterfalvi §8: Case (B) coherence — the per-`φ` constituent dispatch and `X ∪ Y` assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2.3)** core of the (6.8) coherence capstone.

This continues `S08_CaseBCoherence2` (which holds the (6.8.2.2) aggregate, the positive-weight
subtype index, both decomposition branches `columnDecompositionTau` / `irreducibleDecompositionTau`,
and the route-independent anchored-image skeleton `per_phi_anchored_image`).  Here we build the
**mixed per-`φ` family** by dispatching each constituent `θ` of `Ind^L_K φ` to the column branch
(when `Ind^L_H θ = μ_j` is a reducible certain-type column, `θ = Res_H μ_{0j}`) or the irreducible
branch (when `Ind^L_H θ ∈ Irr L`), and assemble the (6.8.2.3) anchored image
`(χᵢ − aᵢ·η₁)^{hyp.tau} = Xᵢ − aᵢ·Y₀` over the whole family.

The constituent dichotomy is taken at the *value* level (`columnSum h46 χ₂ = Ind^L_H θ`, an equation
of class functions on `L`) to avoid the `↥h46.K` vs `↥H` type-mismatch of the index-level form
`chiRestrict χ₂ = θ` (`h46.K = H` is only a propositional equality).

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 41 cont.⁷ 続⁵+").
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The `tau1` field of a (5.4) decomposition is unchanged when its `χ`-index is transported along
an equality `χ = χ'` (the field type `IntegralCharacterMap ↥L G` does not mention `χ`).  Used to
read off `tau1 = hyp.tau` through the column-branch index cast of the per-constituent dispatch. -/
theorem charPsiDecomp_eqRec_tau1
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ χ' ψ : ClassFunction ↥L ℂ} (h : χ = χ')
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) :
    (h ▸ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ' ψ).tau1 = D.tau1 := by
  cases h; rfl

/-- **(6.8.2.3) per-constituent decomposition (mixed dispatch).**  For a constituent `θ : Irr H` of
`Ind^L_K φ` (with `K = H`, case (c2)), the (5.4) decomposition data of `Ind^L_H θ` against the
Sibley–Dade map `hyp.tau`, dispatched on whether `Ind^L_H θ` is a reducible certain-type column
`μ_j = columnSum h46 χ₂` or an irreducible induced character:

* **column branch** (`∃ χ₂ ≠ 1, columnSum h46 χ₂ = Ind^L_H θ`): `columnDecompositionTau` (the
  rebuilt certain-type `R(μ_j)` family), with the column character rewritten to `Ind^L_H θ` along
  the witness equation;
* **irreducible branch** (no nontrivial column equals `Ind^L_H θ`): `irreducibleDecompositionTau`
  (`decompositionDaFromDadeOfDiff hyp.dade hyp.hconj`).

Both branches land in the *same* map `hyp.tau`, so the family
`fun i => caseB_constituentDecomposition …` feeds the pinning `per_phi_anchored_image`.  The per-`θ`
structural hypotheses of each branch are supplied by the (conditional) bundles `hcol` / `hirr`; they
are discharged at the family construction
from the §5/§6 X-member machinery (column: certain-type `(4.9)` reflection; irreducible: as in the
case-A Dade chain). -/
noncomputable def caseB_constituentDecomposition
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) →
      (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (a • η₁) := by
  classical
  by_cases hcase : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · -- column branch: the witness `χ₂` is extracted by choice (the goal is `Type`-valued, so a
    -- direct `obtain` on the `Prop`-`∃` would be an illegal large elimination).  The decomposition
    -- bundle is consumed by `.1`/`.2.…` projections (not `obtain`/`And.casesOn`) so that the `tau1`
    -- field reduces through `caseB_constituentDecomposition_tau1`; the index is cast by `heq ▸`.
    have hχ₂ne := hcase.choose_spec.1
    have heq := hcase.choose_spec.2
    have hb := hcol _ hχ₂ne heq
    exact heq ▸ columnDecompositionTau hyp h46 hχ₂ne hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2.1 hb.2.2.2.2.2
  · -- irreducible branch: no nontrivial column equals `Ind^L_H θ`
    have hnc : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
      fun χ₂ hne heq2 => hcase ⟨χ₂, hne, heq2⟩
    have hb := hirr hnc
    exact irreducibleDecompositionTau hyp θ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
      hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2

/-- The `tau1` field of `caseB_constituentDecomposition` is `hyp.tau`, in both dispatch branches
(`columnDecompositionTau`/`irreducibleDecompositionTau` both build via `ofProjection … hyp.tau …`,
and `hyp.tau = dadeIntegralCharacterMap hyp.dade …`).  This is the `htau1` input of
`per_phi_anchored_image` for the mixed per-`φ` family. -/
theorem caseB_constituentDecomposition_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    {hcol _hirr} :
    (caseB_constituentDecomposition (a := a) (η₁ := η₁) hyp h46 θ hcol _hirr).tau1 = hyp.tau := by
  unfold caseB_constituentDecomposition
  split
  · rw [charPsiDecomp_eqRec_tau1]; rfl
  · rfl

end OddOrder.Peterfalvi.S08
