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

/-- **(6.8.2.3) the mixed per-`φ` decomposition family.**  Over the positive-weight subtype
`{θ : Irr H // 0 < aθ}` (`aθ = ⟨φ, Res^H_{W₂} θ⟩`), each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ`
is decomposed against `hyp.tau` by the per-`θ` dispatch `caseB_constituentDecomposition` (column /
irreducible).  This is the family `D` fed to `caseB_per_phi_anchored`; its `tau1 = hyp.tau` is
`caseB_constituentDecomposition_tau1`.  The per-`θ` column/irreducible bundles `hcol`/`hirr` are the
genuine §5/§6 discharge (supplied at the capstone). -/
noncomputable def caseB_phi_family
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        = ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) →
      (∑ k, ((h46.columnFamily χ₂).mu k : ClassFunction ↥L ℂ) 1
          = ∑ k, ((h46.columnFamily χ₂⁻¹).mu k : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - constituentWeight hφ' i.val • η₁}
            : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)) :
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁) :=
  fun i => caseB_constituentDecomposition hyp h46 i.val (hcol i) (hirr i)

/-- The mixed per-`φ` family lands in `tau1 = hyp.tau` at every constituent — the `htau1` input of
`caseB_per_phi_anchored`. -/
theorem caseB_phi_family_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} {hcol _hirr}
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    (caseB_phi_family hyp h46 hW2H hφ' (η₁ := η₁) hcol _hirr i).tau1 = hyp.tau :=
  caseB_constituentDecomposition_tau1 hyp h46 i.val

/-- **(6.8.2.3) seam-1 orthogonality, column branch.**
`⟨(columnDecompositionTau …).X, cY.ext η₁⟩ = 0`.  The column decomposition's image side
`X ∈ ℤ[R(μ_j)]` is orthogonal to the `Y`-anchor extension `cY.extension η₁`: by
`inner_X_Y_eq_zero_of_orthogonal` it suffices that each member of `R(μ_j) = certainTypeR.imageSet`
(a signed `±δ_j·ω_{ij}^σ`, `certainTypeRImage`) is `⊥ cY.extension η₁`, which is
`inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (the certain-type seam-1, generic in the
coherence `cY`).  The partner anchor `η'` supplies the supported difference `η₁ − η'` the seam-1
proof needs (the `V`-vanishing of `cY.extension η₁ − cY.extension η'`). -/
theorem columnDecompositionTau_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η' : ClassFunction ↥L ℂ} (hη₁Y : η₁ ∈ hyp.Yset) (hη'Y : η' ∈ hyp.Yset)
    (hη₁irr : IsIrreducibleCharacter η₁) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner
        (columnDecompositionTau hyp h46 hχ₂ hdeg hmapagree hSdiff htau1_mema hχψ hχbarψ).X
        (cY.extension η₁) = 0 := by
  classical
  apply inner_X_Y_eq_zero_of_orthogonal
  intro α hα
  change α ∈ Finset.univ.image (OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂⁻¹) at hα
  rw [Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  cases b
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂ i, mul_zero]
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂⁻¹ i, mul_zero]

/-- **(6.8.2.3) `hsq` over the positive-weight subtype.**  The Clifford square-sum
`∑_θ ⟨φ, Res^H_{W₂} θ⟩² = |H : W₂|` (`sum_inner_restrict_sq_eq_index`, `W₂` central in `H`),
reindexed to the positive-weight subtype `{θ // 0 < aθ}` (zero-weight constituents drop) and cast to
`ℤ`.  This is the `hsq` input of `per_phi_anchored_image` (the `n = |H : W₂|` of the (6.8.2.2)
aggregate). -/
theorem sum_constituentWeight_sq_subtype {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥K ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)) :
    ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
        ((constituentWeight hφ' i.val : ℤ)) ^ 2 = ((K.subgroupOf H).index : ℤ) := by
  classical
  -- the full square-sum over `Irr H`, in `ℤ`-form
  have hfull : (∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2)
      = ((K.subgroupOf H).index : ℤ) := by
    have key := sum_inner_restrict_sq_eq_index (M := ↥H) (N := K.subgroupOf H) hcen hφ'
    simp only [constituentWeight_spec hφ'] at key
    have hcast : ((∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2 : ℤ) : ℂ)
        = (((K.subgroupOf H).index : ℤ) : ℂ) := by
      push_cast
      simp only [pow_two]
      exact key
    exact_mod_cast hcast
  refine Eq.trans ?_ hfull
  exact (sum_eq_sum_pos_weight_subtype (constituentWeight hφ')
    (fun θ => ((constituentWeight hφ' θ : ℤ)) ^ 2)
    (fun θ hθ => by
      change (constituentWeight hφ' θ : ℤ) ^ 2 = 0
      rw [hθ]; norm_num)).symm

/-- **(6.8.2.2)→(6.8.2.3) aggregate `hagg` for the mixed per-`φ` family.**  The (6.8.2.2)
decomposition `τ(Ind^L_{W₂} φ − |H:W₂|·η₁) = Xagg − |H:W₂|·Y₀` (`hdecomp`, from
`exists_decomposition_caseB`), combined with the constituent sum
`Ind^L_{W₂} φ − |H:W₂|·η₁ = ∑_θ aθ·(Ind^L_H θ − aθ·η₁)`
(`sum_smul_constituent_diff_pos_weight_subtype`) and the per-constituent images
`τ(Ind^L_H θ − aθ·η₁) = (D θ).X − (D θ).Y` (`(D θ).tau1_image`, `tau1 = hyp.tau` via `htau1`), gives
the `hagg` input of `per_phi_anchored_image`:
`Xagg − |H:W₂|·Y₀ = ∑_θ aθ·((D θ).X − (D θ).Y)`.  The source aggregate's `ℂ`-scalar `(aθ : ℂ)·η₁`
is reconciled with the family's `ℕ`-anchor `aθ • η₁` by `Nat.cast_smul_eq_nsmul`. -/
theorem caseB_hagg
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg Y₀ : ClassFunction G ℂ}
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • Y₀) :
    Xagg - (((W2.subgroupOf H).index : ℤ) : ℂ) • Y₀
      = ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
          ((constituentWeight hφ' i.val : ℤ) : ℂ) • ((D i).X - (D i).Y) := by
  have hagg := aggregate_eq_sum_of_constituent (L := L) Finset.univ hyp.tau
    (fun i => ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
      - constituentWeight hφ' i.val • η₁)
    (fun i => (D i).X) (fun i => (D i).Y) (fun i => (constituentWeight hφ' i.val : ℤ))
    (β := ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
    (n := ((W2.subgroupOf H).index : ℤ))
    -- `hmemimg`: each constituent image is `(D i).tau1_image`, with `tau1 = hyp.tau`.
    (fun i _ => by have h := (D i).tau1_image; rw [htau1 i] at h; exact h)
    -- `hconstit`: the source aggregate, with the `ℂ`-anchor reconciled to the `ℕ`-anchor.
    ((sum_smul_constituent_diff_pos_weight_subtype hW2H hcen φ hφ' η₁).trans
      (Finset.sum_congr rfl fun i _ => by
        simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]))
    -- `hdecomp`: the (6.8.2.2) decomposition (`n = |H:W₂|`), bridging the `ℕ`/`ℤ` index cast.
    (by exact_mod_cast hdecomp)
  exact hagg

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image (mixed family, abstract `D`).**  For the
per-`φ` decomposition family `D` (each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ` decomposed against
`hyp.tau`, e.g. by the dispatch `caseB_constituentDecomposition`), with `(D θ).tau1 = hyp.tau`, the
seam-`1` orthogonality `(D θ).X ⊥ Y₀` (`hXorth`) and integrality `⟨(D θ).Y, Y₀⟩ ∈ ℤ` (`hbi`), and
the (6.8.2.2) decomposition `hdecomp`/`hXaggorth` of `exists_decomposition_caseB`, the pinning gives
the **anchored image**
`(Ind^L_H θ − aθ·η₁)^{hyp.tau} = (D θ).X − aθ·Y₀`   (`Y₀ = cY.extension η₁`, `aθ = ⟨φ, Res θ⟩`).

This is the route-independent (6.8.2.3) core: the `Xagg`/`hsq`/`hagg` are assembled internally
(`caseB_hagg`, `sum_constituentWeight_sq_subtype`); only the family `D` (the constituent dispatch)
and its per-`θ` orthogonality/integrality remain for the capstone. -/
theorem caseB_per_phi_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    {b : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ} → ℤ}
    (hXorth : ∀ i, ClassFunction.inner (D i).X (cY.extension η₁) = 0)
    (hbi : ∀ i, ClassFunction.inner (D i).Y (cY.extension η₁) = (b i : ℂ))
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (D i).X - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ :=
  per_phi_anchored_image hyp cY hη₁ Finset.univ D htau1 hXaggorth
    (caseB_hagg hyp hW2H hcen hφ' D htau1 hdecomp)
    (sum_constituentWeight_sq_subtype hW2H hcen hφ')
    (fun i _ => hXorth i) (fun i _ => hbi i) i (Finset.mem_univ i) i.2

end OddOrder.Peterfalvi.S08
