/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_BridgeCharacter
import OddOrder.Peterfalvi.S16_PairingCoherence
import OddOrder.Peterfalvi.S16_PairingBessel
import OddOrder.Peterfalvi.S16_GridExpansion

/-!
# (13.19) Type-I orthogonality — producer / grid-facts layer

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issues 0103/0102/0111):
the Peterfalvi (13.19) type-I orthogonality **producer and grid facts** —
`OddIntegerInner`, the `TypeIOrthogonalityData` bundle, the (13.19) producer decomposition
(`typeIBetaL`, disjoint-support facts, `exists_zeta_index_of_mem_Sset`), and the
row/column-constancy of the `β_L^τ` grid.  The (13.19.c) dichotomy and the (14.5) complement
exclusion consume this layer and live in `S15_SAndT` (which imports this module).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The parity conclusion in Peterfalvi (13.19.c2): the character inner
product is an odd integer, recorded inside `ℂ`. -/
def OddIntegerInner (χ ψ : ClassFunction G ℂ) : Prop :=
  ∃ n : ℤ, Odd n ∧
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)], ClassFunction.inner χ ψ = (n : ℂ)

/-- Carrier for the type-I comparison in Peterfalvi (13.19). -/
structure TypeIOrthogonalityData (hyp : Hypothesis (G := G)) (L : Subgroup G) where
  typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L
  e : ℕ
  e_eq_index : Prop
  Lset : Set (ClassFunction ↥L ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  disjoint_support : Prop
  Ltau_orthogonal_eta : Prop
  betaL_eta_independent : Prop
  caseC1 : Prop
  caseC2 : Prop
  caseC2_eta0j_odd :
    caseC2 →
      ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
  caseC1_bound :
    caseC1 →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
  caseC1_dual : Prop
  caseC2_dual : Prop
  caseC2_dual_etai0_odd :
    caseC2_dual →
      ∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
  caseC1_dual_bound :
    caseC1_dual →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))

namespace TypeIOrthogonalityData

/-- **Peterfalvi (13.19.c)**, consumer form: any strict gap beyond the
case-(c1) bound forces the parity alternative (c2). -/
theorem caseC2_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1 ∨ data.caseC2)
    (hgap :
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2 := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c)** after swapping `S` and `T`: any strict gap beyond
`(v - 1) / p` excludes the dual case-(c1) bound and forces the dual parity
alternative (c2), the source of the `eta_i0` congruences. -/
theorem caseC2_dual_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1_dual ∨ data.caseC2_dual)
    (hgap :
      ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2_dual := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_dual_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c2)**: once both S- and T-side parity alternatives
hold, the two zero-axis families of `eta` have odd integer inner product with
`beta_L`. -/
theorem eta_axes_odd_of_caseC2_pair {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L) (hcases : data.caseC2 ∧ data.caseC2_dual) :
    (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) := by
  exact ⟨data.caseC2_eta0j_odd hcases.1, data.caseC2_dual_etai0_odd hcases.2⟩

end TypeIOrthogonalityData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §13 grid/Dade producer for Peterfalvi (13.19).**

Given a type-I maximal subgroup `L` with its (12.1) `S14.Hypothesis` `typeISetup`, this bundles the
genuinely grid-dependent data and facts of (13.19) against a concrete kernel index `e`, family
`Lset` and generator `phi`:

* the Dade images `β_L`, `β_S`, disjoint-supported (13.18.a-style);
* `phi ∈ Lset` of degree `e = |L : H|`;
* **(13.19.a)** `L^{τ₁} ⊥ {η_ij}` and `β_L ⊥ {η_ij}` (grid orthogonality, the `Ltau_orthogonal_eta`
  / `betaL_eta_independent` content), bottoming out at the (3.9) `τ`-isometry (σ-pinned);
* **(13.19.c)** the S- and T-side dichotomies `caseC1 ∨ caseC2` where `caseC1` is the rational
  degree bound `(|H|−1)/e ≤ (u−1)/q` and `caseC2` is the genuine `η`-axis odd-integer parity
  `∀ j ≠ 0, ⟨β_L, η_0j⟩ ∈ 2ℤ+1` (dual: `(v−1)/p`, `η_i0`).

Everything grid-dependent is isolated here; the assembling theorem
`typeI_orthogonality_dichotomy` supplies the honest §14 bundle `dataL` (whose
`typeISetup = dataL.typeIHyp` is the (12.1) Dade setup and whose `τ₁ = dataL.coh.extension`
is the (12.6) coherent extension), and reads the dichotomy implication fields off as
identities (no over-claim).  Single-character images use `τ₁` (the raw `tau` is arbitrary
off the supported subspace); the `A(L)`-supported difference `β_L` uses `tau` directly. -/
structure TypeIOrthogonalityGridData [Finite G] (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) where
  e : ℕ
  e_eq_index : ((maxNilpotentNormalHall L).subgroupOf L).index = e
  Lset : Set (ClassFunction ↥L ℂ)
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  /-- The T-side companion `β_T^τ` (the S↔T-swapped `β_S^τ`), pairing with `φ^{τ₁}` in the dual
  (13.19.c1) parity. -/
  betaT : ClassFunction G ℂ
  disjoint_support : Disjoint betaL.support betaS.support
  /-- **(13.19)**: `β_L` is the Dade image `β_L^τ = (Ind_H^L 1_H − φ)^{τ₁}` (the extension
  `τ₁` agrees with `τ = dataL.typeIHyp.tau` on the `A(L)`-supported `Ind_H^L 1_H − φ`). -/
  betaL_eq :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((dataL.typeIHyp.H).subgroupOf L) : ℂ)],
      betaL = dataL.typeIHyp.tau
        (ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
          (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - phi)
  Ltau_orthogonal_eta :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (dataL.coh.extension phi) (hyp.eta i j) = 0
  /-- **(13.19.c)**, first clause: `(β_L^τ, η_{0j})` is independent of `j` for `1 ≤ j < p`. -/
  betaL_eta0_row_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')
  /-- **(13.19.c)**, first clause after the S↔T swap: `(β_L^τ, η_{i0})` is independent of `i`
  for `1 ≤ i < q`. -/
  betaL_eta0_col_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩)
  /-- **(13.19.c)** S-side dichotomy, faithful form: **(c1)** `(β_S^τ, φ^{τ₁}) ≡ 1 (mod 2)` and
  the degree bound `(|H|−1)/e ≤ (u−1)/q`, or **(c2)** the `η_{0j}` odd-parity and `p ≤ e`. -/
  caseC :
    (OddIntegerInner betaS (dataL.coh.extension phi) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ e)
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy, faithful form: **(c1)**
  `(β_T^τ, φ^{τ₁}) ≡ 1 (mod 2)` and `(|H|−1)/e ≤ (v−1)/p`, or **(c2)** the `η_{i0}` odd-parity
  and `q ≤ e`. -/
  caseC_dual :
    (OddIntegerInner betaT (dataL.coh.extension phi) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ e)

/-! #### The (13.19) producer, decomposed

The Tier-A structure (`e`, `𝓛`, `φ`, `β_L`, `β_S`) is built here; the genuinely deep (13.19)
facts are isolated below as `φ`-parametric obligations, each matching one `GridData` field. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19), `φ` existence**: the family `𝓛 = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}` has a member of
degree `e = [L : H]` ("the existence of `φ` is clear"): the nontrivial solvable kernel `H` has a
nontrivial degree-one character `θ`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`); `Ind_H^L θ` lies in
`𝓛` by definition, with degree `(Ind_H^L θ)(1) = [L:H]·θ(1) = e` (`induce_apply_one`).  (The
membership already witnesses irreducibility demands downstream via the Frobenius inertia
argument packaged in `𝓛 ⊆ Irr L`.) -/
theorem exists_Sset_apply_one_eq_index [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∃ φ : ClassFunction ↥L ℂ, φ ∈ typeISetup.Sset ∧
      φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
  classical
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  -- both Frobenius kernels are `L_F`
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  -- the kernel is a nontrivial solvable group, so it has a nontrivial linear character
  haveI : IsSolvable ↥L := hG.solvable_of_lt_top L
    (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp typeISetup.maximal).1)
  haveI : Nontrivial ↥((typeISetup.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hfrob.ne_bot_kernel
  have hcomm : commutator ↥((typeISetup.typeI.typeF.H).subgroupOf L) ≠ ⊤ :=
    ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥((typeISetup.typeI.typeF.H).subgroupOf L)))
  obtain ⟨θ, hθ_ne, hθ1⟩ := OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top
    hcomm
  refine ⟨ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction _ ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ1, mul_one, typeISetup.typeI.typeF.H_eq]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19) `β_L^τ`**: the Dade image `τ₁(Ind_H^L 1_H − φ)` of the `L`-side bridge character,
for a chosen degree-`e` member `φ ∈ 𝓛` (`τ₁ = typeISetup.tau` agrees with `τ` on the
`A(L)`-supported difference). -/
noncomputable def typeIBetaL [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ) :
    ClassFunction G ℂ :=
  typeISetup.tau (ClassFunction.induce ((typeISetup.H).subgroupOf L)
    (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - φ)

/-- `typeIBetaL` is literally `τ₁(Ind_H^L 1_H − φ)` under **any** ambient instances — the
`FiniteInduce`-scoped instances used in the definition agree with the caller's by
`Subsingleton`.  Bridges the `GridData.betaL_eq` field. -/
theorem typeIBetaL_eq_tau_induce_sub [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ) :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((typeISetup.H).subgroupOf L) : ℂ)],
      typeIBetaL typeISetup φ = typeISetup.tau
        (ClassFunction.induce ((typeISetup.H).subgroupOf L)
          (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - φ) := by
  intro _ _ _
  unfold typeIBetaL
  repeat' first
    | rfl
    | exact Subsingleton.elim _ _
    | congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L^τ` is supported in `Ã(A(L))`**: the input `Ind_H^L 1 − φ` is `A(L)`-supported — at
`1` the value is `e − e = 0` (`induce_apply_one` + the degree hypothesis), and off `1` its
support lies in nontrivial kernel-conjugates (`support`s of both `Ind` terms), which land in
`A(L)` by `H^# ⊆ A(L)` (`sharpSubgroup_H_subset_typeIA`) and the `L`-conjugation invariance of
`A(L)` (`L_normalizes_A`).  Hence the Dade lift agrees with the (2.5) Dade map there
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `Ã(A(L)) = dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`). -/
theorem typeIBetaL_support_subset_dadeSupport [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ)
    (hφ : φ ∈ typeISetup.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (typeIBetaL typeISetup φ).support ⊆ typeISetup.dadeData.dade.dadeSupport := by
  classical
  set H' : Subgroup ↥L := (typeISetup.H).subgroupOf L with hH'def
  set ι : ClassFunction ↥L ℂ :=
    ClassFunction.induce H' (trivialClassFunction ↥H') with hιdef
  have hsupp : (ι - φ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typeIA L typeISetup.typeI) L := by
    intro z hz
    have hzne : (ι - φ) z ≠ 0 := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      apply hzne
      rw [ClassFunction.sub_apply, hιdef, ClassFunction.induce_apply_one,
        trivialClassFunction_apply, mul_one, hdeg]
      have hHeq : H' = (maxNilpotentNormalHall L).subgroupOf L := by
        rw [hH'def]
        show (typeISetup.typeI.typeF.H).subgroupOf L = _
        rw [typeISetup.typeI.typeF.H_eq]
      rw [hHeq, sub_self]
    have hzc : z ∈ OddOrder.RepresentationTheory.ClassFunction.conjugatesInto H' := by
      by_contra hnotc
      apply hzne
      rw [ClassFunction.sub_apply]
      obtain ⟨θ, -, hφeq⟩ := hφ
      have hφz : ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((typeISetup.typeI.typeF.H).subgroupOf L) ℂ) z = 0 :=
        ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc
      rw [hιdef, ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc, hφeq, hφz,
        sub_zero]
    obtain ⟨c, hc⟩ := hzc
    have hcne : c⁻¹ * z * c ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg (fun w => c * w * c⁻¹) h1
      simpa [mul_assoc] using h2
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hmem : ((c⁻¹ * z * c : ↥L) : G) ∈ sharpSubgroup typeISetup.typeI.typeF.H :=
      ⟨Subgroup.mem_subgroupOf.mp hc, fun h1 => hcne (Subtype.ext h1)⟩
    have hA := sharpSubgroup_H_subset_typeIA typeISetup.typeI hmem
    have hconjA := typeISetup.dadeData.dade.L_normalizes_A c hA
    simpa [mul_assoc] using hconjA
  intro x hx
  by_contra hnot
  apply hx
  show typeIBetaL typeISetup φ x = 0
  rw [typeIBetaL,
    show typeISetup.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        typeISetup.dadeData.dade
        (typeISetup.dadeData.dade.fullDadeIsometryData typeISetup.hconj) from rfl,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support _ _ hsupp]
  exact (typeISetup.dadeData.dade.isDadeMap_dadeMap).map_eq_zero_of_not_mem_dadeSupport _ _ hnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Any `A(L)`-supported Dade image lands in `Ã(A(L)) = dadeSupport`** — the general form of
`typeIBetaL_support_subset_dadeSupport` (whose input is `ψ = Ind_H^L 1 − φ`).  Since
`τ = dadeIntegralCharacterMap` agrees with the (2.5) Dade map on `A(L)`-supported inputs
(`dadeIntegralCharacterMap_apply_of_support`), the image vanishes off `dadeSupport`
(`map_eq_zero_of_not_mem_dadeSupport`). -/
theorem tau_support_subset_dadeSupport [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (ψ : ClassFunction ↥L ℂ)
    (hψ : ψ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typeIA L typeISetup.typeI) L) :
    (typeISetup.tau ψ).support ⊆ typeISetup.dadeData.dade.dadeSupport := by
  intro x hx
  by_contra hnot
  apply hx
  show typeISetup.tau ψ x = 0
  rw [show typeISetup.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        typeISetup.dadeData.dade
        (typeISetup.dadeData.dade.fullDadeIsometryData typeISetup.hconj) from rfl,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support _ _ hψ]
  exact (typeISetup.dadeData.dade.isDadeMap_dadeMap).map_eq_zero_of_not_mem_dadeSupport _ _ hnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **T-side (14.3.b) bridge character** `β_T = Ind_{QW₂}^T 1_{QW₂} − ν_{10} ∈ CF(T)` — the
S↔T mirror of `betaGrid` (`β_S = Ind_{PW₁}^S 1 − μ_{01}`), with the grid entry `ν_{10}` in
place of `μ_{01}`. -/
noncomputable def betaTGridChar [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction ↥hyp.T ℂ :=
  ClassFunction.induce ((hyp.Q ⊔ hyp.W2).subgroupOf hyp.T)
      (trivialClassFunction ↥((hyp.Q ⊔ hyp.W2).subgroupOf hyp.T))
    - hyp.nu ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **T-side (13.18)-dual Dade image** `τ_T(β_T)` — the S↔T-swapped `tauSbetaGrid`, pairing
with `φ^{τ₁}` in the dual (13.19.c1) parity.  Built from the honest `T`-instance `'A0(T)` Dade
(`hyp.dadeHypT0`), which requires `IsTypeP2 T` — a **(14.9) conclusion** — and a reconciled
`T`-side `TypePData` (`reconciled_typePData_T`), both taken as parameters. -/
noncomputable def tauTbetaGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) : ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
    ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hTP Tdata))
    (betaTGridChar hyp)

/-- **`A(M) ⊆ H^#` for a Frobenius type-I maximal** (with `sharpSubgroup_H_subset_typeIA`,
equality — Coq `FTsupp_Frobenius`): an element of the type-I support `A(M)` centralizes some
`y ∈ H^#`, and in a Frobenius group the centralizer of a nontrivial kernel element lies in the
kernel (`IsFrobeniusGroup.centralizer_kernel_le`, Isaacs Thm 6.4). -/
theorem typeIA_subset_sharpSubgroup_of_frobenius [Finite G] {M : Subgroup G}
    (data : TypeIData M) {E : Subgroup ↥M}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M) E) :
    typeIA M data ⊆ sharpSubgroup data.typeF.H := by
  rintro x ⟨hxM, hx1, y, hy, hxc⟩
  have hyM : y ∈ M := data.typeF.H_le hy.1
  have hyH' : (⟨y, hyM⟩ : ↥M) ∈ data.typeF.H.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact hy.1
  have hy1' : (⟨y, hyM⟩ : ↥M) ≠ 1 := fun h => hy.2 (by
    simpa using congrArg Subtype.val h)
  have hxc' : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer ({⟨y, hyM⟩} : Set ↥M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxc
    exact Subtype.ext (by push_cast; exact hcomm)
  have hxH' := hF.centralizer_kernel_le _ hyH' hy1' hxc'
  rw [Subgroup.mem_subgroupOf] at hxH'
  exact ⟨hxH', hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness, arbitrary-column form** (Coq `o_tauL_S`): for every
`j ≠ 0`, `β_L^τ` (supported in `Ã(L)`-classes) has support disjoint from the `S`-side Dade
image `τ_S(β_j)` (supported in `P^# ∪ (W∖(W₁∪W₂))^S`-classes, (13.18.a)) — the order of an
`Ã(L)`-element is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q`
((8.17.a)).  The column-`#1` instance is `typeIBetaL_betaS_disjoint_support`; the general
column feeds the (13.19.c) zero-axis constancy through `gammaGrid_defGamma`. -/
theorem dadeSupport_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (χ : ClassFunction G ℂ)
    (hχ : χ.support ⊆ typeISetup.dadeData.dade.dadeSupport)
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint χ.support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
        (betaGrid hyp j)).support := by
  classical
  rw [Set.disjoint_left]
  intro x hxL hxS
  -- L-side: a prime `r ∣ orderOf a` (`a ∈ A(L)`) divides `orderOf x`
  have hxD := hχ hxL
  obtain ⟨a, haA, r, hr, hra, hrx⟩ :=
    typeISetup.dadeData.dade.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport hxD
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  have haH := typeIA_subset_sharpSubgroup_of_frobenius typeISetup.typeI hfrob haA
  have hrLF : r ∣ Nat.card ↥(maxNilpotentNormalHall L) := by
    refine hra.trans ?_
    have hdvd := Subgroup.orderOf_dvd_natCard typeISetup.typeI.typeF.H haH.1
    rwa [typeISetup.typeI.typeF.H_eq] at hdvd
  -- S-side: `orderOf x ∣ p^q · (q·p)`
  have hbridge : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
        (betaGrid hyp j)
      = ClassFunction.induce hyp.S (betaGrid hyp j) :=
    hyp.sInstance_dade0_eq_induce _hG hnoV
      (betaGrid_A0_support_of_c_eq_one _hG hyp hc1 j hj)
  rw [hbridge] at hxS
  have hxc :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_conjugatesIntoSet
      (betaGrid_support_of_c_eq_one _hG hyp hc1 j hj) hxS
  obtain ⟨c, hcS, hmem⟩ := hxc
  have hordx : orderOf (c⁻¹ * x * c) = orderOf x := by
    have hinj : orderOf ((MulAut.conj c⁻¹).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulEquiv.injective _) _
    rw [← hinj]
    congr 1
    simp [mul_assoc]
  have hxdvd : orderOf x ∣ hyp.p ^ hyp.q * (hyp.q * hyp.p) := by
    rcases hmem with hP | hV
    · -- `c⁻¹xc ∈ P^#`
      have hdvd : orderOf (c⁻¹ * x * c) ∣ Nat.card ↥hyp.P :=
        Subgroup.orderOf_dvd_natCard hyp.P hP.1
      rw [hordx, hyp.card_P_eq _hG hyp.Sdata_W2_eq] at hdvd
      exact hdvd.trans (dvd_mul_right _ _)
    · -- `c⁻¹xc` is `S`-conjugate to `w ∈ typePV ⊆ W`
      obtain ⟨w, hw, t, htS, hconjw⟩ := hV
      have hconjw' : t * w * t⁻¹ = c⁻¹ * x * c := hconjw
      have hordw : orderOf (c⁻¹ * x * c) = orderOf w := by
        rw [← hconjw']
        have hinj : orderOf ((MulAut.conj t).toMonoidHom w) = orderOf w :=
          orderOf_injective (MulAut.conj t).toMonoidHom (MulEquiv.injective _) _
        rw [← hinj]
        congr 1
      have hwW : w ∈ hyp.W := by
        have h1 : w ∈ hyp.Sdata.W := hw.1
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq] at h1
        rwa [hyp.W_eq_join]
      have hdvdW : orderOf w ∣ Nat.card ↥hyp.W :=
        Subgroup.orderOf_dvd_natCard hyp.W hwW
      have hWnorm : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
        intro v hv
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hyp.W1_commutes_W2 v hv y hy
          rwa [show v * y * v⁻¹ = y by
            rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]]
        · intro hy
          have hz := hyp.W1_commutes_W2 v hv (v * y * v⁻¹) hy
          have h5 : v * (v * y * v⁻¹) = v * y := by
            rw [hz.eq]
            group
          have h6 : v * y * v⁻¹ = y := mul_left_cancel h5
          rwa [h6] at hy
      have hWcard : Nat.card ↥hyp.W = hyp.q * hyp.p := by
        rw [hyp.W_eq_join,
          OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
            hyp.W1_inf_W2_eq_bot, ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
      have hxw : orderOf x = orderOf w := by rw [← hordx, hordw]
      have hxqp : orderOf x ∣ hyp.q * hyp.p := by
        rw [hxw, ← hWcard]
        exact hdvdW
      exact hxqp.trans (dvd_mul_left _ _)
  -- a prime dividing both `|L_F|` and `p·q` contradicts (8.17.a)
  have hrpq : r ∣ hyp.p * hyp.q := by
    have h2 := hrx.trans hxdvd
    rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
    · exact dvd_mul_of_dvd_left (hr.dvd_of_dvd_pow h3) _
    · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
      · exact dvd_mul_of_dvd_right h4 _
      · exact dvd_mul_of_dvd_left h4 _
  have hnconjS := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.S_maximal hyp.S_nonI
  have hnconjT := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp typeISetup.maximal ⟨typeISetup.typeI⟩
    hnconjS hnconjT
  have hone : r ∣ 1 := hcop ▸ Nat.dvd_gcd hrLF hrpq
  exact hr.one_lt.ne' (Nat.dvd_one.mp hone)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a), `β_L^τ`-column instance**: the (13.19.a) support disjointness for the specific
`Ã(L)`-supported `β_L^τ = typeIBetaL φ` (`typeIBetaL_support_subset_dadeSupport`), a thin instance
of the general `dadeSupport_betaGrid_disjoint_support`. -/
theorem typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint (typeIBetaL typeISetup φ).support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
        (betaGrid hyp j)).support :=
  dadeSupport_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1 typeISetup
    (typeIBetaL typeISetup φ)
    (typeIBetaL_support_subset_dadeSupport typeISetup φ _hφ _hdeg) j hj

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness**: `Ã(L) ∩ (P^G ∪ W^G) = ∅` — the order of an `Ã(L)`-element
is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q` ((8.17.a)); `β_L^τ` is
supported in `Ã(L)`-classes while `β_S^τ` is supported in `P^# ∪ (W∖(W₁∪W₂))^G` ((13.18.a)).
The column-`#1` instance of `typeIBetaL_dadeS_betaGrid_disjoint_support`. -/
theorem typeIBetaL_betaS_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    Disjoint (typeIBetaL typeISetup φ).support (tauSbetaGrid _hG hyp).support := by
  rw [tauSbetaGrid]
  exact typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support avoidance** (Coq `tiA_PWG` restricted to `Ŵ^G`): for
a type-I maximal `L`, the Dade support `Ã(L)` avoids the regular-set saturation
`Ŵ^G = (W ∖ (W₁ ∪ W₂))^G` — an `Ã(L)`-element has a prime divisor of `|L_F|` in its order
(`exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport` + `A(L) ⊆ L_F^#`), while a
`Ŵ^G`-element has order dividing `|W| = p q`, coprime to `|L_F|` ((8.17.a)
`card_LF_coprime_pq`).  The conjugation-free core of `typeIBetaL_betaS_disjoint_support`. -/
theorem typeI_dadeSupport_avoids_regular [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∀ x ∈ OddOrder.GroupTheory.conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      x ∉ typeISetup.dadeData.dade.dadeSupport := by
  intro x hx hxD
  -- L-side: a prime `r ∣ |L_F|` divides `orderOf x`
  obtain ⟨a, haA, r, hr, hra, hrx⟩ :=
    typeISetup.dadeData.dade.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport hxD
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  have haH := typeIA_subset_sharpSubgroup_of_frobenius typeISetup.typeI hfrob haA
  have hrLF : r ∣ Nat.card ↥(maxNilpotentNormalHall L) := by
    refine hra.trans ?_
    have hdvd := Subgroup.orderOf_dvd_natCard typeISetup.typeI.typeF.H haH.1
    rwa [typeISetup.typeI.typeF.H_eq] at hdvd
  -- regular side: `orderOf x = orderOf w ∣ |W| = p q`
  obtain ⟨w, hw, c, hcx⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hordx : orderOf x = orderOf w := by
    rw [← hcx]
    have hinj : orderOf ((MulAut.conj c).toMonoidHom w) = orderOf w :=
      orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) _
    rw [← hinj]
    congr 1
  have hword : orderOf w ∣ hyp.p * hyp.q := by
    have h := Subgroup.orderOf_dvd_natCard hyp.W hw.1
    rwa [card_W_eq_pq hyp] at h
  have hxord : orderOf x ∣ hyp.p * hyp.q := by rw [hordx]; exact hword
  have hrpq : r ∣ hyp.p * hyp.q := hrx.trans hxord
  -- a prime dividing both `|L_F|` and `p·q` contradicts (8.17.a)
  have hnconjS := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.S_maximal hyp.S_nonI
  have hnconjT := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp typeISetup.maximal ⟨typeISetup.typeI⟩
    hnconjS hnconjT
  have hone : r ∣ 1 := hcop ▸ Nat.dvd_gcd hrLF hrpq
  exact hr.one_lt.ne' (Nat.dvd_one.mp hone)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every family member is an enumerated `ζ_k` with `k ≠ ind1H`** — the converse of
`TypeICoherent78Data.zeta_mem_Sset`.  The `cover` field supplies an index `k` with
`ζ_k = Ind θ' = φ`; `k = ind1H` is impossible since `Ind 1_H` is real while the nontrivial
induced irreducible `Ind θ'` is not (odd order, Peterfalvi (1.1)). -/
theorem exists_zeta_index_of_mem_Sset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∃ k : Fin (dataL.n + 1), k ≠ dataL.ind1H ∧ dataL.zeta k = φ := by
  haveI := dataL.kernelIn_normal
  obtain ⟨θ', hθ'ne, hφeq⟩ := hφ
  obtain ⟨k, hk⟩ := dataL.cover θ'
  have hk' : ClassFunction.induce dataL.kernelIn (dataL.θ k : ClassFunction _ ℂ)
      = ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ) := hk
  refine ⟨k, ?_, hk'.trans hφeq.symm⟩
  -- `k = ind1H` would identify the non-real `Ind θ'` with the real `Ind 1_H`.
  rintro rfl
  have hind1 : ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce dataL.kernelIn
          (trivialClassFunction ↥dataL.kernelIn) := by
    rw [dataL.triv]
    rfl
  have hreal : ClassFunction.IsReal
      (ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)) := by
    rw [hind1]
    show (ClassFunction.induce dataL.kernelIn (trivialClassFunction _)).conj = _
    rw [conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  rw [hk'] at hreal
  -- `Ind θ'` is a nontrivial irreducible (Frobenius), hence not real in odd order
  have hirr : IsIrreducibleCharacter
      (ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ)) :=
    isIrreducibleCharacter_induce_of_frobeniusGroup dataL.hFrob θ' hθ'ne
  have hodd_L : Odd (Nat.card ↥L) :=
    _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : dataL.kernelIn ≠ ⊤ := by
    intro hKtop
    refine dataL.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := dataL.hFrob.isComplement.disjoint
    rw [show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = dataL.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (dataL.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ'
  have hne_triv : (⟨ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((dataL.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdi, ← ClassFunction.induce_apply_one dataL.kernelIn (θ' : ClassFunction _ ℂ),
        hcf, trivialClassFunction_apply]
    have : (dataL.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (dataL.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv hreal

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b)**: `𝓛^{τ₁}` is orthogonal to the whole `η`-grid, for the honest
coherent extension `τ₁ = dataL.coh.extension`.  For `ψ ∈ 𝓛` (an enumerated `ζ_k`,
`exists_zeta_index_of_mem_Sset`), the conjugate partner `ζ_{k'} = ζ̄_k` is again a family
member (`exists_conjIndex_at`); `ζ_k^{τ₁} − ζ_{k'}^{τ₁}` is supported in `Ã(L)`
(`nu_zeta_sub_conj_support_at`), which avoids `Ŵ^G` by (13.19.a)
(`typeI_dadeSupport_avoids_regular`); the unit norms (`nu_zeta_norm_one`), conjugate
orthogonality (`nu_zeta_inner_nu_conj_eq_zero`), and `ℤ[Irr G]`-membership feed the (3.8)
rigidity engine `eta_orthogonal_of_norm_one_pair_vanish`. -/
theorem coherent_extension_orthogonal_eta_of_mem_Sset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (dataL.coh.extension φ) (hyp.eta i j) = 0 := by
  classical
  have core : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j) (dataL.coh.extension φ) = 0 := by
    obtain ⟨k, hk_ne, hkφ⟩ := exists_zeta_index_of_mem_Sset _hG dataL hφ
    have hk78 : k ≠ (dataL.h78 _hG).ind1H := by
      rw [dataL.h78_ind1H_eq]; exact hk_ne
    obtain ⟨k', hk'_ne, hk'⟩ := dataL.exists_conjIndex_at _hG hk_ne
    -- engine inputs from the coherence bundle
    have hpsiZ : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k) ∈ ZIrr G := by
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq]
      exact dataL.coh.extension_mem_ZIrr _
        (Submodule.subset_span (dataL.zeta_mem_Sset hk_ne))
    have hconjZ : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k') ∈ ZIrr G := by
      have hk'ne_data : k' ≠ dataL.ind1H := by
        rw [← dataL.h78_ind1H_eq _hG]; exact hk'_ne
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq]
      exact dataL.coh.extension_mem_ZIrr _
        (Submodule.subset_span (dataL.zeta_mem_Sset hk'ne_data))
    have hpsi1 := dataL.nu_zeta_norm_one _hG hk78
    have hconj1 := dataL.nu_zeta_norm_one _hG hk'_ne
    have hcross := dataL.nu_zeta_inner_nu_conj_eq_zero _hG _hG.odd hk_ne hk'_ne hk'
    have hsupp := dataL.nu_zeta_sub_conj_support_at _hG hk_ne hk'_ne hk'
    have havoid := typeI_dadeSupport_avoids_regular _hG hnoV hyp dataL.typeIHyp
    have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k)
          - (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k')) x = 0 := by
      intro x hx
      by_contra hval
      have hxD := hsupp (ClassFunction.mem_support.mpr hval)
      rw [dataL.h78_hyp_eq] at hxD
      exact havoid x hx hxD
    intro i j
    have hengine := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
      hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
    have hid : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k)
        = dataL.coh.extension φ := by
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq, hkφ]
    rwa [hid] at hengine
  intro i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, core i j, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c), first clause (row form), difference core** (Coq `betaLeta`):
`(β_L^τ, η_{0j} − η_{0j'}) = 0` for `j, j' ≠ 0`.  By (13.18.c) `j`-independence
(`gammaGrid_defGamma` at `j` and `j'`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`; each
`(β_L^τ, τ_S(β_j))` vanishes by the (13.19.a) support disjointness
(`typeIBetaL_dadeS_betaGrid_disjoint_support`). -/
theorem typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j j' : Fin hyp.p) (hj : (j : ℕ) ≠ 0) (hj' : (j' : ℕ) ≠ 0) :
    ClassFunction.inner (typeIBetaL typeISetup φ)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j') = 0 := by
  classical
  have h1 := gammaGrid_defGamma _hG hnoV hyp j hj
  have h2 := gammaGrid_defGamma _hG hnoV hyp j' hj'
  -- `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)` from the two `Γ`-identities.
  have hkey : hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j'
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
          (betaGrid hyp j')
        - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
          ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
          (betaGrid hyp j) := by
    have h3 := h1.trans h2.symm
    rw [← sub_eq_zero] at h3 ⊢
    rw [← h3]
    abel
  rw [hkey, ClassFunction.inner_sub_right,
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j' hj'),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
        typeISetup φ _hφ _hdeg j hj),
    sub_zero]

/-- **(13.19.c), first clause (row form)**: `(β_L^τ, η_{0j})` is independent of `j ≥ 1` — by
(13.18.c) `j`-independence (`gammaGrid_defGamma`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`,
and (13.19.a) support disjointness kills both `(β_L^τ, τ_S(β_·))` terms
(`typeIBetaL_inner_eta_row_sub_eq_zero`). -/
theorem typeIBetaL_eta_row_constant_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta ⟨0, hyp.q_prime.pos⟩ j') := by
  intro _ _ j j' hj hj'
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_right]
  have h := typeIBetaL_inner_eta_row_sub_eq_zero_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg j j' hj hj'
  convert h using 2
  exact Subsingleton.elim _ _

/-- **(13.19.c), first clause (column form)**: the S↔T-swapped row constancy — the
`typeIBetaL_eta_row_constant` instance at `hyp.swap` (Coq's re-instantiation of the section
with the pair roles interchanged).  The swap's `η`-grid is the transpose, so its row-`0`
constancy *is* the column constancy of `hyp.eta`; `β_L^τ` is `hyp`-independent, so no
transport is needed on the left argument.  Takes the (14.9)-conclusional `IsTypeP2 T` (like
`typeI_caseC_dual_dichotomy`); the reconciled `TypePData T` comes from
`reconciled_typePData_T`, the ν-side grid supply is the explicit `pins` parameter (issue
9096 / 0118 b-5: the canonical `S16.Hypothesis.nuGridSupply` carrier at the Section-16
consumers), and the swap's structural `IsMulCommutative ↥V` input is derived from `hT2` via
the BG type dictionary and `isMulCommutative_V` (issue 9096 bundle split). -/
theorem typeIBetaL_eta_col_constant_of_d_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hd1 : hyp.d = 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (pins : NuGridSupplyData hyp)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta i' ⟨0, hyp.p_prime.pos⟩) := by
  intro _ _ i i' hi hi'
  classical
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T _hG hyp
  have hV : IsMulCommutative ↥hyp.V := isMulCommutative_V _hG hyp
    ((OddOrder.BG.Ch4.S16.proposition_type_classification _hG hyp.T_maximal).2.1.mpr hT2)
  have hc1swap : (hyp.swap hT2 hV Tdata hU hW1 hW2 pins).c = 1 := by
    change hyp.d = 1
    exact hd1
  exact typeIBetaL_eta_row_constant_of_c_eq_one _hG hnoV
    (hyp.swap hT2 hV Tdata hU hW1 hW2 pins)
    hc1swap
    typeISetup φ _hφ _hdeg i i' hi hi'

end OddOrder.Peterfalvi.S15
