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
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issues 0103/0102):
the (13.19) type-I orthogonality layer and the (14.5) complement exclusion.

The (13.19) grid data is stated against the **(12.6) coherence bundle**
`S16.TypeICoherent78Data L` (existence: `TypeICoherent78Data.nonempty`), whose
`coh.extension` is the honest coherent extension `τ₁` of Peterfalvi (13.19) — the raw
`typeISetup.tau` is a Dade lift that is *arbitrary* off the `A(L)`-supported subspace
(`dim CF(L) > dim CF(G)` forbids a global isometry), so single-character images `φ^{τ₁}`
must go through the coherence bundle.
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
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∃ φ : ClassFunction ↥L ℂ, φ ∈ typeISetup.Sset ∧
      φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
  classical
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG typeISetup.maximal
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
    (hyp : Hypothesis (G := G)) (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) : ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
    ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData (hyp.dadeHypT0_hconj hG hT2 Tdata))
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
theorem dadeSupport_betaGrid_disjoint_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
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
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG typeISetup.maximal
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
    hyp.sInstance_dade0_eq_induce _hG (betaGrid_A0_support _hG hyp j hj)
  rw [hbridge] at hxS
  have hxc :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_conjugatesIntoSet
      (betaGrid_support _hG hyp j hj) hxS
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
theorem typeIBetaL_dadeS_betaGrid_disjoint_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint (typeIBetaL typeISetup φ).support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData (hyp.dadeHypS0_hconj _hG))
        (betaGrid hyp j)).support :=
  dadeSupport_betaGrid_disjoint_support _hG hyp typeISetup (typeIBetaL typeISetup φ)
    (typeIBetaL_support_subset_dadeSupport typeISetup φ _hφ _hdeg) j hj

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness**: `Ã(L) ∩ (P^G ∪ W^G) = ∅` — the order of an `Ã(L)`-element
is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q` ((8.17.a)); `β_L^τ` is
supported in `Ã(L)`-classes while `β_S^τ` is supported in `P^# ∪ (W∖(W₁∪W₂))^G` ((13.18.a)).
The column-`#1` instance of `typeIBetaL_dadeS_betaGrid_disjoint_support`. -/
theorem typeIBetaL_betaS_disjoint_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    Disjoint (typeIBetaL typeISetup φ).support (tauSbetaGrid _hG hyp).support := by
  rw [tauSbetaGrid]
  exact typeIBetaL_dadeS_betaGrid_disjoint_support _hG hyp typeISetup φ _hφ _hdeg
    ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support avoidance** (Coq `tiA_PWG` restricted to `Ŵ^G`): for
a type-I maximal `L`, the Dade support `Ã(L)` avoids the regular-set saturation
`Ŵ^G = (W ∖ (W₁ ∪ W₂))^G` — an `Ã(L)`-element has a prime divisor of `|L_F|` in its order
(`exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport` + `A(L) ⊆ L_F^#`), while a
`Ŵ^G`-element has order dividing `|W| = p q`, coprime to `|L_F|` ((8.17.a)
`card_LF_coprime_pq`).  The conjugation-free core of `typeIBetaL_betaS_disjoint_support`. -/
theorem typeI_dadeSupport_avoids_regular [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∀ x ∈ OddOrder.GroupTheory.conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      x ∉ typeISetup.dadeData.dade.dadeSupport := by
  intro x hx hxD
  -- L-side: a prime `r ∣ |L_F|` divides `orderOf x`
  obtain ⟨a, haA, r, hr, hra, hrx⟩ :=
    typeISetup.dadeData.dade.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport hxD
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG typeISetup.maximal
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
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
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
    have havoid := typeI_dadeSupport_avoids_regular _hG hyp dataL.typeIHyp
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
theorem typeIBetaL_inner_eta_row_sub_eq_zero [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j j' : Fin hyp.p) (hj : (j : ℕ) ≠ 0) (hj' : (j' : ℕ) ≠ 0) :
    ClassFunction.inner (typeIBetaL typeISetup φ)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j - hyp.eta ⟨0, hyp.q_prime.pos⟩ j') = 0 := by
  classical
  have h1 := gammaGrid_defGamma _hG hyp j hj
  have h2 := gammaGrid_defGamma _hG hyp j' hj'
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
      (typeIBetaL_dadeS_betaGrid_disjoint_support _hG hyp typeISetup φ _hφ _hdeg j' hj'),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_dadeS_betaGrid_disjoint_support _hG hyp typeISetup φ _hφ _hdeg j hj),
    sub_zero]

/-- **(13.19.c), first clause (row form)**: `(β_L^τ, η_{0j})` is independent of `j ≥ 1` — by
(13.18.c) `j`-independence (`gammaGrid_defGamma`), `η_{0j} − η_{0j'} = τ_S(β_{j'}) − τ_S(β_j)`,
and (13.19.a) support disjointness kills both `(β_L^τ, τ_S(β_·))` terms
(`typeIBetaL_inner_eta_row_sub_eq_zero`). -/
theorem typeIBetaL_eta_row_constant [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
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
  have h := typeIBetaL_inner_eta_row_sub_eq_zero _hG hyp typeISetup φ _hφ _hdeg j j' hj hj'
  convert h using 2
  exact Subsingleton.elim _ _

/-- **(13.19.c), first clause (column form)**: the S↔T-swapped row constancy — the
`typeIBetaL_eta_row_constant` instance at `hyp.swap` (Coq's re-instantiation of the section
with the pair roles interchanged).  The swap's `η`-grid is the transpose, so its row-`0`
constancy *is* the column constancy of `hyp.eta`; `β_L^τ` is `hyp`-independent, so no
transport is needed on the left argument.  Takes the (14.9)-conclusional `IsTypeP2 T` (like
`typeI_caseC_dual_dichotomy`); the reconciled `TypePData T` and the ν-side grid supply come
from `reconciled_typePData_T` and the `nuGridSupply` pin. -/
theorem typeIBetaL_eta_col_constant [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
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
  exact typeIBetaL_eta_row_constant _hG
    (hyp.swap hT2 Tdata hU hW1 hW2 (hyp.nuGridSupply _hG))
    typeISetup φ _hφ _hdeg i i' hi hi'

/-! #### (13.19.c) dichotomy — the isolated deep obligation

We prove `typeI_caseC_dichotomy` for the **distinguished coherent-family member** `ζ_0 = dataL.zeta 0`
(so the §7.8 `betaDecomp`/`normEstimates` of the bundle apply directly), and pass `ζ_0` as the
producer's `φ`.  The pieces: the bridge `β_L^τ = (dataL.h78 hG).beta`, the parity core
`⟨β_S^τ, ζ_0^{τ₁}⟩ + ⟨β_L^τ, η_{01}⟩ ≡ 1 (mod 2)`, and the two case bounds. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Bridge**: `β_L^τ = τ₁(Ind_H^L 1_H − ζ_0)` at the distinguished member `ζ_0 = dataL.zeta 0` is
literally the §7.8 `beta` of the bundle (`(dataL.h78 hG).beta = τ(Ind_H^L 1_H − ζ_0)`).  Both are
the Dade image of `Ind_H^L 1_H − ζ_0`; the §9 `Hypothesis71.τ` and the §7 `tau` agree on supported
inputs (`toHypothesis71_tau_apply`), and `ζ_{ind1H} = Ind_H^L 1_H` (`dataL.triv`). -/
theorem typeIBetaL_zeta0_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    typeIBetaL dataL.typeIHyp (dataL.zeta 0) = (dataL.h78 hG).beta := by
  haveI := dataL.kernelIn_normal
  rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
  change dataL.typeIHyp.tau _ = dataL.typeIHyp.toHypothesis71.τ _
  rw [dataL.typeIHyp.toHypothesis71_tau_apply]
  apply congrArg dataL.typeIHyp.tau
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - dataL.zeta 0
    = (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).ind1H
      - (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct
  rw [dataL.h78_ind1H_eq, dataL.h78_zeta_eq, dataL.h78_zetaDistinct_eq, dataL.h78_zeta_eq]
  congr 1
  -- `Ind_H^L 1_H = ζ_{ind1H}` (`θ ind1H = 1_H`, `dataL.triv`)
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L))
    = ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
  rw [dataL.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) parity core** (Coq `odd_bSphi_bLeta`): at the distinguished member `ζ_0`,
the S-pairing `bSphi = ⟨β_S^τ, ζ_0^{τ₁}⟩` and the `η`-pairing `bLeta = ⟨β_L^τ, η_{01}⟩` are
integers whose **sum is odd**.  From `0 = ⟨β_L^τ, β_S^τ⟩` (disjoint support (13.19.a)),
`β_L^τ = 1 − ζ_0^{τ₁} + Δ_L` (the §7.8 residual `delta`), `β_S^τ = 1 − η_{01} + Γ_S`
((13.18.c) `gammaGrid_defGamma`), and `⟨Δ_L, Γ_S⟩` even (`cfdot_real_vchar_even`: both real
virtual characters orthogonal to `1_G`). -/
theorem typeI_caseC_parity [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    ∃ nS nL : ℤ,
      ClassFunction.inner (tauSbetaGrid hG hyp)
          (dataL.coh.extension (dataL.zeta 0)) = (nS : ℂ) ∧
        ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
            (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          = (nL : ℂ) ∧
        Odd (nS + nL) := by
  classical
  -- Abbreviations (kept as explicit terms to avoid `set`-fold clashes with lemma outputs).
  have hj1lt : (1 : ℕ) < hyp.p := by have := hyp.three_le_p; omega
  -- `ζ_0^{τ₁} = ν(ζ_0)` (definitional bridge).
  have hνζ : (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct)
      = dataL.coh.extension (dataL.zeta 0) := rfl
  -- ZIrr memberships.
  have hζextZ : dataL.coh.extension (dataL.zeta 0) ∈ OddOrder.RepresentationTheory.ZIrr G :=
    dataL.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)))
  have hΓSZ : GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := gammaGrid_mem_ZIrr hG hyp
  have hβLZ : (dataL.h78 hG).beta ∈ OddOrder.RepresentationTheory.ZIrr G :=
    (dataL.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)
  have hη01Z : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp _ _
  -- `β_S^τ = Γ_S + 1 − η_{01}`  ((13.18.c) `gammaGrid_defGamma`).
  have hβSdecomp : tauSbetaGrid hG hyp
      = GammaGrid hG hyp + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ := by
    have h := gammaGrid_defGamma hG hyp ⟨1, hj1lt⟩ (by simp)
    rw [tauSbetaGrid, ← h]; abel
  -- `Δ_L = β_L^τ − 1 + ζ_0^{τ₁}`, hence `β_L^τ = 1 − ζ_0^{τ₁} + Δ_L`.
  have hΔ : (dataL.h78 hG).delta
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + dataL.coh.extension (dataL.zeta 0) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.delta, hνζ]
  have hβLdecomp : (dataL.h78 hG).beta
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - dataL.coh.extension (dataL.zeta 0)
        + (dataL.h78 hG).delta := by rw [hΔ]; abel
  -- The two output integers.
  obtain ⟨nS, hnS⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hΓSZ hζextZ
  obtain ⟨nL, hnL⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hβLZ hη01Z
  -- `⟨Δ_L, Γ_S⟩` is an even integer  (`cfdot_real_vchar_even`, both real virtual `⊥ 1`).
  obtain ⟨z, a, b, hz, ha, hb, heven⟩ := cfdot_real_vchar_even hG.odd
    (dataL.delta_mem_ZIrr hG) (dataL.delta_isReal hG) hΓSZ (gammaGrid_real hG hyp)
  have hΔ_one : ClassFunction.inner (dataL.h78 hG).delta
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)
  have hΓS_one : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := gammaGrid_orthogonal_one hG hyp
  have ha0 : a = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΔ_one] at ha
    exact_mod_cast ha
  have hb0 : b = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΓS_one] at hb
    exact_mod_cast hb
  have hzeven : Even z := by rw [ha0, hb0] at heven; simpa using heven
  -- vanishing inner products.
  have hζ_one : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [← hνζ]; exact (dataL.h78 hG).zetaImage_orth_one (dataL.betaDecomp hG)
  have hζ_eta : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 :=
    coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _
      (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
  have h_one_ext : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_one, star_zero]
  have h_eta_ext : ClassFunction.inner (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_eta, star_zero]
  have hone_eta : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00, OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
      if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by simp))]
  have hone_one : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one
  -- reversed-direction pieces.
  have h_one_ΓS : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (GammaGrid hG hyp) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hΓS_one, star_zero]
  have h_ζext_ΓS : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (GammaGrid hG hyp) = (nS : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hnS,
      star_intCast]
  -- `⟨Δ_L, η_{01}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`.
  have hΔ_eta : ClassFunction.inner (dataL.h78 hG).delta
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = (nL : ℂ) := by
    rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, hone_eta, hζ_eta,
      sub_zero, add_zero, hnL]
  -- `⟨β_S^τ, ζ_0^{τ₁}⟩ = ⟨Γ_S, ζ_0^{τ₁}⟩ = nS`.
  have hbS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
      = (nS : ℂ) := by
    rw [hβSdecomp, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      hnS, h_one_ext, h_eta_ext, add_zero, sub_zero]
  refine ⟨nS, nL, hbS, by rw [typeIBetaL_zeta0_eq_h78_beta hG dataL]; exact hnL, ?_⟩
  -- degree of the distinguished member.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- Parity: `0 = ⟨β_L^τ, β_S^τ⟩ = 1 − nS − nL + z`, hence `nS + nL = 1 + z` is odd.
  have hdisj : ClassFunction.inner ((dataL.h78 hG).beta) (tauSbetaGrid hG hyp) = 0 := by
    rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL]
    exact OddOrder.RepresentationTheory.ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_betaS_disjoint_support hG hyp dataL.typeIHyp _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0)
  have hkey : (0 : ℂ) = 1 - (nS : ℂ) - (nL : ℂ) + (z : ℂ) := by
    have e := hdisj
    rw [hβLdecomp, hβSdecomp] at e
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_add_right, ClassFunction.inner_sub_right] at e
    rw [hone_one, hone_eta, h_one_ΓS, hζ_one, hζ_eta, h_ζext_ΓS, hΔ_one, hΔ_eta, ← hz] at e
    linear_combination -e
  have hInt : nS + nL = 1 + z := by
    have h2 : ((nS + nL : ℤ) : ℂ) = ((1 + z : ℤ) : ℂ) := by push_cast; linear_combination hkey
    exact_mod_cast h2
  rw [hInt]
  obtain ⟨k, hk⟩ := hzeven
  exact ⟨k, by omega⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) case (c2) bound**: if `bLeta = ⟨β_L^τ, η_{01}⟩ ≠ 0` (the `η`-parity is odd),
then `p ≤ e`.  The §7.8 residual `Γ_L = betaDecomp.Gamma` has `⟨Γ_L, η_{0j}⟩ = bLeta` for every
`j ≠ 0` (from `beta_eq`, row constancy (13.19.c), and `1/ζ_0^{τ₁}/W_L ⊥ η`), so the Bessel
inequality against `‖Γ_L‖² ≤ e − 1` ((7.8.b) `normEstimates`) over the `p − 1` orthonormal
`η_{0j}` gives `(p − 1)·bLeta² ≤ ‖Γ_L‖² ≤ e − 1`, hence `p − 1 ≤ e − 1`. -/
theorem typeI_caseC_bound_c2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nL : ℤ)
    (hnL : ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = (nL : ℂ))
    (hnL0 : nL ≠ 0) :
    hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index := by
  classical
  haveI := dataL.kernelIn_normal
  have hp0 : (0 : ℕ) < hyp.p := hyp.p_prime.pos
  -- `e = [L:H]` in the two forms.
  have he_eq : (dataL.h78 hG).complementIndex = ((maxNilpotentNormalHall L).subgroupOf L).index := by
    rw [dataL.complementIndex_eq hG]
    congr 1
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- degree hypothesis for the row-constancy citation.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- `Γ_L = β_L^τ − 1 + ζ_0^{τ₁} − a·W_L`.
  have hΓ_eq : (dataL.betaDecomp hG).Gamma
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
        - ((dataL.betaDecomp hG).a : ℂ) • (dataL.h78 hG).weightedNuSum := by
    rw [(dataL.betaDecomp hG).beta_eq]; abel
  -- `⟨Γ_L, η_{0j}⟩ = nL`  for every `j ≠ 0`.
  have hXη : ∀ (j : Fin hyp.p), (j : ℕ) ≠ 0 →
      ClassFunction.inner (dataL.betaDecomp hG).Gamma (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
    intro j hj
    -- `⟨β_L^τ, η_{0j}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`  (row constancy).
    have hβη : ClassFunction.inner ((dataL.h78 hG).beta) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
      rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL,
        typeIBetaL_eta_row_constant hG hyp dataL.typeIHyp (dataL.zeta 0)
          (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0 j
          ⟨1, by have := hyp.three_le_p; omega⟩ hj (by simp), hnL]
    -- `⟨1, η_{0j}⟩ = 0`  (`η_{00} = 1`, orthonormal).
    have h1η : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ by
        rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
        if_neg (by rintro ⟨-, h2⟩; exact hj (congrArg Fin.val h2).symm)]
    -- `⟨ζ_0^{τ₁}, η_{0j}⟩ = 0`  (coherent image `⊥ η`).
    have hζη : ClassFunction.inner
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct)))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
          = dataL.coh.extension (dataL.zeta 0) from rfl]
      exact coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
    -- `⟨W_L, η_{0j}⟩ = 0`  (each coherent image `⊥ η`).
    have hWη : ClassFunction.inner ((dataL.h78 hG).weightedNuSum)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).weightedNuSum
          = ∑ i ∈ (Finset.univ.erase (dataL.h78 hG).ind1H),
              ((dataL.h78 hG).hyp76.zeta i (1 : ↥L) /
                ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct) (1 : ↥L) *
                  ClassFunction.inner ((dataL.h78 hG).hyp76.zeta i)
                    ((dataL.h78 hG).hyp76.zeta i))) •
                (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
        inner_sum_left _ _ _]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [ClassFunction.inner_smul_left,
        show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
          = dataL.coh.extension (dataL.zeta i) from rfl,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _
          (dataL.zeta_mem_Sset (by
            rw [← dataL.h78_ind1H_eq hG]; exact (Finset.mem_erase.mp hi).1)) _ _, mul_zero]
    rw [hΓ_eq, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hβη, h1η, hζη, hWη,
      mul_zero, sub_zero, add_zero, sub_zero]
  -- Bessel bridge over the `p − 1` orthonormal `η_{0j}` (`j ≠ 0`).
  set B : Finset (Fin hyp.p) := Finset.univ.erase ⟨0, hyp.p_prime.pos⟩ with hB
  have hcardB : B.card = hyp.p - 1 := by
    rw [hB, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hbound := (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  have happly := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := Fin hyp.p) B (fun j => hyp.eta ⟨0, hyp.q_prime.pos⟩ j) (fun _ => nL) (fun _ => (1 : ℚ))
    ((dataL.betaDecomp hG).Gamma)
    ((dataL.betaDecomp hG).Gamma
      - ∑ j ∈ B, (((nL : ℝ) : ℂ)) • hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
    (((dataL.h78 hG).complementIndex : ℚ) - 1)
    (by abel)
    (fun i _ j _ => by
      rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp]
      by_cases hij : i = j
      · rw [if_pos ⟨rfl, hij⟩, if_pos hij]; norm_num
      · rw [if_neg (fun h => hij h.2), if_neg hij])
    (fun j hj => by
      have hj0 : (j : ℕ) ≠ 0 := by
        rintro h0; exact (Finset.mem_erase.mp hj).1 (Fin.ext h0)
      rw [ClassFunction.inner_sub_left, inner_sum_left,
        Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
          rw [ClassFunction.inner_smul_left,
            OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
            if_neg (by rintro ⟨-, h2⟩; exact hkj h2), mul_zero]),
        ClassFunction.inner_smul_left,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp, if_pos ⟨rfl, rfl⟩, mul_one,
        hXη j hj0]
      push_cast; ring)
    (fun _ _ => by norm_num)
    (fun _ _ => hnL0)
    (by
      calc (ClassFunction.inner ((dataL.betaDecomp hG).Gamma)
              ((dataL.betaDecomp hG).Gamma)).re
          = (dataL.h78 hG).gammaNormSq (dataL.betaDecomp hG) := rfl
        _ ≤ ((dataL.h78 hG).complementIndex : ℝ) - 1 := hbound
        _ = (((((dataL.h78 hG).complementIndex : ℚ) - 1 : ℚ)) : ℝ) := by push_cast; ring)
  -- `∑ 1 = p − 1 ≤ e − 1`, hence `p ≤ e`.
  rw [Finset.sum_const, hcardB, nsmul_eq_mul, mul_one] at happly
  have hpe : ((hyp.p : ℚ) - 1) ≤ ((dataL.h78 hG).complementIndex : ℚ) - 1 := by
    have : ((hyp.p - 1 : ℕ) : ℚ) = (hyp.p : ℚ) - 1 := by
      rw [Nat.cast_sub hp0]; norm_num
    rwa [this] at happly
  rw [← he_eq]
  have : (hyp.p : ℚ) ≤ ((dataL.h78 hG).complementIndex : ℚ) := by linarith
  exact_mod_cast this

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`φ`-invariance identity** for the (13.19.c) dichotomy: for a degree-`e` member
`φ ∈ 𝓛`, the coherent-image difference equals the `β_L^τ` difference,
`φ^{τ₁} − ζ_0^{τ₁} = β_L^τ(ζ_0) − β_L^τ(φ)`.  Both sides are `τ₁(φ − ζ_0)`: `φ = ζ_k` with
`d_k = 1` (equal degree, `exists_zeta_index_of_mem_Sset` + `zeta_deg`), so `φ − ζ_0` is
`A(L)`-supported (`psi_support`), where the coherent extension agrees with `τ = typeIHyp.tau`
(`extends_on_supported`); and `β_L^τ(ζ_0) − β_L^τ(φ) = τ(Ind − ζ_0) − τ(Ind − φ) = τ(φ − ζ_0)`
by linearity.  This is the sole bridge from the `ζ_0`-based parity core/case bounds to the
producer's arbitrary degree-`e` `φ`. -/
theorem coh_extension_sub_zeta0_eq_typeIBetaL_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ := by
  classical
  haveI := dataL.kernelIn_normal
  obtain ⟨k, hk_ne, hkφ⟩ := exists_zeta_index_of_mem_Sset hG dataL hφ
  -- `ζ_0(1) = e`, hence `d_k = 1` (equal degree).
  have hζ01 : dataL.zeta 0 (1 : ↥L) = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hidx_ne : (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdk1 : dataL.d k = 1 := by
    have hzk := dataL.zeta_deg k
    rw [hkφ, hdeg, hζ01] at hzk
    have hmul : dataL.d k * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)
        = 1 * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
      rw [one_mul]; exact hzk.symm
    exact mul_right_cancel₀ hidx_ne hmul
  -- `φ − ζ_0 ∈ zSupportedSpan 𝓛 A`.
  have hmem : (φ - dataL.zeta 0) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan dataL.typeIHyp.Sset dataL.typeIHyp.A := by
    refine (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff).mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ)
        (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero))), ?_⟩
    have hval : φ - dataL.zeta 0 = dataL.zeta k - dataL.d k • dataL.zeta 0 := by
      rw [hkφ, hdk1, one_smul]
    rw [hval]
    exact dataL.psi_support hG k
  -- Both sides equal `τ(φ − ζ_0)`.
  have hR : dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    rw [← map_sub]; exact dataL.coh.extends_on_supported _ hmem
  have hL : typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    simp only [typeIBetaL]
    rw [← map_sub]
    congr 1
    abel
  rw [hR, hL]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) `β_S`-pairing `φ`-invariance**: `(β_S^τ, φ^{τ₁}) = (β_S^τ, ζ_0^{τ₁})` for any
degree-`e` member `φ ∈ 𝓛`.  The difference is `(β_S^τ, β_L^τ(ζ_0) − β_L^τ(φ))`
(`coh_extension_sub_zeta0_eq_typeIBetaL_sub`), and each `(β_S^τ, β_L^τ(ψ))` vanishes by the
(13.19.a) support disjointness (`typeIBetaL_betaS_disjoint_support`). -/
theorem tauSbetaGrid_inner_coh_extension_eq_zeta0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension φ)
      = ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0)) := by
  classical
  haveI := dataL.kernelIn_normal
  have hζ01 : dataL.zeta 0 (1 : ↥L) = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hid := coh_extension_sub_zeta0_eq_typeIBetaL_sub hG dataL φ hφ hdeg
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_right, hid, ClassFunction.inner_sub_right,
    ClassFunction.inner_eq_zero_of_disjoint_support
      (Disjoint.symm (typeIBetaL_betaS_disjoint_support hG hyp dataL.typeIHyp _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hζ01)),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (Disjoint.symm (typeIBetaL_betaS_disjoint_support hG hyp dataL.typeIHyp _ hφ hdeg)),
    sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) `β_L`-`η`-pairing `φ`-invariance**: `(β_L^τ(φ), η_{0j}) = (β_L^τ(ζ_0), η_{0j})`
for any degree-`e` member `φ ∈ 𝓛`.  The difference is `(β_L^τ(φ) − β_L^τ(ζ_0), η_{0j})`, and
`β_L^τ(φ) − β_L^τ(ζ_0) = ζ_0^{τ₁} − φ^{τ₁}` (`coh_extension_sub_zeta0_eq_typeIBetaL_sub`);
each coherent image is `⊥ η` ((13.19.b) `coherent_extension_orthogonal_eta_of_mem_Sset`). -/
theorem typeIBetaL_inner_eta_eq_zeta0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) (j : Fin hyp.p) :
    ClassFunction.inner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
      = ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
          (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) := by
  classical
  have hid := coh_extension_sub_zeta0_eq_typeIBetaL_sub hG dataL φ hφ hdeg
  have hid' : typeIBetaL dataL.typeIHyp φ - typeIBetaL dataL.typeIHyp (dataL.zeta 0)
      = dataL.coh.extension (dataL.zeta 0) - dataL.coh.extension φ := by
    rw [show (typeIBetaL dataL.typeIHyp φ - typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        = -(typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ) from
          (neg_sub _ _).symm,
      ← hid, neg_sub]
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_left, hid', ClassFunction.inner_sub_left,
    coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _
      (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _,
    coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _ hφ _ _, sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(β_S^τ, ζ_i^{τ₁}) = d_i·bSphi`** (`i ≠ ind1H`): the `β_S^τ`-pairing is constant along the
`L`-family up to degree.  For `i ≠ 0` the difference `ζ_i^{τ₁} − d_i ζ_0^{τ₁} = τ(ζ_i − d_i ζ_0)`
(`hagree`) is an `Ã(L)`-supported Dade image, disjoint from `supp β_S^τ` ((13.19.a)); for `i = 0`
it is `bSphi` (`d_0 = 1`). -/
theorem inner_tauSbetaGrid_coh_ext_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = dataL.d i * (nS : ℂ) := by
  classical
  haveI := dataL.kernelIn_normal
  by_cases hi0 : i = 0
  · subst hi0
    rw [dataL.d_zero_eq_one, one_mul]; exact hnS
  · have hsupp : (dataL.coh.extension (dataL.zeta i)
        - dataL.d i • dataL.coh.extension (dataL.zeta 0)).support
        ⊆ dataL.typeIHyp.dadeData.dade.dadeSupport := by
      have hagree := dataL.hagree hG i hi0 hi
      rw [← hagree]
      intro g hg
      rw [ClassFunction.mem_support] at hg
      by_contra hgnot
      have hdade := (dataL.typeIHyp.dadeData.dade.fullDadeIsometryData
        dataL.typeIHyp.hconj).toDadeIsometryData.isDadeMap
      exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)
    have hzero : ClassFunction.inner (tauSbetaGrid hG hyp)
        (dataL.coh.extension (dataL.zeta i)
          - dataL.d i • dataL.coh.extension (dataL.zeta 0)) = 0 := by
      apply ClassFunction.inner_eq_zero_of_disjoint_support
      rw [tauSbetaGrid]
      exact (dadeSupport_betaGrid_disjoint_support hG hyp dataL.typeIHyp _ hsupp
        ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)).symm
    rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      dataL.d_star, hnS, sub_eq_zero] at hzero
    exact hzero

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`** (`i ≠ ind1H`): the `η`-orthogonal residual `Γ_S = GammaGrid`
pairs with the `L`-family exactly as `β_S^τ` does — `Γ_S = β_S^τ − 1 + η_{01}` (`gammaGrid_defGamma`),
and the `1_G`/`η_{01}` parts are orthogonal to the coherent image (`(betaDecomp).orth_one`,
(13.19.b)). -/
theorem inner_gammaGrid_coh_ext_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (GammaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = (nS : ℂ) * dataL.d i := by
  classical
  have hGdecomp : GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
    have h := gammaGrid_defGamma hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    rw [tauSbetaGrid, ← h]
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by rw [dataL.h78_ind1H_eq]; exact hi
  have h1 : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [show dataL.coh.extension (dataL.zeta i)
        = (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
      OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      (dataL.betaDecomp hG).orth_one i hi_h78, star_zero]
  have hη : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _ (dataL.zeta_mem_Sset hi) _ _,
      star_zero]
  rw [hGdecomp, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, h1, hη,
    inner_tauSbetaGrid_coh_ext_zeta_eq hG hyp dataL nS hnS hi, sub_zero, add_zero, mul_comm]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) case (c1) bound**: if `bSphi = (β_S^τ, ζ_0^{τ₁}) ≠ 0` (the S-parity is odd),
then `(|H| − 1)/e ≤ (u − 1)/q`.  The `η`-orthogonal projection `Y = bSphi·Σ d_i ζ_i^{τ₁}` of
`Γ_S = GammaGrid` (coefficients `(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`,
`inner_gammaGrid_coh_ext_zeta_eq`) satisfies the (13.18.d) bound `‖Y‖² ≤ (u−1)/q`
(`gammaGrid_Y_norm_bound`); with `‖Y‖² = bSphi²·Σ d_i²`, `Σ d_i² = (|H|−1)/e`
(`card_index_mul_sum_induced_family_degree_sq`), and `bSphi² ≥ 1`, this gives the bound.
Mirror of the M-side `bessel_bound_of_inner_beta_zeta_ne_zero` (S16_PairingBessel). -/
theorem typeI_caseC_bound_c1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    (hnS0 : nS ≠ 0) :
    (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) := by
  classical
  haveI := dataL.kernelIn_normal
  -- index/card bridges to `kernelIn`.
  have he_eq : (dataL.kernelIn).index = ((maxNilpotentNormalHall L).subgroupOf L).index := by
    show ((dataL.typeIHyp.typeI.typeF.H).subgroupOf L).index = _
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hcard_eq : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.typeIHyp.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
  -- the weighted `L`-family vector `v = Σ d_i ζ_i^{τ₁}`.
  set v : ClassFunction G ℂ := ∑ i ∈ Finset.univ.erase dataL.ind1H,
    dataL.d i • dataL.coh.extension (dataL.zeta i) with hvdef
  -- orthonormality of the `ζ_i^{τ₁}`.
  have hON : ∀ i ∈ Finset.univ.erase dataL.ind1H, ∀ j ∈ Finset.univ.erase dataL.ind1H,
      ClassFunction.inner (dataL.coh.extension (dataL.zeta i))
        (dataL.coh.extension (dataL.zeta j)) = if i = j then 1 else 0 := by
    intro i hi j hj
    rw [dataL.nu_isometry i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact IsIrreducibleCharacter.inner_self_eq_one
        (dataL.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1)
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S09.Cert.induce_family_orthogonal_of_injective dataL.kernelIn dataL.θ dataL.inj i j hij
  -- `⟨v, v⟩ = Σ d_i²`.
  have hvv : ClassFunction.inner v v
      = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
        rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi j hj,
          if_neg (Ne.symm hji), mul_zero]),
      OddOrder.RepresentationTheory.inner_smul_right, hON i hi i hi, if_pos rfl,
      dataL.d_star, mul_one, sq]
  -- `Σ d_i² = (|kernelIn| − 1)/e`  (degree-square sum).
  have hidx_ne : ((dataL.kernelIn).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg_sum := card_index_mul_sum_induced_family_degree_sq dataL.hFrob dataL.θ
    dataL.ind1H dataL.triv dataL.inj dataL.cover
  have hSval : ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2
      = ((Nat.card ↥dataL.kernelIn : ℂ) - 1) / ((dataL.kernelIn).index : ℂ) := by
    rw [eq_div_iff hidx_ne, mul_comm]
    exact hdeg_sum
  -- `⟨GammaGrid, v⟩ = nS·Σ d_i²`.
  have hGv : ClassFunction.inner (GammaGrid hG hyp) v
      = (nS : ℂ) * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star,
      inner_gammaGrid_coh_ext_zeta_eq hG hyp dataL nS hnS (Finset.mem_erase.mp hi).1, sq]
    ring
  -- the projection `Y = nS • v` and the complement `X = GammaGrid − Y`.
  set Y : ClassFunction G ℂ := (nS : ℂ) • v with hYdef
  -- `Y ⊥ η`.
  have hYeta : ∀ (a : Fin hyp.q) (b : Fin hyp.p), ClassFunction.inner Y (hyp.eta a b) = 0 := by
    intro a b
    rw [hYdef, hvdef, ClassFunction.inner_smul_left, inner_sum_left]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [ClassFunction.inner_smul_left,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hyp dataL _
          (dataL.zeta_mem_Sset (Finset.mem_erase.mp hi).1) a b, mul_zero], mul_zero]
  -- `⟨Y, Y⟩ = nS²·Σ d_i²`.
  have hYY : ClassFunction.inner Y Y
      = (nS : ℂ) ^ 2 * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hYdef, ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hvv, show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- `⟨GammaGrid − Y, Y⟩ = 0`.
  have hXY : ClassFunction.inner (GammaGrid hG hyp - Y) Y = 0 := by
    rw [ClassFunction.inner_sub_left, hYY, hYdef,
      OddOrder.RepresentationTheory.inner_smul_right, hGv,
      show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- the (13.18.d) bound.
  have hbound := gammaGrid_Y_norm_bound hG hyp (GammaGrid hG hyp - Y) Y (by abel) hXY hYeta
  -- the real value `Sr = (|kernelIn| − 1)/e` of `Σ d_i²`.
  set Sr : ℝ := ((Nat.card ↥dataL.kernelIn : ℝ) - 1) / ((dataL.kernelIn).index : ℝ) with hSrdef
  have hSc : (∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2) = (Sr : ℂ) := by
    rw [hSval, hSrdef]; push_cast; ring
  have hYYre : (ClassFunction.inner Y Y).re = (nS : ℝ) ^ 2 * Sr := by
    rw [hYY, hSc,
      show (nS : ℂ) ^ 2 * (Sr : ℂ) = (((nS : ℝ) ^ 2 * Sr : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [hYYre] at hbound
  -- positivity facts.
  have hidx_pos : (0 : ℝ) < ((dataL.kernelIn).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard1 : (1 : ℝ) ≤ (Nat.card ↥dataL.kernelIn : ℝ) := by exact_mod_cast Nat.card_pos
  have hSr_nonneg : (0 : ℝ) ≤ Sr := by
    rw [hSrdef]; exact div_nonneg (by linarith) hidx_pos.le
  have hnS_sq : (1 : ℝ) ≤ (nS : ℝ) ^ 2 := by
    have hint : (1 : ℤ) ≤ nS ^ 2 := by
      nlinarith [Int.one_le_abs hnS0, sq_abs nS]
    exact_mod_cast hint
  -- `Sr ≤ nS²·Sr = ‖Y‖² ≤ (u−1)/q`.
  have hfinal_R : Sr ≤ (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) :=
    le_trans (le_mul_of_one_le_left hSr_nonneg hnS_sq) hbound
  -- `1 ≤ u` (from `|U| = u·c`).
  have hu_pos : 1 ≤ hyp.u := by
    have hcard : 0 < Nat.card ↥hyp.U := Nat.card_pos
    rw [hyp.card_U_eq_uc] at hcard
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h0
    · rw [h0, zero_mul] at hcard; exact absurd hcard (lt_irrefl 0)
    · exact h0
  -- cast the ℝ inequality back to the ℚ goal (through `kernelIn`).
  rw [← hcard_eq, ← he_eq]
  have hcard_ne : 1 ≤ Nat.card ↥dataL.kernelIn := Nat.card_pos
  have goal_R : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ)
      ≤ ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ) := by
    have e1 : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ) = Sr := by
      rw [hSrdef, Nat.cast_sub hcard_ne]; push_cast; ring
    have e2 : ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ)
        = (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) := by
      rw [Nat.cast_sub hu_pos]; push_cast; ring
    rw [e1, e2]; exact hfinal_R
  exact_mod_cast goal_R

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) S-side dichotomy**: `(Γ_S, φ^{τ₁}) + (Γ_L, η_{01}) ≡ 1 (mod 2)` (from
`0 = (β_L^τ, β_S^τ)` via (13.19.a)/(13.18.a) and the evenness of `(Γ_L, Γ_S)` ((13.18.c)+(1.1))),
so one of (c1) `(β_S^τ, φ^{τ₁}) ≡ 1` — in which case (13.18.d) with `Γ_S`'s `𝓛^{τ₁}`-expansion
bounds `(|H|−1)/e = Σaᵢ² ≤ (u−1)/q` — or (c2) `(β_L^τ, η_{0j}) ≡ 1`, in which case the
`η`-coefficient parity forces `p ≤ e`.

Assembled from the `ζ_0`-based parity core (`typeI_caseC_parity`) and case bounds
(`typeI_caseC_bound_c1`/`typeI_caseC_bound_c2`) via the two `φ`-invariance bridges
(`tauSbetaGrid_inner_coh_extension_eq_zeta0`, `typeIBetaL_inner_eta_eq_zeta0`) and the
row constancy (`typeIBetaL_eta_row_constant`): `Odd (nS + nL)` dispatches to (c1) when `nS`
is odd, else `nL` is odd and (c2) holds. -/
theorem typeI_caseC_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauSbetaGrid _hG hyp) (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
        hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := by
  classical
  obtain ⟨nS, nL, hnS, hnL, hodd⟩ := typeI_caseC_parity _hG hyp dataL
  by_cases hSodd : Odd nS
  · -- case (c1): the S-pairing `(β_S^τ, φ^{τ₁})` is odd.
    -- ambient bridge (built before the instance-quantifier `intro`, to avoid re-elaboration).
    have hbridge : ClassFunction.inner (tauSbetaGrid _hG hyp) (dataL.coh.extension φ) = (nS : ℂ) :=
      (tauSbetaGrid_inner_coh_extension_eq_zeta0 _hG hyp dataL φ _hφ _hdeg).trans hnS
    refine Or.inl ⟨⟨nS, hSodd, ?_⟩, typeI_caseC_bound_c1 _hG hyp dataL nS hnS
      (by rintro rfl; obtain ⟨m, hm⟩ := hSodd; omega)⟩
    intro _ _
    convert hbridge using 2 <;> first | rfl | exact Subsingleton.elim _ _
  · -- case (c2): `nS` even, so `nL` is odd and `p ≤ e`.
    have hLodd : Odd nL := by
      rw [Int.not_odd_iff_even] at hSodd
      obtain ⟨a, ha⟩ := hSodd
      obtain ⟨b, hb⟩ := hodd
      exact ⟨b - a, by omega⟩
    have hnL0 : nL ≠ 0 := by rintro rfl; obtain ⟨m, hm⟩ := hLodd; omega
    -- ambient bridge: `(β_L^τ(φ), η_{0j}) = nL` for every `j ≠ 0` (row constancy + `φ`-invariance).
    have hbridge : ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = (nL : ℂ) := by
      intro j hj
      rw [typeIBetaL_eta_row_constant _hG hyp dataL.typeIHyp φ _hφ _hdeg j
          ⟨1, by have := hyp.three_le_p; omega⟩ hj (by norm_num),
        typeIBetaL_inner_eta_eq_zeta0 _hG hyp dataL φ _hφ _hdeg
          ⟨1, by have := hyp.three_le_p; omega⟩]
      exact hnL
    refine Or.inr ⟨fun j hj => ⟨nL, hLodd, ?_⟩,
      typeI_caseC_bound_c2 _hG hyp dataL nL hnL hnL0⟩
    intro _ _
    convert hbridge j hj using 2 <;> first | rfl | exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) T-side dichotomy** (S↔T swapped): the `typeI_caseC_dichotomy` instance at
`hyp.swap` — the swap's `tauSbetaGrid` is definitionally `tauTbetaGrid` (both are the
`'A0(T)`-Dade image of `Ind_{QW₂}^T 1 − ν_{10}`), its `u/q` are `v/p`, and its `η`-row-`0`
axis is the `η`-column-`0` axis.  Requires the `Tdata` reconciliations (supplied by the
producer from `reconciled_typePData_T`), so the swap's `A₀(T)`-carrier matches the one in
`tauTbetaGrid`'s statement. -/
theorem typeI_caseC_dual_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T) (Tdata : TypePData hyp.T)
    (hU : Tdata.U = hyp.V) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauTbetaGrid _hG hyp hT2 Tdata) (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧
        hyp.q ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) :=
  typeI_caseC_dichotomy _hG (hyp.swap hT2 Tdata hU hW1 hW2 (hyp.nuGridSupply _hG))
    dataL φ _hφ _hdeg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §13 producer for Peterfalvi (13.19).**  The Tier-A structure — `e = [L:H]`
(definitionally), the family `𝓛 = dataL.typeIHyp.Sset`, a chosen degree-`e` member `φ`
(`exists_Sset_apply_one_eq_index`), and the bridge images `β_L = typeIBetaL`,
`β_S = tauSbetaGrid`, `β_T = tauTbetaGrid` — is genuinely constructed; the (13.19.a)/(13.19.b)
facts are **proven** (`typeIBetaL_betaS_disjoint_support`,
`coherent_extension_orthogonal_eta_of_mem_Sset`); the remaining deep (13.19.c) facts are the
isolated `φ`-parametric obligations above, consumed field-by-field. -/
noncomputable def typeIOrthogonalityGridData_of_coherent78 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    TypeIOrthogonalityGridData hyp dataL :=
  { e := ((maxNilpotentNormalHall L).subgroupOf L).index
    e_eq_index := rfl
    Lset := dataL.typeIHyp.Sset
    phi := Classical.choose (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)
    phi_mem := (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
    phi_degree_eq_e :=
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2
    betaL := typeIBetaL dataL.typeIHyp
      (Classical.choose (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp))
    betaS := tauSbetaGrid _hG hyp
    betaT := tauTbetaGrid _hG hyp hT2
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
    disjoint_support := typeIBetaL_betaS_disjoint_support _hG hyp dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2
    betaL_eq := typeIBetaL_eq_tau_induce_sub dataL.typeIHyp _
    Ltau_orthogonal_eta := coherent_extension_orthogonal_eta_of_mem_Sset _hG hyp dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
    betaL_eta0_row_constant := typeIBetaL_eta_row_constant _hG hyp dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2
    betaL_eta0_col_constant := typeIBetaL_eta_col_constant _hG hyp hT2 dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2
    caseC := typeI_caseC_dichotomy _hG hyp dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2
    caseC_dual := typeI_caseC_dual_dichotomy _hG hyp hT2
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.2
      dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG dataL.typeIHyp)).2 }

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has `𝓛^{τ₁}` orthogonal to the `eta_ij`,
`(β_L^τ, η_{0j})` constant along each zero axis, and on each zero axis one of the two (13.19.c)
cases — the faithful conjunction forms `(c1) = parity ∧ degree bound` and
`(c2) = η-axis odd-parity ∧ p ≤ e` — holds.

De-opacified (W3 §15): the honest §14 content — the (12.6) coherence bundle
`S16.TypeICoherent78Data L` (`TypeICoherent78Data.nonempty`) with its (12.1) Dade setup
`typeISetup = dataL.typeIHyp` and genuine coherent extension `τ₁ = dataL.coh.extension` —
is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements.  `betaL_eta_independent` is instantiated to the faithful (13.19.c) first clause — the
zero-axis **constancy** of `(β_L^τ, η_{0j})`/`(β_L^τ, η_{i0})` (NOT orthogonality: in case (c2)
these inner products are odd).  The dichotomy implication fields (`caseC1_bound`,
`caseC2_eta0j_odd`, dual) are the conjunction projections.  The grid-dependent atoms come from the
faithful producer `typeIOrthogonalityGridData_of_coherent78`, whose type is the genuine (13.19)
grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(12.6)/(14.*): the type-I maximal `L` carries a genuine coherence bundle.
  obtain ⟨dataL⟩ := OddOrder.Peterfalvi.S16.TypeICoherent78Data.nonempty _hG hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_coherent78 _hG hyp hT2 dataL
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and
  -- conjunction-projection dichotomy implication fields.
  refine ⟨{ typeISetup := dataL.typeIHyp
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := dataL.coh.extension
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                ClassFunction.inner (dataL.coh.extension g.phi) (hyp.eta i j) = 0
            betaL_eta_independent :=
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
                    = ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')) ∧
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
                    = ClassFunction.inner g.betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩))
            caseC1 :=
              OddIntegerInner g.betaS (dataL.coh.extension g.phi) ∧
                (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ g.e
            caseC2_eta0j_odd := fun h => h.1
            caseC1_bound := fun h => h.2
            caseC1_dual :=
              OddIntegerInner g.betaT (dataL.coh.extension g.phi) ∧
                (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))
            caseC2_dual :=
              (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ g.e
            caseC2_dual_etai0_odd := fun h => h.1
            caseC1_dual_bound := fun h => h.2 },
    g.disjoint_support, g.Ltau_orthogonal_eta,
    ⟨g.betaL_eta0_row_constant, g.betaL_eta0_col_constant⟩, g.caseC, g.caseC_dual⟩

/-! ### Peterfalvi (14.5): exclusion of the small complement `E = W₁`

The (13.17.c) dichotomy leaves two shapes for the `W₁`-containing Frobenius complement `E` of a
type-I maximal `L ⊇ N_G(U)`: `E = W₁` (i.e. `E ≤ Q`) or `|E| = pq`.  The small branch is **not**
excluded at (13.17) — Peterfalvi rules it out only in the §14 endgame: (14.5) applies the
(13.19.c) dichotomy under the `q < p` normalization, and closes with `S` being of type II
(`N_G(U) ⊄ S`).  The earlier repo statement of `complement_not_le_Q` as an unconditional
(13.17)-cluster fact was an over-claim (Coq `FTtypeII_support_facts` (c) keeps the disjunction;
issue-3003 pattern); the faithful (14.5) form and its two consumers live here, downstream of the
(13.19) grid data they consume. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.5), core exclusion**: under the §14 normalization `q < p` and the type-II
fact `N_G(U) ⊄ S`, the `W₁`-containing Frobenius complement `E` of the type-I maximal
`L ⊇ N_G(U)` is not contained in `Q`.

*Proof (Pf p.87).*  If `E ≤ Q` then `E = E ⊓ Q = W₁` (`complement_inf_Q_eq_W1`), so the
Fitting-kernel index of `L` is `e = |W₁| = q < p`.  The (13.19.c) dichotomy
(`typeIOrthogonalityGridData_of_coherent78`) then cannot hold in case (c2) (which forces
`p ≤ e`), so the (c1) bound `(|H|−1)/e ≤ (u−1)/q` holds with `e = q`, giving `|H| ≤ u`.  With
`U ≤ H` ((13.17.b), hypothesis `hUH`) and `u ≤ |U|` this forces `H = U`, so
`L = H ⋊ E = U W₁ ≤ S` — contradicting `N_G(U) ≤ L` and `N_G(U) ⊄ S`. -/
theorem complement_not_le_Q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    ¬ frob.complement.map L.subtype ≤ hyp.Q := by
  intro hle
  -- `E ≤ Q` collapses `E` to `E ⊓ Q = W₁` (the proven (13.17.c) half)
  have hEW1 : frob.complement.map L.subtype = hyp.W1 := by
    have h := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
    rwa [inf_eq_left.mpr hle] at h
  -- hence the Fitting-kernel index of `L` is `|E| = |W₁| = q`
  have hEcard : Nat.card ↥frob.complement = hyp.q := by
    rw [show Nat.card ↥frob.complement
          = Nat.card ↥(frob.complement.map L.subtype) from
        Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
          L.subtype_injective).toEquiv, hEW1]
    exact hyp.q_eq_card_W1.symm
  have hindex : ((maxNilpotentNormalHall L).subgroupOf L).index = hyp.q := by
    rw [typeIFrobenius_kernel_index_eq_complement frob, hEcard]
  -- the (13.19) grid data for `L`
  obtain ⟨dataL⟩ := OddOrder.Peterfalvi.S16.TypeICoherent78Data.nonempty _hG hLmax hLI
  have hHL : dataL.typeIHyp.H = maxNilpotentNormalHall L := dataL.typeIHyp.typeI.typeF.H_eq
  set g := typeIOrthogonalityGridData_of_coherent78 _hG hyp hT2 dataL with hgdef
  have he_q : g.e = hyp.q := by rw [← g.e_eq_index, hindex]
  -- case (c2) is impossible: `p ≤ e = q < p`
  rcases g.caseC with ⟨-, hbound⟩ | ⟨-, hpe⟩
  swap
  · rw [he_q] at hpe
    omega
  -- case (c1): `(|H|−1)/q ≤ (u−1)/q` forces `|H| ≤ u ≤ |U| ≤ |H|`, so `H = U`
  rw [he_q] at hbound
  have hq0 : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hle_nat : Nat.card ↥dataL.typeIHyp.H - 1 ≤ hyp.u - 1 := by
    have h : ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) ≤ ((hyp.u - 1 : ℕ) : ℚ) := by
      have hmul := mul_le_mul_of_nonneg_right hbound hq0.le
      rwa [div_mul_cancel₀ _ hq0.ne', div_mul_cancel₀ _ hq0.ne'] at hmul
    exact_mod_cast h
  have hupos : 0 < hyp.u := by
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h
    · exfalso
      have hcard := hyp.card_U_eq_uc
      rw [h0, Nat.zero_mul] at hcard
      exact absurd hcard Nat.card_pos.ne'
    · exact h
  have hu_le_U : hyp.u ≤ Nat.card ↥hyp.U := by
    rw [hyp.card_U_eq_uc]
    have hc : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact Nat.le_mul_of_pos_right _ hc
  have hU_le_H : Nat.card ↥hyp.U ≤ Nat.card ↥(maxNilpotentNormalHall L) :=
    Subgroup.card_le_of_le hUH
  have hHpos : 0 < Nat.card ↥dataL.typeIHyp.H := Nat.card_pos
  have hcard_eq : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.U := by
    rw [← hHL] at hU_le_H ⊢
    omega
  have hUeq : maxNilpotentNormalHall L = hyp.U :=
    (Subgroup.eq_of_le_of_card_ge hUH (le_of_eq hcard_eq)).symm
  -- `L = H ⊔ E = U ⊔ W₁ ≤ S`, contradicting `N_G(U) ≤ L` with `N_G(U) ⊄ S`
  have hsup : (maxNilpotentNormalHall L).subgroupOf L ⊔ frob.complement = ⊤ := by
    have h := frob.frobenius.isComplement.sup_eq_top
    rwa [frob.typeI.typeF.H_eq] at h
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact h1.trans (Subgroup.map_subtype_le _)
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    rw [hyp.W_eq_inter] at h1
    exact h1.trans inf_le_left
  have hLS : L ≤ hyp.S := by
    have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hLtop, ← hsup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.subgroupOf_map_subtype]
      refine inf_le_left.trans ?_
      rw [hUeq]
      exact hUS
    · rw [hEW1]
      exact hW1S
  exact hNUS (hNUL.trans hLS)

/-- **Peterfalvi (14.5) order consequence.**  Under the (14.5) hypotheses the `W₁`-containing
Frobenius complement `E` of `L` has order `p q`.

*Proof (Pf p.82/p.87).*  `E ⊆ Q W₂` (`complement_le_QW2`), and `Q ⋊ W₂` has `Q ◁ Q W₂` with
`[Q W₂ : Q] = |W₂| = p` (`Q_W2_structure`).  The relative index `[E : E ∩ Q]` divides
`[Q W₂ : Q] = p` (normal-subgroup relative index inside `↥(Q W₂)`) and is `≠ 1` by the (14.5)
exclusion `E ⊄ Q` (`complement_not_le_Q`), hence `= p`; with `E ∩ Q = W₁` of order `q`
(`complement_inf_Q_eq_W1`), `|E| = |E ∩ Q| · [E : E ∩ Q] = q p`. -/
theorem complement_card_eq_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- `E ∩ Q = W₁` (proven (13.17.c) half); the (14.5) exclusion `E ⊄ Q`.
  have hInf := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
  have hnle := complement_not_le_Q _hG hyp hTTypeII hT2 hqp hNUS hLmax hLI hNUL hUH frob hW1E
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hEH : Em ≤ Hg := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp hTTypeII
  have hQleH : hyp.Q ≤ Hg := le_sup_left
  -- `|E ∩ Q| = |W₁| = q`.
  have hInfCard : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q := by rw [hInf]; exact hyp.q_eq_card_W1.symm
  -- `Q ◁ Q W₂` (as `Q W₂ ≤ N_G(Q)`).
  haveI hQnorm : (hyp.Q.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  -- `|Q W₂| = |Q| · p`.
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.Q * hyp.p := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W2 ⊓ hyp.Q = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.p_eq_card_W2]
    exact mul_comm _ _
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  -- `[Q W₂ : Q] = p`.
  have hindexH : (hyp.Q.subgroupOf Hg).index = hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hQpos hmul
  -- `[E : E ∩ Q] = Q.relIndex E` divides `[Q W₂ : Q] = p`, and is `≠ 1` (`E ⊄ Q`), hence `= p`.
  have hdvd : hyp.Q.relIndex Em ∣ hyp.p := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.Q.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.Q.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.Q.relIndex Em = hyp.p :=
    (hyp.p_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  -- `|E| = |E ∩ Q| · [E : E ∩ Q] = q · p`.
  have hEmcard : Nat.card ↥Em = hyp.q * hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Em)
    rw [show (hyp.Q.subgroupOf Em).index = hyp.p from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  -- transfer `|E.map| = |E|`.
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]
  exact mul_comm _ _

/-- **Peterfalvi (14.5), full form**: the `W₁`-containing Frobenius complement of the type-I
subgroup `L` over `N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).

Assembled from the order argument (`complement_card_eq_pq`) and the group-theoretic `∃ y`
extraction (`exists_mem_conj_W2_le_of_dvd_card`, Schur–Zassenhaus), the latter fed `E ⊆ Q W₂`
by the Huppert step (`complement_le_QW2`).  The `W₁ ⊆ E` hypothesis records Peterfalvi's choice
"let `E` be a complement to `H` in `L` such that `W₁ ⊂ E`". -/
theorem typeI_overNormalizer_complement [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq _hG hyp hTTypeII hT2 hqp hNUS hLmax hLI hNUL hUH frob hW1E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp hTTypeII
  have hEQW2 := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  -- `Q` is solvable: `Q = T_F ≤ T < ⊤`.
  haveI hQsolv : IsSolvable ↥hyp.Q := by
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hTlt : hyp.T < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1
    exact _hG.solvable_of_lt_top hyp.Q (lt_of_le_of_lt hQT hTlt)
  -- `p ∣ |E.map| = |E| = p q`.
  have hpE : hyp.p ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_right hyp.p hyp.q
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hQsolv hdisj hyp.p_prime
    hyp.p_eq_card_W2.symm hpQ hEQW2 hpE

/-- **Peterfalvi (14.5), packaged**: if `S` is type II (with the §14 normalization `q < p` and
the type-II consequence `N_G(U) ⊄ S`), a maximal subgroup over `N_G(U)` is type-I Frobenius,
contains `U` in its kernel, and its `W₁`-containing complement has order `p q` with a conjugate
`W₂^y` inside.  Assembled from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), a `W₁`-containing Frobenius decomposition
(`exists_typeIFrobeniusData_W1_le`), and the (14.5) complement structure
(`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ := typeI_overNormalizer_complement _hG hyp hTTypeII hT2 hqp hNUS
    hLmax hLtypeI hNUL hUH frob hW1E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

end OddOrder.Peterfalvi.S15

