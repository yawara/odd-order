/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_ComplementStructure
import OddOrder.Peterfalvi.S15_BridgeCharacterBasic

/-!
# Peterfalvi (13.18): the bridge characters `β_j` and `Γ`

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit): the (13.18) `S`-side
bridge character `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, its Dade image `τ_S(β_{#1})`, the residual
`Γ = τ_S(β_{#1}) − 1_G + η_{01}`, and the full (13.18.a–d) facts (support, norm,
`j`-independence, `⟨Γ,1⟩ = 0`, `Γ` real, and the `‖Y‖²` residual bound), packaged in
`BetaData` / `betaData_of_grid`.
-/

namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting
the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) :=
    indPW1_inner_self_of_c_eq_one hG hyp hc1
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`S10.not_isConj_typePACore_typePV`).

The route: `X := τ_S(μ-diff)` has `‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with
`η_{0j} − η_{01}` on the regular set via `τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`,
`H = ⊥`) + the prime-`TI` `μ`-value `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory,
cf. 9014); then `X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076
piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support hG j _hj
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG hnoV j _hj x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, full-grid form**:
`τ_S(μ_{i,j₁} − μ_{i,j₂}) = η_{i,j₁} − η_{i,j₂}` for any row `i` and distinct nontrivial columns
`j₁ ≠ j₂` (both `≠ 0`).  The all-rows/all-cols generalization of `tauS_mu_row0_cross` (Coq
`prDade_sub_TIirr` with the FT sign `δ = 1`): `X := τ_S(μ-diff)` is a norm-`2` `ZIrr` character
(Dade isometry on the `A₀(S)`-supported difference `tauS_mu_diff_support`) agreeing with
`η_{i,j₁} − η_{i,j₂}` on the regular set `V^S` (`tauS_mu_vanish_on_V`), so `S16.eta_diff_rigidity`
(Pf (3.8), general in the row `i`) pins it.  This is the per-row engine the reducible caseB
`R`-family sums over a μ-column: `τ_S(μ_j − μ̄_j) = ∑ᵢ τ_S(μ_{ij} − μ_{ik}) = ∑ᵢ(η_{ij} − η_{ik})`
(for the two column indices `j ≠ k` of `μ_j`, `μ̄_j`). -/
theorem tauS_mu_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) (hj12 : j1 ≠ j2) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu i j1 - hyp.mu i j2)
      = hyp.eta i j1 - hyp.eta i j2 := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  have hμaIrr : IsIrreducibleCharacter (hyp.mu i j1) := hyp.mu_irreducible _ _
  have hμbIrr : IsIrreducibleCharacter (hyp.mu i j2) := hyp.mu_irreducible _ _
  have h_ab : ClassFunction.inner (hyp.mu i j1) (hyp.mu i j2) = 0 := by
    rw [hyp.mu_orthonormal]; exact if_neg (fun hc => hj12 hc.2)
  have h_ba : ClassFunction.inner (hyp.mu i j2) (hyp.mu i j1) = 0 := by
    rw [hyp.mu_orthonormal]; exact if_neg (fun hc => (Ne.symm hj12) hc.2)
  have hsupp := hyp.tauS_mu_diff_support hG i hj1 hj2
  have hZIrrS : (hyp.mu i j1 - hyp.mu i j2) ∈ ZIrr (↥hyp.S) :=
    (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
  -- (a) `X ∈ ZIrr G`.
  have hXZ : D (hyp.mu i j1 - hyp.mu i j2) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS0 hG) hsupp hZIrrS
  -- (b) `‖μ_{i,j₁} − μ_{i,j₂}‖² = 2`, transported through the Dade isometry.
  have hnorm2 : ClassFunction.inner (hyp.mu i j1 - hyp.mu i j2)
      (hyp.mu i j1 - hyp.mu i j2) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, h_ab, h_ba,
      hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
    ring
  have hX2 : ClassFunction.inner (D (hyp.mu i j1 - hyp.mu i j2))
      (D (hyp.mu i j1 - hyp.mu i j2)) = 2 := by
    rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS0 hG) hsupp hsupp]
    exact hnorm2
  -- (c) `X − (η_{i,j₁} − η_{i,j₂})` vanishes on the regular set `V^S`.
  have hvanish : ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (D (hyp.mu i j1 - hyp.mu i j2)
        - ((1 : ℤ) : ℂ) • (hyp.eta i j1 - hyp.eta i j2)) x = 0 := by
    intro x hx
    have hv := hyp.tauS_mu_vanish_on_V hG hnoV i hj1 hj2 x hx
    simpa [hD] using hv
  -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{i,j₁} − η_{i,j₂}` on `V` is it.
  have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2 i hj12
    (s := (1 : ℤ)) (Or.inl rfl) hvanish
  rw [Int.cast_one, one_smul] at hrig
  exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} −
η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hnoV hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

/-- **The Coq `A0beta` inclusion `P^# ∪ V_S ⊆ 'A0(S)`** (the final step of (13.18.a)): the sharp
Fitting kernel `P^#` and the `S`-class-closure of the cyclic-TI set `V = W − (W₁ ∪ W₂)` both land
in the honest `A₀(S) = A(S) ∪ V^S`.  The `V^S` part is the definitional right component (after the
`Sdata.W1/W2` synchronization); `P^#` lands in `A(S) = centralizerSupport (S_σ^#) S'` because
`P = S_F ≤ S_σ` (`maxNilpotentNormalHall_le_Msigma`, every maximal — general type `P`),
`P ≤ S' = P ⊔ U`, and every element self-centralizes. -/
theorem sharpP_union_V_subset_A0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    sharpSubgroup hyp.P ∪
        conjClassSetIn hyp.S (typePV hyp.S hyp.Sdata)
      ⊆ S10.typePACore0 hyp.S hyp.Sdata := by
  have hPle_Ms : hyp.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  intro z hz
  rcases hz with hzP | hzV
  · -- `P^# ⊆ A(S) ⊆ A₀(S)`.
    refine S10.typePACore_subset_A0Set hyp.Sdata ?_
    obtain ⟨hzP_mem, hz1⟩ := hzP
    rw [Set.mem_singleton_iff] at hz1
    refine S10.mem_typePACore.mpr ⟨?_, hz1, z, ⟨hPle_Ms hzP_mem, ?_⟩, ?_⟩
    · have hPle : hyp.P ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]; exact le_sup_left
      exact hPle hzP_mem
    · rwa [Set.mem_singleton_iff]
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  · exact Set.mem_union_right _ hzV

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), `'A0(S)`-support form**: `supp(β_j) ⊆ 'A0(S)` for `j ≠ 0`.

The Coq `A0beta` (`PFsection13.v:1870`), obtained from `PVSbeta` (`β_j ∈ 'CF(S, P^# ∪ V_S)`,
`PFsection13.v:1833`) via `P^# ∪ V_S ⊆ 'A0(S)`.  `PVSbeta` cancels the induced permutation character
`Ind_{PW₁}^S 1` against `μ_{0j}` off `P^# ∪ V_S`, using the `W₁`-class `normedTI` structure in
`S̄ = S/P = Ū ⋊ W̄₁` (Coq `gammaW1`) together with the prime-`TI` residue value `prTIirr_id`; both
bottom out at the shared prime-`TI` residue content (issue 9014) that connects the free `μ`-grid to
the σ-residue theory.  **This single `'A0`-support obligation is what both
`gammaGrid_orthogonal_one`
and `gammaGrid_Y_norm_bound` reduce to** (the honest `'A0`-Dade=Ind bridge
`sInstance_dade0_eq_induce`, issue 9076, then discharges the remaining Dade content). -/
theorem betaGrid_A0_support_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact sharpP_union_V_subset_A0 hG hyp (betaGrid_support_of_c_eq_one hG hyp hc1 j hj hz)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

**De-scaffolded** (issue 9076): the `'A0(S)` `normedTI` content the old docstring flagged as
"missing" is now supplied by the honest `'A0`-Dade=Ind bridge `sInstance_dade0_eq_induce`.
Reduction
(Coq `oGamma1`): `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − ⟨1,1⟩ + ⟨η_{01},1⟩`, and
* `⟨1,1⟩ = 1` (`constOne_inner_self_eq_one`);
* `⟨η_{01},1⟩ = 0` — grid orthogonality: `1_G = η_{00}` (`eta_principal_eq_trivial`) and `η_{01} ⊥
  η_{00}` (`eta_orthonormal`);
* `⟨τ_S β_{#1},1_G⟩ = 1` — the bridge gives `τ_S β_{#1} = Ind_S^G β_{#1}` (needs `β_{#1}` supported
in
  `'A0(S)`, `betaGrid_A0_support`), so by Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
  `⟨Ind_S^G β_{#1}, 1_G⟩ = ⟨β_{#1}, 1_S⟩ = ⟨Ind_{PW₁}^S 1, 1_S⟩ − ⟨μ_{01}, 1_S⟩ = 1 − 0`, where
  `⟨Ind 1, 1_S⟩ = 1` (`inner_induce_trivialChar_constOne_eq_one`) and `⟨μ_{01}, 1_S⟩ = 0` (`μ_{01}`
  irreducible and `≠ 1_S`, since `⟨Ind 1, μ_{01}⟩ = 0 ≠ 1`, `indPW1_inner_mu`).

The **single** remaining gate is `betaGrid_A0_support` (the (13.18.a) `'A0`-support). -/
private theorem gammaGrid_orthogonal_one_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  classical
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `⟨Ind_{PW₁}^S 1, 1_S⟩ = 1`.
  have hind : ClassFunction.inner (indPW1 hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 1 := by
    rw [indPW1, ←
        OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one
      ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  -- `⟨μ_{01}, 1_S⟩ = 0`: `μ_{01}` is irreducible and `≠ 1_S` (else `⟨Ind 1, μ_{01}⟩ = 1 ≠ 0`).
  have hmu : ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 0 := by
    have hIμ : ClassFunction.inner (indPW1 hyp)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 :=
      indPW1_inner_mu hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    have hne : (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
          hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
        ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S := by
      intro heq
      apply one_ne_zero (α := ℂ)
      have hcf : hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) :=
        congrArg (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) heq
      rw [hcf, hind] at hIμ
      exact hIμ
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
        hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S)
    rw [if_neg hne] at hite
    exact hite
  -- `⟨τ_S(β_{#1}), 1_G⟩ = 1` via the `'A0`-Dade=Ind bridge + Frobenius reciprocity.
  have htau : ClassFunction.inner (tauSbetaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 := by
    have hbridge : tauSbetaGrid hG hyp
        = ClassFunction.induce hyp.S (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩) := by
      rw [tauSbetaGrid]
      exact hyp.sInstance_dade0_eq_induce hG hnoV
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1
          ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num))
    rw [hbridge, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : ClassFunction.restrict hyp.S
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) := by
      ext x; rw [ClassFunction.restrict_apply]; rfl
    rw [hres]
    simp only [betaGrid]
    rw [ClassFunction.inner_sub_left, hind, hmu, sub_zero]
  -- `⟨η_{01}, 1_G⟩ = 0`.
  have heta : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00]
    have horth := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
      ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩ ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by norm_num))] at horth
    exact horth
  rw [GammaGrid, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one, htau, heta]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0` (public form).  Thin wrapper over `gammaGrid_orthogonal_one_aux`
that reconciles the caller's `Fintype G`/`Invertible (Nat.card G : ℂ)` instances with the
`FiniteInduce`-scoped ones the core proof uses (both are `Subsingleton`). -/
theorem gammaGrid_orthogonal_one_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  intro _ _
  convert gammaGrid_orthogonal_one_aux hG hnoV hyp hc1 using 2; exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **(13.18.c)** `Γ` is real: `Γ.conj = Γ` — fully proven (Coq `GammaReal`,
`PFsection13.v:1911`).

Conjugation commutes with the Dade lift on `A₀(S)`-supported inputs
(`dadeIntegralCharacterMap_conj_of_support` at `betaGrid_A0_support`) and with induction
(`induce_conj`, the trivial character being real), and sends grid entries to the negated index
(`mu_conj`/`eta_conj`, the CF-level (4.9.a)/(3.9.a) fields; `finNeg 0 = 0`).  So
`Γ̄ = τ_S(β_{−#1}) − 1_G + η_{0,−#1}`, which is `Γ` by the proven `j`-independence
`gammaGrid_defGamma` at the conjugate column `−#1 = p−1 ≠ 0`. -/
theorem gammaGrid_real_of_c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    (GammaGrid hG hyp).conj = GammaGrid hG hyp := by
  classical
  set j1 : Fin hyp.p := ⟨1, by have := hyp.three_le_p; omega⟩ with hj1def
  set j' : Fin hyp.p := OddOrder.Peterfalvi.S15.finNeg hyp.p_prime.pos j1 with hj'def
  have hp3 := hyp.three_le_p
  have hj'0 : (j' : ℕ) ≠ 0 := by
    simp only [hj'def, OddOrder.Peterfalvi.S15.finNeg, hj1def]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hneg0 : OddOrder.Peterfalvi.S15.finNeg hyp.q_prime.pos ⟨0, hyp.q_prime.pos⟩
      = ⟨0, hyp.q_prime.pos⟩ := by
    apply Fin.ext
    simp [OddOrder.Peterfalvi.S15.finNeg]
  -- the trivial pieces are real
  have hconst : (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G).conj
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    ext g
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne, ClassFunction.conj_apply]
  -- `β̄_{#1} = β_{−#1}`: `Ind_{PW₁}^S 1` is real, `μ̄_{01} = μ_{0,−#1}`
  have hbeta_conj : (betaGrid hyp j1).conj = betaGrid hyp j' := by
    rw [betaGrid, betaGrid, ClassFunction.conj_sub, hyp.mu_conj ⟨0, hyp.q_prime.pos⟩ j1,
      hneg0]
    congr 1
    rw [indPW1, ClassFunction.induce_conj]
    congr 1
    ext g
    simp [ClassFunction.conj_apply, trivialClassFunction]
  -- the Dade lift commutes with conjugation on the `A₀(S)`-supported `β_{#1}`
  have hDconj : (tauSbetaGrid hG hyp).conj
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (betaGrid hyp j') := by
    rw [tauSbetaGrid,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_conj_of_support _ _
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 (by simp [hj1def])),
      hbeta_conj]
  -- assemble and close by `defGamma` at the conjugate column
  rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ j1 from rfl,
    ClassFunction.conj_add, ClassFunction.conj_sub, hDconj, hconst,
    hyp.eta_conj ⟨0, hyp.q_prime.pos⟩ j1, hneg0]
  exact gammaGrid_defGamma hG hnoV hyp j' hj'0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (13.18) residual `Γ` is a virtual character**: each constituent of
`Γ = τ_S(β_{#1}) − 1_G + η_{01}` lies in `ℤ[Irr G]` — the Dade image via the `'A0` Dade=Ind
bridge (`sInstance_dade0_eq_induce` + `induce_mem_ZIrr`, with `β_{#1} ∈ ℤ[Irr S]` from
`induce_mem_ZIrr` on the trivial character and irreducibility of `μ_{01}`), the trivial
character, and `η_{01} = τ₃(ω_{01})` (`tau3_mem_ZIrr` + `omega_mem_ZIrr`).  Feeds the
integrality of `⟨Γ, η_{01}⟩` in the (13.18.d) bound. -/
theorem gammaGrid_mem_ZIrr_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  have hβZ : betaGrid hyp j1 ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ ?_
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr
        (hyp.mu_irreducible _ j1))
    have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter
      ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv)
  have hTZ : tauSbetaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [tauSbetaGrid,
      hyp.sInstance_dade0_eq_induce hG hnoV
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ hβZ
  rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ j1 from rfl]
  refine Submodule.add_mem _ (Submodule.sub_mem _ hTZ ?_) ?_
  · have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter G).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv
  · rw [hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ j1)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Core of the **(13.18.d) residual-norm bound**, with the `FiniteInduce`-scoped instances
(Coq `PFsection13.v:1915-1934`).  The chain: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2` (Dade isometry
on `A₀(S)`-support + `betaGrid_norm`); peel `1_G` (`⟨Γ,1⟩ = 0`, `⟨η_{01},1⟩ = 0`), peel `Y`
(`X ⊥ Y`, `Y ⊥ η`-grid); then split `X − η_{01} = X₁ + a·η_{0,−1} + (a−1)·η_{01}` where
`a = ⟨Γ, η_{01}⟩ ∈ ℤ` (`gammaGrid_mem_ZIrr`), using `Γ` real ((13.18.c)) and
`η̄_{01} = η_{0,−1} ⊥ η_{01}`; drop `‖X₁‖² ≥ 0` and close with the integer inequality
`a² + (a−1)² ≥ 1`. -/
private theorem gammaGrid_Y_norm_bound_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    (X Y : ClassFunction G ℂ) (defXY : GammaGrid hG hyp = X + Y)
    (oXY : ClassFunction.inner X Y = 0)
    (oYeta : ∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) :
    (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  set i0 : Fin hyp.q := ⟨0, hyp.q_prime.pos⟩ with hi0def
  set j' : Fin hyp.p := OddOrder.Peterfalvi.S15.finNeg hyp.p_prime.pos j1 with hj'def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  set η01 : ClassFunction G ℂ := hyp.eta i0 j1 with hη01def
  set η01' : ClassFunction G ℂ := hyp.eta i0 j' with hη01'def
  -- index bookkeeping: `j' ≠ j1`, `j1 ≠ 0`, `finNeg 0 = 0`
  have hj'ne : j' ≠ j1 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [hj'def, OddOrder.Peterfalvi.S15.finNeg, hj1def] at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega
  have hneg0 : OddOrder.Peterfalvi.S15.finNeg hyp.q_prime.pos i0 = i0 := by
    apply Fin.ext
    simp [OddOrder.Peterfalvi.S15.finNeg, hi0def]
  -- `η̄_{01} = η_{0,−1}` (the (3.9.a) conj-pair field at `finNeg 0 = 0`)
  have hconj : η01.conj = η01' := by
    rw [hη01def, hyp.eta_conj i0 j1, hneg0, hη01'def, hj'def]
  -- grid orthonormality instances
  have h_11 : ClassFunction.inner η01 η01 = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j1
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  have h_1'1 : ClassFunction.inner η01' η01 = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j1
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2)] at h
    exact h
  have h_11' : ClassFunction.inner η01 η01' = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j'
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2.symm)] at h
    exact h
  have h_1'1' : ClassFunction.inner η01' η01' = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j'
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  -- `1_G = η_{00}` and its orthogonalities
  have hone : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      = hyp.eta i0 ⟨0, hyp.p_prime.pos⟩ := by
    rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]
    rfl
  have hη01_one : ClassFunction.inner η01
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [hone]
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by
      rintro ⟨-, h2⟩
      exact hj1ne (by simpa using congrArg Fin.val h2))] at h
    exact h
  have hΓone : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    gammaGrid_orthogonal_one_of_c_eq_one hG hnoV hyp hc1
  -- Pythagoras helper
  have pyth : ∀ A B : ClassFunction G ℂ, ClassFunction.inner A B = 0 →
      ClassFunction.inner (A + B) (A + B)
        = ClassFunction.inner A A + ClassFunction.inner B B := by
    intro A B hAB
    have hBA : ClassFunction.inner B A = 0 := by
      rw [ClassFunction.inner_star_comm, hAB, star_zero]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hAB, hBA]
    ring
  -- the isometry: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2`
  have hTT : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
    rw [tauSbetaGrid,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG)
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)]
    exact betaGrid_norm_of_c_eq_one hG hyp hc1 j1 hj1ne
  -- Pythagoras 1: `τ_S β₁ = (Γ − η_{01}) + 1_G`
  have hTdecomp : tauSbetaGrid hG hyp
      = (GammaGrid hG hyp - η01) + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + η01 from rfl]
    abel
  have hP1 : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01) + 1 := by
    rw [hTdecomp, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, hΓone, hη01_one, sub_zero]),
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one]
  -- Pythagoras 2: `Γ − η_{01} = (X − η_{01}) + Y`
  have hP2 : ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01)
      = ClassFunction.inner (X - η01) (X - η01) + ClassFunction.inner Y Y := by
    have hd : GammaGrid hG hyp - η01 = (X - η01) + Y := by rw [defXY]; abel
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [hd, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, oXY]
      rw [show ClassFunction.inner η01 Y = 0 by
        rw [ClassFunction.inner_star_comm, oY01, star_zero]]
      ring)]
  -- the grid coefficient `a = ⟨Γ, η_{01}⟩` is an integer `m`
  have hηZ : η01 ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [hη01def, hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr i0 j1)
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int
    (gammaGrid_mem_ZIrr_of_c_eq_one hG hnoV hyp hc1) hηZ
  -- `⟨X, η_{01}⟩ = m` and `⟨X, η_{0,−1}⟩ = m` (the latter via `Γ` real + conj-pair)
  have hXη : ClassFunction.inner X η01 = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01) defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [oY01, add_zero] at h
    rw [← h, hm]
  have hΓη' : ClassFunction.inner (GammaGrid hG hyp) η01' = (m : ℂ) := by
    rw [← hconj, ← gammaGrid_real_of_c_eq_one hG hnoV hyp hc1,
      OddOrder.RepresentationTheory.ClassFunction.inner_conj_conj,
      ClassFunction.inner_star_comm, hm, star_intCast]
  have hXη' : ClassFunction.inner X η01' = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01') defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01' : ClassFunction.inner Y η01' = 0 := oYeta i0 j'
    rw [oY01', add_zero] at h
    rw [← h, hΓη']
  -- Pythagoras 3+4: `X − η_{01} = (X₁ + m·η_{0,−1}) + (m−1)·η_{01}`
  set X1 : ClassFunction G ℂ := X - (m : ℂ) • η01 - (m : ℂ) • η01' with hX1def
  have hX1η : ClassFunction.inner X1 η01 = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη, h_11, h_1'1]
    ring
  have hX1η' : ClassFunction.inner X1 η01' = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη', h_11', h_1'1']
    ring
  have hXdecomp : X - η01 = (X1 + (m : ℂ) • η01') + ((m : ℂ) - 1) • η01 := by
    rw [hX1def, sub_smul, one_smul]
    abel
  have hstar_m : star ((m : ℂ)) = (m : ℂ) := star_intCast m
  have hstar_m1 : star ((m : ℂ) - 1) = (m : ℂ) - 1 := by
    rw [star_sub, star_one, hstar_m]
  have hP3 : ClassFunction.inner (X - η01) (X - η01)
      = ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
        + ((m : ℂ) - 1) * ((m : ℂ) - 1) := by
    rw [hXdecomp, pyth _ _ (by
      rw [ClassFunction.inner_smul_right, ClassFunction.inner_add_left,
        ClassFunction.inner_smul_left, hX1η, h_1'1]
      ring)]
    rw [ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m1, h_11]
    ring
  have hP4 : ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
      = ClassFunction.inner X1 X1 + (m : ℂ) * (m : ℂ) := by
    rw [pyth _ _ (by rw [ClassFunction.inner_smul_right, hX1η', hstar_m]; ring),
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m, h_1'1']
    ring
  -- assemble the ℂ-level identity and take real parts
  have hX1re := OddOrder.RepresentationTheory.ClassFunction.inner_self_eq_re X1
  have hchain : ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
      = (((ClassFunction.inner X1 X1).re : ℝ) : ℂ)
        + ((m * m + (m - 1) * (m - 1) : ℤ) : ℂ)
        + ClassFunction.inner Y Y + 1 := by
    rw [← hTT, hP1, hP2, hP3, hP4, ← hX1re]
    push_cast
    ring
  have hre := congrArg Complex.re hchain
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.intCast_re,
    Complex.ratCast_re] at hre
  -- final integer inequality `m² + (m−1)² ≥ 1` and the nonnegativity of `‖X₁‖²`
  have hmm1 : (1 : ℤ) ≤ m * m + (m - 1) * (m - 1) := by
    by_cases h : 1 ≤ m
    · nlinarith
    · have h' : m ≤ 0 := by omega
      nlinarith
  have hX1nonneg : 0 ≤ (ClassFunction.inner X1 X1).re :=
    OddOrder.RepresentationTheory.ClassFunction.inner_self_re_nonneg X1
  have hmm1' : (1 : ℝ) ≤ ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) := by exact_mod_cast hmm1
  have hgoal : (ClassFunction.inner Y Y).re
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℝ)
        - (ClassFunction.inner X1 X1).re
        - ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) - 1 := by linarith [hre]
  rw [hgoal]
  push_cast at hmm1' ⊢
  linarith

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.d) residual-norm bound**: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
to the whole `η`-grid `{η_{ik}}`, `‖Y‖² ≤ (u−1)/q` — fully proven (Coq `PFsection13.v:1915-1934`;
the earlier `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1` overstatement was corrected in issue 3003: `‖Γ‖²` itself is
**not** bounded, only the grid-orthogonal residual `Y`).  Public form of
`gammaGrid_Y_norm_bound_aux`, reconciling the caller's `Fintype G`/`Invertible` instances with
the `FiniteInduce`-scoped ones (both are `Subsingleton`). -/
theorem gammaGrid_Y_norm_bound_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), GammaGrid hG hyp = X + Y →
        ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  intro _ _ X Y defXY oXY oYeta
  have h := gammaGrid_Y_norm_bound_aux hG hnoV hyp hc1 X Y defXY
    (by convert oXY using 2; exact Subsingleton.elim _ _)
    (fun i k => by convert oYeta i k using 2; exact Subsingleton.elim _ _)
  convert h using 3
  exact Subsingleton.elim _ _

/-- **Faithful §13 producer for Peterfalvi (13.18).**  The (13.18) virtual characters `β_j`/`Γ`
and their genuine properties (support (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`,
orthogonality of `Γ` to `1_G`, reality, and the (13.18.d) `‖Y‖²` residual bound) are supplied here.
The concrete `β_j = betaGrid hyp j` and `Γ = GammaGrid hG hyp` are built from the honest `S`-side
Dade isometry `τ_S` (`hyp.dadeHypS0`, **not** the `= 0` placeholder `hyp.tauS`) and the induced
trivial character `Ind_{PW₁}^S 1`.  The bundled properties are the precisely-isolated §13
obligations `betaGrid_support` / `betaGrid_norm` / `gammaGrid_orthogonal_one` /
`gammaGrid_real` / `gammaGrid_Y_norm_bound`; the (13.18.c) `j`-independence is the standalone
`gammaGrid_defGamma` (proven, modulo the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`).
Their deep content bottoms out at the (13.2.e) `A₀(S)` normedTI Dade=Ind bridge, the (5.3)
`S`↔`W` Dade cross-relation, and the Frobenius norm `norm_induce_one_frobenius`. -/
noncomputable def betaData_of_grid_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    BetaData hyp where
  j := j
  j_ne_zero := hj
  beta := betaGrid hyp j
  Gamma := GammaGrid hG hyp
  support_formula := betaGrid_support_of_c_eq_one hG hyp hc1 j hj
  norm_formula := betaGrid_norm_of_c_eq_one hG hyp hc1 j hj
  Gamma_orthogonal_one := gammaGrid_orthogonal_one_of_c_eq_one hG hnoV hyp hc1
  Gamma_real := gammaGrid_real_of_c_eq_one hG hnoV hyp hc1
  Y_norm_bound := gammaGrid_Y_norm_bound_of_c_eq_one hG hnoV hyp hc1

/-- **Peterfalvi (13.18)**: the virtual character `beta_j` has controlled
support, norm, and orthogonal remainder.

De-opacified (W3 §15): the conclusions are the genuine (13.18) statements — `β_j`'s support
control (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`, and the residual `Γ`'s orthogonality
to `1_G` (13.18.c), reality (13.18.c), and the (13.18.d) `‖Y‖²` bound — each about the produced
characters `data.beta`/`data.Gamma`.  They are the genuine fields of the faithful producer
`betaData_of_grid`; the (13.18.b) Frobenius induced-trivial norm half is the already-proven
`norm_induce_one_frobenius`.  The (13.18.c) `j`-independence half is the standalone
`gammaGrid_defGamma` (kept separate to avoid mixing the `FiniteInduce` `τ_S` instances with the
explicit inner-product instance binders here).  (The earlier grid-orthogonality and `‖Γ‖²`
conjuncts were overstatements — issue 3003.) -/
theorem beta_support_norm_and_remainder_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∃ data : BetaData hyp,
      (data.beta.support ⊆
        {z : ↥hyp.S |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.S
              (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)}) ∧
        (∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
          ClassFunction.inner data.beta data.beta
            = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)) ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ClassFunction.inner data.Gamma
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0) ∧
        data.Gamma.conj = data.Gamma ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ∀ (X Y : ClassFunction G ℂ), data.Gamma = X + Y →
            ClassFunction.inner X Y = 0 →
            (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
            (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)) := by
  -- The principal index `j = 1` (nonzero, using `p ≥ 3`).
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  refine ⟨betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1 ⟨1, by omega⟩ (by simp),
    (betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1
      ⟨1, by omega⟩ (by simp)).support_formula,
    (betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1
      ⟨1, by omega⟩ (by simp)).norm_formula,
    (betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1
      ⟨1, by omega⟩ (by simp)).Gamma_orthogonal_one,
    (betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1
      ⟨1, by omega⟩ (by simp)).Gamma_real,
    (betaData_of_grid_of_c_eq_one _hG hnoV hyp hc1
      ⟨1, by omega⟩ (by simp)).Y_norm_bound⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `T`-side full-grid form** (mirror of
`tauS_mu_cross`): `τ_T(ν_{r,j} − ν_{s,j}) = η_{r,j} − η_{s,j}` for any column `j` and
distinct nontrivial rows `r ≠ s` (both `≠ 0`).  `X := τ_T(ν-diff)` is a norm-`2` `ZIrr`
character (Dade isometry on the `A₀(T)`-supported difference `tauT_nu_diff_support`)
agreeing with `η_{r,j} − η_{s,j}` on the regular set (`tauT_nu_vanish_on_V`); the (3.8)
rigidity is the **swap-transposed** `S16.eta_diff_rigidity` at `hyp.swap` (whose `η`-grid is
the transpose, so its row-fixed/column-difference form *is* the `T`-side
column-fixed/row-difference form), with the swap's structural input `hV` supplied by the
unconditional `isMulCommutative_V_unconditional`.  This is the per-column engine the
reducible caseB-`T` `R`-family sums over a ν-row:
`τ_T(ν_r − ν̄_r) = ∑_j τ_T(ν_{rj} − ν_{sj}) = ∑_j(η_{rj} − η_{sj})`. -/
theorem tauT_nu_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
        (hyp.nu r j - hyp.nu s j)
      = hyp.eta r j - hyp.eta s j := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
      ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
    with hD
  have hνaIrr : IsIrreducibleCharacter (hyp.nu r j) := pins.nu_irreducible _ _
  have hνbIrr : IsIrreducibleCharacter (hyp.nu s j) := pins.nu_irreducible _ _
  have h_ab : ClassFunction.inner (hyp.nu r j) (hyp.nu s j) = 0 := by
    rw [pins.nu_orthonormal]; exact if_neg (fun hc => hrs hc.1)
  have h_ba : ClassFunction.inner (hyp.nu s j) (hyp.nu r j) = 0 := by
    rw [pins.nu_orthonormal]; exact if_neg (fun hc => (Ne.symm hrs) hc.1)
  have hsupp := hyp.tauT_nu_diff_support hG pins Tdata hU hW1 hW2 j hr hs
  have hZIrrT : (hyp.nu r j - hyp.nu s j) ∈ ZIrr (↥hyp.T) :=
    (ZIrr (↥hyp.T)).sub_mem hνaIrr.mem_ZIrr hνbIrr.mem_ZIrr
  -- (a) `X ∈ ZIrr G`.
  have hXZ : D (hyp.nu r j - hyp.nu s j) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypT0 hG hTP Tdata) hsupp hZIrrT
  -- (b) norm `2`, transported through the Dade isometry.
  have hnorm2 : ClassFunction.inner (hyp.nu r j - hyp.nu s j)
      (hyp.nu r j - hyp.nu s j) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, h_ab, h_ba,
      hνaIrr.inner_self_eq_one, hνbIrr.inner_self_eq_one]
    ring
  have hX2 : ClassFunction.inner (D (hyp.nu r j - hyp.nu s j))
      (D (hyp.nu r j - hyp.nu s j)) = 2 := by
    rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypT0 hG hTP Tdata) hsupp hsupp]
    exact hnorm2
  -- (c) `X − (η_{r,j} − η_{s,j})` vanishes on the regular set.
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (D (hyp.nu r j - hyp.nu s j)
        - ((1 : ℤ) : ℂ) • (hyp.eta r j - hyp.eta s j)) x = 0 := by
    intro x hx
    have hv := hyp.tauT_nu_vanish_on_V hG hnoV pins hTP Tdata hU hW1 hW2 j hr hs x hx
    simpa [hD] using hv
  -- (3.8) rigidity, column form — directly at `hyp` (issue 2035 #86 de-swap)
  have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity_col
    hyp hXZ hX2 hrs j (s := (1 : ℤ)) (Or.inl rfl) hvanish
  rw [Int.cast_one, one_smul] at hrig
  exact hrig


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The honest Dade image of a reducible `𝒯`-member row difference** (mirror of
`tauS_muColumn_diff_eq`; route B, the core of the reducible caseB-`T` `R`-family): for a
reducible `η = ∑_j ν_{rj} ∈ 𝒯` with conjugate `η̄ = ∑_j ν_{sj}` (`r ≠ s`, both `≠ 0`), the
honest `A(T)`-Dade image is `τ_T(η − η̄) = ∑_j(η_{rj} − η_{sj})` — the `A`/`A₀` Dade maps agree
with `Ind_T^G` on the `A(T)`-supported difference (`tInstance_dade_eq_induce` /
`tInstance_dade0_eq_induce`), and the per-column cross-relation `tauT_nu_cross` evaluates each
summand. -/
theorem tauT_nuRow_diff_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {r s : Fin hyp.q}
    (hr0 : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs0 : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s)
    {η : ClassFunction ↥hyp.T ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hreq : η = ∑ j : Fin hyp.p, hyp.nu r j)
    (hseq : (η : ClassFunction ↥hyp.T ℂ).conj = ∑ j : Fin hyp.p, hyp.nu s j) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = ∑ j : Fin hyp.p, (hyp.eta r j - hyp.eta s j) := by
  classical
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  -- `η − η̄ = ∑_j(ν_{rj} − ν_{sj})`.
  have hsub : (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = ∑ j : Fin hyp.p, (hyp.nu r j - hyp.nu s j) := by
    rw [hseq, hreq, ← Finset.sum_sub_distrib]
  -- `A(T)`-support of the row difference.
  have hAsupp : (η - (η : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    rw [show (η - (η : ClassFunction ↥hyp.T ℂ).conj)
        = -((η : ClassFunction ↥hyp.T ℂ).conj - η) from by abel,
      ClassFunction.support_neg]
    exact hyp.sSet_member_conjDiff_supported_T hG hvd hη
  have hA0supp : (η - (η : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T :=
    hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set Tdata))
  -- the honest `A`-Dade agrees with the `A₀`-Dade on the `A(T)`-supported row difference.
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
          ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
          (η - (η : ClassFunction ↥hyp.T ℂ).conj) := by
    rw [hyp.tInstance_dade_eq_induce hG hnoV hTP hAsupp,
      hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hA0supp]
  rw [hτeq, hsub, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    tauT_nu_cross hG hnoV hyp pins hTP Tdata hU hW1 hW2 j hr0 hs0 hrs

end OddOrder.Peterfalvi.S15
