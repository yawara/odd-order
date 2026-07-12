/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_BridgeCharacter

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issues 0103/0102):
the (13.19) type-I orthogonality layer and the (14.5) complement exclusion.
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
`typeI_orthogonality_dichotomy` supplies the honest §14 `typeISetup`, the `τ₁ = typeISetup.tau`
Dade map, and reads the dichotomy implication fields off as identities (no over-claim). -/
structure TypeIOrthogonalityGridData (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) where
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
  `τ₁ = typeISetup.tau` agrees with `τ` on the `A(L)`-supported `Ind_H^L 1_H − φ`). -/
  betaL_eq :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((typeISetup.H).subgroupOf L) : ℂ)],
      betaL = typeISetup.tau
        (ClassFunction.induce ((typeISetup.H).subgroupOf L)
          (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - phi)
  Ltau_orthogonal_eta :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p),
        ClassFunction.inner (typeISetup.tau phi) (hyp.eta i j) = 0
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
    (OddIntegerInner betaS (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ e)
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy, faithful form: **(c1)**
  `(β_T^τ, φ^{τ₁}) ≡ 1 (mod 2)` and `(|H|−1)/e ≤ (v−1)/p`, or **(c2)** the `η_{i0}` odd-parity
  and `q ≤ e`. -/
  caseC_dual :
    (OddIntegerInner betaT (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ e)

/-! #### The (13.19) producer, decomposed

The Tier-A structure (`e`, `𝓛`, `φ`, `β_L`, `β_S`) is built here; the genuinely deep (13.19)
facts are isolated below as `φ`-parametric obligations, each matching one `GridData` field. -/

/-- **(13.19), `φ` existence**: the family `𝓛 = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}` has a member of
degree `e = [L : H]` ("the existence of `φ` is clear"): induce any nontrivial *linear* character
of the nontrivial nilpotent kernel `H` (one exists as `H^{ab} ≠ 1`); it is irreducible by the
Frobenius inertia argument (`I_L(θ) = H` for `θ ≠ 1_H`), and `(Ind_H^L θ)(1) = [L:H]·θ(1) = e`.
Isolated obligation. -/
theorem exists_Sset_apply_one_eq_index [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∃ φ : ClassFunction ↥L ℂ, φ ∈ typeISetup.Sset ∧
      φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := sorry

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

/-- T-side (13.18) bridge image `τ_T(β_T) = τ_T(Ind_{QW₂}^T 1 − ν₁₀)` — the S↔T-swapped
`tauSbetaGrid`, pairing with `φ^{τ₁}` in the dual (13.19.c1) parity.  Needs the honest T-side
`'A0(T)` Dade instance (dual of `hyp.dadeHypS0`).  Isolated obligation. -/
noncomputable def tauTbetaGrid [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ClassFunction G ℂ := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness**: `Ã(L) ∩ (P^G ∪ W^G) = ∅` — the order of an `Ã(L)`-element
is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q` ((8.17.a)); `β_L^τ` is
supported in `Ã(L)`-classes while `β_S^τ` is supported in `P^# ∪ (W∖(W₁∪W₂))^G` ((13.18.a)).
Isolated obligation. -/
theorem typeIBetaL_betaS_disjoint_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset) :
    Disjoint (typeIBetaL typeISetup φ).support (tauSbetaGrid _hG hyp).support := sorry

/-- **(13.19.b)**: `𝓛^{τ₁}` is orthogonal to the whole `η`-grid.  For `ψ ∈ 𝓛`,
`(ψ − ψ̄)^τ` vanishes on `W ∖ (W₁ ∪ W₂)` by (13.19.a), so `NC((ψ−ψ̄)^τ) ≤ ‖ψ−ψ̄‖² = 2` and
(3.8) forces `ψ^{τ₁} ⊥ η_{ij}`.  Isolated obligation. -/
theorem tau_apply_orthogonal_eta_of_mem_Sset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p),
        ClassFunction.inner (typeISetup.tau φ) (hyp.eta i j) = 0 := sorry

/-- **(13.19.c), first clause (row form)**: `(β_L^τ, η_{0j})` is independent of `j ≥ 1` — by
(13.18.a) `Supp(μ_{0j} − μ_{01}) ⊆ P^# ∪ (W∖(W₁∪W₂))^S`, (4.8) and (13.19.a) give
`(β_L^τ, η_{0j} − η_{01}) = (β_L^τ, (μ_{0j} − μ_{01})^τ) = 0`.  Isolated obligation. -/
theorem typeIBetaL_eta_row_constant [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta ⟨0, hyp.q_prime.pos⟩ j') := sorry

/-- **(13.19.c), first clause (column form)**: the S↔T-swapped row constancy.  Isolated
obligation. -/
theorem typeIBetaL_eta_col_constant [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL typeISetup φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner (typeIBetaL typeISetup φ)
              (hyp.eta i' ⟨0, hyp.p_prime.pos⟩) := sorry

/-- **(13.19.c) S-side dichotomy**: `(Γ_S, φ^{τ₁}) + (Γ_L, η_{01}) ≡ 1 (mod 2)` (from
`0 = (β_L^τ, β_S^τ)` via (13.19.a)/(13.18.a) and the evenness of `(Γ_L, Γ_S)` ((13.18.c)+(1.1))),
so one of (c1) `(β_S^τ, φ^{τ₁}) ≡ 1` — in which case (13.18.d) with `Γ_S`'s `𝓛^{τ₁}`-expansion
bounds `(|H|−1)/e = Σaᵢ² ≤ (u−1)/q` — or (c2) `(β_L^τ, η_{0j}) ≡ 1`, in which case the
`η`-coefficient parity forces `p ≤ e`.  Isolated obligation (the (13.19) proof body). -/
theorem typeI_caseC_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauSbetaGrid _hG hyp) (typeISetup.tau φ) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL typeISetup φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
        hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := sorry

/-- **(13.19.c) T-side dichotomy** (S↔T swapped): as `typeI_caseC_dichotomy` with
`β_T`/`v`/`p` in place of `β_S`/`u`/`q`.  Isolated obligation. -/
theorem typeI_caseC_dual_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauTbetaGrid _hG hyp) (typeISetup.tau φ) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL typeISetup φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧
        hyp.q ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := sorry

/-- **Faithful §13 producer for Peterfalvi (13.19).**  The Tier-A structure — `e = [L:H]`
(definitionally), the family `𝓛 = typeISetup.Sset`, a chosen degree-`e` member `φ`
(`exists_Sset_apply_one_eq_index`), and the bridge images `β_L = typeIBetaL`,
`β_S = tauSbetaGrid`, `β_T = tauTbetaGrid` — is genuinely constructed; the deep (13.19)
facts are the isolated `φ`-parametric obligations above, consumed field-by-field. -/
noncomputable def typeIOrthogonalityGridData_of_typeISetup [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    TypeIOrthogonalityGridData hyp typeISetup :=
  { e := ((maxNilpotentNormalHall L).subgroupOf L).index
    e_eq_index := rfl
    Lset := typeISetup.Sset
    phi := Classical.choose (exists_Sset_apply_one_eq_index typeISetup)
    phi_mem := (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
    phi_degree_eq_e := (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).2
    betaL := typeIBetaL typeISetup
      (Classical.choose (exists_Sset_apply_one_eq_index typeISetup))
    betaS := tauSbetaGrid _hG hyp
    betaT := tauTbetaGrid _hG hyp
    disjoint_support := typeIBetaL_betaS_disjoint_support _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
    betaL_eq := typeIBetaL_eq_tau_induce_sub typeISetup _
    Ltau_orthogonal_eta := tau_apply_orthogonal_eta_of_mem_Sset _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
    betaL_eta0_row_constant := typeIBetaL_eta_row_constant _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
    betaL_eta0_col_constant := typeIBetaL_eta_col_constant _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
    caseC := typeI_caseC_dichotomy _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).2
    caseC_dual := typeI_caseC_dual_dichotomy _hG hyp typeISetup _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index typeISetup)).2 }

/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has `𝓛^{τ₁}` orthogonal to the `eta_ij`,
`(β_L^τ, η_{0j})` constant along each zero axis, and on each zero axis one of the two (13.19.c)
cases — the faithful conjunction forms `(c1) = parity ∧ degree bound` and
`(c2) = η-axis odd-parity ∧ p ≤ e` — holds.

De-opacified (W3 §15): the honest §14 content — the (12.1) `S14.Hypothesis` of `L`
(`S14.exists_typeI_hypothesis`) and its genuine Dade map `τ₁ = typeISetup.tau` —
is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements.  `betaL_eta_independent` is instantiated to the faithful (13.19.c) first clause — the
zero-axis **constancy** of `(β_L^τ, η_{0j})`/`(β_L^τ, η_{i0})` (NOT orthogonality: in case (c2)
these inner products are odd).  The dichotomy implication fields (`caseC1_bound`,
`caseC2_eta0j_odd`, dual) are the conjunction projections.  The grid-dependent atoms come from the
faithful producer `typeIOrthogonalityGridData_of_typeISetup`, whose type is the genuine (13.19)
grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(14.*): the type-I maximal `L` carries a genuine `S14.Hypothesis` (honest own-logic).
  obtain ⟨typeISetup⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis _hG hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_typeISetup _hG hyp typeISetup
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and
  -- conjunction-projection dichotomy implication fields.
  refine ⟨{ typeISetup := typeISetup
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := typeISetup.tau
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                  ClassFunction.inner (typeISetup.tau g.phi) (hyp.eta i j) = 0
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
              OddIntegerInner g.betaS (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ g.e
            caseC2_eta0j_odd := fun h => h.1
            caseC1_bound := fun h => h.2
            caseC1_dual :=
              OddIntegerInner g.betaT (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
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

/-- **Peterfalvi (14.5), core exclusion**: under the §14 normalization `q < p` and the type-II
fact `N_G(U) ⊄ S`, the `W₁`-containing Frobenius complement `E` of the type-I maximal
`L ⊇ N_G(U)` is not contained in `Q`.

*Proof (Pf p.87).*  If `E ≤ Q` then `E = E ⊓ Q = W₁` (`complement_inf_Q_eq_W1`), so the
Fitting-kernel index of `L` is `e = |W₁| = q < p`.  The (13.19.c) dichotomy
(`typeIOrthogonalityGridData_of_typeISetup`) then cannot hold in case (c2) (which forces
`p ≤ e`), so the (c1) bound `(|H|−1)/e ≤ (u−1)/q` holds with `e = q`, giving `|H| ≤ u`.  With
`U ≤ H` ((13.17.b), hypothesis `hUH`) and `u ≤ |U|` this forces `H = U`, so
`L = H ⋊ E = U W₁ ≤ S` — contradicting `N_G(U) ≤ L` and `N_G(U) ⊄ S`. -/
theorem complement_not_le_Q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
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
  obtain ⟨typeISetup⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis _hG hLmax hLI
  have hHL : typeISetup.H = maxNilpotentNormalHall L := typeISetup.typeI.typeF.H_eq
  set g := typeIOrthogonalityGridData_of_typeISetup _hG hyp typeISetup with hgdef
  have he_q : g.e = hyp.q := by rw [← g.e_eq_index, hindex]
  -- case (c2) is impossible: `p ≤ e = q < p`
  rcases g.caseC with ⟨-, hbound⟩ | ⟨-, hpe⟩
  swap
  · rw [he_q] at hpe
    omega
  -- case (c1): `(|H|−1)/q ≤ (u−1)/q` forces `|H| ≤ u ≤ |U| ≤ |H|`, so `H = U`
  rw [he_q] at hbound
  have hq0 : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hle_nat : Nat.card ↥typeISetup.H - 1 ≤ hyp.u - 1 := by
    have h : ((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) ≤ ((hyp.u - 1 : ℕ) : ℚ) := by
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
  have hHpos : 0 < Nat.card ↥typeISetup.H := Nat.card_pos
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
  have hnle := complement_not_le_Q _hG hyp hTTypeII hqp hNUS hLmax hLI hNUL hUH frob hW1E
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
  have hcard := complement_card_eq_pq _hG hyp hTTypeII hqp hNUS hLmax hLI hNUL hUH frob hW1E
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
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ := typeI_overNormalizer_complement _hG hyp hTTypeII hqp hNUS
    hLmax hLtypeI hNUL hUH frob hW1E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

end OddOrder.Peterfalvi.S15

