/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.HSharpChosenBase
import OddOrder.Peterfalvi.S15_CharacterDegreeEngines
import OddOrder.Peterfalvi.S15_SSetMemberRFamily

/-!
# Peterfalvi §13 (p. 79) — the `S`-side `η₀₁` correction supply (13.8)

This file builds the `S`-side instance of Peterfalvi (13.8),
`∑_{x∈H^#} |η₀₁(x)|² ≥ |S′| − u²` (`H = PC`), from the honest `CharacterDegreeCore`
(issue 1041).  The already-formalized `eta10_Qsharp_norm_lower_core` is the book's
"(13.8) applied to `T`" instance consumed by (13.10.2); the present file is the book's
literal statement.

Structure (mirroring the `T`-side `Eta10Correction.lean` at the `CharacterDegreeCore`
level):

* the distinguished `μ`-column pairing `⟨τ₁ μ_{j₀}, η₀₁⟩ = δ = ±1`, all other nonzero
  columns orthogonal — from the (13.3.c) column formula `mu_tau1_formula` and the grid
  orthonormality (this is the book's "the hypothesis of (13.5) has been checked with
  `ζ₁ = μ_j`, `χ = η₀₁`, `a = δ`");
* the coefficient-zero chosen base `φ₀` — the linear character inducing the *other*
  nonzero `μ`-column, so `⟨τ₁(Ind φ₀), η₀₁⟩ = 0`;
* (subsequent commits) the (7.7.a) coefficient computation over the chosen family
  `H_sharp_hypothesis76_base`, the `(S, H^#)` correction package, and the final norm
  bound via `caseB_eta01_norm_bound`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.3.c), (13.5), (13.8): the chosen `H^#` base and the `η₀₁` pairing (p. 79) -/

open scoped FiniteInduce in
/-- **The `η`-column sums pair with `η₀₁` exactly at column `1`**: `⟨∑_i η_{ic}, η₀₁⟩ = [c = 1]`.
Grid orthonormality (`eta_orthonormal`); the `(0,1)` entry appears in the column-`c` sum iff
`c = 1`. -/
theorem Hypothesis.etaColumn_inner_eta01 [Finite G] (hyp : Hypothesis (G := G))
    (c : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.eta i c) hyp.eta01
      = if c = ⟨1, hyp.p_prime.one_lt⟩ then 1 else 0 := by
  rw [show hyp.eta01 = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ from rfl,
    OddOrder.RepresentationTheory.inner_sum_left]
  by_cases hc : c = ⟨1, hyp.p_prime.one_lt⟩
  · rw [if_pos hc,
      Finset.sum_eq_single_of_mem ⟨0, hyp.q_prime.pos⟩ (Finset.mem_univ _)
        (fun i _ hi => by
          rw [hyp.eta_orthonormal i ⟨0, hyp.q_prime.pos⟩ c ⟨1, hyp.p_prime.one_lt⟩,
            if_neg (fun h => hi h.1)]),
      hyp.eta_orthonormal ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩ c
        ⟨1, hyp.p_prime.one_lt⟩, if_pos ⟨rfl, hc⟩]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hyp.eta_orthonormal i ⟨0, hyp.q_prime.pos⟩ c ⟨1, hyp.p_prime.one_lt⟩,
      if_neg (fun h => hc h.2)]

open scoped FiniteInduce in
/-- **Distinct nonzero `μ`-column sums are distinct**: for `c ≠ j` the sums `μ_c` and `μ_j` are
orthogonal (`mu_orthonormal`), while `‖μ_j‖² = q ≠ 0` (`muColumn_inner_self`). -/
theorem Hypothesis.muColumnSum_ne_of_ne [Finite G] (hyp : Hypothesis (G := G))
    {c j : Fin hyp.p} (hcj : c ≠ j) :
    (∑ i : Fin hyp.q, hyp.mu i c) ≠ ∑ i : Fin hyp.q, hyp.mu i j := by
  intro heq
  have horth : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i c)
      (∑ i : Fin hyp.q, hyp.mu i j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hyp.mu_orthonormal i k c j, if_neg (fun h => hcj h.2)]
  rw [heq, hyp.muColumn_inner_self] at horth
  exact_mod_cast absurd horth (by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hyp.q_prime.pos.ne')

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c) → (13.5)-for-`η₀₁` input data** (the `S`-side mirror of the
`T`-side pinned-row block in `exists_muT_index_core_of_base_condition`, issue 1041):
a distinguished nonzero column `j₀` with `⟨τ₁ μ_{j₀}, η₀₁⟩ = δ = ±1`, every other nonzero
column `τ₁`-orthogonal to `η₀₁`, together with the coefficient-zero chosen base: the
linear `P`-nonkernel character `φ₀` inducing a *different* nonzero column `c₀`, so
`⟨τ₁(Ind φ₀), η₀₁⟩ = 0` and `Ind φ₀ ≠ μ_{j₀}`.

In the clean branch of `mu_tau1_formula` this is `j₀ = 1, δ = 1, c₀ = 2`; in the `p = 3`
sign-flip branch `j₀ = 2, δ = −1, c₀ = 1` (the flip sends `μ_{j₀}` to `−∑_i η_{i1}` and
`μ_{c₀}` to `−∑_i η_{i2}`). -/
theorem CharacterDegreeCore.exists_eta01_column_data [Finite G]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp) :
    ∃ (j₀ c₀ : Fin hyp.p) (δ : ℤ)
      (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S)),
      j₀ ≠ ⟨0, hyp.p_prime.pos⟩ ∧ c₀ ≠ ⟨0, hyp.p_prime.pos⟩ ∧ c₀ ≠ j₀ ∧
      (δ = 1 ∨ δ = -1) ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) ∧
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
        = ∑ i : Fin hyp.q, hyp.mu i c₀ ∧
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
        ≠ ∑ i : Fin hyp.q, hyp.mu i j₀ ∧
      ClassFunction.inner
        (core.tau1S (∑ i : Fin hyp.q, hyp.mu i j₀)) hyp.eta01 = (δ : ℂ) ∧
      (∀ c : Fin hyp.p, c ≠ ⟨0, hyp.p_prime.pos⟩ → c ≠ j₀ →
        ClassFunction.inner
          (core.tau1S (∑ i : Fin hyp.q, hyp.mu i c)) hyp.eta01 = 0) := by
  haveI := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have h2lt : 2 < hyp.p := by have := hyp.three_le_p; omega
  have hp2 : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) (by norm_num)
  have hp21 : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨1, hyp.p_prime.one_lt⟩ := by
    intro h; exact absurd (congrArg Fin.val h) (by norm_num)
  rcases core.mu_tau1_formula with hclean | ⟨hp3, hflip⟩
  · -- clean branch: `j₀ = 1`, `δ = 1`, base column `c₀ = 2`
    obtain ⟨θ, hθirr, -, hθP, hθeq⟩ := core.mu_j_linear_induced ⟨2, h2lt⟩ hp2
    refine ⟨⟨1, hyp.p_prime.one_lt⟩, ⟨2, h2lt⟩, 1, ⟨θ, hθirr⟩, hp1, hp2, hp21,
      Or.inl rfl, hθP, hθeq.symm, ?_, ?_, ?_⟩
    · rw [hθeq.symm]
      exact fun h => hyp.muColumnSum_ne_of_ne hp21 h
    · rw [hclean ⟨1, hyp.p_prime.one_lt⟩ hp1, hyp.etaColumn_inner_eta01, if_pos rfl]
      norm_num
    · intro c hc0 hc1
      rw [hclean c hc0, hyp.etaColumn_inner_eta01, if_neg hc1]
  · -- `p = 3` sign-flip branch: `j₀ = 2`, `δ = −1`, base column `c₀ = 1`
    obtain ⟨θ, hθirr, -, hθP, hθeq⟩ :=
      core.mu_j_linear_induced ⟨1, hyp.p_prime.one_lt⟩ hp1
    refine ⟨⟨2, h2lt⟩, ⟨1, hyp.p_prime.one_lt⟩, -1, ⟨θ, hθirr⟩, hp2, hp1,
      fun h => hp21 h.symm, Or.inr rfl, hθP, hθeq.symm, ?_, ?_, ?_⟩
    · rw [hθeq.symm]
      exact fun h => hyp.muColumnSum_ne_of_ne (fun h' => hp21 h'.symm) h
    · rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.p_prime.one_lt⟩ hp2 hp1 hp21,
        OddOrder.RepresentationTheory.ClassFunction.inner_neg_left,
        hyp.etaColumn_inner_eta01, if_pos rfl]
      norm_num
    · intro c hc0 hc2
      have hc1 : c = ⟨1, hyp.p_prime.one_lt⟩ := by
        have hlt := c.isLt
        have hv0 : c.val ≠ 0 := fun h => hc0 (Fin.ext h)
        have hv2 : c.val ≠ 2 := fun h => hc2 (Fin.ext h)
        have hv1 : c.val = 1 := by omega
        exact Fin.ext hv1
      subst hc1
      rw [hflip ⟨1, hyp.p_prime.one_lt⟩ ⟨2, h2lt⟩ hp1 hp2 (fun h => hp21 h.symm),
        OddOrder.RepresentationTheory.ClassFunction.inner_neg_left,
        hyp.etaColumn_inner_eta01, if_neg hp21, neg_zero]

end

section /- (13.5)/(13.8): the `S`-side distinguished family index (p. 79) -/

set_option maxHeartbeats 1600000 in
-- The (7.6)-family bookkeeping (constituent expansion + per-index coefficient computation)
-- elaborates as a single large proof term, as in the `T`-side twin.
open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **The `S`-side (13.3.c) distinguished index over the chosen base** (Peterfalvi (13.8),
issue 1041; the `S`-side mirror of `exists_muT_index_core_of_base_condition`): with the
(7.6) family `H_sharp_hypothesis76_base` based at `ζ₀ = Ind_{PC}^S φ₀` — `φ₀` the linear
`P`-nonkernel character inducing the *other* nonzero `μ`-column, so
`⟨τ₁(Ind φ₀), η₀₁⟩ = 0` — there is a family index `i₁` carrying the distinguished
`μ`-column (`ζ_{i₁} = μ_{j₀} = ∑_i μ_{i j₀}`) with `⟨τψ_{i₁}, η₀₁⟩ = δ = ±1`, and every
other `P`-nonkernel coefficient vanishes; `‖ζ_{i₁}‖² = q` and `ζ_{i₁}(1) = uq`.

This is the book's "By (13.3.c) … the hypothesis of (13.5) has thus been checked with
`ζ₁ = μ_j`, `χ = η₀₁` and `a = δ`" (p. 79).  The per-constituent dispatch mirrors the
`T`-side: an irreducible constituent of an `Ind_{PC}^S`-member is grid-orthogonal by the
(5.3.b) crux (`coherentIndS_image_inner_eta_eq_zero`); a reducible constituent is a
`μ`-column (`sSet_reducible_eq_muColumnSum`), equal to `μ_{j₀}` only when forced by the
`ℕ`-coefficient orthogonality count. -/
theorem Hypothesis.exists_muS_index_eta01_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    ∃ (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S))
      (i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1)) (δ : ℤ),
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)) ∧
      0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i = 0) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = (hyp.q : ℂ) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  set HU : Subgroup ↥hyp.S := huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `PC = H.subgroupOf S ≤ S' = HU`
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    change hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set K : Subgroup ↥hyp.S := hyp.H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  set core := hyp.characterDegreeCore hG hnoV chief with hcore
  set τ₁ := hyp.tau1S_ofHonest hG hnoV chief with hτ₁
  -- the (13.5)-for-`η₀₁` input data: distinguished column, sign, chosen base
  obtain ⟨j₀, c₀, δ, φ₀, hj₀0, hc₀0, hc₀j₀, hδpm, hφ₀P, hφ₀eq, hφ₀ne, hkeyr, hkey⟩ :=
    core.exists_eta01_column_data
  have hkeyr' : ClassFunction.inner (τ₁ (∑ i : Fin hyp.q, hyp.mu i j₀)) hyp.eta01
      = (δ : ℂ) := hkeyr
  have hkey' : ∀ c : Fin hyp.p, c ≠ ⟨0, hyp.p_prime.pos⟩ → c ≠ j₀ →
      ClassFunction.inner (τ₁ (∑ i : Fin hyp.q, hyp.mu i c)) hyp.eta01 = 0 := hkey
  -- (13.3.a): the distinguished column source `θr` (`μ_{j₀} = Ind_{PC}^S θr`)
  obtain ⟨θr, hθrirr, hθr1, hμeq, hθrP⟩ := hyp.mu_j_isIndPC_not_ker hG j₀ hj₀0
  -- degree-one values on `Irr K` (`K ≅ H = PC` abelian)
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hdeg1 : ∀ θ : ClassFunction ↥K ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ → θ 1 = 1 := fun _ hθ =>
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  -- `μ_{j₀} ∈ 𝒮` (13.3.a membership)
  have hμmem : (∑ i : Fin hyp.q, hyp.mu i j₀) ∈ sSet data :=
    sOf_subset_sSet data chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j₀ hj₀0)
  -- distinct `K`-inductions are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          ≠ ClassFunction.induce K (ψ : ClassFunction ↥K ℂ) →
      ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce K
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.S) (H := K) g _
    rw [← h1, heq]
  -- `⟨τ₁(Ind φ₀), η₀₁⟩ = 0`: the base is the other `μ`-column
  have hφ₀eta : ClassFunction.inner
      (τ₁ (ClassFunction.induce K (φ₀ : ClassFunction ↥K ℂ))) hyp.eta01 = 0 := by
    rw [show ClassFunction.induce K (φ₀ : ClassFunction ↥K ℂ)
        = ∑ i : Fin hyp.q, hyp.mu i c₀ from hφ₀eq]
    exact hkey' c₀ hc₀0 hc₀j₀
  -- ⟨τ₁(Ind_K θ), η₀₁⟩ = 0 for every `P`-nonkernel irreducible source with `Ind θ ≠ μ_{j₀}`:
  -- two-stage constituent expansion over `HU`, per-constituent (5.3.b)/(13.3.c) dispatch
  have hTau1IndEta : ∀ θ : ClassFunction ↥K ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ClassFunction.induce K θ ≠ ∑ i : Fin hyp.q, hyp.mu i j₀ →
      ClassFunction.inner (τ₁ (ClassFunction.induce K θ)) hyp.eta01 = 0 := by
    intro θ hθirr hθP hθne
    -- transport onto `PC-in-HU`
    have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hKle).surjective hθirr
    have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          (K.subgroupOf HU) :
        Set ↥(K.subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      have himg : ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
            (K.subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom)
          = (hyp.P.subgroupOf hyp.S).subgroupOf K := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]
      exact hθP
    -- two-stage constituent expansion with `ℕ`-coefficients
    have hzeta : ClassFunction.induce K θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            ClassFunction.inner
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
              (ClassFunction.restrict (K.subgroupOf HU)
                (s : ClassFunction ↥HU ℂ))
              • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ,
        OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
        ClassFunction.induce_sum]
      exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
    have hcoefNat : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, ∃ n : ℕ,
        ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
          (ClassFunction.restrict (K.subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
      intro s
      have hResChar : IsCharacter (ClassFunction.restrict
          (K.subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
        OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
      obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
      exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
    choose k hk using hcoefNat
    have hmem : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, k s ≠ 0 →
        ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
      intro s hks
      rw [mem_sSet]
      refine ⟨s, ?_, rfl⟩
      change ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
      have hHInHu : (hInHu data : Set ↥HU)
          = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
        congr 1
        change (data.H.subgroupOf hyp.S).subgroupOf HU
          = (hyp.P.subgroupOf hyp.S).subgroupOf HU
        have hPeq : data.H = hyp.P := by
          change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
        rw [hPeq]
      rw [hHInHu]
      have hs : ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
          (ClassFunction.restrict (K.subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
        rw [hk s]
        exact_mod_cast hks
      exact constituent_P_not_subset_characterKernel
        ((hyp.P.subgroupOf hyp.S).subgroupOf HU) (K.subgroupOf HU)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        hθ'irr hθ'P s hs
    -- expand the τ₁-image and dispatch per constituent
    have hzetaN : ClassFunction.induce K θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            k s • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [hzeta]
      exact Finset.sum_congr rfl fun s _ => by rw [hk s, Nat.cast_smul_eq_nsmul]
    rw [hzetaN, map_sum, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun s _ => ?_
    rcases Nat.eq_zero_or_pos (k s) with hk0 | hkpos
    · rw [hk0, zero_smul, map_zero, ClassFunction.inner_zero_left]
    · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ (k s), ClassFunction.inner_smul_left]
      suffices hterm0 : ClassFunction.inner
          (τ₁ (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))) hyp.eta01 = 0 by
        rw [hterm0, mul_zero]
      by_cases hsirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
      · -- irreducible constituent: (5.3.b) grid orthogonality at the `(0,1)` entry
        rw [show hyp.eta01 = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ from rfl]
        exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
          (sSet_closedUnderConjugate data)
          (sSet_hasNoRealCharacters data (hyp.oddCardS hG))
          (fun ζ' hζ' => by
            rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
                = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
              ClassFunction.support_neg]
            exact hyp.sSet_member_conjDiff_supported hG hζ')
          (hyp.coherent_H0Cprime_S hG hnoV chief) (hmem s hkpos.ne') hsirr
          ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩
      · -- reducible constituent: a nonzero `μ`-column `μ_c` with `c ≠ j₀`
        obtain ⟨c, hc0, heqcol⟩ :=
          hyp.sSet_reducible_eq_muColumnSum hG (hmem s hkpos.ne') hsirr
        by_cases hcj : c = j₀
        · -- `c = j₀` would make `μ_{j₀}` a constituent of `Ind_K θ`, contradicting
          -- `⟨Ind_K θ, μ_{j₀}⟩ = 0` (distinct-source `K`-inductions are orthogonal)
          exfalso
          subst hcj
          have hzmu : ClassFunction.inner (ClassFunction.induce K θ)
              (∑ i : Fin hyp.q, hyp.mu i c) = 0 := by
            rw [hμeq]
            exact hInd0 ⟨θ, hθirr⟩ ⟨θr, hθrirr⟩ fun h => hθne (h.trans hμeq.symm)
          have hexp : ClassFunction.inner (ClassFunction.induce K θ)
              (∑ i : Fin hyp.q, hyp.mu i c)
              = ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, (k s' : ℂ) *
                  ClassFunction.inner (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                    (∑ i : Fin hyp.q, hyp.mu i c) := by
            rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [hk s', ClassFunction.inner_smul_left]
          have hterm : ∀ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              ∃ n : ℕ,
              (k s' : ℂ) * ClassFunction.inner
                (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                (∑ i : Fin hyp.q, hyp.mu i c) = (n : ℂ) := by
            intro s'
            rcases Nat.eq_zero_or_pos (k s') with h0 | hpos
            · exact ⟨0, by rw [h0]; simp⟩
            · by_cases heq : ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ)
                  = ∑ i : Fin hyp.q, hyp.mu i c
              · refine ⟨k s' * hyp.q, ?_⟩
                rw [heq, hyp.muColumn_inner_self c]
                push_cast
                ring
              · exact ⟨0, by rw [sSet_pairwiseOrthogonal data (hmem s' hpos.ne') hμmem heq,
                  mul_zero, Nat.cast_zero]⟩
          choose n hn using hterm
          have hsumC : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              ((n s' : ℕ) : ℂ) = 0 := by
            rw [Finset.sum_congr rfl fun s' _ => (hn s').symm, ← hexp, hzmu]
          have hsumN : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              n s' = 0 := by
            rw [← Nat.cast_sum] at hsumC
            exact_mod_cast hsumC
          have hn0 : n s = 0 := (Finset.sum_eq_zero_iff.mp hsumN) s (Finset.mem_univ s)
          have hcontra : ((n s : ℕ) : ℂ) ≠ 0 := by
            rw [← hn s, heqcol, hyp.muColumn_inner_self c]
            exact mul_ne_zero (Nat.cast_ne_zero.mpr hkpos.ne')
              (Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne')
          exact hcontra (by rw [hn0, Nat.cast_zero])
        · -- `c ≠ j₀`: the (13.3.c) column orthogonality
          rw [heqcol]
          exact hkey' c hc0 hcj
  -- the distinguished family index: the family cover at the `μ_{j₀}`-source
  obtain ⟨i₁, hi₁0⟩ :=
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta_family_cover ⟨θr, hθrirr⟩
  have hζi₁ : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁
      = ∑ i : Fin hyp.q, hyp.mu i j₀ := by
    rw [hi₁0, hμeq]
    congr!
  have hζ0 : (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce K (φ₀ : ClassFunction ↥K ℂ) :=
    H_sharp_hypothesis76_base_zeta_zero hG hyp φ₀
  have hi₁pos : 0 < i₁ := by
    rw [Fin.pos_iff_ne_zero]
    intro h0
    apply hφ₀ne
    rw [← hζ0, ← h0, hζi₁]
  -- `P ⊄ Ker ζ_{i₁}` at the `S`-level
  have hζi₁P : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) := by
    obtain ⟨x₀, hx₀mem, hx₀ker⟩ := Set.not_subset.mp hθrP
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mp hx₀mem
    have hmem1 : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce K θr) := by
      have h1 := hsub hx₀S
      rw [hζi₁, hμeq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := K) hθrirr x₀.2 hmem1
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥K) = x₀ from rfl] at hbridge
  -- family degrees are constant (`K` abelian) ⟹ `d ≡ 1`
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ0, hθ0⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    obtain ⟨θQ, hθQirr, hθQeq⟩ : ∃ θQ : ClassFunction ↥K ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θQ ∧
        (H_sharp_hypothesis76_base hG hyp φ₀).zeta j = ClassFunction.induce K θQ :=
      ⟨θ0.val, θ0.2, by rw [hθ0]; congr!⟩
    rw [hθQeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      hdeg1 θQ hθQirr, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).d j = 1 := by
    intro j
    have h := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- the guarded τ₁ ↔ `Ind_S^G` bridge on `𝒮₁`-differences
  have hbridge : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) →
      τ₁ (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    intro θ θ' hθP hθ'P
    exact hyp.tau1S_ofHonest_apply_induce_sub hG hnoV chief _ _ θ.2 θ'.2 hθP hθ'P
  -- conjunct: the distinguished coefficient is `δ`
  have hθrP' : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((⟨θr, hθrirr⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ)) := hθrP
  have hc1 : (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i₁ = (δ : ℂ) := by
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i₁
        = ClassFunction.inner
            ((H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
              ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i₁)) hyp.eta01 from rfl,
      show (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
        = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    have hψ : (((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i₁) :
        ClassFunction ↥hyp.S ℂ)
        = ClassFunction.induce K (θr : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (φ₀ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i₁, one_smul, hζi₁, hζ0,
        hμeq]
    rw [hψ, ← hbridge ⟨θr, hθrirr⟩ φ₀ hθrP' hφ₀P,
      map_sub, ClassFunction.inner_sub_left]
    have h1 : ClassFunction.inner (τ₁ (ClassFunction.induce K θr)) hyp.eta01 = (δ : ℂ) := by
      rw [← hμeq]
      exact hkeyr'
    rw [show ClassFunction.inner
        (τ₁ (ClassFunction.induce K (θr : ClassFunction ↥K ℂ))) hyp.eta01
        = ClassFunction.inner (τ₁ (ClassFunction.induce K θr)) hyp.eta01 from rfl,
      h1, hφ₀eta, sub_zero]
  -- conjunct: all other `P`-nonkernel coefficients vanish
  have hmid : ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i → i ≠ i₁ →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i = 0 := by
    intro i _hipos hine hiP
    obtain ⟨θi0, hθi0⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced i
    obtain ⟨θiQ, hθiQirr, hθiQeq⟩ : ∃ θiQ : ClassFunction ↥K ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θiQ ∧
        (H_sharp_hypothesis76_base hG hyp φ₀).zeta i = ClassFunction.induce K θiQ :=
      ⟨θi0.val, θi0.2, by rw [hθi0]; congr!⟩
    -- `P`-nonkernel witness at the `K`-level
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle' : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle').mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPle : hyp.P.subgroupOf hyp.S ≤ K := by
      rw [hKdef]
      exact Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hθiP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θiQ) := by
      intro hker
      apply hiP
      have hfwd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (A := hyp.P.subgroupOf hyp.S) (H := K) hPle θiQ hker
      rw [hθiQeq]
      exact hfwd
    have hne : ClassFunction.induce K θiQ
        ≠ ∑ i' : Fin hyp.q, hyp.mu i' j₀ := by
      intro heq
      refine hine ((H_sharp_hypothesis76_base hG hyp φ₀).zeta_injective ?_)
      rw [hθiQeq, heq, hζi₁]
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i
        = ClassFunction.inner
            ((H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
              ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i)) hyp.eta01 from rfl,
      show (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
        = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    have hψi : (((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i) :
        ClassFunction ↥hyp.S ℂ)
        = ClassFunction.induce K θiQ
          - ClassFunction.induce K (φ₀ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i, one_smul, hθiQeq, hζ0]
    rw [hψi, ← hbridge ⟨θiQ, hθiQirr⟩ φ₀ hθiP hφ₀P,
      map_sub, ClassFunction.inner_sub_left,
      hTau1IndEta θiQ hθiQirr hθiP hne,
      hφ₀eta, sub_zero]
  -- conjuncts: norm square `q`, degree `uq`, sign square
  have hnormSq : (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = (hyp.q : ℂ) := by
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁
        = ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁) from rfl,
      hζi₁, hyp.muColumn_inner_self j₀]
  have hdegVal : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ 1
      = ((hyp.u * hyp.q : ℕ) : ℂ) := by
    rw [hζi₁]
    exact hyp.mu_j_degree hG j₀ hj₀0
  have hδ2 : δ ^ 2 = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  exact ⟨φ₀, i₁, δ, hφ₀P, hi₁pos, hζi₁P, hδ2, hc1, hmid, hnormSq, hdegVal⟩

end

section /- (13.5.a): integrality of the `η₀₁` correction at `1` -/

open scoped Classical in
open scoped FiniteInduce in
/-- **The `(S, H^#)` chosen-base (7.7.a) coefficients of a virtual character are integers**
(mirror of `Q_sharp_hypothesis76_base_cCoeff_int`): `c_i = ⟨τψ_i, χ⟩` with both arguments
virtual characters — `ψ_i = ζ_i − d_i ζ_0` has `d_i = 1` (all family degrees are `[S : H]`
since `H = PC` is abelian, (13.2.a)) and `τ = Ind_S^G` on the `(S, H^#)` TI-datum
(`H_sharp_tau_eq_induce`) preserves virtual characters. -/
theorem H_sharp_hypothesis76_base_cCoeff_int [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i = (z : ℂ) := by
  classical
  haveI := hyp.finiteG
  intro i
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S
    with hKdef
  -- `K ≅ H = PC` is abelian, so every `θ_j` is linear and all `ζ_j` have degree `[S:K]`.
  have hHS : hyp.H ≤ hyp.S := hyp.H_le_S
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  -- Degrees: `ζ_j(1) = [S:K]` for every `j`, so the degree ratio is `1`.
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76_base hG hyp φ₀).d i = 1 := by
    have h := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- `ψ_i = ζ_i − ζ_0 ∈ ℤ[Irr S]`.
  have hzetaZ : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j ∈ ZIrr ↥hyp.S := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hψZ : (((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i) :
      ClassFunction ↥hyp.S ℂ) ∈ ZIrr ↥hyp.S := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  -- The `τ`-image is a virtual character: `τ = Ind_S^G` preserves `ℤ[Irr]`.
  have hpres : (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
      ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i) ∈ ZIrr G := by
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
        = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr hyp.S hψZ
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ

open scoped Classical in
open scoped FiniteInduce in
/-- **The `S`-side correction has integer value at `1`** over the chosen base (Peterfalvi
(13.5.a) integrality for the (13.8) estimate; mirror of `exists_etaT_alphaFun_one_int_core`):
`α(1) ∈ ℤ` for the `P`-kernel tail `α = hypothesis76AlphaFun` of the `(S, H^#)` (7.7.a)
decomposition of `η₀₁`, via the integer (7.7.a) coefficients and `η₀₁ ∈ ℤ[Irr G]`
(`eta01_mem_ZIrr`). -/
theorem Hypothesis.exists_etaS_alphaFun_one_int_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) :
    ∃ α1 : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) hyp.eta01 1 = (α1 : ℂ) := by
  haveI := hyp.finiteG
  exact hypothesis76AlphaFun_one_int (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) hyp.eta01
    (H_sharp_hypothesis76_base_cCoeff_int hG hyp φ₀ hyp.eta01_mem_ZIrr)

end

section /- (13.8): the `(S, H^#)` correction package and the norm bound (p. 79) -/

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5)/(13.8), the `(S, H^#)` correction package** (mirror of
`exists_caseB_data_eta10_T_core`): the normalized distinguished `μ`-column
`ζ = q⁻¹·μ_{j₀}`, the `P`-kernel tail `α`, the point formula `η₀₁ = δζ + α` on `H^#`,
the exact first term `|S′| − u²`, the cross term `u·α(1)`, and the `(|P|−1)α(1)²`
inflation bound — the seven inputs of `caseB_eta01_norm_bound`. -/
theorem Hypothesis.exists_caseB_data_eta01_S_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ (ζ α : ↥hyp.S → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
        hyp.eta01 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.S) : ℝ) - (hyp.u : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.u : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2 := by
  classical
  haveI := hyp.finiteG
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupS hG)
  obtain ⟨φ₀, i₁, δ, _hφ₀P, hi₁pos, hi₁ker, hδ2, hi₁c, hmiddle, hnormQ, hdeg⟩ :=
    hyp.exists_muS_index_eta01_core hG hnoV chief
  obtain ⟨α1, hα1⟩ := hyp.exists_etaS_alphaFun_one_int_core hG φ₀
  let H76 := H_sharp_hypothesis76_base hG hyp φ₀
  have hqC : (hyp.q : ℂ) ≠ 0 := by
    exact_mod_cast (show hyp.q ≠ 0 from hyp.q_prime.ne_zero)
  have hqR : (hyp.q : ℝ) ≠ 0 := by
    exact_mod_cast (show hyp.q ≠ 0 from hyp.q_prime.ne_zero)
  have hvanishZ : ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → H76.zeta i₁ x = 0 :=
    fun x hx => H76.zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  refine ⟨fun x => ((hyp.q : ℂ))⁻¹ * H76.zeta i₁ x,
    hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01, α1, δ,
    ?_, ?_, ?_, ?_, ?_, hδ2, ?_⟩
  · intro x hx
    change ((hyp.q : ℂ))⁻¹ * H76.zeta i₁ x = 0
    rw [hvanishZ x hx, mul_zero]
  · have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero H76
      (hyp.P.subgroupOf hyp.S) hyp.eta01 i₁ hi₁ker
    have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x))
        = ∑ x : ↥hyp.S, H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (· ∈ hyp.H.subgroupOf hyp.S)
        (fun x => H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x))]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
          H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [hvanishZ x (Finset.mem_filter.mp hx).2, zero_mul]
      rw [h0, add_zero]
    calc
      ∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
          ((hyp.q : ℂ))⁻¹ * H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x)
          = ((hyp.q : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter
              (· ∈ hyp.H.subgroupOf hyp.S), H76.zeta i₁ x * (starRingEnd ℂ)
                (hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [hext, hfull, mul_zero]
  · intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxH : (↑x : G) ∈ hyp.H :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := hypothesis76_point_formula H76 (fun _ => rfl)
      (hyp.P.subgroupOf hyp.S) hyp.eta01 i₁ hi₁pos hi₁ker hmiddle x hxsharp
    have htail : (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff hyp.eta01 i) / H76.zetaNormSq i) * H76.zeta i x)
        = hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 x := rfl
    rw [hpt, htail, hi₁c, star_intCast, hnormQ]
    ring
  · have hpars : ((∑ x : ↥hyp.S, ‖H76.zeta i₁ x‖ ^ 2 : ℝ) : ℂ)
        = (Nat.card ↥hyp.S : ℂ) * (hyp.q : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, ← OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq,
        hnormQ]
    have hparsR : ∑ x : ↥hyp.S, ‖H76.zeta i₁ x‖ ^ 2
        = (Nat.card ↥hyp.S : ℝ) * (hyp.q : ℝ) := by
      exact_mod_cast hpars
    have hscale : ∀ x : ↥hyp.S,
        ‖((hyp.q : ℂ))⁻¹ * H76.zeta i₁ x‖ ^ 2
          = ((hyp.q : ℝ))⁻¹ ^ 2 * ‖H76.zeta i₁ x‖ ^ 2 := by
      intro x
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hζ1 : ‖((hyp.q : ℂ))⁻¹ * H76.zeta i₁ 1‖ ^ 2 = (hyp.u : ℝ) ^ 2 := by
      rw [hdeg, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      rw [show ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) from by
        push_cast; ring]
      field_simp
    have hSq : (Nat.card ↥hyp.S : ℝ)
        = (Nat.card ↥(derivedInG hyp.S) : ℝ) * (hyp.q : ℝ) := by
      exact_mod_cast hyp.card_S_eq_deriv_mul_q
    rw [Finset.sum_congr rfl (fun x _ => hscale x), ← Finset.mul_sum, hparsR, hζ1, hSq]
    field_simp
  · have hζ1u : ((hyp.q : ℂ))⁻¹ * H76.zeta i₁ 1 = ((hyp.u : ℕ) : ℂ) := by
      rw [hdeg, show ((hyp.u * hyp.q : ℕ) : ℂ) = (hyp.u : ℂ) * (hyp.q : ℂ) from by
        push_cast; ring]
      field_simp
    change ((((hyp.q : ℂ))⁻¹ * H76.zeta i₁ 1) *
        (starRingEnd ℂ) (hypothesis76AlphaFun H76
          (hyp.P.subgroupOf hyp.S) hyp.eta01 1)).re = (hyp.u : ℝ) * (α1 : ℝ)
    rw [hζ1u, hα1]
    rw [show ((hyp.u : ℕ) : ℂ) = (((hyp.u : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      show ((α1 : ℤ) : ℂ) = (((α1 : ℤ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · have hF : ∀ x : ↥hyp.S,
        x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1 ↔
          ((x : G) ∈ H76.H ∧ x ≠ 1) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨Subgroup.mem_subgroupOf.mp h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr h2⟩
    have hP'H : ∀ x : ↥hyp.S, x ∈ hyp.P.subgroupOf hyp.S → (x : G) ∈ H76.H := by
      intro x hx
      exact (show hyp.P ≤ hyp.H from le_sup_left) (Subgroup.mem_subgroupOf.mp hx)
    have hinfl := hypothesis76AlphaFun_inflation H76 (hyp.P.subgroupOf hyp.S)
      hyp.eta01 _ hF hP'H
    have hPS : hyp.P ≤ hyp.S := by
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    have hcardPS : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
      exact hyp.card_P_eq hG hyp.Sdata_W2_eq
    have hpq1 : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
      Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
    have hcoeff : ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ)) - 1
        = ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) := by
      rw [hcardPS, Nat.cast_sub hpq1]
      norm_num
    have hval : ‖hypothesis76AlphaFun H76 (hyp.P.subgroupOf hyp.S) hyp.eta01 1‖ ^ 2
        = ((α1 : ℤ) : ℝ) ^ 2 := by
      rw [hα1, Complex.norm_intCast, sq_abs]
    rw [← hval, ← hcoeff]
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8)**: `∑_{x∈H^#} |η₀₁(x)|² ≥ |S′| − u²` (`H = PC`; p. 79) — the book's
literal `S`-side statement (issue 1041; `eta10_Qsharp_norm_lower_core` is the
"(13.8) applied to `T`" instance of (13.10.2)).  Chains the `(S, H^#)` correction package
into the side-independent engine `caseB_eta01_norm_bound`; the (13.2.c) bound
`2u ≤ |P| − 1` is `two_mul_u_le`. -/
theorem Hypothesis.eta01_Hsharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (Nat.card ↥(derivedInG hyp.S) : ℝ) - (hyp.u : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta01 x‖ ^ 2 := by
  classical
  haveI := hyp.finiteG
  obtain ⟨ζ, α, α1, δ, hvanish, hinner, hχ, hfirstTerm, hcross, hδ, hinfl⟩ :=
    hyp.exists_caseB_data_eta01_S_core hG
  have hHS : hyp.H ≤ hyp.S := hyp.H_le_S
  have hu := hyp.two_mul_u_le hG
  have hengine : (Nat.card ↥(derivedInG hyp.S) : ℝ) - (hyp.u : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖hyp.eta01 ↑x‖ ^ 2 := by
    have h := caseB_eta01_norm_bound (S := ↥hyp.S) (hyp.H.subgroupOf hyp.S)
      ζ α (fun x => hyp.eta01 ↑x)
      (Pm1 := hyp.p ^ hyp.q - 1) (u := hyp.u)
      (firstTerm := (Nat.card ↥(derivedInG hyp.S) : ℝ) - (hyp.u : ℝ) ^ 2)
      (α1 := α1) (δ := δ)
      hvanish (by convert hinner using 2)
      (fun x hx => hχ x (by convert hx using 2))
      hfirstTerm hcross hδ
      (by convert hinfl using 2; congr!) hu
    convert h using 2; congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hHS
    (fun y => ‖hyp.eta01 y‖ ^ 2)] at hengine

end

end OddOrder.Peterfalvi.S15
