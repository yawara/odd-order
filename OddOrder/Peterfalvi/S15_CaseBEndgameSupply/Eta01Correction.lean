/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.HSharpChosenBase
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

end OddOrder.Peterfalvi.S15
