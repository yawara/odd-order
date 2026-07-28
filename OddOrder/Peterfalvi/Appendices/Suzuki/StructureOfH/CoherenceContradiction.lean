/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.InducedLambda
import OddOrder.Peterfalvi.Appendices.FeitSibleyCoherentImage

/-!
# Peterfalvi Part II, Ch. III: the coherence contradiction (Theorem C, step (10))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 116:

> Suppose that `f₁ = ±eᵢ` for some `i`.  By Lemma 2(c) of Appendix IV,
> `χ̄ᵢ ≠ χᵢ` and `χ̄ᵢ ∈ 𝒮`.  Therefore there is an element `e′ᵢ ∈ {eⱼ | j ≠ i}`
> such that `Ind_H^G(χᵢ − χ̄ᵢ) = eᵢ − e′ᵢ`. […] Then
> `(Ind_H^G λ, eᵢ − e′ᵢ) = (λ, χᵢ − χ̄ᵢ) = 0`, whence
> `Ind_H^G λ = ±(eᵢ + e′ᵢ)` and `|Q| + 1 = (Ind_H^G λ)(1) = ±2eᵢ(1)`, which is
> impossible since `|Q|` is even.

This leaf assembles the contradiction: `f ⊥ e_χ` for each irreducible
constituent `f` of `Ind λ` and each member `χ ∈ 𝒮` — the orthogonality input
of the step (11) bookkeeping.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.RepresentationTheory

universe uG uΩ

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **`[G : H] = |Q| + 1`**: `H` is a point stabilizer of the doubly transitive
action on `Ω`, and `|Ω| = |Q| + 1`. -/
theorem index_H_eq :
    sc.toHypothesis.H.index = Nat.card ↥sc.toHypothesis.Q + 1 := by
  haveI := sc.toHypothesis.doubly_transitive
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [sc.toHypothesis.H_def,
    MulAction.index_stabilizer_of_transitive G sc.toHypothesis.basept,
    sc.toHypothesis.card_Omega]

/-- **`[G : H]` is odd** (`= |Q| + 1` with `|Q|` even) — the parity that step
(10) plays against the even `±2eᵢ(1)`. -/
theorem odd_index_H : Odd sc.toHypothesis.H.index := by
  rw [sc.index_H_eq]
  obtain ⟨k, hk⟩ := sc.toHypothesis.Q_even
  exact ⟨k, by omega⟩

/-- **`(Ind_H^G θ)(1) = |Q| + 1` for a degree-one `θ`** — the book's
"`|Q| + 1 = (Ind_H^G λ)(1)`" (p. 116). -/
theorem induce_apply_one_eq [Fintype G]
    [Invertible (Nat.card ↥sc.toHypothesis.H : ℂ)]
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ}
    (hdeg : (θ : ↥sc.toHypothesis.H → ℂ) 1 = 1) :
    ClassFunction.induce sc.toHypothesis.H θ (1 : G)
      = (Nat.card ↥sc.toHypothesis.Q : ℂ) + 1 := by
  rw [ClassFunction.induce_apply_one]
  rw [show θ (1 : ↥sc.toHypothesis.H) = 1 from hdeg, mul_one, sc.index_H_eq]
  push_cast
  ring

/-- **`λ ∉ 𝒮`**: a class function with `QK` in its kernel kills
`Q₁ ≤ Q ≤ QK`, while members of `𝒮` do not. -/
theorem notMem_fs_Sset_of_leKer_QK
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ}
    (hker : ((sc.toHypothesis.QK.subgroupOf sc.toHypothesis.H :
      Subgroup ↥sc.toHypothesis.H) : Set ↥sc.toHypothesis.H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) :
    θ ∉ (sc.feitSibleyHypothesis ind hQ1).Sset := by
  rintro ⟨-, hnk⟩
  apply hnk
  intro x hx
  have hxQK : (x : G) ∈ sc.toHypothesis.QK :=
    sc.toHypothesis.Q_le_QK (sc.toHypothesis.Q1_le_Q hx)
  have hmem := hker (Subgroup.mem_subgroupOf.mpr hxQK)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
  exact hmem

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
