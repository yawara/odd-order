/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBWeightedEndgame

/-!
# Peterfalvi (6.2)/(6.3): the coherence-break degree bound and the `≤ 4|L:K|² + 1` index bound

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.2)/(6.3).

These two theorems are the gate (the `hbound` input of the (6.5)(b) `p`-group reduction
`S08_PGroupReduction`): the contrapositive of Theorem (6.3) — `¬coherent S` + `H` nilpotent +
`S(⁅H,H⁆) = Y` coherent ⟹ `|H : ⁅H,H⁆| ≤ 4|W₁|² + 1` — supplies `hbound` for the (6.8) capstone.

This leaf starts with the **degree-square sum identity** over a filtration set `S(A)`, the
character-theoretic content of (6.2):
`∑_{χ ∈ S(A)} χ(1)²/‖χ‖² = |L:K|·(|K:A| − 1)`.
It is the single-filter analogue of `sum_re_div_normSq_Xset_eq` (the case-(B) `X`-set difference
sum), routing through the complex orbit count `sum_div_normSq_induce_kernelFilter_eq`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.2) degree-square sum over a filtration set `S(A)`.**

The norm-weighted degree-square sum over `S(A) = {Ind_H^L θ | A ⊆ Ker θ, θ ≠ 1}` is
`|L:H|·(|H : A| − 1)` (Peterfalvi (6.2) proof, mmd 04.8 L13-17: `∑_{χ∈S(A)} χ(1)²/‖χ‖² =
|L:K|(|K:A| − 1)`, with `K = H` the kernel).  Single-filter form of `sum_re_div_normSq_Xset_eq`:
the complex orbit-count identity `sum_div_normSq_induce_kernelFilter_eq` followed by the per-summand
real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)` (`χ(1)` a real degree, `⟨χ,χ⟩` real). -/
theorem sum_re_div_normSq_SsubFiltration_eq (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) := by
  letI : H.Normal := hyp.H_normal
  -- the complex weighted `S(A)` identity.
  have hcomplex := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ A _
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hχ1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
        = ((H.index * d : ℕ) : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd]; push_cast; ring
    have hr : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)).re
        = ((H.index * d : ℕ) : ℝ) := by
      rw [hχ1, Complex.natCast_re]
    rw [hr, hχ1, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    congr 1
    rw [inner_self_eq_realCast (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)), Complex.ofReal_re]
  -- combine: cast the real sum to `ℂ`, rewrite each summand, identify with `hcomplex`.
  have key : (((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

end OddOrder.Peterfalvi.S08
