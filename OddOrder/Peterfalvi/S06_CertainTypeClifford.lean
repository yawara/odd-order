/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeCharacters

/-!
# Peterfalvi §6 (4.5): Clifford theory of the certain-type characters

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§6, pp. 21-24.

Building on the certain-type character family `μ_{ij}` of (4.3.b) and its kernel
description (4.4) from `S06_CertainTypeCharacters`, this file formalizes Peterfalvi
**(4.5)**: the column sums `μ_j = ∑_i μ_{ij}` and the restrictions
`χ_j = Res^L_K μ_{ij}` (independent of `i`, irreducible, with `Ind^L_K χ_j = μ_j`),
and the exhaustion of `Irr(L)` by the `μ_{ij}` together with the irreducible
inductions `Ind^L_K χ` of the remaining `χ ∈ Irr(K)`.

The starting structural fact is that the signed differences `μ_{ij} − μ_{0j}` vanish
on `K`: they equal `δ_j · Ind_W^L(ω_{ij} − ω_{0j})`, the source difference is supported
on `W − W₂` (the linear characters of a column agree on `W₂`), and
`(W₁ ⊔ W₂) ⊓ K = W₂` so no `L`-conjugate of `W − W₂` meets `K`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

namespace Hypothesis

variable (h : Hypothesis L)

/-- **`W ⊓ K = W₂` (membership form)** (mmd 04.6, (4.5) proof "`K ∩ W = W₂`"): an element of
`W = W₁ ⊔ W₂` that lies in `K` already lies in `W₂`.  Writing it as `x·y` with `x ∈ W₁`,
`y ∈ W₂ ≤ K`, the `W₁`-part `x = (x·y)·y⁻¹` lies in `K`, hence in `K ⊓ W₁ = ⊥`
(`isComplement.disjoint`), so `x = 1` and the element is `y ∈ W₂`. -/
theorem mem_W2_of_mem_sup_of_mem_K {a : L} (ha : a ∈ h.W1 ⊔ h.W2) (haK : a ∈ h.K) :
    a ∈ h.W2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_of_mem_sup ha
  have hyK : y ∈ h.K := h.W2_le_K hy
  have hxK : x ∈ h.K := by
    have hx_eq : x = a * y⁻¹ := by rw [← hxy]; group
    rw [hx_eq]
    exact h.K.mul_mem haK (h.K.inv_mem hyK)
  have hx1 : x = 1 := by
    have hmem : x ∈ h.K ⊓ h.W1 := ⟨hxK, hx⟩
    rwa [disjoint_iff.mp h.isComplement.disjoint, Subgroup.mem_bot] at hmem
  rw [← hxy, hx1, one_mul]
  exact hy

section Recipe

variable [Invertible (Nat.card L : ℂ)]
  [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]

/-- **The induced column difference `Ind_W^L(ω_{ij} − ω_{0j})` vanishes on `K`** (mmd 04.6,
(4.5.a) proof).  The source difference `ω_{ij} − ω_{0j}` is supported on `W − W₂` (the two
linear characters of a column agree on `W₂`, `omega_omegaProdChar_sub_eq_zero_of_mem_W2`), so
the induced class function vanishes off the `L`-conjugates of `W − W₂`.  No conjugate of an
element `k ∈ K` lands there: `K ⊴ L` gives `x⁻¹kx ∈ K`, and if it also lies in `W` then it lies
in `W ⊓ K = W₂` (`mem_W2_of_mem_sup_of_mem_K`), i.e. outside `W − W₂`. -/
theorem induce_chiColumnDiff_eq_zero_of_mem_K [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {k : L} (hk : k ∈ h.K) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
      ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) k = 0 := by
  refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
    (A := {w : ↥h.sdiffTICyclicHypothesis.W | (w : L) ∉ h.W2}) ?_ ?_
  · -- the difference is supported on `W − W₂`: it vanishes on `W₂`
    intro w hw
    rw [ClassFunction.mem_support] at hw
    rw [Set.mem_setOf_eq]
    intro hwmem
    apply hw
    have hwW2 : w ∈ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W := by
      rw [Subgroup.mem_subgroupOf]; exact hwmem
    rw [ClassFunction.sub_apply]
    exact omega_omegaProdChar_sub_eq_zero_of_mem_W2 h.sdiffTICyclicHypothesis
      (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂ hwW2
  · -- `k` is not conjugate into `W − W₂`
    rintro ⟨x, hx, hxA⟩
    rw [Set.mem_setOf_eq] at hxA
    apply hxA
    have hconjK : x⁻¹ * k * x ∈ h.K := by
      simpa using h.K_normal.conj_mem k hk x⁻¹
    have hxW : x⁻¹ * k * x ∈ h.W1 ⊔ h.W2 := hx
    exact h.mem_W2_of_mem_sup_of_mem_K hxW hconjK

/-- **Peterfalvi (4.5.a), key vanishing**: the signed difference `μ_{ij} − μ_{0j}` of a column
vanishes on `K`.  It equals `δ_j · Ind_W^L(ω_{ij} − ω_{0j})` (`columnFamily_spec`,
`isometryDifferenceImage_induceZ`), which vanishes on `K`
(`induce_chiColumnDiff_eq_zero_of_mem_K`), and `δ_j = ±1 ≠ 0`. -/
theorem columnFamily_difference_vanishes_on_K [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {k : L} (hk : k ∈ h.K) :
    (h.columnFamily χ₂).difference i k = 0 := by
  have hsd : (h.columnFamily χ₂).signedDifference i k = 0 := by
    rw [← h.columnFamily_spec χ₂ i, isometryDifferenceImage_induceZ]
    exact h.induce_chiColumnDiff_eq_zero_of_mem_K χ₂ i hk
  rw [SignedIrreducibleDifferenceFamily.signedDifference_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul] at hsd
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp hsd).resolve_left hs

/-- **Peterfalvi (4.5.a), independence of `i`**: the restriction `χ_j = Res^L_K μ_{ij}` does
not depend on the `W₁`-index `i`.  Indeed `μ_{ij} − μ_{0j}` vanishes on `K`
(`columnFamily_difference_vanishes_on_K`), so `μ_{ij}` and `μ_{0j}` agree on `K`. -/
theorem restrict_certainType_eq [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.restrict h.K ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
      = ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) := by
  ext k
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ← sub_eq_zero]
  have hdiff := h.columnFamily_difference_vanishes_on_K χ₂ i k.2
  rwa [SignedIrreducibleDifferenceFamily.difference_apply, ClassFunction.sub_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply] at hdiff

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06
