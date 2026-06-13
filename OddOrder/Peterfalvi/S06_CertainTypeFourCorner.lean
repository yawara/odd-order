/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeIsometry

/-!
# Peterfalvi (4.10): the four-corner Dade identity

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, p. 24, statement (4.10).

For `0 ≤ i < w₁` and `0 ≤ j < w₂`,
`(δ_j μ_{ij} − δ_j μ_{0j} − μ_{i0} + μ_{00})^τ = ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ`.

Following the book proof: the `L`-side four-corner `β = δ_j(μ_{ij} − μ_{0j}) − (μ_{i0} − μ_{00})`
is the induced four-corner `Ind_W^L α` of the `W`-side `α = ω_{ij} − ω_{0j} − ω_{i0} + ω_{00}`
(the (3.4) `alphaCF`, supported on `V`).  By (3.4) `Supp α ⊂ V`, so `Supp β ⊂ V^L`, and the §4 Dade
map preserves values on `V` while both sides vanish off `V^G`, giving `β^τ = α^σ`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **(4.10), piece (a): the `L`-side four-corner is the induced `W`-side four-corner.**
`δ_j(μ_{ij} − μ_{0j}) − δ_0(μ_{i0} − μ_{00}) = Ind_W^L(ω_{ij} − ω_{0j} − ω_{i0} + ω_{00})`, by the
(1.4) image relation `Ind_W^L(ω_{·j} − ω_{0j}) = δ_j(μ_{·j} − μ_{0j})` (`columnFamily_spec`,
`isometryDifferenceImage_induceZ`) for columns `χ₂` and `1`, with `Ind` additivity. -/
theorem fourcorner_signedDiff_eq_induce (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).signedDifference i - (h.columnFamily 1).signedDifference i
      = ClassFunction.induce h.sdiffTICyclicHypothesis.W
          ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
              - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))) := by
  rw [← h.columnFamily_spec χ₂ i, ← h.columnFamily_spec 1 i,
    h.isometryDifferenceImage_induceZ χ₂ i, h.isometryDifferenceImage_induceZ 1 i]
  simp only [← h.sdiffTICyclicHypothesis.induceLinear_apply]
  rw [← map_sub]

/-- **Pointwise value of the grid character** `ω_{ij}(w) = (w1CharEquiv i)(wFst w)·χ₂(wSnd w)`.
The `change` step unfolds `omegaProdChar` definitionally — bypassing the `sdiff`/`h` `1`-type
mismatch that defeats `simp` on `(1 : _ →* ℂˣ)(x)`; `Units.val_mul` splits the product.  This is
the value tool for the (4.10) support proof (`Supp(four-corner) ⊂ V`). -/
theorem chiColumn_apply_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (w : ↥h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = ((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) : ℂ)
        * (χ₂ (h.sdiffTICyclicHypothesis.wSnd w) : ℂ) := by
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
  change (((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
      * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) : ℂˣ) : ℂ) = _
  rw [Units.val_mul]

/-- On `W₂`, the column character `ω_{ij} = chiColumn χ₂ i` is independent of the row `i`:
`wFst` kills `W₂` (`wFst_eq_one_of_mem_W2`), so the `W₁`-character factor `(w1CharEquiv i)(wFst w)`
collapses to `1` and `ω_{ij}(w) = χ₂(wSnd w)` for every row.  The `W₂` companion of
`chiColumn_apply_of_mem_W1`. -/
theorem chiColumn_apply_of_mem_W2 (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {w : ↥h.sdiffTICyclicHypothesis.W}
    (hw : w ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = (χ₂ (h.sdiffTICyclicHypothesis.wSnd w) : ℂ) := by
  have hχ : (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) = 1 := by
    rw [h.sdiffTICyclicHypothesis.wFst_eq_one_of_mem_W2 hw]; exact map_one _
  have h1 : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂ w
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
        * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) := rfl
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply, h1, hχ, one_mul]

/-- **(4.10), piece (b): the `W`-side four-corner is supported on `V = W − (W₁ ∪ W₂)`.**
The four-corner `ω_{ij} − ω_{0j} − (ω_{i0} − ω_{00})` vanishes off `V` because it dies on both
`W₁` and `W₂`:
* on `W₂` (`chiColumn_apply_of_mem_W2`) every `ω` collapses to its `χ₂`-value, independent of the
  row, so `ω_{ij} − ω_{0j} = 0` and `ω_{i0} − ω_{00} = 0`;
* on `W₁` (`chiColumn_apply_of_mem_W1`) every `ω` collapses to its `W₁`-character value,
  independent of the column, so `ω_{ij} − ω_{i0} = 0` and `ω_{0j} − ω_{00} = 0` (the four-corner
  rearranges to a cancelling pair).

This is the strong support `CF(W, W − (W₁ ∪ W₂)) = SupportedOnV ℂ toTICyclicHypothesis` that the
induced four-corner `Ind_W^L(·)` (piece (a)) needs for `Supp ⊆ V^L ⊆ A₀`, sidestepping the
`chiColumn`/`alphaCF` coercion mismatch of the direct `= alphaCF` route. -/
theorem chiColumn_fourcorner_mem_supportedSubmodule (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)))
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup h.toTICyclicHypothesis.V
            h.sdiffTICyclicHypothesis.W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro w hw
  rw [ClassFunction.mem_support] at hw
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  -- `toTICyclicHypothesis.V = ↑(W₁ ⊔ W₂) ∖ (↑W₁ ∪ ↑W₂)`
  have hVdef : h.toTICyclicHypothesis.V
      = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ ((h.W1 : Set ↥L) ∪ (h.W2 : Set ↥L)) := rfl
  rw [hVdef, Set.mem_diff, Set.mem_union, not_or]
  refine ⟨w.2, fun h1 => hw ?_, fun h2 => hw ?_⟩
  · -- `(w : L) ∈ W₁`: column difference cancels (row-only dependence)
    have hwmem : w ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr h1
    simp only [ClassFunction.sub_apply, chiColumn_apply_of_mem_W1 h χ₂ i hwmem,
      chiColumn_apply_of_mem_W1 h χ₂ 0 hwmem, chiColumn_apply_of_mem_W1 h 1 i hwmem,
      chiColumn_apply_of_mem_W1 h 1 0 hwmem]
    ring
  · -- `(w : L) ∈ W₂`: row difference cancels (column-only dependence)
    have hwmem : w ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr h2
    simp only [ClassFunction.sub_apply, chiColumn_apply_of_mem_W2 h χ₂ i hwmem,
      chiColumn_apply_of_mem_W2 h χ₂ 0 hwmem, chiColumn_apply_of_mem_W2 h 1 i hwmem,
      chiColumn_apply_of_mem_W2 h 1 0 hwmem]
    ring

end OddOrder.Peterfalvi.S06
