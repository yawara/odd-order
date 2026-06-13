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

/-- **(4.10), piece (b): the `W`-side four-corner is supported on `V = W − W₂`.**
The four-corner `ω_{ij} − ω_{0j} − (ω_{i0} − ω_{00})` is the difference of the two column
differences `ω_{·j} − ω_{0j}` (column `χ₂`) and `ω_{·0} − ω_{00}` (column `1`), each of which is
the `SupportedOnV` element `omegaColumnDiff` of (4.3.b): it vanishes on `W₂`, where the
`W₁`-character factor `(w1CharEquiv i)(wFst w)` is killed, so the row difference dies.  The
support submodule `CF(W, W − W₂)` is closed under subtraction (`Submodule.sub_mem`), so the
four-corner lies in it too — no pointwise computation, sidestepping the `chiColumn`/`alphaCF`
coercion mismatch of the direct route. -/
theorem chiColumn_fourcorner_mem_supportedSubmodule (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)))
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
            h.sdiffTICyclicHypothesis.W) := by
  -- the four-corner is `↑(ω_{·j} − ω_{0j}) − ↑(ω_{·0} − ω_{00})`, a difference of two
  -- `omegaColumnDiff` carriers; `chiColumn = omega ∘ omegaProdChar` makes the match definitional.
  have key : (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))
      = (↑(h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂) :
            ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (↑(h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) 1) :
            ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    rw [h.omegaColumnDiff_coe, h.omegaColumnDiff_coe]
    rfl
  rw [key]
  exact Submodule.sub_mem _
    (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂).2
    (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) 1).2

end OddOrder.Peterfalvi.S06
