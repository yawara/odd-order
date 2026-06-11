/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeSupport

/-!
# Peterfalvi (4.8): equal-degree certain-type differences are σ-isometric

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, pp. 23-24, statement (4.8).

Under Hypothesis (4.6), fix a row index `i` (`0 ≤ i < w₁`) and two nontrivial columns
`j, k` (`0 < j, k < w₂`).  If the two certain-type characters have equal degree,
`μ_{ij}(1) = μ_{ik}(1)`, then:

* `Supp(μ_{ij} − μ_{ik}) ⊆ A₀`;
* the column signs agree, `δ_j = δ_k`;
* the Dade image is `(μ_{ij} − μ_{ik})^τ = δ_j·(ω_{ij}^σ − ω_{ik}^σ)`.

This file develops the proof in stages (Peterfalvi's eight-step argument).  The present
commit lands **step (1)**: the sign equality `δ_j = δ_k`, an independent consequence of the
degree congruence (4.3.d) and `w₁ > 2`.

## Step (1): `δ_j = δ_k`

By (4.3.d) (`certainType_degree_modEq`) there are integers `a, b` with
`μ_{ij}(1) = δ_j + a·w₁` and `μ_{ik}(1) = δ_k + b·w₁`.  The equal-degree hypothesis gives
`δ_j − δ_k = (b − a)·w₁`, so `w₁ ∣ (δ_j − δ_k)`.  As `δ_j, δ_k ∈ {±1}` we have
`|δ_j − δ_k| ≤ 2 < 3 ≤ w₁` (`three_le_card_W1`: `W₁ ≠ 1` is of odd order), forcing
`δ_j − δ_k = 0`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` ("session 30").
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi (4.8), step (1)** (the sign equality `δ_j = δ_k`).  Fix a row `i` and two
columns `χ₂, χ₂'`.  If the certain-type characters `μ_{ij}` and `μ_{ik}` have equal degree at
`1`, then the two column signs coincide.

By the degree congruence (4.3.d), `μ_{ij}(1) ≡ δ_j` and `μ_{ik}(1) ≡ δ_k` modulo `w₁`, so the
equal-degree hypothesis forces `w₁ ∣ (δ_j − δ_k)`.  Since `δ_j, δ_k ∈ {±1}` and `w₁ ≥ 3`
(`W₁ ≠ 1` of odd order), the only multiple of `w₁` in `[-2, 2]` is `0`. -/
theorem certainType_sign_eq_of_degree_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    (h.columnFamily χ₂).sign = (h.columnFamily χ₂').sign := by
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ i
  obtain ⟨b, hb⟩ := h.certainType_degree_modEq χ₂' i
  have hw3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
  -- `δ_j + w₁·a = δ_k + w₁·b` in `ℤ`, transported from the `ℂ`-valued degree identity.
  have hZ : (h.columnFamily χ₂).sign + (Nat.card h.W1 : ℤ) * a
          = (h.columnFamily χ₂').sign + (Nat.card h.W1 : ℤ) * b := by
    have hC : ((h.columnFamily χ₂).sign : ℂ) + (Nat.card h.W1 : ℂ) * (a : ℂ)
            = ((h.columnFamily χ₂').sign : ℂ) + (Nat.card h.W1 : ℂ) * (b : ℂ) := by
      rw [← ha, ← hb]; exact hdeg
    exact_mod_cast hC
  -- Case split on the two signs.  Diagonal cases are reflexive; off-diagonal cases give
  -- `w₁ ∣ 2`, contradicting `w₁ ≥ 3`.
  rcases (h.columnFamily χ₂).sign_eq with hd | hd <;>
    rcases (h.columnFamily χ₂').sign_eq with hd' | hd' <;>
    rw [hd, hd'] at hZ ⊢ <;>
    first
    | rfl
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨b - a, by linear_combination hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨a - b, by linear_combination -hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)

end OddOrder.Peterfalvi.S06
