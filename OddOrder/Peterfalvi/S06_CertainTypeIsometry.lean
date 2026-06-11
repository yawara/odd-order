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

/-- On `W₁`, the column character `ω_{ij} = chiColumn χ₂ i` is independent of the column `χ₂`:
the `W₂`-projection `wSnd` is trivial on `W₁` (`wSnd_eq_one_of_mem_W1`), so
`ω_{ij}(w) = (w1CharEquiv i)(wFst w)` for every column `χ₂`.  (Generalizes `chiColumn_one_apply`
— the `χ₂ = 1` column for all `w` — to every column, with the point restricted to `W₁`.) -/
theorem chiColumn_apply_of_mem_W1 (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {w : ↥h.sdiffTICyclicHypothesis.W}
    (hw : w ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = ((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) : ℂ) := by
  have hχ : χ₂ (h.sdiffTICyclicHypothesis.wSnd w) = 1 := by
    rw [h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hw]; exact map_one χ₂
  have h1 : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂ w
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
        * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) := rfl
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply, h1, hχ, mul_one]

/-- **Peterfalvi (4.8), step (2)** (agreement on `W₁`).  Two equal-degree certain-type characters
`μ_{ij}, μ_{ik}` (same row `i`, columns `χ₂, χ₂'`) agree on all of `W₁`, so `μ_{ij} − μ_{ik}`
vanishes there.

On `W₁^# ⊆ W − W₂` the (4.3.c) value identity gives `μ_{ij}(w) = δ_j·ω_{ij}(w)` and
`μ_{ik}(w) = δ_k·ω_{ik}(w)`; `δ_j = δ_k` (step (1), `certainType_sign_eq_of_degree_eq`) and the
column-independence of `ω` on `W₁` (`chiColumn_apply_of_mem_W1`) make these equal.  At `1` it is
the equal-degree hypothesis. -/
theorem certainType_apply_eq_of_mem_W1 (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {w : ↥L} (hw : w ∈ h.W1) :
    ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) w
      = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) w := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact hdeg
  · -- `w ∈ W₁^# ⊆ sdiff.V = W − W₂`
    have hwV : w ∈ h.sdiffTICyclicHypothesis.V := by
      have hVdef : h.sdiffTICyclicHypothesis.V
          = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ (h.W2 : Set ↥L) := rfl
      rw [hVdef]
      refine ⟨(le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hw, fun hw2 => hw1 ?_⟩
      exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hw, hw2⟩))
    -- the point `⟨w, _⟩` lies in `W₁` inside `sdiff.W`
    have hwsub : (⟨w, h.sdiffTICyclicHypothesis.V_subset_W hwV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hw
    rw [h.certainType_apply_eq_of_mem_V χ₂ i hwV, h.certainType_apply_eq_of_mem_V χ₂' i hwV,
      certainType_sign_eq_of_degree_eq h χ₂ χ₂' i hdeg,
      chiColumn_apply_of_mem_W1 h χ₂ i hwsub, chiColumn_apply_of_mem_W1 h χ₂' i hwsub]

end OddOrder.Peterfalvi.S06
