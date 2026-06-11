/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S05_GridTrichotomy

/-!
# Peterfalvi (3.8): the trichotomy for the `σ`-coefficient grid

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §3, pp. 15-20.

This file specialises the abstract grid trichotomy `grid_trichotomy` (`S05_GridTrichotomy`) to the
concrete `σ`-image coefficient grid `a_{ij} = ⟨ψ, ω_{ij}^σ⟩ =` `sigmaCoeff` (`S05_SigmaIsometry`),
giving the full **Peterfalvi Theorem (3.8)** for a class function `ψ` vanishing on `V`.

The companion `sigmaCoeff_eq_zero_of_sigmaNC_lt` (`S05_SigmaIsometry`) is the `NC(ψ) < min(w₁,w₂)`
corollary (the part used by (3.9.a)); this file supplies the full `NC(ψ) < 2w₁` trichotomy needed by
the §6 certain-type analysis (Peterfalvi (4.8)).
-/

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.Peterfalvi.S05
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **Peterfalvi Theorem (3.8)** (full trichotomy for the `σ`-coefficient grid).  Let `ψ` vanish on
`V`, with `w₁ + 2 ≤ w₂` (the odd-order gap from `w₁ < w₂`) and `NC(ψ) < 2w₁`.  Then one of:

* (a) every `σ`-image coefficient `⟨ψ, ω_{ij}^σ⟩` vanishes (`ψ = β`, orthogonal to `Im σ`);
* (b) a single `W₂`-column `j₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_i ω_{i,j₀}^σ + β`);
* (c) a single `W₁`-row `i₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_j ω_{i₀,j}^σ + β`).

Immediate from `grid_trichotomy` applied to `sigmaCoeff`, whose additive separability is
`sigmaCoeff_add_eq` (3.7) and whose support count is `sigmaNC` (3.6) by definition; the index sets
`Ŵ₁, Ŵ₂` have `|Ŵ_k| = w_k` (`card_charGroup_subgroupOf`). -/
theorem sigmaCoeff_trichotomy (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hgap : Nat.card hyp.W1 + 2 ≤ Nat.card hyp.W2)
    (hNC : hyp.sigmaNC hVeq app ψ < 2 * Nat.card hyp.W1) :
    (∀ pq, hyp.sigmaCoeff hVeq app ψ pq = 0) ∨
      (∃ (j₀ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ p, hyp.sigmaCoeff hVeq app ψ (p, j₀) = c) ∧
        ∀ p q, q ≠ j₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) ∨
      (∃ (i₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ q, hyp.sigmaCoeff hVeq app ψ (i₀, q) = c) ∧
        ∀ p q, p ≠ i₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  haveI : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  refine grid_trichotomy (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ ?_
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    exact hgap
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    exact hNC

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
