/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_TICyclic

/-!
# Peterfalvi §5: The isometry `σ` (Theorem (3.2)) and its construction (3.5)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 17-20.

This file continues `S05_TICyclic` (which fixes Hypothesis (3.1) and builds the
`ω`/`α` families and the `CF(W, V)` basis (3.3)-(3.4)).  Here we build the
linear isometry `σ : CF(W) → CF(G)` of **Theorem (3.2)**, whose existence is the
content of **(3.5)**: there is an orthonormal family `(χ_{ij})` of virtual
characters of `G` with `χ_{00} = 1_G` and `Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j}
+ χ_{ij}` for `i, j ≥ 1`.

The current slice is **(3.5.1)**, the inner-product foundations: the Gram matrix
of the family `(Ind_W^G α_{ij})`.  Writing `α_{ij} = 1_W - ω_{i0} - ω_{0j} +
ω_{ij}` (`alphaCF_eq_omega_combination`) and using that `Ind_W^G` is an isometry
on `CF(W, V)` (the §4 Dade isometry, carried by `FullDadeApplication`), the inner
products of the induced family are read off from the orthonormality of the
`ω_{ij}`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` (session 11+).
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

/- 3.5.1: the Gram matrix of `(Ind_W^G α_{ij})` (pp. 17-18) -/

open Classical in
/-- Orthonormality of the `ω`-family, in the `omegaProdChar`-indexed form used to compute the
Gram matrix of the `α_{ij}`: `⟨ω_{b}, ω_{a}⟩ = δ_{b,a}`, with the Kronecker delta decided by
equality of the two index pairs (`omegaProdChar` is injective). -/
theorem omega_omegaProdChar_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (b₁ a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b₂ a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner (hyp.omega (hyp.omegaProdChar b₁ b₂) : ClassFunction hyp.W ℂ)
        (hyp.omega (hyp.omegaProdChar a₁ a₂) : ClassFunction hyp.W ℂ) =
      if b₁ = a₁ ∧ b₂ = a₂ then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hyp.omega_inner_self _
  · exact hyp.omega_inner_ne (hyp.omegaProdChar_ne h)

/-- **Peterfalvi (3.4)/(3.5)**: `α_{ij} = ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}`, with every term
written as `ω` of an `omegaProdChar` index pair.  This is the form of
`alphaCF_eq_omega_combination` that makes the Gram-matrix computation uniform
(`omega_omegaProdChar_inner`). -/
theorem alphaCF_eq_omegaProdChar_combination (hyp : TICyclicHypothesis G)
    (p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.alphaCF p₁ p₂ : ClassFunction hyp.W ℂ) =
      (hyp.omega (hyp.omegaProdChar 1 1) : ClassFunction hyp.W ℂ)
        - hyp.omega (hyp.omegaProdChar p₁ 1) - hyp.omega (hyp.omegaProdChar 1 p₂)
        + hyp.omega (hyp.omegaProdChar p₁ p₂) := by
  rw [hyp.omegaProdChar_one_one, hyp.omegaProdChar_one_right, hyp.omegaProdChar_one_left]
  exact hyp.alphaCF_eq_omega_combination p₁ p₂

open Classical in
/-- **Peterfalvi (3.5.1)**: the Gram matrix of the family `(α_{ij})` (`i, j ≥ 1`).  For nontrivial
index characters,
`⟨α_{ij}, α_{kl}⟩ = 1 + δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`,
i.e. `4` on the diagonal, `2` when exactly one index agrees, and `1` when both differ.  This is the
inner-product input that, after applying the `Ind_W^G` isometry and subtracting `1_G`, gives the
norm-`3` virtual characters `β_{ij}` of (3.5.1). -/
theorem alphaCF_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    {p₁ q₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ q₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) (hq₁ : q₁ ≠ 1) (hq₂ : q₂ ≠ 1) :
    ClassFunction.inner (hyp.alphaCF p₁ p₂) (hyp.alphaCF q₁ q₂) =
      1 + (if p₁ = q₁ then 1 else 0) + (if p₂ = q₂ then 1 else 0)
        + (if p₁ = q₁ ∧ p₂ = q₂ then 1 else 0) := by
  rw [hyp.alphaCF_eq_omegaProdChar_combination p₁ p₂,
      hyp.alphaCF_eq_omegaProdChar_combination q₁ q₂]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
    hyp.omega_omegaProdChar_inner]
  -- Kill the cross-type matches (any condition forcing a nontrivial character to be `1`).
  simp only [hp₁, hp₂, hq₁.symm, hq₂.symm,
    false_and, and_false, if_false, if_true, true_and, and_true]
  ring

end TICyclicHypothesis

variable [Invertible (Nat.card G : ℂ)]

namespace TICyclicHypothesis

open Classical in
/-- **Peterfalvi (3.5.1)**, induced form: the Gram matrix of `(Ind_W^G α_{ij})` (`i, j ≥ 1`).
Since `Ind_W^G` is an isometry on `CF(W, V)` (the §4 Dade isometry, `full_inner_eq`), the inner
products of the induced family equal those of the `α_{ij}` (`alphaCF_inner`):
`⟨Ind α_{ij}, Ind α_{kl}⟩ = 1 + δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`. -/
theorem tau_alpha_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p₁ q₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ q₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) (hq₁ : q₁ ≠ 1) (hq₂ : q₂ ≠ 1) :
    ClassFunction.inner (app.tau.toDadeMap (hyp.alpha hVeq p₁ p₂))
        (app.tau.toDadeMap (hyp.alpha hVeq q₁ q₂)) =
      1 + (if p₁ = q₁ then 1 else 0) + (if p₂ = q₂ then 1 else 0)
        + (if p₁ = q₁ ∧ p₂ = q₂ then 1 else 0) := by
  rw [hyp.full_inner_eq app, hyp.alpha_coe, hyp.alpha_coe, hyp.alphaCF_inner hp₁ hp₂ hq₁ hq₂]

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
