/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Peterfalvi §7: the `ρ` projection (Hypothesis (7.1))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §7, pp. 38–43.

Under Hypothesis (2.2) (`S04.Hypothesis G A L`, with its family of subgroups `H(a)` for `a ∈ A`),
**(7.1)** attaches to each `χ ∈ CF(G)` the function `χ^ρ` on `A` defined by averaging `χ` over the
coset `aH(a)`:
$$ \chi^\rho(a) = \frac{1}{|H(a)|}\sum_{x \in H(a)} \chi(ax). $$
This `ρ` is the adjoint of the Dade isometry `τ`: (7.2.a) `α^{τρ} = α` for `α ∈ CF(L,A)`, and
(7.2.b)/(7.3) give the norm bounds `‖χ^ρ‖² ≤ ‖χ‖²` and
`(1/|G|)∑_{g∈A^τ}|χ(g)|² ≥ ‖χ^ρ‖²` feeding the final inequality of (12.16).

This file builds the foundational **value** `rhoValue` of (7.1) and its `ℂ`-linearity in `χ`; the
class-function packaging (`L`-conjugation equivariance of the average) and the (7.2)/(7.3) norm
theory follow.
-/

namespace OddOrder.Peterfalvi.S07

open scoped BigOperators
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}

/-- **Peterfalvi (7.1)**, the value of the `ρ` projection at a support point `a ∈ A`:
`χ^ρ(a) = (1/|H(a)|) ∑_{x ∈ H(a)} χ(a·x)`, the average of `χ` over the coset `aH(a)`. -/
noncomputable def rhoValue (hyp : S04.Hypothesis G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) : ℂ :=
  letI : Fintype (hyp.H a) := Fintype.ofFinite _
  (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : (hyp.H a), χ (a.1 * (x : G))

variable (hyp : S04.Hypothesis G A L)

@[simp] theorem rhoValue_zero (a : {a : G // a ∈ A}) : rhoValue hyp 0 a = 0 := by
  simp [rhoValue]

theorem rhoValue_add (χ ψ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (χ + ψ) a = rhoValue hyp χ a + rhoValue hyp ψ a := by
  simp only [rhoValue, ClassFunction.add_apply, Finset.sum_add_distrib, mul_add]

theorem rhoValue_smul (c : ℂ) (χ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (c • χ) a = c * rhoValue hyp χ a := by
  simp only [rhoValue, ClassFunction.smul_apply, Finset.mul_sum]
  ring

theorem rhoValue_sub (χ ψ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (χ - ψ) a = rhoValue hyp χ a - rhoValue hyp ψ a := by
  simp only [rhoValue, ClassFunction.sub_apply, Finset.sum_sub_distrib, mul_sub]

end OddOrder.Peterfalvi.S07
