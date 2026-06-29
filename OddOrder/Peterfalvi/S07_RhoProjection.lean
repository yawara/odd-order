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

/-- **Peterfalvi (7.1), `L`-conjugation invariance of the average.**  The value `χ^ρ(a)` is
invariant under conjugating the support point `a` by `ℓ ∈ L`: `χ^ρ(ℓ·a·ℓ⁻¹) = χ^ρ(a)`.  This is the
class-function (equivariance) property of `ρ` — the input needed to package `χ^ρ` as an element of
`CF(L, A)` — and rests on `(2.4.a)` (`HConjInvariant`, i.e. `H(ℓ·a·ℓ⁻¹) = ℓ·H(a)·ℓ⁻¹`) together with
`χ` being a class function on `G`.  Concretely, conjugation by `ℓ` is a bijection
`H(ℓ·a·ℓ⁻¹) ≃ H(a)`, `y ↦ ℓ⁻¹·y·ℓ`, under which the coset element `(ℓ·a·ℓ⁻¹)·y` is `G`-conjugate to
`a·(ℓ⁻¹·y·ℓ)`, so the two averages agree term by term. -/
theorem rhoValue_conjA (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ)
    (l : L) (a : {a : G // a ∈ A}) :
    rhoValue hyp χ (hyp.conjA l a) = rhoValue hyp χ a := by
  letI iA : Fintype (hyp.H a) := Fintype.ofFinite _
  letI iB : Fintype (hyp.H (hyp.conjA l a)) := Fintype.ofFinite _
  -- conjugation by `ℓ⁻¹` is the bijection `H(ℓ·a·ℓ⁻¹) ≃ H(a)`
  let e : (hyp.H (hyp.conjA l a)) ≃ (hyp.H a) :=
    { toFun := fun y => ⟨(l : G)⁻¹ * (y : G) * (l : G),
        (hyp.mem_H_conjA_iff hconj a l).mp y.2⟩
      invFun := fun x => ⟨(l : G) * (x : G) * (l : G)⁻¹,
        (hyp.mem_H_conjA_iff hconj a l).mpr (by
          have hx : (l : G)⁻¹ * ((l : G) * (x : G) * (l : G)⁻¹) * (l : G) = (x : G) := by group
          rw [hx]; exact x.2)⟩
      left_inv := fun y => by
        apply Subtype.ext
        change (l : G) * ((l : G)⁻¹ * (y : G) * (l : G)) * (l : G)⁻¹ = (y : G); group
      right_inv := fun x => by
        apply Subtype.ext
        change (l : G)⁻¹ * ((l : G) * (x : G) * (l : G)⁻¹) * (l : G) = (x : G); group }
  -- rewrite both `rhoValue`s into their averaging form under the chosen `Fintype` instances
  have hB : rhoValue hyp χ (hyp.conjA l a)
      = (Nat.card (hyp.H (hyp.conjA l a)) : ℂ)⁻¹
          * ∑ y : (hyp.H (hyp.conjA l a)), χ ((hyp.conjA l a).1 * (y : G)) := rfl
  have hA : rhoValue hyp χ a
      = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : (hyp.H a), χ (a.1 * (x : G)) := rfl
  rw [hA, hB, Nat.card_congr e]
  congr 1
  refine Fintype.sum_equiv e _ _ (fun y => ?_)
  change χ ((hyp.conjA l a).1 * (y : G)) = χ (a.1 * ((l : G)⁻¹ * (y : G) * (l : G)))
  rw [hyp.conjA_coe]
  exact χ.of_isConj (isConj_iff.mpr ⟨(l : G)⁻¹, by group⟩)

end OddOrder.Peterfalvi.S07
