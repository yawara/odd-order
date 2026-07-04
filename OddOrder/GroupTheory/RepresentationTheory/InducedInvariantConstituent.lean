/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.GroupTheory.RepresentationTheory.GallagherDecomposition
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit

/-!
# The general Peterfalvi (1.7.b): equal-degree induced constituents (abelian inertia quotient)

For a normal subgroup `H ⊴ K` with `K/H` **abelian** and a `K`-invariant `θ ∈ Irr H`, the
irreducible constituents of `Ind_H^K θ` all share the common degree `ψ(1) = e·θ(1)` (where `ψ` is any
one constituent and `e = ⟨Res ψ, θ⟩`).  This is Peterfalvi (1.7.b) at the inertia group
`T = I_K(θ)` (where `θ` is invariant); **no coprimality** is assumed, so it applies where the
coprime Gallagher decomposition (`induce_eq_sum_mul_linearClassFunction`) does not — in particular at
the `H'/H` level of Peterfalvi (12.5), where `K/H = H/H'` is abelian automatically (`H' = [H,H]`) but
`|H'|` and `[H:H']` share prime divisors.

The proof assembles the bottom-up chain:
* `induce_restrict_mul` — projection formula `Ind_H^K(Res_H φ · χ) = φ · Ind_H^K χ`;
* `induce_trivial_eq_sum_linearClassFunction` — `Ind_H^K 1_H = ∑_β Inf(β)`;
* `induce_restrict_eq_mul_sum_linearClassFunction` — `Ind_H^K(Res ψ) = ψ · ∑_β Inf(β)`;
* `restrict_eq_restrictionMultiplicity_smul_of_invariant` — `Res_H ψ = e · θ` (Clifford, invariant).

Here `induce_smul_eq_mul_sum_of_invariant` combines the last two into
`e · Ind_H^K θ = ψ · ∑_β Inf(β)`, exhibiting the constituents `ψ·Inf(β)` (all of degree `ψ(1)`).
-/

namespace OddOrder.RepresentationTheory

open scoped commutatorElement

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

open scoped commutatorElement in
/-- **Peterfalvi (1.7.b), the invariant-constituent decomposition.**  For `H ⊴ K` with `K/H` abelian
and a `K`-invariant `θ ∈ Irr H`, if `ψ ∈ Irr K` lies over `θ` then
`e · Ind_H^K θ = ψ · ∑_β Inf(β)`, where `e = ⟨Res ψ, θ⟩` and `β` ranges over `Hom(K/H, ℂˣ)`.

Combines `induce_restrict_eq_mul_sum_linearClassFunction` (`Ind_H^K(Res ψ) = ψ·∑_β Inf(β)`) with the
invariant Clifford restriction `restrict_eq_restrictionMultiplicity_smul_of_invariant`
(`Res_H ψ = e·θ`), pushing the scalar through `Ind` (`induce_smul`).  The right side displays the
irreducible constituents `ψ·Inf(β)` of `Ind_H^K θ`, each of degree `ψ(1)`. -/
theorem induce_smul_eq_mul_sum_of_invariant [Finite K] [Fintype K] [Fintype ↥H]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter ↥H)] [Fintype ((K ⧸ H) →* ℂˣ)]
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    (θ : IrreducibleCharacter ↥H) (ψ : IrreducibleCharacter K)
    (hover : IrreducibleCharacter.LiesOver H ψ θ) (hinv : ∀ g : K, IrreducibleCharacter.conjBy g θ = θ) :
    ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ) (θ : ClassFunction ↥H ℂ) •
        ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = (ψ : ClassFunction K ℂ) *
          ∑ β : (K ⧸ H) →* ℂˣ, linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  have h3 := induce_restrict_eq_mul_sum_linearClassFunction hab (ψ : ClassFunction K ℂ)
  have h4 := restrict_eq_restrictionMultiplicity_smul_of_invariant ψ θ hover hinv
  rw [h4, ClassFunction.induce_smul] at h3
  exact h3

open scoped commutatorElement in
/-- **The general Peterfalvi (1.7.b): equal-degree induced constituents.**  For `H ⊴ K` with `K/H`
abelian and a `K`-invariant `θ ∈ Irr H`, every irreducible constituent `φ` of `Ind_H^K θ` has the
common degree `φ(1) = ψ(1)`, where `ψ` is any fixed constituent.

By `induce_smul_eq_mul_sum_of_invariant`, `e·Ind_H^K θ = ∑_β ψ·Inf(β)` (distributing
`ClassFunction.mul_sum`), whose summands `ψ·Inf(β)` are irreducible
(`isIrreducibleCharacter_mul_linearClassFunction`).  Taking `⟨·, φ⟩` and using orthonormality of
irreducibles, `e·⟨Ind θ, φ⟩ = #{β : ψ·Inf(β) = φ}`; since `φ` is a constituent (`⟨Ind θ, φ⟩ ≠ 0`)
and `e = ⟨Res ψ, θ⟩ ≠ 0` (`ψ` over `θ`), some `β` has `φ = ψ·Inf(β)`, so
`φ(1) = ψ(1)·Inf(β)(1) = ψ(1)`.  No coprimality is used, so this applies at the `H'/H` level of
Peterfalvi (12.5) where the coprime Gallagher decomposition does not. -/
theorem induce_invariant_constituent_apply_one_eq [Finite K] [Fintype K] [Fintype ↥H]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter ↥H)] [Fintype ((K ⧸ H) →* ℂˣ)]
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    (θ : IrreducibleCharacter ↥H) (ψ : IrreducibleCharacter K)
    (hover : IrreducibleCharacter.LiesOver H ψ θ)
    (hinv : ∀ g : K, IrreducibleCharacter.conjBy g θ = θ)
    (φ : IrreducibleCharacter K)
    (hφ : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (φ : ClassFunction K ℂ) ≠ 0) :
    (φ : ClassFunction K ℂ) (1 : K) = (ψ : ClassFunction K ℂ) (1 : K) := by
  classical
  -- The irreducible twists `ψ·Inf(β)`, bundled.
  set Φ : ((K ⧸ H) →* ℂˣ) → IrreducibleCharacter K := fun β =>
    ⟨(ψ : ClassFunction K ℂ) * linearClassFunction (β.comp (QuotientGroup.mk' H)),
      isIrreducibleCharacter_mul_linearClassFunction ψ.isIrreducible _⟩ with hΦ
  -- `e · Ind_H^K θ = ∑_β (Φ β)`.
  have h5a := induce_smul_eq_mul_sum_of_invariant hab θ ψ hover hinv
  rw [ClassFunction.mul_sum] at h5a
  -- Pair with `φ`: `e · ⟨Ind θ, φ⟩ = ∑_β [Φ β = φ]`.
  have hkey : ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ)
        (θ : ClassFunction ↥H ℂ)
        * ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (φ : ClassFunction K ℂ)
      = ∑ β : (K ⧸ H) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0) := by
    rw [← ClassFunction.inner_smul_left, h5a, inner_sum_left]
    refine Finset.sum_congr rfl fun β _ => ?_
    have := irreducibleCharacter_inner (Φ β) φ
    simpa [hΦ] using this
  -- `e ≠ 0` (`ψ` lies over `θ`) and `⟨Ind θ, φ⟩ ≠ 0`, so the sum of indicators is nonzero.
  have he : ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ)
      (θ : ClassFunction ↥H ℂ) ≠ 0 := hover
  have hsum_ne : (∑ β : (K ⧸ H) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0)) ≠ 0 := by
    rw [← hkey]; exact mul_ne_zero he hφ
  obtain ⟨β, _, hβ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hΦβ : Φ β = φ := by by_contra h; rw [if_neg h] at hβ; exact hβ rfl
  -- Read off the degree: `φ(1) = (ψ·Inf β)(1) = ψ(1) · 1 = ψ(1)`.
  have hcoe : (φ : ClassFunction K ℂ)
      = (ψ : ClassFunction K ℂ) * linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
    rw [← hΦβ]
  rw [hcoe, ClassFunction.mul_apply, linearClassFunction_apply, map_one, Units.val_one, mul_one]

end OddOrder.RepresentationTheory
