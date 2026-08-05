/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.VirtualCharacterPairing

/-!
# Induction of class functions: Frobenius reciprocity and the projection formula

For `H ≤ G` and `ψ : H → K` the induced function is

`(Ind_H^G ψ)(g) = (1/|H|) ∑_{x ∈ G} ψ̇(x g x⁻¹)`,

where `ψ̇` is `ψ` extended by `0` off `H`.  Two identities are proved, both pure computations with
no representation theory:

* **the projection formula** (Gorenstein Lemma 7.2) `Ind_H^G (ψ · Res_H θ) = (Ind_H^G ψ) · θ`;
* **Frobenius reciprocity** `(Ind_H^G ψ, θ)_G = (ψ, Res_H θ)_H`.

Together with `charPairing_mem_intRange` these are what replace the construction of the induced
module `K[G] ⊗_{K[H]} V`: to see that `Ind_H^G` maps virtual characters to virtual characters one
never computes a trace, one only checks that all the pairings against `Irr(G)` are integers, and
Frobenius reciprocity turns those into pairings on `H`.

The unbundled `G → K` form is used throughout, matching the modular development of
`OddOrder.RepresentationTheory.Modular` (which works with bare functions plus `IsConj`
hypotheses).  It is the same operator as the bundled `ClassFunction.induce` of
`RepresentationTheory.InducedCharacter` — that one sums `θ(x⁻¹ g x)`, which is this sum reindexed
by `x ↦ x⁻¹` — but the two are kept apart on purpose: `ClassFunction.induce` drags in the whole
Peterfalvi `ClassFunction`/`ZIrrFourier` import closure, which this development has no use for.

## Main definitions

* `OddOrder.RepresentationTheory.extendByZero` — `ψ̇`
* `OddOrder.RepresentationTheory.induceFun` — `Ind_H^G ψ`

## Main results

* `OddOrder.RepresentationTheory.induceFun_mul_restrict` — the projection formula
* `OddOrder.RepresentationTheory.charPairing_induceFun` — Frobenius reciprocity

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.2 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

variable {K G : Type*} [Field K] [Group G] {H : Subgroup G}

open scoped Classical in
/-- **Extension by zero** of a function on a subgroup. -/
noncomputable def extendByZero (H : Subgroup G) (ψ : ↥H → K) : G → K := fun g =>
  if hg : g ∈ H then ψ ⟨g, hg⟩ else 0

theorem extendByZero_of_mem (ψ : ↥H → K) {g : G} (hg : g ∈ H) :
    extendByZero H ψ g = ψ ⟨g, hg⟩ := dif_pos hg

theorem extendByZero_of_not_mem (ψ : ↥H → K) {g : G} (hg : g ∉ H) :
    extendByZero H ψ g = 0 := dif_neg hg

variable [Fintype G]

/-- Summing an extension by zero over `G` is summing the original function over `H`. -/
theorem sum_extendByZero [Fintype ↥H] (ψ : ↥H → K) :
    ∑ g : G, extendByZero H ψ g = ∑ u : ↥H, ψ u := by
  classical
  have hsub : ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ H), extendByZero H ψ g
      = ∑ g : G, extendByZero H ψ g := by
    refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
    exact extendByZero_of_not_mem ψ (by simpa using hx)
  rw [← hsub, Finset.sum_subtype (p := fun x : G => x ∈ H) _ (fun x => by simp)
    (extendByZero H ψ)]
  exact Finset.sum_congr rfl fun u _ => extendByZero_of_mem ψ u.2

/-- **The induced class function** `(Ind_H^G ψ)(g) = (1/|H|) ∑_{x ∈ G} ψ̇(x g x⁻¹)`. -/
noncomputable def induceFun (H : Subgroup G) (ψ : ↥H → K) : G → K := fun g =>
  (Nat.card ↥H : K)⁻¹ * ∑ x : G, extendByZero H ψ (x * g * x⁻¹)

/-- The induced function is a class function. -/
theorem induceFun_conj (ψ : ↥H → K) (g h : G) :
    induceFun H ψ (h * g * h⁻¹) = induceFun H ψ g := by
  have hre : (∑ x : G, extendByZero H ψ (x * (h * g * h⁻¹) * x⁻¹))
      = ∑ x : G, extendByZero H ψ (x * g * x⁻¹) :=
    Fintype.sum_equiv (Equiv.mulRight h) _ _ fun x =>
      congrArg _ (by simp only [Equiv.coe_mulRight]; group)
  simp only [induceFun, hre]

/-! ### The projection formula -/

/-- **Gorenstein Lemma 7.2, the projection formula**: `Ind_H^G (ψ · Res_H θ) = (Ind_H^G ψ) · θ`
for any class function `θ` on `G`.  The whole content is that `θ` is constant on the conjugacy
class of `g`, so it can be pulled out of the induction sum. -/
theorem induceFun_mul_restrict (ψ : ↥H → K) {θ : G → K}
    (hθ : ∀ g h : G, θ (h * g * h⁻¹) = θ g) :
    induceFun H (ψ * (θ ∘ H.subtype)) = induceFun H ψ * θ := by
  funext g
  have hext : ∀ y : G, extendByZero H (ψ * (θ ∘ H.subtype)) y = extendByZero H ψ y * θ y := by
    intro y
    by_cases hy : y ∈ H
    · rw [extendByZero_of_mem _ hy, extendByZero_of_mem _ hy]
      rfl
    · rw [extendByZero_of_not_mem _ hy, extendByZero_of_not_mem _ hy, zero_mul]
  simp only [induceFun, Pi.mul_apply, hext, hθ g]
  rw [← Finset.sum_mul, mul_assoc]

/-! ### Frobenius reciprocity -/

/-- **Frobenius reciprocity** `(Ind_H^G ψ, θ)_G = (ψ, Res_H θ)_H`, for `θ` a class function on
`G`.  Reindexing the double sum by `g ↦ x⁻¹ g⁻¹ x` makes the inner sum independent of `x`, and the
`|G|` copies cancel the `1/|G|`. -/
theorem charPairing_induceFun [Invertible (Nat.card G : K)] [Fintype ↥H] (ψ : ↥H → K)
    {θ : G → K}
    (hθ : ∀ g h : G, θ (h * g * h⁻¹) = θ g) :
    charPairing K (induceFun H ψ) θ = charPairing K ψ (θ ∘ H.subtype) := by
  classical
  have hGne : (Nat.card G : K) ≠ 0 := (isUnit_of_invertible (Nat.card G : K)).ne_zero
  set S : K := ∑ h : G, extendByZero H ψ h * θ h⁻¹ with hS
  -- the inner sum does not depend on `x`
  have hinner : ∀ x : G, (∑ g : G, extendByZero H ψ (x * g⁻¹ * x⁻¹) * θ g) = S := by
    intro x
    refine (Equiv.sum_comp (((Equiv.inv G).trans (Equiv.mulLeft x⁻¹)).trans (Equiv.mulRight x))
      (fun g : G => extendByZero H ψ (x * g⁻¹ * x⁻¹) * θ g)).symm.trans ?_
    refine Finset.sum_congr rfl fun h _ => ?_
    have hconj : x * (x⁻¹ * h⁻¹ * x)⁻¹ * x⁻¹ = h := by group
    have hval : θ (x⁻¹ * h⁻¹ * x) = θ h⁻¹ := by
      have := hθ h⁻¹ x⁻¹
      rwa [inv_inv] at this
    change extendByZero H ψ (x * (x⁻¹ * h⁻¹ * x)⁻¹ * x⁻¹) * θ (x⁻¹ * h⁻¹ * x) = _
    rw [hconj, hval]
  -- the outer sum is `|G|` copies of it
  have hsum : (∑ g : G, induceFun H ψ g⁻¹ * θ g)
      = (Nat.card G : K) * ((Nat.card ↥H : K)⁻¹ * S) := by
    calc (∑ g : G, induceFun H ψ g⁻¹ * θ g)
        = ∑ g : G, (Nat.card ↥H : K)⁻¹ * ∑ x : G, extendByZero H ψ (x * g⁻¹ * x⁻¹) * θ g := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [induceFun, mul_assoc, Finset.sum_mul]
      _ = ∑ x : G, (Nat.card ↥H : K)⁻¹ * ∑ g : G, extendByZero H ψ (x * g⁻¹ * x⁻¹) * θ g := by
          simp only [← Finset.mul_sum]
          exact congrArg _ (Finset.sum_comm)
      _ = (Nat.card G : K) * ((Nat.card ↥H : K)⁻¹ * S) := by
          rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => by rw [hinner x],
            Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  -- the `H`-side sum
  have hH : S = ∑ u : ↥H, ψ u⁻¹ * (θ ∘ H.subtype) u := by
    calc S = ∑ h : G, extendByZero H (fun u : ↥H => ψ u * θ ((u : G))⁻¹) h := by
          refine Finset.sum_congr rfl fun h _ => ?_
          by_cases hh : h ∈ H
          · rw [extendByZero_of_mem _ hh, extendByZero_of_mem _ hh]
          · rw [extendByZero_of_not_mem _ hh, extendByZero_of_not_mem _ hh, zero_mul]
      _ = ∑ u : ↥H, ψ u * θ ((u : G))⁻¹ := sum_extendByZero _
      _ = ∑ u : ↥H, ψ u⁻¹ * (θ ∘ H.subtype) u := by
          refine (Equiv.sum_comp (Equiv.inv ↥H)
            (fun u : ↥H => ψ u * θ ((u : G))⁻¹)).symm.trans ?_
          exact Finset.sum_congr rfl fun u _ => by simp
  rw [charPairing, hsum, ← mul_assoc, inv_mul_cancel₀ hGne, one_mul, charPairing, hH]

end OddOrder.RepresentationTheory
