/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCore

/-!
# Peterfalvi §8: Case (B) coherence (`X ∪ Y` is coherent in case (B))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2)** branch of the (6.8) coherence capstone
(`OddOrder.Peterfalvi.S08.sibleySetup_is_coherent`).

This is the case-`(B)` (`Z = W₂`, `W₂` prime central) analogue of the case-`(A)`/Frobenius
central-commutator program in `S08_CoherenceCore`.  The textbook proof (mmd 04.8 L178-224) runs:

* **(6.8.2.1)** `η^{τ₁}` is constant on `Z^#` — already available in full generality as
  `OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime` (it needs `Z` of prime
  order, which is exactly the case-`(B)` hypothesis `w₂` prime, and `hyp.tau` is the genuine
  `dadeIntegralCharacterMap`, so the general lemma applies to `hyp.coherentYset`).
* **(6.8.2.2)** the `(6.7)`-congruence inner-product formula (`peterfalvi_67_centralCommutator`
  + the regular-character decomposition).
* **(6.8.2.3)** the `X`-side `(χ − a η₁)^τ` decomposition ([Is] Lemma 2.27).
* the final `τ₂` assembly.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 39 cont.²").
-/

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G]

/-- **Galois action commutes with induction.**  For a ring automorphism `σ` of `ℂ` (the cyclotomic
Galois action of Peterfalvi (1.9)) and `θ : ClassFunction ↥H ℂ`,
`σ(Ind_H^G θ) = Ind_H^G (σθ)`.  Indeed `Ind_H^G θ (g) = |H|⁻¹ ∑_x induceTerm θ x g` and `σ` is a
ring homomorphism that fixes the rational coefficient `|H|⁻¹` (`map_natCast`/`map_inv₀`) and acts
termwise on the `θ`-values (`induceTerm` is `θ ⟨x⁻¹gx,·⟩` or `0`, both `σ`-equivariant).

This is the engine behind the Galois-closure of the `Y = S(H')` family (each `Ind_H^L (linear χ)`
maps to `Ind_H^L (linear (σ∘χ))`), one of the hypotheses of
`IsCoherent.extension_constant_on_sharp_of_prime` (Peterfalvi (6.8.2.1)).  Stated in the general
`ClassFunction` namespace (it is not §8-specific) and upstreamable to `InducedCharacter`. -/
theorem ClassFunction.mapRingEquiv_induce {H : Subgroup G} [Fintype G]
    [Invertible (Nat.card H : ℂ)] (σ : ℂ ≃+* ℂ) (θ : ClassFunction ↥H ℂ) :
    mapRingEquiv σ (induce H θ) = induce H (mapRingEquiv σ θ) := by
  ext g
  rw [mapRingEquiv_apply, induce_apply, induce_apply, map_mul, map_sum]
  have hcoef : σ (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    simp [invOf_eq_inv, map_inv₀, map_natCast]
  rw [hcoef]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem _ hx, induceTerm_of_mem _ hx, mapRingEquiv_apply]
  · rw [induceTerm_of_not_mem _ hx, induceTerm_of_not_mem _ hx, map_zero]

end OddOrder.RepresentationTheory
