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

/-- **Galois twist of a linear character.**  For `σ : ℂ ≃+* ℂ` and a linear character
`χ : H →* ℂˣ`, the `σ`-image of the class function `linearIrreducibleCharacter χ` is again a linear
character, namely the one of the `σ`-twisted units homomorphism `(Units.map σ) ∘ χ`.  This is the
linear-character case of the Galois-twist `character_galoisTwist` (`σ ∘ χ_ρ`), specialized so it
feeds `mapRingEquiv_induce` directly. -/
theorem ClassFunction.mapRingEquiv_linearIrreducibleCharacter {H : Type*} [Group H]
    (σ : ℂ ≃+* ℂ) (χ : H →* ℂˣ) :
    mapRingEquiv σ (linearIrreducibleCharacter χ : ClassFunction H ℂ)
      = (linearIrreducibleCharacter ((Units.map (σ.toRingHom.toMonoidHom)).comp χ) :
          ClassFunction H ℂ) := by
  ext h
  rw [mapRingEquiv_apply, linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply,
    MonoidHom.comp_apply, Units.coe_map]
  rfl

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.1) input — the `Y = S(H')` family is closed under the cyclotomic Galois action.**
For any `σ : ℂ ≃+* ℂ`, the `σ`-image of an `η ∈ Y` is again in `Y`.  Indeed every `η ∈ Y` is
`Ind_H^L (linear χ)` with `χ ≠ 1` (`exists_linear_source_of_mem_Yset`); `σ` commutes with induction
(`mapRingEquiv_induce`) and twists the linear source to `(Units.map σ) ∘ χ`
(`mapRingEquiv_linearIrreducibleCharacter`), which is still a nontrivial linear character
(`σ` injective), so the image is `Ind_H^L (linear ((Units.map σ) ∘ χ)) ∈ Y`.

This is the `hSu` hypothesis of `S07.IsCoherent.extension_constant_on_sharp_of_prime`, used to
establish Peterfalvi (6.8.2.1) (`η^{τ₁}` constant on `Z^#`) for the Sibley `Y`-coherence. -/
theorem SibleyDadeHypothesis.Yset_mapRingEquiv_mem (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (σ : ℂ ≃+* ℂ) {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ClassFunction.mapRingEquiv σ φ ∈ hyp.Yset := by
  obtain ⟨χ, hχ_ne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [ClassFunction.mapRingEquiv_induce, ClassFunction.mapRingEquiv_linearIrreducibleCharacter]
  refine hyp.induce_linearIrreducibleCharacter_mem_Yset ?_
  intro hχ'
  refine hχ_ne ?_
  have hinj : Function.Injective (Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) :=
    Units.map_injective (f := (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) σ.injective
  ext h
  have key : Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ) (χ h) = 1 := by
    have h0 := DFunLike.congr_fun hχ' h
    simpa [MonoidHom.comp_apply] using h0
  have hh : χ h = 1 := hinj (key.trans (map_one _).symm)
  simpa using hh

end OddOrder.Peterfalvi.S08
