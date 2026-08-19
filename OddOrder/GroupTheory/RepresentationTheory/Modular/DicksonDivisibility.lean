/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.ProjectiveCharacterVanishing
import OddOrder.GroupTheory.RepresentationTheory.SubgroupAverageTrace

/-!
# Dickson's theorem: `|G|_p` divides `Φ_φ(1)`

The projective indecomposable character `Φ_φ` vanishes off the `p`-regular elements
(`projectiveIndecomposableCharacter_eq_zero`), so on a Sylow `p`-subgroup `P` it is supported at
`1`:

`Φ_φ(1) = ∑_{u ∈ P} Φ_φ(u)`.

Expanding `Φ_φ = ∑_i d_{iφ} χ_i` and averaging each ordinary character over `P`
(`exists_sum_character_subgroup`) turns the right-hand side into `|P|` times an integer.

This is the arithmetic input of Navarro (3.8) (Osima): it is what makes the coefficient
`|G|⁻¹ ∑_{φ ∈ S} Φ_φ(1) φ(x⁻¹)` of the idempotent `f_A` an algebraic integer, and hence what makes
`Irr(B)` a *single* connected component of the Brauer graph (Navarro (3.9)).

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_card_sylow_mul_projectiveIndecomposableCharacter`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (3.8).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)] [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

include hp hω hω' hπ hlin hkerJ e in
/-- **`Φ_φ` is supported at `1` on a Sylow `p`-subgroup.** -/
theorem sum_projectiveIndecomposableCharacter_sylow [Fact p.Prime] (P : Sylow p G)
    [Fintype ↥(P : Subgroup G)] (φ : ι) :
    (∑ u : ↥(P : Subgroup G),
        projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ ((u : G)))
      = projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ 1 := by
  classical
  refine Finset.sum_eq_single (1 : ↥(P : Subgroup G)) (fun u _ hu => ?_) (fun h => ?_)
  · refine projectiveIndecomposableCharacter_eq_zero hp hω hω' hπ hlin hkerJ e φ fun hreg => ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') u
    have hu1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hk0 : k ≠ 0 := fun h => hu1 (orderOf_eq_one_iff.mp (by
      rw [Subgroup.orderOf_coe, hk, h, pow_zero]))
    exact hreg (by rw [Subgroup.orderOf_coe, hk]; exact dvd_pow_self p hk0)
  · exact absurd (Finset.mem_univ (1 : ↥(P : Subgroup G))) h

include hp hω hω' hπ hlin hkerJ e in
/-- **Dickson's theorem**: `|G|_p` divides `Φ_φ(1)`.

`Φ_φ` vanishes off the `p`-regular elements, so summing it over a Sylow `p`-subgroup `P` picks out
`Φ_φ(1)`; and each ordinary character averages over `P` to `|P|` times a natural number
(`exists_sum_character_subgroup`). -/
theorem exists_card_sylow_mul_projectiveIndecomposableCharacter [Fact p.Prime] (P : Sylow p G)
    (φ : ι) :
    ∃ n : ℕ, projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ 1
      = (Nat.card ↥(P : Subgroup G) : 𝒪) * (n : 𝒪) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  choose n hn using fun i : ι' =>
    exists_sum_character_subgroup (wedderburnRepresentation e i) (P : Subgroup G)
  refine ⟨∑ i : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ * n i, ?_⟩
  refine IsFractionRing.injective 𝒪 K ?_
  rw [← sum_projectiveIndecomposableCharacter_sylow hp hω hω' hπ hlin hkerJ e P φ, map_sum]
  have hstep : ∀ u : ↥(P : Subgroup G),
      algebraMap 𝒪 K (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ ((u : G)))
        = ∑ i : ι', (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : K)
            * (wedderburnRepresentation e i).character ((u : G)) := by
    intro u
    rw [projectiveIndecomposableCharacter, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, map_natCast, algebraMap_ordinaryCharacter, Representation.character]
  rw [Finset.sum_congr rfl fun u _ => hstep u, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => by
    rw [← Finset.mul_sum, hn i, Fintype.card_eq_nat_card]]
  rw [map_mul, map_natCast, map_natCast, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.cast_mul]
    ring

end OddOrder.RepresentationTheory.Modular
