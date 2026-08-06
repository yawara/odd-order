/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.DicksonDivisibility
import OddOrder.GroupTheory.RepresentationTheory.Modular.OsimaBlockSupport

/-!
# Osima (3.8), the `p`-regular half: `|G|_p` divides `∑_{i ∈ A} χ_i(1) χ_i(x)`

For `A` a union of connected components of the Brauer graph, Navarro's (3.8) says that the
idempotent `f_A = ∑_{χ ∈ A} e_χ` has coefficients in `𝒪`.  Its coefficient at `x` is
`|G|⁻¹ ∑_{i ∈ A} χ_i(1) χ_i(x⁻¹)`, and the `p`-singular case is
`sum_ordinaryCharacter_one_mul_eq_zero_of_linkedClosed`.

This file is the `p`-regular case.  Expanding `χ_i(x)` by its row of the decomposition matrix and
exchanging the sums turns the pairing into `∑_φ φ(x) (∑_{i ∈ A} d_{iφ} χ_i(1))`; the inner sum is
`Φ_φ(1)` or `0` by the dichotomy of `OsimaBlockSupport`, and `|G|_p` divides `Φ_φ(1)` by Dickson's
theorem.  Since `|G|_{p'}` is invertible in `𝒪`, the coefficient is integral.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_card_sylow_mul_sum_ordinaryCharacter_one_mul`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (3.8).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
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

set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hω hω' hkerJ e in
/-- **Osima (3.8), the `p`-regular half**: for `A` closed under linking and `x` `p`-regular,
`|G|_p` divides `∑_{i ∈ A} χ_i(1) χ_i(x)`.

Expand `χ_i(x)` by its row of `D` (legitimate because `x` is `p`-regular) and exchange the sums:
the coefficient of `φ(x)` is `∑_{i ∈ A} d_{iφ} χ_i(1)`, which is `Φ_φ(1)` when `A` meets the
support of the column and `0` otherwise; Dickson's theorem divides `Φ_φ(1)` by `|P|`. -/
theorem exists_card_sylow_mul_sum_ordinaryCharacter_one_mul [Fact p.Prime] (P : Sylow p G)
    {Q : ι' → Prop}
    (hQ : ∀ (i j : ι') (ψ : ι), Q i →
      decompositionMatrix hp hω hω' hπ hlin hkerJ e i ψ ≠ 0 →
      decompositionMatrix hp hω hω' hπ hlin hkerJ e j ψ ≠ 0 → Q j)
    {x : G} (hx : IsPRegular p x) :
    ∃ z : 𝒪, (∑ i ∈ Finset.univ.filter Q,
        ordinaryCharacter (𝒪 := 𝒪) e i 1 * ordinaryCharacter (𝒪 := 𝒪) e i x)
      = (Nat.card ↥(P : Subgroup G) : 𝒪) * z := by
  classical
  choose n hn using fun φ : ι =>
    exists_card_sylow_mul_projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e P φ
  -- the inner sum is `Φ_φ(1)` or `0`
  have hinner : ∀ φ : ι, (∑ i ∈ Finset.univ.filter Q,
        (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
          * ordinaryCharacter (𝒪 := 𝒪) e i 1)
      = (Nat.card ↥(P : Subgroup G) : 𝒪)
        * (if ∃ i, Q i ∧ decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ ≠ 0 then
            ((n φ : ℕ) : 𝒪) else 0) := by
    intro φ
    by_cases hex : ∃ i, Q i ∧ decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ ≠ 0
    · rw [if_pos hex, sum_decompositionMatrix_mul_ordinaryCharacter_of_linkedClosed hp hω hω' hπ
        hlin hkerJ e hQ hex 1, hn φ]
    · rw [if_neg hex, mul_zero,
        sum_decompositionMatrix_mul_ordinaryCharacter_eq_zero_of_not_exists hp hω hω' hπ hlin
          hkerJ e hex 1]
  have hrow : ∀ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i x
      = ∑ φ : ι, (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x :=
    fun i => trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i x hx
  refine ⟨∑ φ : ι, irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x
      * (if ∃ i, Q i ∧ decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ ≠ 0 then
          ((n φ : ℕ) : 𝒪) else 0), ?_⟩
  calc (∑ i ∈ Finset.univ.filter Q,
        ordinaryCharacter (𝒪 := 𝒪) e i 1 * ordinaryCharacter (𝒪 := 𝒪) e i x)
      = ∑ i ∈ Finset.univ.filter Q, ∑ φ : ι,
          irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x
            * ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
              * ordinaryCharacter (𝒪 := 𝒪) e i 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hrow i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun φ _ => by ring
    _ = ∑ φ : ι, irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x
          * ∑ i ∈ Finset.univ.filter Q,
            ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
              * ordinaryCharacter (𝒪 := 𝒪) e i 1) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun φ _ => (Finset.mul_sum _ _ _).symm
    _ = (Nat.card ↥(P : Subgroup G) : 𝒪) * ∑ φ : ι,
          irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ x
            * (if ∃ i, Q i ∧ decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ ≠ 0 then
                ((n φ : ℕ) : 𝒪) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun φ _ => by rw [hinner φ]; ring

end OddOrder.RepresentationTheory.Modular
