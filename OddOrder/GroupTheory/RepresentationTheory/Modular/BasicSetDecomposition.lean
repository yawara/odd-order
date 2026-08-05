/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionInverse

/-!
# Generalized decomposition numbers with respect to a basic set — Navarro (7.5)

A **basic set** `𝓑` for a block `b` of `H` is a basis of the lattice spanned by
`{ψ⁰ : ψ ∈ Irr(b)}`; `IBr(b)` is one, and any other is obtained from it by an integer matrix
`U = (u_{μφ})` with integer inverse.  Navarro's equation (1) on p. 135 then *defines* the
generalized decomposition numbers relative to `𝓑` by

`d^x_{χφ} = ∑_{μ ∈ IBr(b)} d^x_{χμ} u_{μφ}`.

Once that is taken as the definition, Lemma (7.5) is pure bilinearity on top of the `IBr`-versions
already available:

* (a) `d^x_{χφ} = 0` as soon as every `μ` with `u_{μφ} ≠ 0` has `d^x_{χμ} = 0` — i.e. the second
  main theorem plus the block-diagonality of `U`;
* (b)/(c) the pairing of two columns is the `U`-congruent of the pairing of the `IBr`-columns,
  `∑_χ d^{x⁻¹}_{χφ} d^x_{χη} = (UᵗCU)_{φη}` (and `0` for two non-conjugate `p`-elements).

This file supplies the definition and those two computations; the choice of `U` (i.e. of the basic
set) is left to the caller, which is what Navarro (7.4) provides for the principal block of a
group with a Klein four Sylow `2`-subgroup.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.basicDecompositionNumber` — Navarro's equation (1)

## Main results

* `OddOrder.RepresentationTheory.Modular.basicDecompositionNumber_eq_zero` — (7.5)(a)
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber` — the `U`-congruence
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber_eq_cartanMatrix` —
  (7.5)(c)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

/-! ### The definition and the two bilinear computations -/

section Generic

variable {K ι ι₂ J : Type*} [CommRing K] [Fintype ι] [Fintype J]

/-- **Navarro's equation (1), p. 135**: the generalized decomposition numbers relative to a basic
set, `d^x_{χφ} = ∑_μ d^x_{χμ} u_{μφ}`. -/
def basicDecompositionNumber (d : ι → K) (u : ι → ι₂ → ℤ) (φ : ι₂) : K :=
  ∑ μ : ι, d μ * (u μ φ : K)

/-- **Navarro (7.5)(a)**: the basic-set number vanishes as soon as every `IBr`-number it uses
does.  For a basic set of a block `b` the matrix `U` is supported on `IBr(b)`, and the second main
theorem kills `d^x_{χμ}` for `μ ∈ IBr(b)` when `b` does not induce the block of `χ`. -/
theorem basicDecompositionNumber_eq_zero {d : ι → K} {u : ι → ι₂ → ℤ} {φ : ι₂}
    (h : ∀ μ : ι, u μ φ ≠ 0 → d μ = 0) : basicDecompositionNumber d u φ = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases hμ : u μ φ = 0
  · rw [hμ, Int.cast_zero, mul_zero]
  · rw [h μ hμ, zero_mul]

/-- **The pairing of two basic-set columns is the `U`-congruent of the `IBr`-pairing.**  This is
what turns Navarro (5.13) into (7.5)(b),(c): whatever the matrix `c` of pairings of the
`IBr`-columns is, the basic-set pairing is `UᵗcU`. -/
theorem sum_mul_basicDecompositionNumber {dinv d : J → ι → K} {u : ι → ι₂ → ℤ} (φ η : ι₂)
    (c : ι → ι → K) (hc : ∀ μ τ : ι, (∑ j : J, dinv j μ * d j τ) = c μ τ) :
    (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u η)
      = ∑ μ : ι, ∑ τ : ι, (u μ φ : K) * c μ τ * (u τ η : K) := by
  classical
  calc (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u η)
      = ∑ j : J, ∑ μ : ι, ∑ τ : ι,
          (dinv j μ * (u μ φ : K)) * (d j τ * (u τ η : K)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [basicDecompositionNumber, basicDecompositionNumber, Finset.sum_mul]
        exact Finset.sum_congr rfl fun μ _ => Finset.mul_sum _ _ _
    _ = ∑ μ : ι, ∑ τ : ι, (u μ φ : K) * (∑ j : J, dinv j μ * d j τ) * (u τ η : K) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ μ : ι, ∑ τ : ι, (u μ φ : K) * c μ τ * (u τ η : K) :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun τ _ => by rw [hc μ τ]

end Generic

/-! ### Navarro (7.5)(c) -/

section Cartan

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
variable [Invertible (Nat.card G : K)]
variable (hpC : p.Prime) {ω : 𝒪}
  (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (7.5)(c)**: for a basic set given by the integer matrix `U`, the pairing of two
columns of the basic-set generalized decomposition matrix is `UᵗCU`, where `C` is the Cartan
matrix of `C_G(x)` in the `IBr` basis. -/
theorem sum_mul_basicDecompositionNumber_eq_cartanMatrix {ι₂ : Type*} (u : ι → ι₂ → ℤ)
    (hx : IsPElement p x) (φ η : ι₂) :
    (∑ j : J, basicDecompositionNumber
        (generalizedDecompositionNumberInv (x := x) hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u φ *
      basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u η)
      = ∑ μ : ι, ∑ τ : ι, (u μ φ : K)
          * (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ τ : K) * (u τ η : K) :=
  sum_mul_basicDecompositionNumber (J := J) φ η _ fun μ τ =>
    sum_mul_generalizedDecompositionNumberInv_eq_cartanMatrix hpC hω hω' hπ hlin hkerJ e eG hx μ τ

end Cartan

end OddOrder.RepresentationTheory.Modular
