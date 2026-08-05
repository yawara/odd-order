/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerFromOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeOrderCartan

/-!
# `IBr(G) ⊆ ℕ · Irr(G)` for a `p'`-group

The payoff of `PPrimeOrderCartan`.  Over `K` the combination expressing `μ_0 ∈ IBr(G)` in the
ordinary characters has coefficients `a_χ = ∑_τ d_{χτ} [τ, μ_0]⁰` (`BrauerFromOrdinary`), and
`([τ,μ]⁰)` is the inverse of the Cartan matrix.  For a `p'`-group the Cartan matrix is the
identity, so its inverse is too and the coefficient collapses to the single decomposition number
`d_{χμ_0}` — a *natural number*.

So for `p ∤ |G|` every irreducible Brauer character is the honest character
`∑_χ d_{χμ_0} χ` of a `K`-representation.  This is the half of Navarro (2.12) that Brauer's
characterization of characters needs: on an elementary subgroup the `p'`-part is where a Brauer
character has to be recognised as an ordinary one.

## Main results

* `OddOrder.RepresentationTheory.Modular.pairingZero_eq_ite_of_not_dvd_card` — `[τ,μ]⁰ = δ_{τμ}`
* `OddOrder.RepresentationTheory.Modular.ordinaryCombinationCoeff_eq_natCast_of_not_dvd_card`
* `OddOrder.RepresentationTheory.Modular.sum_decompositionMatrix_mul_ordinaryCharacter` —
  `φ = ∑_χ d_{χφ} χ`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.12) (p. 25).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

-- The Cartan matrix and the decomposition matrix are what the proofs run on, and the section's
-- `Fintype`/`DecidableEq` instances are what make them elaborate; they do not surface in the
-- conclusions.  Same suppression, for the same reason, as in `BrauerFromOrdinary`.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
include hp hω hω' hπ hlin hkerJ e in
/-- **`[τ,μ]⁰ = δ_{τμ}` for a `p'`-group.**  The pairing matrix inverts `C`, and `C = 1`. -/
theorem pairingZero_eq_ite_of_not_dvd_card [IsAlgClosed (ResidueField 𝒪)]
    (hG : ¬ p ∣ Nat.card G) (τ μ₀ : ι) :
    pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀) = if τ = μ₀ then 1 else 0 := by
  classical
  have hinv := sum_cartanMatrix_mul_pairingZero hp hω hω' hπ hlin hkerJ e μ₀ τ
  rw [Finset.sum_congr rfl fun ν (_ : ν ∈ Finset.univ) => by
    rw [cartanMatrix_eq_ite_of_not_dvd_card hp hω hω' hπ hlin hkerJ e hG ν τ],
    Finset.sum_eq_single τ (fun ν _ hν => by rw [if_neg hν, Nat.cast_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ τ) h), if_pos rfl, Nat.cast_one, one_mul] at hinv
  rw [hinv]
  exact if_congr eq_comm rfl rfl

-- Instances driving the Cartan/decomposition matrices, as above.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
include hp hω hω' hπ hlin hkerJ e in
/-- **The coefficients of `BrauerFromOrdinary` are natural numbers for a `p'`-group.** -/
theorem ordinaryCombinationCoeff_eq_natCast_of_not_dvd_card [IsAlgClosed (ResidueField 𝒪)]
    (hG : ¬ p ∣ Nat.card G) (μ₀ : ι) (i : ι') :
    ordinaryCombinationCoeff hp hω hω' hπ hlin hkerJ e μ₀ i
      = ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ₀ : ℕ) : K) := by
  classical
  rw [ordinaryCombinationCoeff, Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => by
    rw [pairingZero_eq_ite_of_not_dvd_card hp hω hω' hπ hlin hkerJ e hG τ μ₀],
    Finset.sum_eq_single μ₀ (fun τ _ hτ => by rw [if_neg hτ, mul_zero])
      (fun h => absurd (Finset.mem_univ μ₀) h), if_pos rfl, mul_one]

-- Instances driving the Cartan/decomposition matrices, as above.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
include hp hω hω' hπ hlin hkerJ e in
/-- **Navarro (2.12)**: for `p ∤ |G|` every irreducible Brauer character is the ordinary character
`∑_χ d_{χφ} χ`.  Note there is no `p`-regularity hypothesis on `g`: in a `p'`-group there is
nothing else. -/
theorem sum_decompositionMatrix_mul_ordinaryCharacter [IsAlgClosed (ResidueField 𝒪)]
    (hG : ¬ p ∣ Nat.card G) (μ₀ : ι) (g : G) :
    (∑ i : ι', ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ₀ : ℕ) : K) *
        algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g))
      = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g) := by
  classical
  have hg : IsPRegular p g := fun hdvd => hG (hdvd.trans (orderOf_dvd_natCard g))
  rw [← sum_ordinaryCombination_eq_irreducibleBrauerCharacter hp hω hω' hπ hlin hkerJ e μ₀ hg]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ordinaryCombinationCoeff_eq_natCast_of_not_dvd_card hp hω hω' hπ hlin hkerJ e hG μ₀ i]

end OddOrder.RepresentationTheory.Modular
