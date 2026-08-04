/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionNumber

/-!
# Navarro's pairing `[·,·]⁰` in terms of the decomposition numbers

Navarro's Lemma (3.20) rests on the identity

`[χ, ψ]⁰ = ∑_{φ, μ ∈ IBr(G)} d_{χφ} d_{ψμ} [φ, μ]⁰`,

which is nothing but bilinearity: on the `p`-regular elements `χ = ∑_φ d_{χφ} φ`
(`trace_eq_sum_decompositionNumber`), and `[·,·]⁰` only looks at `p`-regular elements.

Combined with

* `[φ, μ]⁰ = 0` unless `φ` and `μ` lie in the same block (the inverse of the Cartan matrix is
  block diagonal — `sum_cartanMatrix_mul_pairingZero`), and
* `d_{χφ} ≠ 0 ⟹ χ` and `φ` lie in the same block
  (`centralCharacterAlg_eq_of_decompositionNumber_ne_zero`),

this gives Navarro's "`[χ, ψ]⁰ ≠ 0 ⟹ χ, ψ` lie in the same block", the statement that makes
`∑_{g ∈ G⁰} χ(g) = 0` for `χ ∉ Irr(B_0)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.pairingZero_trace_eq_sum_decompositionNumber`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι]
  [∀ i, Nonempty (nn i)] [Invertible (Nat.card G : K)]
variable {L L' : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  [AddCommGroup L'] [Module 𝒪 L'] [Module.Free 𝒪 L'] [Module.Finite 𝒪 L']
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (ρ : Representation 𝒪 G L) (σ : Representation 𝒪 G L')

omit [IsFractionRing 𝒪 K] in
include hp hω hω' hπ hlin hkerJ in
open scoped Classical in
/-- **`[χ, ψ]⁰ = ∑_{φ, μ} d_{χφ} d_{ψμ} [φ, μ]⁰`.**  The pairing only sees `p`-regular elements,
where both characters are the `ℕ`-combinations of Brauer characters prescribed by the
decomposition numbers. -/
theorem pairingZero_trace_eq_sum_decompositionNumber :
    pairingZero (𝒪 := 𝒪) p K (fun g => LinearMap.trace 𝒪 L (ρ g))
        (fun g => LinearMap.trace 𝒪 L' (σ g))
      = ∑ φ : ι, ∑ μ : ι,
          ((decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ ρ φ : ℕ) : K)
            * ((decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ σ μ : ℕ) : K)
            * pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ)
                (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ) := by
  classical
  -- expand each summand of the pairing
  have hterm : ∀ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
      algebraMap 𝒪 K (LinearMap.trace 𝒪 L (ρ g) * LinearMap.trace 𝒪 L' (σ g⁻¹))
        = ∑ φ : ι, ∑ μ : ι,
            ((decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ ρ φ : ℕ) : K)
              * ((decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ σ μ : ℕ) : K)
              * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g
                  * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g⁻¹) := by
    intro g hg
    have hgreg : IsPRegular p g := (Finset.mem_filter.mp hg).2
    have hginv : IsPRegular p g⁻¹ := by
      simpa [IsPRegular] using hgreg
    rw [trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ ρ g hgreg,
      trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ σ g⁻¹ hginv,
      Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [map_mul, map_natCast]
    ring
  rw [pairingZero, Finset.sum_congr rfl hterm]
  -- pull the double sum out through the scaling
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pairingZero]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

end OddOrder.RepresentationTheory.Modular
