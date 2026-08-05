/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanBlockDiagonal
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse

/-!
# Every irreducible Brauer character is a combination of the ordinary ones

Navarro's Lemma (3.16) says that `IBr(G)` lies in the **`ℤ`**-span of `{χ⁰ : χ ∈ Irr(G)}`.  Over
the fraction field the statement is a one-line consequence of the invertibility of the Cartan
matrix, which `CartanInverse` already supplies in the explicit form
`∑_μ c_{μθ} [μ, φ]⁰ = δ_{φθ}`: with

`a_χ := ∑_τ d_{χτ} [τ, μ_0]⁰`,

the combination `∑_{χ ∈ Irr(G)} a_χ χ⁰` collapses to `μ_0`, because
`∑_χ d_{χτ} d_{χμ} = c_{τμ}` is the definition of the Cartan matrix and `([τ,μ]⁰)` inverts it.

This is what makes the change-of-basis matrix `U` of Navarro (7.3) exist over `K`: a basic set
spans the same space as `IBr` of the block.  (The integrality of `U` is the content of (3.16)
proper and is not proved here.)

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_ordinaryCombination_eq_irreducibleBrauerCharacter`
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

/-! ### The inverse of the Cartan matrix is block diagonal -/

set_option maxHeartbeats 800000 in
-- The two matrices carry the full modular-datum chain; `Fintype ι` / `Fintype ι'` are what make
-- the Cartan matrix and its inverse elaborate, and the section fixes them.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hω hω' hkerJ e in
/-- **`([τ,μ]⁰)` is block diagonal.**  It is the inverse of the Cartan matrix, which is block
diagonal (`cartanMatrix_eq_zero_of_centralCharacterAlg_ne`); zeroing out the off-block entries of
a right inverse of a block-diagonal matrix leaves a right inverse, and the inverse is unique. -/
theorem pairingZero_irreducibleBrauerCharacter_eq_zero_of_centralCharacterAlg_ne {τ μ₀ : ι}
    (hne : MatrixModule.centralCharacterAlg π τ hπ hlin
      ≠ MatrixModule.centralCharacterAlg π μ₀ hπ hlin) :
    pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀) = 0 := by
  classical
  set cc : ι → _ := fun μ => MatrixModule.centralCharacterAlg π μ hπ hlin with hcc
  set C : Matrix ι ι K := fun μ φ =>
    ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ φ : ℕ) : K) with hC
  set P : Matrix ι ι K := fun μ φ =>
    pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ)
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ) with hP
  set P' : Matrix ι ι K := fun μ φ => if cc μ = cc φ then P μ φ else 0 with hP'
  have hCzero : ∀ μ φ : ι, cc μ ≠ cc φ → C μ φ = 0 := fun μ φ h => by
    rw [hC]
    simp only
    rw [cartanMatrix_eq_zero_of_centralCharacterAlg_ne hp hω hω' hπ hlin hkerJ e h, Nat.cast_zero]
  have hCP : Cᵀ * P = 1 := by
    ext θ φ
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, hC, hP]
    rw [sum_cartanMatrix_mul_pairingZero hp hω hω' hπ hlin hkerJ e φ θ]
    exact if_congr eq_comm rfl rfl
  have hCP' : Cᵀ * P' = 1 := by
    ext θ φ
    by_cases hθφ : cc θ = cc φ
    · rw [← hCP, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun μ _ => ?_
      by_cases hμθ : cc μ = cc θ
      · simp only [hP', if_pos (hμθ.trans hθφ)]
      · rw [Matrix.transpose_apply, hCzero μ θ hμθ, zero_mul, zero_mul]
    · rw [Matrix.mul_apply, Matrix.one_apply, if_neg (fun h => hθφ (by rw [h]))]
      refine Finset.sum_eq_zero fun μ _ => ?_
      by_cases hμθ : cc μ = cc θ
      · simp only [hP', if_neg (fun hc => hθφ (hμθ.symm.trans hc)), mul_zero]
      · rw [Matrix.transpose_apply, hCzero μ θ hμθ, zero_mul]
  have hPP' : P' = P := by
    have hPC : P * Cᵀ = 1 := mul_eq_one_comm.mp hCP
    calc P' = 1 * P' := (Matrix.one_mul _).symm
      _ = (P * Cᵀ) * P' := by rw [hPC]
      _ = P * (Cᵀ * P') := Matrix.mul_assoc _ _ _
      _ = P := by rw [hCP', Matrix.mul_one]
  have hzero : P' τ μ₀ = 0 := by
    simp only [hP']
    exact if_neg hne
  have hval := congrFun (congrFun hPP' τ) μ₀
  rw [hzero] at hval
  exact hval.symm

/-- The coefficients expressing `μ_0 ∈ IBr(G)` in the ordinary characters:
`a_χ = ∑_τ d_{χτ} [τ, μ_0]⁰`. -/
noncomputable def ordinaryCombinationCoeff (μ₀ : ι) (i : ι') : K :=
  ∑ τ : ι, ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i τ : ℕ) : K)
    * pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀)

set_option maxHeartbeats 800000 in
-- The decomposition matrix and the Cartan inverse are elaborated under the same chains;
-- `DecidableEq ι` is what makes `pairingZero` (via the class-sum filters) elaborate.
set_option linter.unusedDecidableInType false in
include hp hω hω' hπ hlin hkerJ in
/-- **`μ_0` is a `K`-combination of the ordinary characters on the `p`-regular classes** — the
`K`-version of Navarro (3.16).

`∑_χ a_χ χ⁰ = ∑_{τ,μ} [τ,μ_0]⁰ (∑_χ d_{χτ} d_{χμ}) μ = ∑_μ (∑_τ c_{τμ} [τ,μ_0]⁰) μ = μ_0`,
the last step being that `([τ,μ]⁰)` inverts the Cartan matrix. -/
theorem sum_ordinaryCombination_eq_irreducibleBrauerCharacter (μ₀ : ι) {g : G}
    (hg : IsPRegular p g) :
    (∑ i : ι', ordinaryCombinationCoeff hp hω hω' hπ hlin hkerJ e μ₀ i *
        algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g))
      = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g) := by
  classical
  have hexp : ∀ i : ι',
      algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g)
        = ∑ μ : ι,
            ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i μ : ℕ) : K)
            * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g) := by
    intro i
    rw [ordinaryCharacter, trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i g hg,
      map_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [map_mul, map_natCast]
  calc (∑ i : ι', ordinaryCombinationCoeff hp hω hω' hπ hlin hkerJ e μ₀ i *
          algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g))
      = ∑ τ : ι, ∑ μ : ι,
          (∑ i : ι',
            ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i τ : ℕ) : K)
              * ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i μ : ℕ) : K))
          * (pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ)
              (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀)
            * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g)) := by
        rw [Finset.sum_congr rfl fun i _ => by
          rw [ordinaryCombinationCoeff, hexp i, Finset.sum_mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ μ : ι, (∑ τ : ι,
          ((cartanMatrix hp hω hω' hπ hlin hkerJ e τ μ : ℕ) : K)
            * pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ)
                (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀))
          * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [cartanMatrix, Nat.cast_sum, Nat.cast_mul]
        ring
    _ = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g) := by
        rw [Finset.sum_congr rfl fun μ _ => by
          rw [sum_cartanMatrix_mul_pairingZero hp hω hω' hπ hlin hkerJ e μ₀ μ]]
        simp

end OddOrder.RepresentationTheory.Modular
