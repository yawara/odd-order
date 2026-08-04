/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanBlockDiagonal
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse
import OddOrder.GroupTheory.RepresentationTheory.Modular.PairingZeroDecomposition

/-!
# The inverse of the Cartan matrix is block diagonal

`([μ, φ]⁰)` inverts the Cartan matrix (`sum_cartanMatrix_mul_pairingZero`), and `C` is block
diagonal (`cartanMatrix_eq_zero_of_centralCharacterAlg_ne`).  Hence so is the inverse:
`[μ, φ]⁰ = 0` unless `μ` and `φ` lie in the same block.

The proof is uniqueness of solutions rather than a conjugation argument.  Fix `φ` and let
`b_μ = [μ, φ]⁰`, so that `∑_μ c_{μθ} b_μ = δ_{φθ}` for every `θ`.  Truncating `b` to the block of
`φ` gives a vector `b'` satisfying the *same* equations — for `θ` in the block the discarded terms
had `c_{μθ} = 0`, and for `θ` outside it both sides vanish.  Since `C` is invertible, `b = b'`.

## Main results

* `OddOrder.RepresentationTheory.Modular.pairingZero_eq_zero_of_centralCharacterAlg_ne`
* `OddOrder.RepresentationTheory.Modular.pairingZero_trace_eq_zero_of_centralCharacterAlg_ne` —
  Navarro (3.20): `[χ, ψ]⁰ = 0` for ordinary characters in different blocks
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
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

set_option maxHeartbeats 800000 in
-- The Cartan matrix, its inverse and the block truncation are elaborated under the same chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
include hp hω hω' hπ hlin hkerJ e in
/-- **`[μ, φ]⁰ = 0` for Brauer characters in different blocks.**  The inverse of a block diagonal
invertible matrix is block diagonal. -/
theorem pairingZero_eq_zero_of_centralCharacterAlg_ne {φ ν : ι}
    (h : MatrixModule.centralCharacterAlg π ν hπ hlin
      ≠ MatrixModule.centralCharacterAlg π φ hπ hlin) :
    pairingZero (𝒪 := 𝒪) p K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ν)
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ) = 0 := by
  classical
  set Cm : Matrix ι ι K :=
    fun μ θ => ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ θ : ℕ) : K) with hCm
  set Bm : Matrix ι ι K := fun a b => pairingZero (𝒪 := 𝒪) p K
    (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π b)
    (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π a) with hBm
  -- `B · C = 1`, hence `C · B = 1` and `Bᵀ · Cᵀ = 1`
  have hBC : Bm * Cm = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply,
      ← sum_cartanMatrix_mul_pairingZero hp hω hω' hπ hlin hkerJ e a c]
    exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  have hTT : Bmᵀ * Cmᵀ = 1 := by
    rw [← Matrix.transpose_mul, mul_eq_one_comm.mp hBC, Matrix.transpose_one]
  -- the block of `φ`, and the two solutions
  set X : Finset ι := Finset.univ.filter
    (fun τ => MatrixModule.centralCharacterAlg π τ hπ hlin
      = MatrixModule.centralCharacterAlg π φ hπ hlin) with hX
  have hmemX : ∀ τ : ι, τ ∈ X ↔ MatrixModule.centralCharacterAlg π τ hπ hlin
      = MatrixModule.centralCharacterAlg π φ hπ hlin := by
    intro τ; rw [hX, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  set b : ι → K := fun τ => Bm φ τ with hb
  set b' : ι → K := fun τ => if τ ∈ X then b τ else 0 with hb'
  -- both solve `Cᵀ x = e_φ`
  have hrow : ∀ θ : ι, Cmᵀ.mulVec b θ = (1 : Matrix ι ι K) φ θ := by
    intro θ
    rw [← hBC, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  have hzero : ∀ μ θ : ι, MatrixModule.centralCharacterAlg π μ hπ hlin
      ≠ MatrixModule.centralCharacterAlg π θ hπ hlin → Cmᵀ θ μ = 0 := by
    intro μ θ hne
    change ((cartanMatrix hp hω hω' hπ hlin hkerJ e μ θ : ℕ) : K) = 0
    rw [cartanMatrix_eq_zero_of_centralCharacterAlg_ne hp hω hω' hπ hlin hkerJ e hne, Nat.cast_zero]
  have hrow' : ∀ θ : ι, Cmᵀ.mulVec b' θ = (1 : Matrix ι ι K) φ θ := by
    intro θ
    by_cases hθ : θ ∈ X
    · rw [← hrow θ]
      refine Finset.sum_congr rfl fun μ _ => ?_
      change Cmᵀ θ μ * b' μ = Cmᵀ θ μ * b μ
      by_cases hμ : μ ∈ X
      · rw [hb']; simp only [hμ, if_true]
      · have hz : Cmᵀ θ μ = 0 := hzero μ θ fun heq =>
          hμ ((hmemX μ).mpr (heq.trans ((hmemX θ).mp hθ)))
        rw [hz, zero_mul, zero_mul]
    · have hφθ : φ ≠ θ := fun heq => hθ (heq ▸ (hmemX φ).mpr rfl)
      rw [Matrix.one_apply_ne hφθ]
      refine Finset.sum_eq_zero fun μ _ => ?_
      change Cmᵀ θ μ * b' μ = 0
      by_cases hμ : μ ∈ X
      · have hz : Cmᵀ θ μ = 0 := hzero μ θ fun heq =>
          hθ ((hmemX θ).mpr (heq.symm.trans ((hmemX μ).mp hμ)))
        rw [hz, zero_mul]
      · rw [hb']; simp only [hμ, if_false, mul_zero]
  -- uniqueness
  have hbb : b = b' := by
    have hmul : ∀ x : ι → K, Bmᵀ.mulVec (Cmᵀ.mulVec x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec]
    rw [← hmul b, ← hmul b', funext hrow, funext hrow']
  have hνX : ν ∉ X := fun hin => h ((hmemX ν).mp hin)
  have := congrFun hbb ν
  rw [hb'] at this
  simp only [hνX, if_false] at this
  rw [hb] at this
  exact this

variable {L L' : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  [AddCommGroup L'] [Module 𝒪 L'] [Module.Free 𝒪 L'] [Module.Finite 𝒪 L']

set_option maxHeartbeats 800000 in
-- The decomposition expansion and the block vanishing are elaborated under the same chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
include hp hω hω' hπ hlin hkerJ e in
/-- **Navarro (3.20).**  If no irreducible Brauer character occurring in `χ` shares a central
character with one occurring in `ψ` — that is, if `χ` and `ψ` lie in different blocks — then
`[χ, ψ]⁰ = 0`.

Expanding the pairing by the decomposition numbers
(`pairingZero_trace_eq_sum_decompositionNumber`) leaves only terms `d_{χφ} d_{ψμ} [φ, μ]⁰`, and
each factor vanishes: the decomposition numbers by hypothesis, or `[φ, μ]⁰` because `φ` and `μ`
are then in different blocks. -/
theorem pairingZero_trace_eq_zero_of_centralCharacterAlg_ne (ρ : Representation 𝒪 G L)
    (σ : Representation 𝒪 G L')
    (hne : ∀ φ μ : ι,
      decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ ρ φ ≠ 0 →
      decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ σ μ ≠ 0 →
      MatrixModule.centralCharacterAlg π φ hπ hlin
        ≠ MatrixModule.centralCharacterAlg π μ hπ hlin) :
    pairingZero (𝒪 := 𝒪) p K (fun g => LinearMap.trace 𝒪 L (ρ g))
      (fun g => LinearMap.trace 𝒪 L' (σ g)) = 0 := by
  classical
  rw [pairingZero_trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ ρ σ]
  refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun μ _ => ?_
  by_cases hφ : decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ ρ φ = 0
  · rw [hφ]; simp
  by_cases hμ : decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ σ μ = 0
  · rw [hμ]; simp
  rw [pairingZero_eq_zero_of_centralCharacterAlg_ne hp hω hω' hπ hlin hkerJ e
    (hne φ μ hφ hμ), mul_zero]

end OddOrder.RepresentationTheory.Modular
