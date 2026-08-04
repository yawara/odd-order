/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularClassIndex
import OddOrder.GroupTheory.RepresentationTheory.Modular.ProjectiveCharacterVanishing

/-!
# The orthogonality of `Φ_θ` against `IBr(G)`

Navarro (2.13) says `[Φ_θ, φ]⁰ = δ_{θφ}`, and hence that `([θ,φ]⁰)` inverts the Cartan matrix.
This file proves the matrix content of that statement.

Index the `p`-regular classes by `ι` (`PRegularClassIndex`) and write `x_j` for the chosen
`p`-regular representative.  Then

`A_{j φ} := Φ_φ(x_j)`,  `B_{φ j} := φ(x_j⁻¹) / |C_G(x_j)|`

satisfy `A · B = 1`: that is exactly
`∑_φ Φ_φ(x_j) φ(x_{j'}⁻¹) = |C_G(x_{j'})| δ_{j j'}`
(`algebraMap_sum_projectiveIndecomposableCharacter_mul_inv`), and the classes are pairwise
non-conjugate.  Both matrices are **square**, because `|IBr(G)| = #cl(G°)`, so the inverse is
two-sided and `B · A = 1` — which is `[Φ_θ, φ]⁰ = δ_{θφ}` once the pairing is written as a sum
over the `p`-regular classes.

## Main results

* `OddOrder.RepresentationTheory.Modular.isUnit_card_centralizer`
* `OddOrder.RepresentationTheory.Modular.projMatrix_mul_brauerMatrix` — `A · B = 1`
* `OddOrder.RepresentationTheory.Modular.brauerMatrix_mul_projMatrix` — `B · A = 1`
* `OddOrder.RepresentationTheory.Modular.sum_brauer_mul_projectiveIndecomposableCharacter` —
  `∑_j |C_G(x_j)|⁻¹ φ(x_j⁻¹) Φ_θ(x_j) = δ_{φθ}`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]

/-- The order of a centralizer is invertible in `K`: it divides `|G|`, which is. -/
theorem isUnit_card_centralizer (g : G) :
    IsUnit ((Nat.card (Subgroup.centralizer ({g} : Set G)) : K)) := by
  refine isUnit_of_mul_isUnit_right (x := (conjugacyClassSize (ConjClasses.mk g) : K)) ?_
  rw [show (conjugacyClassSize (ConjClasses.mk g) : K)
      * (Nat.card (Subgroup.centralizer ({g} : Set G)) : K) = (Nat.card G : K) from
    mod_cast congrArg (Nat.cast : ℕ → K)
      (conjugacyClassSize_mk_mul_card_centralizer (G := G) g)]
  exact isUnit_of_invertible _

variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- The matrix of projective indecomposable characters on the `p`-regular classes. -/
noncomputable def projMatrix : Matrix ι ι K := fun j φ =>
  algebraMap 𝒪 K (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ
    (pRegularRep hp hπ hlin hkerJ j))

/-- The matrix of irreducible Brauer characters at inverses, weighted by `|C_G|⁻¹`. -/
noncomputable def brauerMatrix : Matrix ι ι K := fun φ j =>
  (Nat.card (Subgroup.centralizer ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
    algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
      (pRegularRep hp hπ hlin hkerJ j)⁻¹)

/-- **`A · B = 1`** — the defining relation of the projective indecomposable characters, read on
the `p`-regular class representatives. -/
theorem projMatrix_mul_brauerMatrix :
    projMatrix hp hω hω' hπ hlin hkerJ e * brauerMatrix hp hπ hlin hkerJ = 1 := by
  classical
  ext j j'
  set y := pRegularRep hp hπ hlin hkerJ j' with hy
  have hyreg : IsPRegular p y := isPRegular_pRegularRep hp hπ hlin hkerJ j'
  have hrel := algebraMap_sum_projectiveIndecomposableCharacter_mul_inv hp hω hω' hπ hlin hkerJ e
    (pRegularRep hp hπ hlin hkerJ j) hyreg
  rw [map_sum] at hrel
  have hunit := isUnit_card_centralizer (K := K) y
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hexp : ∀ φ : ι, projMatrix hp hω hω' hπ hlin hkerJ e j φ
      * brauerMatrix hp hπ hlin hkerJ φ j'
      = (Nat.card (Subgroup.centralizer ({y} : Set G)) : K)⁻¹ *
        algebraMap 𝒪 K (projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ
            (pRegularRep hp hπ hlin hkerJ j)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y⁻¹) := by
    intro φ
    simp only [projMatrix, brauerMatrix, map_mul, hy]
    ring
  rw [Finset.sum_congr rfl fun φ _ => hexp φ, ← Finset.mul_sum, hrel]
  by_cases h : j = j'
  · rw [if_pos h, if_pos (by rw [h]), inv_mul_cancel₀ hunit.ne_zero]
  · rw [if_neg h, if_neg fun hc =>
      h ((pRegularRep_isConj_iff hp hπ hlin hkerJ j' j).mp hc).symm, mul_zero]

/-- **`B · A = 1`** — the character table of the `p`-regular classes is square (`|IBr(G)| =
#cl(G°)`), so the one-sided inverse of `projMatrix_mul_brauerMatrix` is two-sided. -/
theorem brauerMatrix_mul_projMatrix :
    brauerMatrix hp hπ hlin hkerJ * projMatrix hp hω hω' hπ hlin hkerJ e = 1 :=
  mul_eq_one_comm.mp (projMatrix_mul_brauerMatrix hp hω hω' hπ hlin hkerJ e)

/-- **`[Φ_θ, φ]⁰ = δ_{φθ}`, as a sum over the `p`-regular classes** — the matrix content of
Navarro (2.13). -/
theorem sum_brauer_mul_projectiveIndecomposableCharacter (φ θ : ι) :
    ∑ j : ι, (Nat.card (Subgroup.centralizer
          ({pRegularRep hp hπ hlin hkerJ j} : Set G)) : K)⁻¹ *
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
            (pRegularRep hp hπ hlin hkerJ j)⁻¹
          * projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e θ
            (pRegularRep hp hπ hlin hkerJ j))
      = if φ = θ then 1 else 0 := by
  classical
  have hmul := congrFun (congrFun (brauerMatrix_mul_projMatrix hp hω hω' hπ hlin hkerJ e) φ) θ
  rw [Matrix.mul_apply, Matrix.one_apply] at hmul
  rw [← hmul]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [projMatrix, brauerMatrix, map_mul]
    ring

end OddOrder.RepresentationTheory.Modular
