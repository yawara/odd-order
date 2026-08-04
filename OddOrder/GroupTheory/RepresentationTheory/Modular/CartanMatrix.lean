/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrreducibles

/-!
# The Cartan matrix and the projective indecomposable characters

**Navarro, p. 25.**  Once the decomposition matrix `D` is available (`OrdinaryIrreducibles`) the
Cartan matrix is *defined* as

`C = DᵀD`,  that is  `c_{μφ} = ∑_{χ ∈ Irr(G)} d_{χμ} d_{χφ}`,

and the **projective indecomposable character** attached to `φ ∈ IBr(G)` is

`Φ_φ = ∑_{χ ∈ Irr(G)} d_{χφ} χ`.

The one identity that ties them together — and the algebraic half of Navarro (2.13), which says
that `([θ,φ]⁰)` inverts `C` — is that on the `p`-regular classes `Φ_φ` is the `C`-combination of
the irreducible Brauer characters:

`Φ_φ(g) = ∑_{μ ∈ IBr(G)} c_{μφ} μ(g)`  for `g` `p`-regular.

That is immediate from the two definitions once the ordinary characters are expanded by
`trace_eq_sum_decompositionMatrix`; the analytic half of (2.13) — that `Φ_φ` vanishes off the
`p`-regular classes — needs the second orthogonality relation over the splitting field and is not
done here.

Characters are taken with values in `𝒪`, not in `K`: the trace of a lattice representation is
automatically integral, which is the standard "character values are algebraic integers" for free.
`algebraMap_ordinaryCharacter` records that this is the ordinary character.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.ordinaryCharacter` — the character of the `i`-th
  ordinary irreducible, valued in `𝒪`
* `OddOrder.RepresentationTheory.Modular.cartanMatrix` — `C = DᵀD`
* `OddOrder.RepresentationTheory.Modular.projectiveIndecomposableCharacter` — `Φ_φ`

## Main results

* `OddOrder.RepresentationTheory.Modular.cartanMatrix_comm` — `C` is symmetric
* `OddOrder.RepresentationTheory.Modular.projectiveIndecomposableCharacter_eq_sum_cartanMatrix`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-! ### The ordinary characters -/

section Ordinary

variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- **The character of the `i`-th ordinary irreducible**, read on the invariant lattice and
therefore valued in `𝒪`. -/
noncomputable def ordinaryCharacter (i : ι') (g : G) : 𝒪 :=
  LinearMap.trace 𝒪 _ (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i g)

omit [HenselianLocalRing 𝒪] [Fintype ι'] in
/-- The `𝒪`-valued character really is the ordinary character of the `i`-th irreducible. -/
theorem algebraMap_ordinaryCharacter (i : ι') (g : G) :
    algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g)
      = LinearMap.trace K _ (wedderburnRepresentation e i g) :=
  algebraMap_trace_latticeRepresentation _ (invariant_wedderburnLattice e i) g

end Ordinary

/-! ### The Cartan matrix -/

variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- **The Cartan matrix** `C = DᵀD` of Navarro p. 25:
`c_{μφ} = ∑_{χ ∈ Irr(G)} d_{χμ} d_{χφ}`. -/
noncomputable def cartanMatrix : ι → ι → ℕ := fun μ φ =>
  ∑ i : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ
    * decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ

/-- `C` is symmetric — it is a Gram matrix. -/
theorem cartanMatrix_comm (μ φ : ι) :
    cartanMatrix hp hω hω' hπ hlin hkerJ e μ φ = cartanMatrix hp hω hω' hπ hlin hkerJ e φ μ :=
  Finset.sum_congr rfl fun _ _ => Nat.mul_comm _ _

/-- **The projective indecomposable character** `Φ_φ = ∑_{χ ∈ Irr(G)} d_{χφ} χ`. -/
noncomputable def projectiveIndecomposableCharacter (φ : ι) (g : G) : 𝒪 :=
  ∑ i : ι', (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
    * ordinaryCharacter (𝒪 := 𝒪) e i g

/-- **`Φ_φ` is the `C`-combination of the irreducible Brauer characters on the `p`-regular
classes.**  Expand each ordinary character by its row of `D` and collect: the coefficient of `μ`
is `∑_χ d_{χφ} d_{χμ} = c_{μφ}`.

This is the algebraic half of Navarro (2.13); it is what turns `[Φ_θ, φ]⁰ = δ_{θφ}` into the
statement that `([θ,φ]⁰)` is the inverse of `C`. -/
theorem projectiveIndecomposableCharacter_eq_sum_cartanMatrix (φ : ι) (g : G)
    (hg : IsPRegular p g) :
    projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ g
      = ∑ μ, (cartanMatrix hp hω hω' hπ hlin hkerJ e μ φ : 𝒪)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g := by
  classical
  simp only [projectiveIndecomposableCharacter, ordinaryCharacter,
    trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e _ g hg, Finset.mul_sum,
    cartanMatrix, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end OddOrder.RepresentationTheory.Modular
