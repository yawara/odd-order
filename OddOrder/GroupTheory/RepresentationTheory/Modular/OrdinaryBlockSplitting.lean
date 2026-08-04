/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrreducibles
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBridge

/-!
# The Wedderburn splitting of `K[G]` is a block splitting

`OrdinaryDecomposition` decomposes a character along a *surjection*
`π : K[G] ↠ ∏_i M_{m_i}(K)` with `ker π = J(K[G])`, while `OrdinaryIrreducibles` indexes `Irr(G)`
by an *isomorphism* `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)`.  In characteristic `0` the two agree: `K[G]`
is semisimple by Maschke, so `J(K[G]) = ⊥ = ker e`, and the block representation of `↑e` *is* the
`i`-th ordinary irreducible.

That identification is what lets Navarro (5.2) use the decomposition matrix `D` — which is defined
through `e` — inside the trace computation of `OrdinaryDecomposition`, which is phrased through
`π`.

## Main results

* `OddOrder.RepresentationTheory.Modular.blockRepresentation_algEquiv` — `↑e`'s blocks are the
  ordinary irreducibles
* `OddOrder.RepresentationTheory.Modular.ker_algEquiv_eq_jacobson` — `ker e = J(K[G])`
* `OddOrder.RepresentationTheory.Modular.trace_wedderburn_eq_sum_decompositionMatrix` — the
  defining property of `D`, read in `K`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-! ### The splitting as a surjection -/

section Splitting

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- **The blocks of the Wedderburn isomorphism are the ordinary irreducibles.**  Both act on
column vectors through the `i`-th matrix component. -/
theorem blockRepresentation_algEquiv
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι') :
    blockRepresentation (e.toAlgHom.toRingHom) i = wedderburnRepresentation e i := rfl

theorem surjective_algEquiv (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) :
    Function.Surjective (e.toAlgHom.toRingHom) := e.surjective

theorem smul_algEquiv (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
    (c : K) (a : MonoidAlgebra K G) : e.toAlgHom.toRingHom (c • a) = c • e.toAlgHom.toRingHom a :=
  _root_.map_smul e.toAlgHom c a

/-- **In characteristic `0` the Wedderburn isomorphism has kernel the Jacobson radical.**  Maschke
makes `K[G]` semisimple, so both sides are `⊥`. -/
theorem ker_algEquiv_eq_jacobson [Finite G] [NeZero (Nat.card G : K)]
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) :
    RingHom.ker (e.toAlgHom.toRingHom) = Ring.jacobson (MonoidAlgebra K G) := by
  rw [IsSemisimpleRing.jacobson_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  exact e.injective (by rw [map_zero]; exact hx)

end Splitting

/-! ### The decomposition matrix, read in `K` -/

section DecompositionMatrix

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

include hp hω hω' hπ hlin hkerJ in
/-- **The defining property of `D`, read in `K`.**  Applying `algebraMap 𝒪 K` to
`trace_eq_sum_decompositionMatrix` and using that the lattice character *is* the ordinary
character.  This is the form the trace computation of Navarro (5.2) consumes. -/
theorem trace_wedderburn_eq_sum_decompositionMatrix (i : ι') (g : G) (hg : IsPRegular p g) :
    LinearMap.trace K (m i → K) (wedderburnRepresentation e i g)
      = ∑ φ, (decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ : K)
          * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) := by
  rw [← algebraMap_trace_latticeRepresentation (𝒪 := 𝒪) (wedderburnRepresentation e i)
    (invariant_wedderburnLattice e i) g]
  rw [show latticeRepresentation (wedderburnRepresentation e i) (invariant_wedderburnLattice e i)
      = wedderburnLatticeRepresentation (𝒪 := 𝒪) e i from rfl,
    trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i g hg, map_sum]
  exact Finset.sum_congr rfl fun φ _ => by rw [map_mul, map_natCast]

end DecompositionMatrix

end OddOrder.RepresentationTheory.Modular
