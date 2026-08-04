/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionOfOrdinary

/-!
# `Irr(G)` and the decomposition matrix

Over a splitting field `K` of characteristic `0` — for the splitting `p`-modular system
`𝓞_ℂ_[p]` this is `K = ℂ_[p]` (`PadicComplexSystem`) — Maschke and Wedderburn–Artin write

`K[G] ≃ₐ[K] ∏_i M_{m_i}(K)`,

and the simple `K[G]`-modules are exactly the natural modules `m_i → K` of the factors, one for
each `i`.  So the index set of the product *is* `Irr(G)`, and `wedderburnRepresentation` is the
corresponding representation: act on column vectors through the `i`-th matrix block.

Each of these has a `G`-invariant `𝒪`-lattice (`exists_isLattice_invariant`), whose decomposition
numbers do not depend on which lattice was chosen
(`decompositionNumber_latticeRepresentation_eq`).  That makes

`decompositionMatrix e i φ`

a genuine matrix `Irr(G) × IBr(G) → ℕ`: the decomposition matrix `D`.  The Cartan matrix is
`C = DᵀD`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.wedderburnRepresentation` — the `i`-th ordinary
  irreducible
* `OddOrder.RepresentationTheory.Modular.decompositionMatrix` — `D`

## Main results

* `OddOrder.RepresentationTheory.Modular.trace_eq_sum_decompositionMatrix` — the defining
  property of `D`, on the `p`-regular classes
* `OddOrder.RepresentationTheory.Modular.eq_decompositionMatrix` — anything with that property
  *is* the row of `D`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-! ### The ordinary irreducible representations -/

section Wedderburn

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- **The `i`-th ordinary irreducible representation.**  A Wedderburn splitting of `K[G]` makes
`G` act on the column vectors `m i → K` through the `i`-th matrix block. -/
noncomputable def wedderburnRepresentation
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι') :
    Representation K G (m i → K) :=
  (Matrix.toLinAlgEquiv' (n := m i) (R := K)).toAlgHom.toMonoidHom.comp
    ((((Pi.evalAlgHom K (fun j => Matrix (m j) (m j) K) i).comp
      e.toAlgHom).toMonoidHom).comp (MonoidAlgebra.of K G))

@[simp]
theorem wedderburnRepresentation_apply
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι') (g : G) (v : m i → K) :
    wedderburnRepresentation e i g v = (e (MonoidAlgebra.single g 1) i).mulVec v := rfl

end Wedderburn

/-! ### The decomposition matrix -/

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

section

variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι')

/-- A `G`-invariant `𝒪`-lattice in the `i`-th ordinary irreducible.  Which one is irrelevant:
`decompositionNumber_latticeRepresentation_eq` says the decomposition numbers do not see it. -/
noncomputable def wedderburnLattice : Submodule 𝒪 (m i → K) :=
  (exists_isLattice_invariant (𝒪 := 𝒪) (wedderburnRepresentation e i)).choose

instance isLattice_wedderburnLattice : (wedderburnLattice (𝒪 := 𝒪) e i).IsLattice K :=
  (exists_isLattice_invariant (𝒪 := 𝒪) (wedderburnRepresentation e i)).choose_spec.1

omit [IsDomain 𝒪] [ValuationRing 𝒪] [HenselianLocalRing 𝒪] [IsFractionRing 𝒪 K] in
theorem invariant_wedderburnLattice (g : G) :
    ∀ v ∈ wedderburnLattice (𝒪 := 𝒪) e i, wedderburnRepresentation e i g v ∈
      wedderburnLattice (𝒪 := 𝒪) e i :=
  (exists_isLattice_invariant (𝒪 := 𝒪) (wedderburnRepresentation e i)).choose_spec.2 g

/-- The lattice representation carried by `wedderburnLattice`. -/
noncomputable def wedderburnLatticeRepresentation :
    Representation 𝒪 G (wedderburnLattice (𝒪 := 𝒪) e i) :=
  latticeRepresentation (wedderburnRepresentation e i) (invariant_wedderburnLattice e i)

end

variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-- **The decomposition matrix `D`.**  Row `i` is the decomposition of the `i`-th ordinary
irreducible into irreducible Brauer characters; column `φ` runs over `IBr(G)`.  The Cartan matrix
is `C = DᵀD`. -/
noncomputable def decompositionMatrix : ι' → ι → ℕ := fun i =>
  decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ
    (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i)

/-- **The defining property of `D`**: on the `p`-regular classes the ordinary character of the
`i`-th irreducible is the `ℕ`-combination of irreducible Brauer characters that row `i`
prescribes. -/
theorem trace_eq_sum_decompositionMatrix (i : ι') (g : G) (hg : IsPRegular p g) :
    LinearMap.trace 𝒪 _ (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i g)
      = ∑ φ, (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g :=
  trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ
    (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i) g hg

/-- **Uniqueness**: any `ℕ`-family with the defining property is the corresponding row of `D`.
Combined with `decompositionNumber_latticeRepresentation_eq` this makes `D` computable from *any*
invariant lattice in the `i`-th irreducible, not just the chosen one. -/
theorem eq_decompositionMatrix (i : ι') {d : ι → ℕ}
    (hd : ∀ g : G, IsPRegular p g →
      LinearMap.trace 𝒪 _ (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i g)
        = ∑ φ, (d φ : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) :
    d = decompositionMatrix hp hω hω' hπ hlin hkerJ e i :=
  eq_decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ
    (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i) hd

/-- **Any invariant lattice computes the same row of `D`.**  The chosen `wedderburnLattice` is a
convenience; the matrix is an invariant of the ordinary representation. -/
theorem decompositionMatrix_eq_of_invariant_lattice (i : ι') {L : Submodule 𝒪 (m i → K)}
    [L.IsLattice K] (hL : ∀ (g : G), ∀ v ∈ L, wedderburnRepresentation e i g v ∈ L) :
    decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ
        (latticeRepresentation (wedderburnRepresentation e i) hL)
      = decompositionMatrix hp hω hω' hπ hlin hkerJ e i :=
  decompositionNumber_latticeRepresentation_eq hp hω hω' hπ hlin hkerJ
    (wedderburnRepresentation e i) hL (invariant_wedderburnLattice e i)

end OddOrder.RepresentationTheory.Modular
