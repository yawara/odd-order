/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionNumber
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeRepresentation

/-!
# The decomposition numbers of an ordinary representation

`decompositionNumber` is attached to an `𝒪`-lattice representation, but the lattice is not part of
the data one wants: the rows of the decomposition matrix are indexed by `Irr(G)`, that is, by
representations over the fraction field `K`.  This file removes the choice.

Two `G`-invariant lattices in the same `K`-representation have the same character, because both
characters map to the ordinary character under the injection `𝒪 ↪ K`
(`algebraMap_trace_latticeRepresentation`).  The decomposition numbers are determined by the
character on the `p`-regular classes (`eq_decompositionNumber`), so they agree.

This is the classical statement that the decomposition map `Irr(G) → ℤ IBr(G)` is well defined —
Navarro (2.9), Isaacs Ch. 15 — and it is what lets `D` be a matrix.

## Main results

* `OddOrder.RepresentationTheory.Modular.trace_latticeRepresentation_eq` — the character of a
  lattice representation does not depend on the lattice
* `OddOrder.RepresentationTheory.Modular.decompositionNumber_latticeRepresentation_eq` — nor do
  the decomposition numbers
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K V : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
  [AddCommGroup V] [Module K V] [Module 𝒪 V] [IsScalarTower 𝒪 K V]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

omit [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [Finite G] in
/-- **The character of a lattice representation does not depend on the lattice.**  Both traces
have the same image in `K` — the ordinary character — and `𝒪 → K` is injective. -/
theorem trace_latticeRepresentation_eq (ρ : Representation K G V) {L L' : Submodule 𝒪 V}
    [L.IsLattice K] [L'.IsLattice K] (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L)
    (hL' : ∀ (g : G), ∀ v ∈ L', ρ g v ∈ L') (g : G) :
    LinearMap.trace 𝒪 L (latticeRepresentation ρ hL g)
      = LinearMap.trace 𝒪 L' (latticeRepresentation ρ hL' g) :=
  IsFractionRing.injective 𝒪 K <| by
    rw [algebraMap_trace_latticeRepresentation, algebraMap_trace_latticeRepresentation]

/-- **The decomposition numbers depend only on the ordinary representation**, not on the choice of
invariant lattice inside it.  This is what makes the decomposition matrix a matrix on `Irr(G)`. -/
theorem decompositionNumber_latticeRepresentation_eq (hp : p.Prime)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
    {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
    (ρ : Representation K G V) {L L' : Submodule 𝒪 V} [L.IsLattice K] [L'.IsLattice K]
    (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) (hL' : ∀ (g : G), ∀ v ∈ L', ρ g v ∈ L') :
    decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ (latticeRepresentation ρ hL)
      = decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ (latticeRepresentation ρ hL') :=
  eq_decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ (latticeRepresentation ρ hL')
    fun g hg => by
      rw [← trace_latticeRepresentation_eq ρ hL hL' g]
      exact trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ (latticeRepresentation ρ hL)
        g hg

end OddOrder.RepresentationTheory.Modular
