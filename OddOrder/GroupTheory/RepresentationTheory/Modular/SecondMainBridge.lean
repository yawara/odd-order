/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SubgroupTruncation
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeRepresentation

/-!
# Plumbing between the three group algebras of Navarro (5.2)

Brauer's second main theorem is stated for `χ ∈ Irr(G)` but computed inside `H = C_G(x)`, and it
moves between three group algebras:

* `𝒪G` — where (5.7) (`InducedBlockTrace`) lives, because the block idempotents and the witness
  `w` of (5.6) have integral coefficients;
* `K[H]` — where the ordinary decomposition of `χ_H` lives (`OrdinaryDecomposition`);
* `𝒪H` — where the block idempotent `f_b` itself lives.

The two moves between them are *restriction along `H ≤ G`* (`inclusionHom`) and *base change
along `𝒪 → K`* (`MonoidAlgebra.mapRingHom`); they commute, and both are compatible with
`Representation.asAlgebraHom`.  This file records those compatibilities, together with the
corresponding statement for an invariant lattice.

## Main results

* `OddOrder.RepresentationTheory.Modular.asAlgebraHom_comp_subtype` — restricting a representation
  restricts its group-algebra action along `inclusionHom`
* `OddOrder.RepresentationTheory.Modular.mapRingHom_inclusionHom` — the two moves commute
* `OddOrder.RepresentationTheory.Modular.coe_latticeRepresentation_asAlgebraHom` — the lattice
  representation carries the restriction of the ambient group-algebra action
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra
open OddOrder.GroupAlgebra (inclusionHom)

/-! ### Restriction to a subgroup -/

section Restriction

variable {R G V : Type*} [CommSemiring R] [Group G] [AddCommMonoid V] [Module R V]

/-- **Restricting a representation to `H` restricts its group-algebra action along
`inclusionHom`.**  Both sides are additive in `a` and agree on the monomials. -/
theorem asAlgebraHom_comp_subtype (σ : Representation R G V) (H : Subgroup G)
    (a : MonoidAlgebra R ↥H) :
    Representation.asAlgebraHom (σ.comp H.subtype) a
      = σ.asAlgebraHom (inclusionHom H a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single u r =>
    rw [Representation.asAlgebraHom_single, OddOrder.GroupAlgebra.inclusionHom_single,
      Representation.asAlgebraHom_single]
    rfl

end Restriction

/-! ### Base change of the coefficients -/

section BaseChange

variable {R S G : Type*} [Semiring R] [Semiring S] [Group G]

/-- **Restriction and base change commute.**  Both sides are additive and agree on the
monomials. -/
theorem mapRingHom_inclusionHom (H : Subgroup G) (φ : R →+* S) (a : MonoidAlgebra R ↥H) :
    MonoidAlgebra.mapRingHom G φ (inclusionHom H a)
      = inclusionHom H (MonoidAlgebra.mapRingHom (↥H) φ a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single u r =>
    rw [OddOrder.GroupAlgebra.inclusionHom_single, MonoidAlgebra.mapRingHom_single,
      MonoidAlgebra.mapRingHom_single, OddOrder.GroupAlgebra.inclusionHom_single]

end BaseChange

/-! ### The group-algebra action on an invariant lattice -/

section Lattice

variable {𝒪 K V : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪] [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] [AddCommGroup V] [Module K V] [Module 𝒪 V] [IsScalarTower 𝒪 K V]
variable {G : Type*} [Group G]

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/-- **The lattice representation carries the restriction of the ambient group-algebra action.**
An element of `𝒪G` acts on the lattice the way its image in `KG` acts on the ambient space. -/
theorem coe_latticeRepresentation_asAlgebraHom (ρ : Representation K G V) {L : Submodule 𝒪 V}
    (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) (a : MonoidAlgebra 𝒪 G) (v : L) :
    (((latticeRepresentation ρ hL).asAlgebraHom a v : L) : V)
      = ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a) v := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply,
      Submodule.coe_zero]
  | add u w hu hw =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add,
      hu, hw]
  | single g r =>
    rw [Representation.asAlgebraHom_single, MonoidAlgebra.mapRingHom_single,
      Representation.asAlgebraHom_single, LinearMap.smul_apply, LinearMap.smul_apply,
      Submodule.coe_smul, coe_latticeRepresentation_apply, algebraMap_smul]

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/-- **An element of `𝒪G` killing the ambient space kills the lattice.**  This is how the vanishing
of a central character over `K` propagates down to the reduction. -/
theorem latticeRepresentation_asAlgebraHom_eq_zero (ρ : Representation K G V)
    {L : Submodule 𝒪 V} (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) {a : MonoidAlgebra 𝒪 G}
    (ha : ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a) = 0) :
    (latticeRepresentation ρ hL).asAlgebraHom a = 0 :=
  LinearMap.ext fun v => Subtype.ext <| by
    rw [coe_latticeRepresentation_asAlgebraHom ρ hL a v, ha]
    simp

end Lattice

end OddOrder.RepresentationTheory.Modular
