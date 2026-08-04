/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CenterIdempotentLift
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfIrreducible
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBridge

/-!
# The lattice central character and the Wedderburn central character agree

The `i`-th ordinary irreducible carries two central characters:

* `ω^L_i`, the scalar by which a central element of `𝒪G` acts on the invariant lattice
  (`Modular.centralScalar`, valued in `𝒪` — this is the one `blockOfIrr` is built from);
* `ω^K_i`, the scalar by which the image in `K[G]` acts on the `i`-th Wedderburn block
  (`MatrixModule.centralScalar`, valued in `K` — this is the one Burnside's formula uses).

They agree under `𝒪 → K`.  The proof is the standard "a lattice spans" argument: `z - ω^L_i(z)`
kills the lattice, hence kills the ambient space
(`asAlgebraHom_eq_zero_of_latticeRepresentation`), and the ambient action is the `i`-th matrix
block (`asAlgebraHom_wedderburnRepresentation`).

This is what lets the block partition `blockOfIrr` — defined on the lattice side — be read off the
Wedderburn side, where the orthogonality relations and the primitive idempotents live.

## Main results

* `OddOrder.RepresentationTheory.Modular.algebraMap_centralScalar_eq`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

-- `Fintype G` is what makes the invariant lattice (and hence `centralScalar`) elaborate in the
-- statement; the section fixes it, so it cannot be replaced by `Finite` here.
set_option linter.unusedFintypeInType false in
/-- **The two central characters of the `i`-th ordinary irreducible agree.**  The lattice one is
valued in `𝒪`, the Wedderburn one in `K`, and `algebraMap` matches them. -/
theorem algebraMap_centralScalar_eq (z : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :
    algebraMap 𝒪 K (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i) z)
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i
          (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G)) := by
  classical
  set c : 𝒪 := centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
    (exists_smul_id_of_commute_wedderburnLattice e i) z with hcdef
  -- `z - c` kills the lattice …
  have hψ : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (z : MonoidAlgebra 𝒪 G) = c • LinearMap.id :=
    apply_center_eq_centralScalar_smul K _
      (exists_smul_id_of_commute_wedderburnLattice e i) z
  have hzero : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      ((z : MonoidAlgebra 𝒪 G) - MonoidAlgebra.single 1 c) = 0 := by
    rw [map_sub, hψ, Representation.asAlgebraHom_single, map_one, Module.End.one_eq_id, sub_self]
  -- … hence kills the ambient space
  have hamb := asAlgebraHom_eq_zero_of_latticeRepresentation (wedderburnRepresentation e i)
    (invariant_wedderburnLattice e i) hzero
  rw [map_sub, MonoidAlgebra.mapRingHom_single, map_sub,
    Representation.asAlgebraHom_single, map_one, Module.End.one_eq_id, sub_eq_zero] at hamb
  -- and the ambient action is the `i`-th matrix block
  rw [asAlgebraHom_wedderburnRepresentation] at hamb
  have hmat : e (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G)) i
      = Matrix.scalar (m i) (algebraMap 𝒪 K c) := by
    refine (Matrix.toLinAlgEquiv' (R := K) (n := m i)).injective ?_
    have hL : Matrix.toLinAlgEquiv'
        (e (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G)) i)
        = (algebraMap 𝒪 K c) • LinearMap.id := hamb
    rw [hL]
    ext v
    simp [Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal, Finset.sum_ite_eq,
      Algebra.smul_def]
  have hcentral : (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G))
      ∈ Set.center (MonoidAlgebra K G) :=
    Semigroup.mem_center_iff.mpr
      (Subalgebra.mem_center_iff.mp (OddOrder.mapRingHom_mem_center (algebraMap 𝒪 K) z.2))
  have hscal := MatrixModule.scalar_centralScalar e.toAlgHom.toRingHom i e.surjective hcentral
  have hboth : Matrix.scalar (m i) (MatrixModule.centralScalar e.toAlgHom.toRingHom i
      (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G)))
      = Matrix.scalar (m i) (algebraMap 𝒪 K c) := hscal.symm.trans hmat
  have := congrFun (congrFun hboth (Classical.arbitrary (m i))) (Classical.arbitrary (m i))
  simpa [Matrix.scalar_apply] using this.symm

end OddOrder.RepresentationTheory.Modular
