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
* `OddOrder.RepresentationTheory.Modular.exists_blockOfIrr_eq` — `blockOfIrr` is surjective:
  every block contains an ordinary irreducible character
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

/-! ### Every block contains an ordinary irreducible character -/

section Surjective

open IsLocalRing

variable {p : ℕ} [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] [Fintype ι']
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

omit [∀ i, Nonempty (m i)] [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Coefficient maps of group algebras are injective when the coefficient map is.** -/
theorem mapRingHom_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro a b hab
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun x => hf ?_)
  have := congrArg (fun w => (w : MonoidAlgebra S G).coeff x) hab
  simpa [MonoidAlgebra.coeff_mapRingHom] using this

set_option maxHeartbeats 1000000 in
-- The lattice side and the Wedderburn side of the block idempotent are compared under the full
-- modular-datum chain.
set_option linter.unusedFintypeInType false in
/-- **`blockOfIrr` is surjective**: every block of `kG` is the block of some ordinary irreducible
character.

If no `χ_i` had block `B`, then by Navarro (3.13.a) (`apply_eq_zero_of_blockOfLattice_ne`) the
block idempotent `f_B ∈ Z(𝒪G)` would act as `0` on every Wedderburn lattice, hence — the lattice
spanning the ambient space — its image in `K[G]` would act as `0` in every Wedderburn component,
so it would be `0`; and `𝒪 → K` is injective, so `f_B = 0`.  But the reduction of `f_B` has block
character `Pi.single B 1 ≠ 0`. -/
theorem exists_blockOfIrr_eq [DecidableEq (MatrixModule.Block πG hπG hlinG)]
    (B : MatrixModule.Block πG hπG hlinG)
    {fB : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {fB' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : IsIdempotentElem fB)
    (hfB : MonoidAlgebra.mapRingHom G (residue 𝒪) (fB : MonoidAlgebra 𝒪 G)
      = (fB' : MonoidAlgebra (ResidueField 𝒪) G))
    (hB : MatrixModule.blockCharacterPi πG hπG hlinG fB' = Pi.single B 1) :
    ∃ i : ι', blockOfIrr e hπG hlinG hnilG i = B := by
  classical
  by_contra hcon
  push Not at hcon
  -- every Wedderburn lattice kills `f_B`
  have hzero : ∀ j : ι', ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e j).asAlgebraHom)
      (fB : MonoidAlgebra 𝒪 G) = 0 := fun j =>
    apply_eq_zero_of_blockOfLattice_ne K _
      (exists_smul_id_of_commute_wedderburnLattice e j) residue_surjective πG hπG hlinG hnilG
      ker_residue hidem hfB hB (hcon j)
  -- hence so does every Wedderburn component of the image in `K[G]`
  have hmat : ∀ j : ι',
      e (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (fB : MonoidAlgebra 𝒪 G)) j = 0 := by
    intro j
    have hamb := asAlgebraHom_eq_zero_of_latticeRepresentation (wedderburnRepresentation e j)
      (invariant_wedderburnLattice e j) (hzero j)
    rw [asAlgebraHom_wedderburnRepresentation] at hamb
    refine (Matrix.toLinAlgEquiv' (R := K) (n := m j)).injective ?_
    rw [map_zero]
    exact hamb
  have hK : MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (fB : MonoidAlgebra 𝒪 G) = 0 := by
    refine e.injective ?_
    rw [map_zero]
    funext j
    exact hmat j
  have hfB0 : (fB : MonoidAlgebra 𝒪 G) = 0 := by
    refine mapRingHom_injective (f := algebraMap 𝒪 K) (FaithfulSMul.algebraMap_injective 𝒪 K) ?_
    rw [hK, map_zero]
  rw [hfB0, map_zero] at hfB
  rw [show fB' = 0 from Subtype.ext hfB.symm, map_zero] at hB
  have hone := congrFun hB B
  rw [Pi.zero_apply, Pi.single_eq_same] at hone
  exact zero_ne_one hone

end Surjective

end OddOrder.RepresentationTheory.Modular
