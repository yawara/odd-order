/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockOfSimpleModule
import OddOrder.GroupTheory.RepresentationTheory.Modular.MinimalSubrepresentation

/-!
# The block of a representation whose centre acts by a scalar

If the centre of `k[G]` acts on a representation by a single scalar `c`, then `c` is the central
character of one of the blocks.  Take a minimal invariant subspace: it is simple, the scalar
action restricts to it, and a simple module is a block.

This is the assembly of the four pieces:

1. `exists_minimal_invariant` — a nonzero finite-dimensional representation has one;
2. `isSimpleModule_subrepresentation_of_minimal` — it is simple;
3. `subrepresentation_asAlgebraHom_eq_smul` — the scalar action restricts to it;
4. `MatrixModule.exists_eq_centralCharacterAlg_of_forall_smul_eq` — a simple module is a block.

Applied to the reduction of an absolutely irreducible `𝒪`-lattice — where the centre acts by
`λ_χ = residue ∘ ω_χ` (`baseChange_apply_center` composed with
`asAlgebraHom_reduction_mapRingHom`) — this attaches a block to an ordinary character, which is
Navarro's Chapter 3 (3.1)/(3.3).

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_eq_centralCharacterAlg_of_asAlgebraHom_eq_smul`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra

variable {k G V ι : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
  [Finite ι]

/-- **A representation on which the centre acts by a scalar lies in a block**, and the scalar is
that block's central character. -/
theorem exists_eq_centralCharacterAlg_of_asAlgebraHom_eq_smul
    (ρ : Representation k G V) [FiniteDimensional k V] [Nontrivial V]
    {π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra k G))
    {z : Subalgebra.center k (MonoidAlgebra k G)} {c : k}
    (hz : ρ.asAlgebraHom (z : MonoidAlgebra k G) = c • LinearMap.id) :
    ∃ i : ι, c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  classical
  obtain ⟨W, hWinv, hWne, hWmin⟩ := exists_minimal_invariant ρ
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  have := isSimpleModule_subrepresentation_of_minimal ρ hWinv hWne hWmin
  refine MatrixModule.exists_eq_centralCharacterAlg_of_forall_smul_eq (nn := nn)
    (M := (ρ.subrepresentation W hWinv).asModule) hπ hlin
    (hkerJ ▸ IsSemisimpleModule.jacobson_le_annihilator _ _) fun m => ?_
  apply (ρ.subrepresentation W hWinv).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
    subrepresentation_asAlgebraHom_eq_smul ρ hWinv hz, AlgHom.commutes]
  simp

end OddOrder.RepresentationTheory.Modular
