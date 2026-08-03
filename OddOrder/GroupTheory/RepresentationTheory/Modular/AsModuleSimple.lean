/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Irreducible representations have simple `asModule`

The module-theoretic classification of the blocks (`Algebra/PiMatrixSimpleModules`) speaks about
`IsSimpleModule (kG) M`, while a representation is naturally described by its lattice of
`G`-invariant subspaces.  The two agree: a `kG`-submodule of `ρ.asModule` is exactly an invariant
subspace, transported by `ρ.asModuleEquiv`.

Only the direction needed downstream is recorded — from "no proper nonzero invariant subspace" to
`IsSimpleModule` — since that is what feeds `exists_irreducibleBrauerCharacter_eq`.

## Main results

* `OddOrder.RepresentationTheory.Modular.isSimpleModule_asModule`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

/-- The invariant subspace of `V` underlying a `kG`-submodule of `ρ.asModule`. -/
noncomputable def toInvariantSubspace (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    Submodule k V :=
  (N.restrictScalars k).map (ρ.asModuleEquiv : ρ.asModule →ₗ[k] V)

theorem asModuleEquiv_smul_of (g : G) (m : ρ.asModule) :
    ρ.asModuleEquiv (of k G g • m) = (ρ g) (ρ.asModuleEquiv m) := by
  have h := Representation.asModuleEquiv_symm_map_rho ρ g (ρ.asModuleEquiv m)
  rw [ρ.asModuleEquiv.symm_apply_apply] at h
  rw [← h, ρ.asModuleEquiv.apply_symm_apply]

/-- The subspace attached to a submodule is `G`-invariant. -/
theorem invariant_toInvariantSubspace (N : Submodule (MonoidAlgebra k G) ρ.asModule) (g : G) :
    toInvariantSubspace ρ N ≤ (toInvariantSubspace ρ N).comap (ρ g) := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨of k G g • m, N.smul_mem _ hm, asModuleEquiv_smul_of ρ g m⟩

/-- **A representation with no proper nonzero invariant subspace has simple `asModule`.**  This
is the bridge from the representation-theoretic notion of irreducibility to the module-theoretic
one used by the classification of the blocks. -/
theorem isSimpleModule_asModule [Nontrivial V]
    (h : ∀ W : Submodule k V, (∀ g : G, W ≤ W.comap (ρ g)) → W = ⊥ ∨ W = ⊤) :
    IsSimpleModule (MonoidAlgebra k G) ρ.asModule := by
  haveI : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  refine { eq_bot_or_eq_top := fun N => ?_ }
  rcases h _ (invariant_toInvariantSubspace ρ N) with hbot | htop
  · left
    simpa only [toInvariantSubspace, Submodule.map_eq_bot_iff,
      Submodule.restrictScalars_eq_bot_iff] using hbot
  · right
    simpa only [toInvariantSubspace, Submodule.map_eq_top_iff,
      Submodule.restrictScalars_eq_top_iff] using htop

end OddOrder.RepresentationTheory.Modular
