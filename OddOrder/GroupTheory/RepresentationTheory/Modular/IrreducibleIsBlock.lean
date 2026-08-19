/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockOfSimpleModule
import OddOrder.GroupTheory.RepresentationTheory.Modular.IrreducibleBrauerCharacter

/-!
# An irreducible representation has one of the irreducible Brauer characters

The module classification (`Algebra/PiMatrixSimpleModules`) says a simple `kG`-module annihilated
by `ker π` is a block; `Representation.asModule` turns a representation into such a module and
`Representation.asModuleEquiv_symm_map_rho` says the group acts through `single g 1`.  Composing,
a `kG`-linear isomorphism onto a block restricts to a `k`-linear intertwiner, and
`brauerCharacter_congr` translates it into an equality of Brauer characters.

This is the step that makes the decomposition numbers meaningful: every composition factor of a
`kG`-module contributes one of the `irreducibleBrauerCharacter π i`.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_irreducibleBrauerCharacter_eq`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Finite ι] [∀ i, Nonempty (nn i)]
variable {V : Type*} [AddCommGroup V] [Module (ResidueField 𝒪) V]

omit [IsPModularSystem p 𝒪] [Finite G] in
/-- **An irreducible `kG`-representation has one of the irreducible Brauer characters.**

`hlin` says the splitting surjection is `k`-linear (it is, being built from algebra maps); it is
what makes a `kG`-linear isomorphism restrict to a `k`-linear one. -/
theorem exists_irreducibleBrauerCharacter_eq (ρ : Representation (ResidueField 𝒪) G V)
    [IsSimpleModule (MonoidAlgebra (ResidueField 𝒪) G) ρ.asModule]
    {π : MonoidAlgebra (ResidueField 𝒪) G →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)} (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G),
      π (c • a) = c • π a)
    (hker : RingHom.ker π ≤ Module.annihilator (MonoidAlgebra (ResidueField 𝒪) G) ρ.asModule) :
    ∃ i : ι, (∀ g : G,
        brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g
          = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g) ∧
      ∀ {z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
        {c : ResidueField 𝒪},
        (∀ m : ρ.asModule, (z : MonoidAlgebra (ResidueField 𝒪) G) • m
          = (algebraMap (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G) c) • m) →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  obtain ⟨i, ⟨e⟩⟩ := MatrixModule.exists_linearEquiv_blockModule (nn := nn) hπ hker
  let := MatrixModule.blockModule nn π i
  have := MatrixModule.isScalarTower_blockModule (nn := nn) hlin i
  -- the `kG`-linear isomorphism, restricted to the scalars, is an intertwiner
  refine ⟨i, fun g => ?_, fun {z c} hzc => ?_⟩
  · set f : V ≃ₗ[ResidueField 𝒪] (nn i → ResidueField 𝒪) :=
      (ρ.asModuleEquiv.symm).trans (e.restrictScalars (ResidueField 𝒪)) with hf
    have hint : ∀ (g : G) (v : V), f ((ρ g) v) = (blockRepresentation π i g) (f v) := by
      intro g v
      have h1 : ρ.asModuleEquiv.symm ((ρ g) v)
          = (single g (1 : ResidueField 𝒪)) • ρ.asModuleEquiv.symm v :=
        Representation.asModuleEquiv_symm_map_rho ρ g v
      simp only [hf, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1]
      rw [e.map_smul]
      rfl
    exact brauerCharacter_congr ρ (blockRepresentation π i) f hint g
  · refine MatrixModule.eq_centralCharacterAlg_of_forall_smul_eq π i hπ hlin fun v => ?_
    have hv := congrArg e (hzc (e.symm v))
    rw [map_smul, map_smul, e.apply_symm_apply] at hv
    rw [hv, algebraMap_smul]

end OddOrder.RepresentationTheory.Modular
