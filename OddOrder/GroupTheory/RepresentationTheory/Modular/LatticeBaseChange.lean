/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockRepresentation
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBridge

/-!
# A lattice recovers its ambient space after base change

For a lattice `L ⊆ V` over `𝒪` with fraction field `K`, the canonical map

`K ⊗[𝒪] L → V`,  `c ⊗ v ↦ c • v`

is an isomorphism: a basis of `L` base-changes to a basis of `K ⊗[𝒪] L`
(`Module.Basis.baseChange`) and extends to a basis of `V`
(`Module.Basis.extendOfIsLattice`), and the map matches them up.

This is the identification that `OrdinaryLatticeCharacter` and `BlockOfLattice` carry as a
hypothesis: the absolute irreducibility condition `hEnd` and the comparison of the two central
characters are both stated on `K ⊗[𝒪] L`, whereas everything that is known about the ordinary
irreducible lives on `V`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.latticeBaseChangeEquiv` — `K ⊗[𝒪] L ≃ₗ[K] V`

## Main results

* `OddOrder.RepresentationTheory.Modular.latticeBaseChangeEquiv_tmul`
* `OddOrder.RepresentationTheory.Modular.latticeBaseChangeEquiv_baseChange` — it intertwines the
  base-changed lattice action with the ambient action
* `OddOrder.RepresentationTheory.Modular.exists_smul_id_of_commute_baseChange` — **absolute
  irreducibility of a Wedderburn component**, in the form `BlockOfLattice` asks for
-/

namespace OddOrder.RepresentationTheory.Modular

open Module TensorProduct
open scoped Matrix

variable {𝒪 K V : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪] [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] [AddCommGroup V] [Module K V] [Module 𝒪 V] [IsScalarTower 𝒪 K V]

variable (K) in
/-- **A lattice recovers its ambient space after base change.**  Both sides carry a basis indexed
by a basis of `L`: `Module.Basis.baseChange` on the left and `Module.Basis.extendOfIsLattice` on
the right. -/
noncomputable def latticeBaseChangeEquiv (L : Submodule 𝒪 V) [L.IsLattice K] :
    (K ⊗[𝒪] ↥L) ≃ₗ[K] V :=
  ((Free.chooseBasis 𝒪 ↥L).baseChange K).equiv
    ((Free.chooseBasis 𝒪 ↥L).extendOfIsLattice K) (Equiv.refl _)

variable (K) in
/-- The equivalence is the canonical map `c ⊗ v ↦ c • v`. -/
theorem coe_latticeBaseChangeEquiv (L : Submodule 𝒪 V) [L.IsLattice K] :
    (latticeBaseChangeEquiv K L : (K ⊗[𝒪] ↥L) →ₗ[K] V)
      = LinearMap.liftBaseChange K L.subtype := by
  refine Basis.ext ((Free.chooseBasis 𝒪 ↥L).baseChange K) fun i => ?_
  rw [LinearEquiv.coe_coe, latticeBaseChangeEquiv, Basis.equiv_apply, Equiv.refl_apply,
    Basis.extendOfIsLattice_apply, Basis.baseChange_apply, LinearMap.liftBaseChange_tmul,
    one_smul]
  rfl

variable (K) in
@[simp]
theorem latticeBaseChangeEquiv_tmul (L : Submodule 𝒪 V) [L.IsLattice K] (c : K) (v : ↥L) :
    latticeBaseChangeEquiv K L (c ⊗ₜ v) = c • (v : V) := by
  rw [show latticeBaseChangeEquiv K L (c ⊗ₜ v)
      = (latticeBaseChangeEquiv K L : (K ⊗[𝒪] ↥L) →ₗ[K] V) (c ⊗ₜ v) from rfl,
    coe_latticeBaseChangeEquiv, LinearMap.liftBaseChange_tmul]
  rfl

variable {G : Type*} [Group G]

variable (K) in
/-- **The equivalence intertwines the two group-algebra actions.**  On the left `𝒪G` acts through
the lattice representation, base-changed; on the right `KG` acts on the ambient space, and the two
are matched by the coefficient reduction `𝒪G → KG`. -/
theorem latticeBaseChangeEquiv_baseChange (ρ : Representation K G V) {L : Submodule 𝒪 V}
    [L.IsLattice K] (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) (a : MonoidAlgebra 𝒪 G)
    (w : K ⊗[𝒪] ↥L) :
    latticeBaseChangeEquiv K L
        (LinearMap.baseChange K ((latticeRepresentation ρ hL).asAlgebraHom a) w)
      = ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a)
          (latticeBaseChangeEquiv K L w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, latticeBaseChangeEquiv_tmul, latticeBaseChangeEquiv_tmul,
      map_smul]
    exact congrArg (c • ·) (coe_latticeRepresentation_asAlgebraHom ρ hL a v)
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-! ### Absolute irreducibility of a Wedderburn component -/

section AbsolutelyIrreducible

open MonoidAlgebra

variable {ι' : Type*} {mm : ι' → Type*} [∀ j, Fintype (mm j)] [∀ j, DecidableEq (mm j)]

/-- **The commutant of a base-changed lattice in a block is the scalars.**  Transport of
`MatrixModule.exists_smul_id_of_commute_blockAction` along `latticeBaseChangeEquiv`.

This is exactly the hypothesis `hEnd` of `LatticeCentralCharacter.centralCharacter` and of
`BlockOfLattice.blockOfLattice`, so it is what lets those be applied to the ordinary irreducibles
rather than to an abstract absolutely irreducible lattice. -/
theorem exists_smul_id_of_commute_baseChange
    {π : MonoidAlgebra K G →+* ∀ j, Matrix (mm j) (mm j) K} (hπ : Function.Surjective π)
    (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a) (i : ι')
    {L : Submodule 𝒪 (mm i → K)} [L.IsLattice K]
    (hL : ∀ (g : G), ∀ v ∈ L, blockRepresentation π i g v ∈ L)
    (E : Module.End K (K ⊗[𝒪] ↥L))
    (hE : ∀ a : MonoidAlgebra 𝒪 G,
      E * LinearMap.baseChange K
          ((latticeRepresentation (blockRepresentation π i) hL).asAlgebraHom a)
        = LinearMap.baseChange K
            ((latticeRepresentation (blockRepresentation π i) hL).asAlgebraHom a) * E) :
    ∃ c : K, E = c • LinearMap.id := by
  set eqv := latticeBaseChangeEquiv K L with heqv
  set E' : Module.End K (mm i → K) :=
    (eqv : (K ⊗[𝒪] ↥L) →ₗ[K] (mm i → K)) ∘ₗ E ∘ₗ (eqv.symm : (mm i → K) →ₗ[K] (K ⊗[𝒪] ↥L))
    with hE'def
  have hE'apply : ∀ w : K ⊗[𝒪] ↥L, E' (eqv w) = eqv (E w) := by
    intro w
    rw [hE'def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  -- `E'` commutes with the ambient action of `𝒪G`
  have hcomm : ∀ (a : MonoidAlgebra 𝒪 G) (v : mm i → K),
      E' ((blockRepresentation π i).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a) v)
        = (blockRepresentation π i).asAlgebraHom
            (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a) (E' v) := by
    intro a v
    obtain ⟨w, rfl⟩ := eqv.surjective v
    rw [← latticeBaseChangeEquiv_baseChange K (blockRepresentation π i) hL a w, hE'apply, hE'apply,
      ← latticeBaseChangeEquiv_baseChange K (blockRepresentation π i) hL a (E w)]
    exact congrArg eqv (congrFun (congrArg DFunLike.coe (hE a)) w)
  -- hence with every matrix in the image of the splitting
  have hall : ∀ (a : MonoidAlgebra K G) (v : mm i → K), E' (π a i *ᵥ v) = π a i *ᵥ E' v := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
      intro v
      rw [map_zero, Pi.zero_apply, Matrix.zero_mulVec, Matrix.zero_mulVec, map_zero]
    | add u w hu hw =>
      intro v
      rw [map_add, Pi.add_apply, Matrix.add_mulVec, map_add, hu, hw, Matrix.add_mulVec]
    | single g r =>
      intro v
      have hr : (MonoidAlgebra.single g r : MonoidAlgebra K G)
          = r • MonoidAlgebra.single g (1 : K) := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      have hmono : E' (π (MonoidAlgebra.single g (1 : K)) i *ᵥ v)
          = π (MonoidAlgebra.single g (1 : K)) i *ᵥ E' v := by
        have := hcomm (MonoidAlgebra.single g (1 : 𝒪)) v
        rwa [MonoidAlgebra.mapRingHom_single, map_one,
          Representation.asAlgebraHom_single_one] at this
      rw [hr, hlin, Pi.smul_apply, Matrix.smul_mulVec, map_smul, hmono, Matrix.smul_mulVec]
  obtain ⟨c, hc⟩ := MatrixModule.exists_smul_id_of_commute_blockAction hπ i E' hall
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  have h1 : eqv (E w) = c • eqv w := by
    rw [← hE'apply w, hc]
    rfl
  have h2 : E w = eqv.symm (c • eqv w) := by rw [← h1, LinearEquiv.symm_apply_apply]
  rw [h2, map_smul, LinearEquiv.symm_apply_apply]
  rfl

end AbsolutelyIrreducible

end OddOrder.RepresentationTheory.Modular
