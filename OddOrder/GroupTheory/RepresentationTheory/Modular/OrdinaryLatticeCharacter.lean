/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import OddOrder.Algebra.CentralCharacter
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeCentralCharacter

/-!
# The `K`-side and the `𝒪`-side central characters agree

An ordinary irreducible `χ` carries two central characters in this development:

* `ω^𝒪_χ : Z(𝒪G) →ₐ[𝒪] 𝒪`, the scalar by which the centre acts on an invariant lattice
  (`LatticeCentralCharacter.centralCharacter`) — this is the one whose *reduction* attaches a
  block to `χ` (`BlockOfLattice`);
* `ω^K_χ : Z(KG) →ₐ[K] K`, the scalar by which the centre acts on the `χ`-block of the Wedderburn
  splitting (`MatrixModule.centralCharacterAlg`) — this is the one appearing in the ordinary
  decomposition of characters (`OrdinaryDecomposition`).

They are the same scalar seen in two rings.  Navarro (5.2) needs to move between them: the block
idempotent `f_b` is recognised by `ω^K` (it selects `Irr(b)` in the character decomposition) but
its block is decided by the reduction of `ω^𝒪`.

The identification of the base-changed lattice with the block is carried as a hypothesis — an
intertwining `K`-linear equivalence — because supplying it is a separate matter (for the Wedderburn
components it comes from `OrdinaryIrreducibles.wedderburnLattice`).

## Main results

* `OddOrder.RepresentationTheory.Modular.centralCharacterAlg_eq_algebraMap_centralScalar`
-/

namespace OddOrder.RepresentationTheory.Modular

open TensorProduct MonoidAlgebra

variable {𝒪 K G : Type*} [CommRing 𝒪] [Field K] [Algebra 𝒪 K] [FaithfulSMul 𝒪 K]
  [Group G]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Nontrivial L]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]

variable (K) in
omit [Finite ι] in
/-- **The two central characters of an ordinary irreducible agree.**  If the base change of the
lattice representation is the `i`-th block — via a `K`-linear equivalence intertwining the two
actions — then the block's central character is the image of the lattice's. -/
theorem centralCharacterAlg_eq_algebraMap_centralScalar
    (ψ : MonoidAlgebra 𝒪 G →ₐ[𝒪] Module.End 𝒪 L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] L),
      (∀ a : MonoidAlgebra 𝒪 G,
        E * LinearMap.baseChange K (ψ a) = LinearMap.baseChange K (ψ a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    {π : MonoidAlgebra K G →+* ∀ j, Matrix (nn j) (nn j) K} (hπ : Function.Surjective π)
    (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a) (i : ι)
    (e : (K ⊗[𝒪] L) ≃ₗ[K] (nn i → K))
    (hint : ∀ (a : MonoidAlgebra 𝒪 G) (v : K ⊗[𝒪] L),
      letI := MatrixModule.blockModule nn π i
      e (LinearMap.baseChange K (ψ a) v)
        = (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a) • e v)
    (z : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))
    (zK : Subalgebra.center K (MonoidAlgebra K G))
    (hzK : (zK : MonoidAlgebra K G)
      = MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (z : MonoidAlgebra 𝒪 G)) :
    MatrixModule.centralCharacterAlg π i hπ hlin zK
      = algebraMap 𝒪 K (centralScalar K ψ hEnd z) := by
  letI := MatrixModule.blockModule nn π i
  refine (MatrixModule.eq_centralCharacterAlg_of_forall_smul_eq π i hπ hlin fun v => ?_).symm
  obtain ⟨w, rfl⟩ := e.surjective v
  rw [hzK, ← hint (z : MonoidAlgebra 𝒪 G) w,
    show LinearMap.baseChange K (ψ (z : MonoidAlgebra 𝒪 G)) w
      = algebraMap 𝒪 K (centralScalar K ψ hEnd z) • w from by
      rw [baseChange_apply_center K ψ hEnd K z]; rfl,
    map_smul]

end OddOrder.RepresentationTheory.Modular
