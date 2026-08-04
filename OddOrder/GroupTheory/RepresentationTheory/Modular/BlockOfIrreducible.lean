/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfLattice
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeBaseChange
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryBlockSplitting

/-!
# The block of an ordinary irreducible character

`BlockOfLattice.blockOfLattice` attaches a block of `kG` to an *absolutely irreducible*
`𝒪`-lattice.  With `LatticeBaseChange.exists_smul_id_of_commute_baseChange` the absolute
irreducibility of a Wedderburn component is no longer a hypothesis but a theorem, so the
construction applies to the ordinary irreducibles themselves:

`blockOfIrr e i : Bl(G)`  — the block of `χ_i`.

This is what makes `Irr(B) = {i | blockOfIrr e i = B}` a definable set, and hence what the
`B`-parts of class functions in Navarro (5.10)–(5.13) are indexed by.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockOfIrr` — the block of `χ_i`

## Main results

* `OddOrder.RepresentationTheory.Modular.nontrivial_of_isLattice` — a lattice in a nonzero space
  is nonzero
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.MatrixModule
open scoped TensorProduct

/-! ### A lattice in a nonzero space is nonzero -/

section Nontrivial

variable {𝒪 K V : Type*} [CommRing 𝒪] [Field K] [Algebra 𝒪 K] [AddCommGroup V] [Module K V]
  [Module 𝒪 V] [IsScalarTower 𝒪 K V]

/-- **A lattice in a nonzero space is nonzero**: it spans, and the zero submodule does not. -/
theorem nontrivial_of_isLattice [Nontrivial V] (L : Submodule 𝒪 V) [L.IsLattice K] :
    Nontrivial ↥L := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hbot : L = ⊥ := by
    refine Submodule.eq_bot_of_subsingleton
  have htop := Submodule.IsLattice.span_eq_top (A := K) (M := L)
  rw [hbot] at htop
  simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
  exact absurd htop bot_ne_top

end Nontrivial

/-! ### The block of `χ_i` -/

section Wedderburn

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

/-- **Absolute irreducibility of the `i`-th ordinary irreducible**, in the form
`blockOfLattice` consumes. -/
theorem exists_smul_id_of_commute_wedderburnLattice (i : ι')
    (E : Module.End K (K ⊗[𝒪] ↥(wedderburnLattice (𝒪 := 𝒪) e i)))
    (hE : ∀ a : MonoidAlgebra 𝒪 G,
      E * LinearMap.baseChange K
          ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom a)
        = LinearMap.baseChange K
            ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom a) * E) :
    ∃ c : K, E = c • LinearMap.id :=
  exists_smul_id_of_commute_baseChange (surjective_algEquiv e) (smul_algEquiv e) i
    (invariant_wedderburnLattice e i) E hE

instance nontrivial_wedderburnLattice [∀ i, Nonempty (m i)] (i : ι') :
    Nontrivial ↥(wedderburnLattice (𝒪 := 𝒪) e i) :=
  nontrivial_of_isLattice (K := K) _

end Wedderburn

section BlockOfIrr

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

/-- **The block of the `i`-th ordinary irreducible character.**  Navarro (3.11): the unique block
whose central character is the reduction of `ω_{χ_i}`. -/
noncomputable def blockOfIrr (i : ι') : Block πG hπG hlinG :=
  blockOfLattice K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
    (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG

end BlockOfIrr

end OddOrder.RepresentationTheory.Modular
