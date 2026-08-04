/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfIrreducible
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionNumber

/-!
# The Cartan matrix is block diagonal

`C = DᵀD`, so `c_{μφ} = ∑_χ d_{χμ} d_{χφ}`.  If a term is nonzero then the same ordinary
character `χ` involves both `φ_μ` and `φ_φ`, and then the centre of `kG` acts on the reduction of
`χ`'s lattice by a single scalar which has to be *both* central characters
(`centralCharacterAlg_eq_of_decompositionNumber_ne_zero`).  So `μ` and `φ` lie in the same block,
and `c_{μφ} = 0` whenever they do not.

The scalar itself comes from the `𝒪`-side: a central `z ∈ Z(kG)` lifts to `Z(𝒪G)`, which acts on
an absolutely irreducible lattice by `ω_χ(z)` (`apply_center_eq_centralScalar_smul`), and
reduction is compatible with the whole group-algebra action
(`asAlgebraHom_reduction_mapRingHom`).

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_smul_id_asAlgebraHom_reduction`
* `OddOrder.RepresentationTheory.Modular.centralCharacterAlg_eq_of_decompositionMatrix_ne_zero` —
  two Brauer characters occurring in the same ordinary character have the same central character
* `OddOrder.RepresentationTheory.Modular.cartanMatrix_eq_zero_of_centralCharacterAlg_ne`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.GroupTheory.CenterClassSum

open scoped TensorProduct

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  [Nontrivial L]

set_option linter.unusedFintypeInType false in
omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] [Module.Finite 𝒪 L] in
/-- **The centre acts on the reduction of an absolutely irreducible lattice by a scalar.**  A
central `z ∈ Z(kG)` lifts to `Z(𝒪G)`, which acts by `ω_χ(z)`; reduction carries that through. -/
theorem exists_smul_id_asAlgebraHom_reduction (ρ : Representation 𝒪 G L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] L),
      (∀ a : MonoidAlgebra 𝒪 G,
        E * LinearMap.baseChange K (ρ.asAlgebraHom a)
          = LinearMap.baseChange K (ρ.asAlgebraHom a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    (z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)) :
    ∃ c : ResidueField 𝒪,
      (reduction ρ).asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G) = c • LinearMap.id := by
  classical
  set c : 𝒪 := centralScalar K ρ.asAlgebraHom hEnd
    (centerLift (residue_surjective (R := 𝒪)) z) with hc
  refine ⟨residue 𝒪 c, ?_⟩
  have hbase : (reduction ρ).asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G)
      = LinearMap.baseChange (ResidueField 𝒪) (ρ.asAlgebraHom
          ((centerLift (residue_surjective (R := 𝒪)) z :
            Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) : MonoidAlgebra 𝒪 G)) := by
    rw [← mapRingHom_centerLift (residue_surjective (R := 𝒪)) z,
      asAlgebraHom_reduction_mapRingHom]
  have halg : residue 𝒪 c = algebraMap 𝒪 (ResidueField 𝒪) c := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  rw [hbase, apply_center_eq_centralScalar_smul K ρ.asAlgebraHom hEnd, ← hc,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, halg]
  exact (algebraMap_smul (ResidueField 𝒪) c LinearMap.id).symm


variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

set_option linter.unusedFintypeInType false in
omit [Fintype ι'] in
include hp hω hω' hπ hlin hkerJ in
/-- **Two Brauer characters occurring in the same ordinary character have the same central
character.**  This is the block diagonality of the decomposition matrix. -/
theorem centralCharacterAlg_eq_of_decompositionMatrix_ne_zero (i : ι') {μ φ : ι}
    (hμ : decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i μ ≠ 0)
    (hφ : decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ ≠ 0) :
    MatrixModule.centralCharacterAlg π μ hπ hlin
      = MatrixModule.centralCharacterAlg π φ hπ hlin := by
  classical
  refine AlgHom.ext fun z => ?_
  obtain ⟨c, hc⟩ := exists_smul_id_asAlgebraHom_reduction (K := K)
    (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i)
    (exists_smul_id_of_commute_wedderburnLattice (𝒪 := 𝒪) e i) z
  rw [← centralCharacterAlg_eq_of_decompositionNumber_ne_zero (nn := nn) hp hω hω' hπ hlin hkerJ
      _ hμ hc,
    ← centralCharacterAlg_eq_of_decompositionNumber_ne_zero (nn := nn) hp hω hω' hπ hlin hkerJ
      _ hφ hc]

set_option linter.unusedFintypeInType false in
include hp hω hω' hπ hlin hkerJ in
/-- **The Cartan matrix is block diagonal**: `c_{μφ} = 0` unless `μ` and `φ` have the same central
character. -/
theorem cartanMatrix_eq_zero_of_centralCharacterAlg_ne {μ φ : ι}
    (h : MatrixModule.centralCharacterAlg π μ hπ hlin
      ≠ MatrixModule.centralCharacterAlg π φ hπ hlin) :
    cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e μ φ = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => ?_
  by_contra hne
  obtain ⟨hμ, hφ⟩ := Nat.mul_ne_zero_iff.mp hne
  exact h (centralCharacterAlg_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ e i hμ hφ)

end OddOrder.RepresentationTheory.Modular
