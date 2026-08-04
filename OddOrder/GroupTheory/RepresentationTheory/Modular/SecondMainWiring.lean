/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerBasis
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryBlockSplitting

/-!
# Discharging the hypotheses of Navarro (5.2)

`SecondMainCore.blockCoeff_eq_zero_of_vanishing` is stated for abstract data: a family `d` of
multiplicities, a matrix `D`, a family `φ` of functions, an independence hypothesis, a vanishing
hypothesis and a block-diagonality hypothesis.  This file supplies the two of those that are not
immediate from `OrdinaryDecomposition`, for the actual `p`-modular system:

* **independence** — the irreducible Brauer characters are `K`-independent on the `p`-regular
  classes (`BrauerBasis`, transported from the `vecMul` form);
* **block diagonality** — if the ordinary irreducible `χ_i` has `d_{iφ} ≠ 0` for some
  `φ ∈ IBr(b)`, then `ω^K_i(f_b) = 1`.

The second is the one with content.  It runs down the three group algebras: `ω^K_i(f_b)` is an
idempotent of `K`, hence `0` or `1`; if it were `0` then `f_b` would kill the `i`-th ordinary
irreducible, hence its lattice, hence the reduction of that lattice — and then block-diagonality
of the decomposition numbers (`centralCharacterAlg_eq_of_decompositionNumber_ne_zero`) would give
`0 = ω^k_φ(f̄_b) = 1`.

⚠ Note that no absolute irreducibility (`hEnd`) is needed: the scalar by which `f_b` acts comes
straight from the block structure of `K[H]`, not from a commutant argument.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter`
* `OddOrder.RepresentationTheory.Modular.centralCharacterAlg_eq_one_of_decompositionMatrix_ne_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))

/-! ### Independence of the irreducible Brauer characters over `K` -/

include hp hω' hπ hlin hkerJ in
/-- **The irreducible Brauer characters are `K`-independent on the `p`-regular classes.**  This is
`existsUnique_coeff_irreducibleBrauerCharacter` for the zero class function. -/
theorem eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter (c : ι → K)
    (hc : ∀ g : G, IsPRegular p g →
      ∑ j, c j * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π j g) = 0) :
    c = 0 := by
  obtain ⟨d, -, huniq⟩ := existsUnique_coeff_irreducibleBrauerCharacter (K := K) hp hω' hπ hlin
    hkerJ (fun _ => 0) fun _ _ _ => rfl
  exact (huniq c hc).trans (huniq 0 fun _ _ => by simp).symm

/-! ### Block diagonality of the decomposition numbers, over `K` -/

section BlockDiagonality

variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

include hp hω hω' hπ hlin hkerJ in
/-- **Block diagonality of the decomposition matrix, read through `K`.**  If the irreducible
Brauer character `φ_j` occurs in the ordinary irreducible `χ_i`, and `φ_j` lies in the block cut
out by the idempotent `f` — that is `ω^k_j(f̄) = 1` — then `ω^K_i(f) = 1` as well, i.e. `χ_i` lies
in that block too.

This is the hypothesis `hblock` of `blockCoeff_eq_zero_of_vanishing`, in contrapositive form. -/
theorem centralCharacterAlg_eq_one_of_decompositionMatrix_ne_zero (i : ι') (j : ι)
    {f𝒪 : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {fK : Subalgebra.center K (MonoidAlgebra K G)}
    (hfK : MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (f𝒪 : MonoidAlgebra 𝒪 G)
      = (fK : MonoidAlgebra K G))
    {fk : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hfk : MonoidAlgebra.mapRingHom G (residue 𝒪) (f𝒪 : MonoidAlgebra 𝒪 G)
      = (fk : MonoidAlgebra (ResidueField 𝒪) G))
    (hidem : IsIdempotentElem fK)
    (hj : MatrixModule.centralCharacterAlg π j hπ hlin fk = 1)
    (hD : decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i j ≠ 0) :
    MatrixModule.centralCharacterAlg (e.toAlgHom.toRingHom) i (surjective_algEquiv e)
      (smul_algEquiv e) fK = 1 := by
  rcases centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem (surjective_algEquiv e)
    (smul_algEquiv e) i hidem with h0 | h1
  · exfalso
    -- `f` kills the `i`-th ordinary irreducible …
    have hzeroK : (wedderburnRepresentation e i).asAlgebraHom (fK : MonoidAlgebra K G) = 0 := by
      rw [← blockRepresentation_algEquiv e i, blockRepresentation_asAlgebraHom_center
        (surjective_algEquiv e) (smul_algEquiv e) i fK, h0, zero_smul]
    -- … hence its lattice …
    have hzeroL : (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom
        (f𝒪 : MonoidAlgebra 𝒪 G) = 0 :=
      latticeRepresentation_asAlgebraHom_eq_zero _ _ (by rw [hfK]; exact hzeroK)
    -- … hence the reduction of that lattice.
    have hred : (reduction (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i)).asAlgebraHom
        (fk : MonoidAlgebra (ResidueField 𝒪) G) = (0 : ResidueField 𝒪) • LinearMap.id := by
      rw [← hfk, asAlgebraHom_reduction_mapRingHom, hzeroL, LinearMap.baseChange_zero, zero_smul]
    have hcontra := centralCharacterAlg_eq_of_decompositionNumber_ne_zero hp hω hω' hπ hlin hkerJ
      (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i) hD hred
    rw [hj] at hcontra
    exact zero_ne_one hcontra
  · exact h1

end BlockDiagonality

end OddOrder.RepresentationTheory.Modular
