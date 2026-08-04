/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerLinearIndependence
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionMatrix

/-!
# Uniqueness of the decomposition numbers

`exists_decomposition_trace` produces *some* family `d : ι → ℕ` with
`χ(g) = ∑_φ d_φ φ(g)` for `p`-regular `g`.  For the decomposition matrix `D` — and hence for the
Cartan matrix `C = DᵀD` — that family has to be a *function* of `χ`, so the multiplicities must
be pinned down.  They are: the irreducible Brauer characters are linearly independent on the
`p`-regular classes (`eq_zero_of_sum_irreducibleBrauerCharacter`), so two decompositions of the
same class function differ by a relation, which vanishes.

The only work is plumbing.  The independence theorem is stated for an `AlgHom` into an abstract
`B` carrying an `AlgEquiv` onto the matrix product, and asks for the kernel to be *uniformly
nilpotent*; `exists_decomposition_trace` is stated for a bare `RingHom` onto the matrix product
with `ker π = J(kG)`.  `exists_pow_eq_zero_of_ker_eq_jacobson` converts the kernel hypothesis
(the Jacobson radical of a finite-dimensional algebra is nilpotent) and `AlgHom.mk'` together
with `AlgEquiv.refl` converts the map.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_pow_eq_zero_of_ker_eq_jacobson`
* `OddOrder.RepresentationTheory.Modular.eq_of_sum_irreducibleBrauerCharacter_eq`
* `OddOrder.RepresentationTheory.Modular.existsUnique_decomposition_trace`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [Fintype ι] [∀ i, Nonempty (nn i)] in
/-- **A kernel equal to the Jacobson radical is uniformly nilpotent.**  `kG` is a finite
dimensional algebra over a field, hence Artinian, hence semiprimary, so `J(kG)^N = 0` for a
single `N`. -/
theorem exists_pow_eq_zero_of_ker_eq_jacobson
    {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G)) :
    ∃ N : ℕ, ∀ y : MonoidAlgebra (ResidueField 𝒪) G, π y = 0 → y ^ N = 0 := by
  haveI : IsArtinianRing (MonoidAlgebra (ResidueField 𝒪) G) :=
    isArtinian_of_tower (ResidueField 𝒪) inferInstance
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := MonoidAlgebra (ResidueField 𝒪) G)
  refine ⟨N, fun y hy => ?_⟩
  have hyJ : y ∈ Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G) := by
    rw [← hkerJ]; exact hy
  have hpow := Ideal.pow_mem_pow hyJ N
  rw [hN] at hpow
  simpa using hpow

/-- **The decomposition numbers are unique.**  Two `ℕ`-coefficient families that give the same
values on the `p`-regular classes are equal, because their difference is a relation among the
irreducible Brauer characters. -/
theorem eq_of_sum_irreducibleBrauerCharacter_eq (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
    {d d' : ι → ℕ}
    (h : ∀ g : G, IsPRegular p g →
      ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g
        = ∑ i, (d' i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g) :
    d = d' := by
  classical
  obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_ker_eq_jacobson hkerJ
  -- package the bare ring hom as an algebra hom onto the matrix product
  set πA : MonoidAlgebra (ResidueField 𝒪) G →ₐ[ResidueField 𝒪]
      (∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)) := AlgHom.mk' π hlin with hπA
  have hcoe : ((AlgEquiv.refl (A₁ := ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))
      (R := ResidueField 𝒪)).toAlgHom.comp πA).toRingHom = π := rfl
  -- the difference of the two families is a relation, hence zero
  have hrel : ∀ g : G, IsPRegular p g →
      ∑ i, ((d i : 𝒪) - (d' i : 𝒪)) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        ((AlgEquiv.refl (A₁ := ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))
          (R := ResidueField 𝒪)).toAlgHom.comp πA).toRingHom i g = 0 := by
    intro g hg
    rw [hcoe]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [h g hg, sub_self]
  have hzero := eq_zero_of_sum_irreducibleBrauerCharacter (𝒪 := 𝒪) (nn := nn) hp hω
    (π := πA) hπ hN (AlgEquiv.refl) _ hrel
  funext i
  have hi : (d i : 𝒪) - (d' i : 𝒪) = 0 := congrFun hzero i
  exact_mod_cast sub_eq_zero.mp hi

/-- **Existence and uniqueness of the decomposition of an ordinary character.**  This is what
makes the decomposition matrix `D` well defined: the multiplicities are a function of the
representation, not just a witness. -/
theorem existsUnique_decomposition_trace
    {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
    (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
    {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
    (ρ : Representation 𝒪 G L) :
    ∃! d : ι → ℕ, ∀ g : G, IsPRegular p g →
      LinearMap.trace 𝒪 L (ρ g)
        = ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g := by
  obtain ⟨d, hd⟩ := exists_decomposition_trace (nn := nn) hp hω hω' hπ hlin hkerJ ρ
  refine ⟨d, hd, fun d' hd' => ?_⟩
  exact eq_of_sum_irreducibleBrauerCharacter_eq hp hω' hπ hlin hkerJ
    (fun g hg => by rw [← hd' g hg, hd g hg])

section DecompositionNumber

variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (ρ : Representation 𝒪 G L)

/-- **The decomposition numbers `d_{χφ}` of a lattice representation.**  Ranging `ρ` over
representatives of `Irr(G)` this is the row of the decomposition matrix `D` at `χ`; the Cartan
matrix is `C = DᵀD`.

Well defined by `existsUnique_decomposition_trace`. -/
noncomputable def decompositionNumber : ι → ℕ :=
  (existsUnique_decomposition_trace (nn := nn) hp hω hω' hπ hlin hkerJ ρ).choose

/-- **The defining property of the decomposition numbers**: on the `p`-regular classes the
ordinary character is the `ℕ`-combination of the irreducible Brauer characters they prescribe. -/
theorem trace_eq_sum_decompositionNumber (g : G) (hg : IsPRegular p g) :
    LinearMap.trace 𝒪 L (ρ g)
      = ∑ i, (decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ ρ i : 𝒪)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g :=
  (existsUnique_decomposition_trace (nn := nn) hp hω hω' hπ hlin hkerJ ρ).choose_spec.1 g hg

/-- **Anything satisfying the defining property *is* the family of decomposition numbers.**  This
is the form in which uniqueness gets used: identify `d` by exhibiting one decomposition. -/
theorem eq_decompositionNumber {d : ι → ℕ}
    (hd : ∀ g : G, IsPRegular p g →
      LinearMap.trace 𝒪 L (ρ g)
        = ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g) :
    d = decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ ρ :=
  (existsUnique_decomposition_trace (nn := nn) hp hω hω' hπ hlin hkerJ ρ).choose_spec.2 d hd

end DecompositionNumber

end OddOrder.RepresentationTheory.Modular
