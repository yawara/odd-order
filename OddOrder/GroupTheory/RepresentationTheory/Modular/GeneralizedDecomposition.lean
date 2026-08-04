/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerBasis

/-!
# The generalized decomposition numbers — Navarro (5.1)

**Navarro (5.1).**  Let `x ∈ G` and `H = C_G(x)`.  For a class function `χ` of `G` there are
unique `d^x_{χφ}`, indexed by `IBr(H)`, with

`χ(xy) = ∑_{φ ∈ IBr(H)} d^x_{χφ} φ(y)`   for every `p`-regular `y ∈ H`.

Taking `x = 1` recovers the ordinary decomposition numbers; the interest is in `x` a `p`-element,
where the `d^x_{χφ}` extend the decomposition numbers from the `p`-regular classes to the
`p`-sections, and Brauer's second main theorem (5.2) says which of them vanish.

The proof is a two-liner given `existsUnique_coeff_irreducibleBrauerCharacter`: `y ↦ χ(xy)` is a
class function of `H` because `x` is centralised by `H`, so it expands uniquely in `IBr(H)`.

Navarro's own argument decomposes `χ|_H` into `Irr(H)` and uses that `x` acts as a scalar in each
irreducible representation of `H` (`x ∈ Z(H)`); that route also shows `d^x_{χφ} ∈ ℤ[ζ]` for `ζ` a
primitive `o(x)`-th root of unity, which the basis argument does not see and which is not proved
here.  ⚠ Nothing below needs `x` to be a `p`-element.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber` — `d^x_{χφ}`

## Main results

* `OddOrder.RepresentationTheory.Modular.existsUnique_generalizedDecomposition` — Navarro (5.1)
* `OddOrder.RepresentationTheory.Modular.sum_generalizedDecompositionNumber`
* `OddOrder.RepresentationTheory.Modular.eq_generalizedDecompositionNumber`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Finite ι] [Fintype ι]
  [∀ i, Nonempty (nn i)]
variable (x : G)

/-- `C_G(x)`, the group over which the generalized decomposition numbers are indexed. -/
abbrev centralizerOf : Subgroup G := Subgroup.centralizer ({x} : Set G)

variable (hp : p.Prime)
  {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))

omit [Finite G] in
/-- Multiplying by `x` turns `H`-conjugacy into `G`-conjugacy: `H` centralises `x`. -/
theorem isConj_mul_of_isConj {y y' : ↥(centralizerOf x)} (h : IsConj y y') :
    IsConj (x * (y : G)) (x * (y' : G)) := by
  obtain ⟨u, hu⟩ := h
  set v : G := ((u : ↥(centralizerOf x)) : G) with hv
  have hcomm : v * x = x * v :=
    ((Subgroup.mem_centralizer_iff.mp (u : ↥(centralizerOf x)).2) x rfl).symm
  have hy' : (u : ↥(centralizerOf x)) * y * (u : ↥(centralizerOf x))⁻¹ = y' := by
    rw [hu.eq]; group
  have hcoe : v * (y : G) * v⁻¹ = (y' : G) := by
    rw [hv, ← hy']; push_cast; group
  refine isConj_iff.mpr ⟨v, ?_⟩
  calc v * (x * (y : G)) * v⁻¹ = (v * x) * (y : G) * v⁻¹ := by group
    _ = (x * v) * (y : G) * v⁻¹ := by rw [hcomm]
    _ = x * (v * (y : G) * v⁻¹) := by group
    _ = x * (y' : G) := by rw [hcoe]

include hp hω hπ hlin hkerJ in
/-- **Navarro (5.1).**  For a class function `χ` of `G` and `x ∈ G`, the function `y ↦ χ(xy)` on
the `p`-regular elements of `C_G(x)` has a unique expansion in the irreducible Brauer characters
of `C_G(x)`.  Its coefficients are the **generalized decomposition numbers** `d^x_{χφ}`. -/
theorem existsUnique_generalizedDecomposition (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) :
    ∃! d : ι → K, ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) = χ (x * (y : G)) := by
  classical
  exact existsUnique_coeff_irreducibleBrauerCharacter hp hω hπ hlin hkerJ
    (fun y => χ (x * (y : G))) fun y y' h => hχ _ _ (isConj_mul_of_isConj x h)

/-- **The generalized decomposition numbers** `d^x_{χφ}` of Navarro (5.1). -/
noncomputable def generalizedDecompositionNumber (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) : ι → K :=
  (existsUnique_generalizedDecomposition x hp hω hπ hlin hkerJ χ hχ).choose

include hp hω hπ hlin hkerJ in
/-- **The defining property**: `χ(xy) = ∑_φ d^x_{χφ} φ(y)` for `p`-regular `y ∈ C_G(x)`. -/
theorem sum_generalizedDecompositionNumber (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    ∑ φ, generalizedDecompositionNumber x hp hω hπ hlin hkerJ χ hχ φ *
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y)
      = χ (x * (y : G)) :=
  (existsUnique_generalizedDecomposition x hp hω hπ hlin hkerJ χ hχ).choose_spec.1 y hy

include hp hω hπ hlin hkerJ in
/-- **Uniqueness**: any family with the defining property is the generalized decomposition. -/
theorem eq_generalizedDecompositionNumber (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) {d : ι → K}
    (hd : ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) = χ (x * (y : G))) :
    d = generalizedDecompositionNumber x hp hω hπ hlin hkerJ χ hχ :=
  (existsUnique_generalizedDecomposition x hp hω hπ hlin hkerJ χ hχ).choose_spec.2 d hd

end OddOrder.RepresentationTheory.Modular
