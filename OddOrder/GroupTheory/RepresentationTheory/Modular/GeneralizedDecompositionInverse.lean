/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionOrthogonality

/-!
# The generalized decomposition numbers at `x⁻¹`, read inside `C_G(x)`

Navarro (5.13)(b) reads `∑_{χ ∈ Irr(G)} d^{x⁻¹}_{χμ} d^x_{χφ} = c_{μφ}`, and
`sum_mul_generalizedDecompositionNumber_eq_cartanMatrix` takes the numbers at `x⁻¹` as an
abstract family `dinv` satisfying the defining expansion **read inside `C_G(x)`** — precisely so
that no datum on `C_G(x⁻¹)` is needed (`centralizerOf x⁻¹ = centralizerOf x` is only a
propositional equality of subgroups, so the two carrier types are not interchangeable).

This file *builds* that family for an arbitrary `x`.  Since `x⁻¹` centralises `C_G(x)`, the
function `y ↦ χ(x⁻¹ y)` is a class function of `C_G(x)`, so it has a unique expansion in
`IBr(C_G(x))` exactly as `y ↦ χ(x y)` does.  Evaluating that expansion at `y⁻¹` and using
`(x y)⁻¹ = x⁻¹ y⁻¹` gives the hypothesis `hdinv` verbatim.

`GeneralizedDecompositionInvolution` did the same for an involution by *reusing* the family at
`x`; that is the special case `x⁻¹ = x`.  The construction here has no hypothesis on `x` at all.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumberInv` — `d^{x⁻¹}_{χφ}`

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_generalizedDecompositionNumberInv`
* `OddOrder.RepresentationTheory.Modular.eq_generalizedDecompositionNumberInv`
* `OddOrder.RepresentationTheory.Modular.sum_generalizedDecompositionNumberInv_inv` — the
  hypothesis `hdinv` of (5.13)(b)
* `OddOrder.RepresentationTheory.Modular.sum_mul_generalizedDecompositionNumberInv_eq_cartanMatrix`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]

/-! ### The expansion of `y ↦ χ(x⁻¹ y)` -/

section Construction

variable (hp : p.Prime)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))

omit [Finite G] in
/-- `x⁻¹` centralises `C_G(x)`, so multiplying by it turns `C_G(x)`-conjugacy into
`G`-conjugacy. -/
theorem isConj_inv_mul_of_isConj (x : G) {y y' : ↥(centralizerOf x)} (h : IsConj y y') :
    IsConj (x⁻¹ * (y : G)) (x⁻¹ * (y' : G)) := by
  obtain ⟨u, hu⟩ := h
  set v : G := ((u : ↥(centralizerOf x)) : G) with hv
  have hxv : Commute x v := (Subgroup.mem_centralizer_iff.mp (u : ↥(centralizerOf x)).2) x rfl
  have hcomm : v * x⁻¹ = x⁻¹ * v := (hxv.symm.inv_right).eq
  have hy' : (u : ↥(centralizerOf x)) * y * (u : ↥(centralizerOf x))⁻¹ = y' := by
    rw [hu.eq]; group
  have hcoe : v * (y : G) * v⁻¹ = (y' : G) := by
    rw [hv, ← hy']; push_cast; group
  refine isConj_iff.mpr ⟨v, ?_⟩
  calc v * (x⁻¹ * (y : G)) * v⁻¹ = (v * x⁻¹) * (y : G) * v⁻¹ := by group
    _ = (x⁻¹ * v) * (y : G) * v⁻¹ := by rw [hcomm]
    _ = x⁻¹ * (v * (y : G) * v⁻¹) := by group
    _ = x⁻¹ * (y' : G) := by rw [hcoe]

include hp hω' hπ hlin hkerJ in
/-- **The generalized decomposition at `x⁻¹`, read inside `C_G(x)`.**  Same statement as
`existsUnique_generalizedDecomposition` with `x` replaced by `x⁻¹` in the *argument* only: the
group, the modular datum and the index set are those of `C_G(x)`. -/
theorem existsUnique_generalizedDecompositionInv (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) :
    ∃! d : ι → K, ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) = χ (x⁻¹ * (y : G)) := by
  classical
  exact existsUnique_coeff_irreducibleBrauerCharacter hp hω' hπ hlin hkerJ
    (fun y => χ (x⁻¹ * (y : G))) fun y y' h => hχ _ _ (isConj_inv_mul_of_isConj x h)

/-- **The generalized decomposition numbers `d^{x⁻¹}_{χφ}`**, indexed by `IBr(C_G(x))`. -/
noncomputable def generalizedDecompositionNumberInv (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) : ι → K :=
  (existsUnique_generalizedDecompositionInv (x := x) hp hω' hπ hlin hkerJ χ hχ).choose

include hp hω' hπ hlin hkerJ in
/-- **The defining property**: `χ(x⁻¹ y) = ∑_φ d^{x⁻¹}_{χφ} φ(y)` for `p`-regular `y ∈ C_G(x)`. -/
theorem sum_generalizedDecompositionNumberInv (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    ∑ φ, generalizedDecompositionNumberInv (x := x) hp hω' hπ hlin hkerJ χ hχ φ *
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y)
      = χ (x⁻¹ * (y : G)) :=
  (existsUnique_generalizedDecompositionInv (x := x) hp hω' hπ hlin hkerJ χ hχ).choose_spec.1 y hy

include hp hω' hπ hlin hkerJ in
/-- **Uniqueness**: any family with the defining property *is* `d^{x⁻¹}_{χ·}`. -/
theorem eq_generalizedDecompositionNumberInv (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) {d : ι → K}
    (hd : ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) = χ (x⁻¹ * (y : G))) :
    d = generalizedDecompositionNumberInv (x := x) hp hω' hπ hlin hkerJ χ hχ :=
  (existsUnique_generalizedDecompositionInv (x := x) hp hω' hπ hlin hkerJ χ hχ).choose_spec.2 d hd

include hp hω' hπ hlin hkerJ in
/-- **The hypothesis `hdinv` of (5.13)(b)**: reading the defining property at `y⁻¹` computes
`χ((x y)⁻¹)`, because `x` and `y` commute. -/
theorem sum_generalizedDecompositionNumberInv_inv (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    ∑ φ, generalizedDecompositionNumberInv (x := x) hp hω' hπ hlin hkerJ χ hχ φ *
        algebraMap 𝒪 K
          (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y⁻¹)
      = χ ((x * (y : G))⁻¹) := by
  rw [sum_generalizedDecompositionNumberInv hp hω' hπ hlin hkerJ χ hχ hy.inv]
  have hxy : Commute x (y : G) := (Subgroup.mem_centralizer_iff.mp y.2) x rfl
  congr 1
  rw [show ((y⁻¹ : ↥(centralizerOf x)) : G) = ((y : G))⁻¹ from rfl, ← _root_.mul_inv_rev, hxy.eq]

end Construction

/-! ### (5.13)(b) for an arbitrary `p`-element -/

section Cartan

variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
variable [Invertible (Nat.card G : K)]
variable (hpC : p.Prime) {ω : 𝒪}
  (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (5.13)(b) for an arbitrary `p`-element**:
`∑_{χ ∈ Irr(G)} d^{x⁻¹}_{χμ} d^x_{χφ} = c_{μφ}`, with the numbers at `x⁻¹` supplied by
`generalizedDecompositionNumberInv`. -/
theorem sum_mul_generalizedDecompositionNumberInv_eq_cartanMatrix
    (hx : IsPElement p x) (μ φ : ι) :
    (∑ j : J, generalizedDecompositionNumberInv (x := x) hpC hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ h => character_eq_of_isConj _ h) μ *
      generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ h => character_eq_of_isConj _ h) φ)
      = (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ φ : K) :=
  sum_mul_generalizedDecompositionNumber_eq_cartanMatrix hpC hω hω' hπ hlin hkerJ e eG hx μ φ
    (fun j => generalizedDecompositionNumberInv (x := x) hpC hω' hπ hlin hkerJ
      ((wedderburnRepresentation eG j).character)
      (fun _ _ h => character_eq_of_isConj _ h))
    (fun _ _ hy => sum_generalizedDecompositionNumberInv_inv hpC hω' hπ hlin hkerJ _ _ hy)

end Cartan

end OddOrder.RepresentationTheory.Modular
