/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality

/-!
# The projective indecomposable characters vanish off the `p`-regular classes

This is the analytic half of Navarro (2.13): `Φ_φ ∈ vcf(G)`.

For `y` `p`-regular and any `x`, second orthogonality (`sum_character_inv_mul_character`) gives

`∑_{χ ∈ Irr(G)} χ(y⁻¹) χ(x) = |C_G(y)| δ_{y ~ x}`.

Expanding `χ(y⁻¹)` by its row of the decomposition matrix — legitimate, since `y⁻¹` is again
`p`-regular — turns the left side into `∑_φ Φ_φ(x) φ(y⁻¹)`.  If `x` is `p`-singular it is
conjugate to no `p`-regular element, so the right side vanishes for every `p`-regular `y`; the
irreducible Brauer characters are linearly independent on the `p`-regular classes
(`eq_zero_of_sum_irreducibleBrauerCharacter_ringHom`), so every coefficient `Φ_φ(x)` is `0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.isPRegular_of_isConj`
* `OddOrder.RepresentationTheory.Modular.algebraMap_sum_projectiveIndecomposableCharacter_mul_inv`
* `OddOrder.RepresentationTheory.Modular.projectiveIndecomposableCharacter_eq_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

/-- `p`-regularity is a class property. -/
theorem isPRegular_of_isConj {G : Type*} [Group G] {p : ℕ} {x y : G} (h : IsPRegular p y)
    (hc : IsConj y x) : IsPRegular p x := by
  obtain ⟨u, hu⟩ := hc
  have hh : (u : G) * y * ((u : G))⁻¹ = x := by rw [hu.eq]; group
  rw [← hh]
  exact h.conj _

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

omit [∀ (i : ι'), Nonempty (m i)] [Invertible (Nat.card G : K)] in
/-- **`∑_φ Φ_φ(x) φ(g)` is the column pairing of `x` against `g`.**  Expand each ordinary
character at the `p`-regular element `g` by its row of `D` and collect. -/
theorem sum_projectiveIndecomposableCharacter_mul (x : G) {g : G} (hg : IsPRegular p g) :
    ∑ ψ, projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e ψ x
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ψ g
      = ∑ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i g * ordinaryCharacter (𝒪 := 𝒪) e i x := by
  classical
  have hexp : ∀ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i g
      = ∑ ψ, (decompositionMatrix hp hω hω' hπ hlin hkerJ e i ψ : 𝒪)
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ψ g :=
    fun i => trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i g hg
  have hRHS : (∑ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i g * ordinaryCharacter (𝒪 := 𝒪) e i x)
      = ∑ i : ι', ∑ ψ, ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i ψ : 𝒪)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ψ g)
        * ordinaryCharacter (𝒪 := 𝒪) e i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp i, Finset.sum_mul]
  rw [hRHS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [projectiveIndecomposableCharacter, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

open scoped Classical in
/-- **The defining relation of the projective indecomposable characters** — Navarro (2.13):
for `y` `p`-regular and *any* `x`,

`∑_φ Φ_φ(x) φ(y⁻¹) = |C_G(y)| δ_{y ~ x}`.

Expand the ordinary characters at the `p`-regular element `y⁻¹` and apply column orthogonality.
This is the matrix identity that inverts the Cartan matrix. -/
theorem algebraMap_sum_projectiveIndecomposableCharacter_mul_inv (x : G) {y : G}
    (hy : IsPRegular p y) :
    algebraMap 𝒪 K (∑ ψ, projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e ψ x
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ψ y⁻¹)
      = if IsConj y x then (Nat.card (Subgroup.centralizer ({y} : Set G)) : K) else 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [sum_projectiveIndecomposableCharacter_mul hp hω hω' hπ hlin hkerJ e x hy.inv, map_sum,
    show (∑ i : ι', algebraMap 𝒪 K
        (ordinaryCharacter (𝒪 := 𝒪) e i y⁻¹ * ordinaryCharacter (𝒪 := 𝒪) e i x))
      = ∑ i : ι', (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character x from
      Finset.sum_congr rfl fun i _ => by
        rw [map_mul, algebraMap_ordinaryCharacter, algebraMap_ordinaryCharacter]; rfl]
  convert sum_character_inv_mul_character e y x using 2

/-- **The projective indecomposable characters vanish off the `p`-regular classes** — Navarro
(2.13), analytic half. -/
theorem projectiveIndecomposableCharacter_eq_zero (φ : ι) {x : G} (hx : ¬ IsPRegular p x) :
    projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e φ x = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  have hrel : ∀ g : G, IsPRegular p g →
      ∑ ψ, projectiveIndecomposableCharacter hp hω hω' hπ hlin hkerJ e ψ x
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ψ g = 0 := by
    intro g hg
    rw [sum_projectiveIndecomposableCharacter_mul hp hω hω' hπ hlin hkerJ e x hg]
    refine hinj ?_
    rw [map_zero, map_sum]
    have hcol := sum_character_inv_mul_character e g⁻¹ x
    rw [inv_inv, if_neg fun hc => hx (isPRegular_of_isConj hg.inv hc)] at hcol
    rw [← hcol]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, algebraMap_ordinaryCharacter, algebraMap_ordinaryCharacter]
      rfl
  exact congrFun
    (eq_zero_of_sum_irreducibleBrauerCharacter_ringHom hp hω' hπ hlin hkerJ _ hrel) φ

end OddOrder.RepresentationTheory.Modular
