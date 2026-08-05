/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.Modular.SectionProjectiveCharacter

/-!
# The orthogonality of the generalized decomposition numbers — Navarro (5.13)(b)

For a `p`-element `x` and `μ, φ ∈ IBr(C_G(x))`, Navarro (5.13)(b) reads

`∑_{χ ∈ Irr(G)} conj(d^x_{χμ}) d^x_{χφ} = c_{μφ}`,

the Cartan invariant of `C_G(x)`.  Over an abstract splitting field there is no complex
conjugation, and the conjugated factor is the generalized decomposition number **at `x⁻¹`**
(`conj(d^x_{χμ}) = d^{x⁻¹}_{χμ}`, because `μ(y⁻¹) = conj(μ(y))` for Brauer characters).  The
statement proved here is therefore

`∑_{χ ∈ Irr(G)} d^{x⁻¹}_{χμ} · d^x_{χφ} = c_{μφ}`.

The numbers at `x⁻¹` are *not* obtained from a splitting datum for `C_G(x⁻¹)`: although
`C_G(x⁻¹) = C_G(x)` (`centralizerOf_inv`), the two are not equal as types, and transporting a
`p`-modular splitting along that equality is a nuisance.  They enter as a family `dinv` with its
defining property written **inside `C_G(x)`**,

`∑_τ dinv_{j τ} τ(y⁻¹) = χ_j((x y)⁻¹)`   for `p`-regular `y ∈ C_G(x)`,

which is the definition of `d^{x⁻¹}_{χ_j ·}` read at `z = y⁻¹`.

Navarro's proof computes `[Φ^x_μ, Φ^x_φ]` in two ways.  The route taken here does not need the
class function `Φ^{x⁻¹}_φ` (which would again require the datum at `x⁻¹`): both generalized
decomposition numbers are turned into sums over `C_G(x)⁰` by `[Φ_μ, F]⁰ = d_μ`
(`sum_projectiveIndecomposableCharacter_mul_eq`), and the resulting double sum is collapsed by
the **second orthogonality relation of `G`** (`sum_character_inv_mul_character`) evaluated on the
coset `x C_G(x)⁰`.  The class-size weight it produces is `|C_G(x y)| = |C_{C_G(x)}(y)|`
(`card_centralizerOf_mul_eq_card_centralizer_subtype`), which is exactly what cancels the size of
the `C_G(x)`-class of `y`.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_centralizerOf_mul_generalizedDecompositionNumber` —
  `|C_G(x)| d^x_{χφ} = ∑_{z ∈ C_G(x)⁰} Φ_φ(z) χ(x z⁻¹)`
* `OddOrder.RepresentationTheory.Modular.sum_character_mul_generalizedDecompositionNumber` —
  `∑_{χ ∈ Irr(G)} χ((x y)⁻¹) d^x_{χφ} = Φ_φ(y⁻¹)`, i.e. the value of `Φ^{x⁻¹}_φ` on the section
* `OddOrder.RepresentationTheory.Modular.sum_mul_generalizedDecompositionNumber_eq_cartanMatrix` —
  Navarro (5.13)(b)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
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

/-! ### The generalized decomposition numbers as an inner product -/

include hpC hω hω' hπ hlin hkerJ in
/-- **`|C_G(x)| d^x_{χφ} = ∑_{z ∈ C_G(x)⁰} Φ_φ(z) χ(x z⁻¹)`.**

Substitute the defining expansion `χ(x z⁻¹) = ∑_τ d^x_{χτ} τ(z⁻¹)` and use `[Φ_φ, τ]⁰ = δ_{τφ}`.
The sum runs over an arbitrary `Finset` cut out by `p`-regularity. -/
theorem card_centralizerOf_mul_generalizedDecompositionNumber
    (φ : ι) (χ : G → K) (hχ : ∀ a b : G, IsConj a b → χ a = χ b)
    (s : Finset ↥(centralizerOf x)) (hs : ∀ y : ↥(centralizerOf x), y ∈ s ↔ IsPRegular p y) :
    (∑ z ∈ s, algebraMap 𝒪 K
        (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ z)
        * χ (x * ((z⁻¹ : ↥(centralizerOf x)) : G)))
      = (Nat.card ↥(centralizerOf x) : K)
        * generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ φ := by
  haveI : Invertible ((Nat.card ↥(centralizerOf x) : K)) :=
    (isUnit_card_centralizer (K := K) x).invertible
  exact sum_projectiveIndecomposableCharacter_mul_eq hpC hω hω' hπ hlin hkerJ e φ
    (fun z : ↥(centralizerOf x) => χ (x * ((z⁻¹ : ↥(centralizerOf x)) : G)))
    (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ)
    (fun z hz => sum_generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ
      (y := z⁻¹) hz.inv) s hs

/-! ### `Φ^{x⁻¹}_φ` on the `p`-section, without a datum at `x⁻¹` -/

open scoped Classical in
include hpC hω hω' hπ hlin hkerJ in
/-- **`∑_{χ ∈ Irr(G)} χ((x y)⁻¹) d^x_{χφ} = Φ_φ(y⁻¹)`** for `p`-regular `y ∈ C_G(x)`.

The left-hand side is the value at `(x y)⁻¹` of the class function of `G` whose Fourier
coefficients are the `d^x_{·φ}` — that is, of `Φ^{x⁻¹}_φ` — but it is computed here without ever
building that function.  Expand each `d^x_{χφ}` by
`card_centralizerOf_mul_generalizedDecompositionNumber`, apply the second orthogonality relation
of `G` to `∑_χ χ((x y)⁻¹) χ(x z⁻¹)`, and note that the surviving `z` are exactly the
`C_G(x)`-conjugates of `y⁻¹`, on which `Φ_φ` is constant.  The weight `|C_G(x y)|` produced by
second orthogonality is `|C_{C_G(x)}(y⁻¹)|`, which cancels the size of that class against
`|C_G(x)|`. -/
theorem sum_character_mul_generalizedDecompositionNumber
    (hx : IsPElement p x) (φ : ι) {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    (∑ j : J, (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)
        * generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
            ((wedderburnRepresentation eG j).character)
            (fun _ _ h => character_eq_of_isConj _ h) φ)
      = algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ y⁻¹) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible ((Nat.card ↥(centralizerOf x) : K)) :=
    (isUnit_card_centralizer (K := K) x).invertible
  have hCne : (Nat.card ↥(centralizerOf x) : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  obtain ⟨s, hs⟩ : ∃ s : Finset ↥(centralizerOf x),
      ∀ z : ↥(centralizerOf x), z ∈ s ↔ IsPRegular p z :=
    ⟨Finset.univ.filter (fun z : ↥(centralizerOf x) => IsPRegular p z), by simp⟩
  -- the surviving `z` are the `C_G(x)`-conjugates of `y⁻¹`
  set t : Finset ↥(centralizerOf x) :=
    s.filter (fun z => IsConj (x * (y : G)) (x * ((z⁻¹ : ↥(centralizerOf x)) : G))) with htdef
  have ht : ∀ z : ↥(centralizerOf x), z ∈ t ↔ IsConj z y⁻¹ := by
    intro z
    rw [htdef, Finset.mem_filter]
    constructor
    · rintro ⟨hzs, hconj⟩
      obtain ⟨g, hg, hgy⟩ := isConj_centralizer_of_isConj_mul hpC hx
        (isPRegular_coe hy) (isPRegular_coe ((hs z).mp hzs).inv) y.2 (z⁻¹).2 hconj
      have hyzinv : IsConj y z⁻¹ :=
        isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext (by push_cast; exact hgy)⟩
      exact IsConj.symm (by simpa using IsConj.inv' hyzinv)
    · intro hconj
      have hyz : IsConj y z⁻¹ := IsConj.symm (by simpa using IsConj.inv' hconj)
      have hzreg : IsPRegular p z := isPRegular_of_isConj hy.inv (IsConj.symm hconj)
      exact ⟨(hs z).mpr hzreg, isConj_mul_of_isConj x hyz⟩
  -- the class-size bookkeeping
  have hcard : (Nat.card ↥(centralizerOf (x * (y : G))) : K) * (t.card : K)
      = (Nat.card ↥(centralizerOf x) : K) := by
    have hprod := card_mul_card_centralizer_of_forall_isConj (G := ↥(centralizerOf x)) y⁻¹ t ht
    rw [card_centralizerOf_mul_eq_card_centralizer_subtype hpC hx (isPRegular_coe hy),
      show Subgroup.centralizer ({y} : Set ↥(centralizerOf x))
        = Subgroup.centralizer ({y⁻¹} : Set ↥(centralizerOf x)) from (centralizerOf_inv y).symm,
      mul_comm]
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hprod
  refine mul_left_cancel₀ hCne ?_
  calc (Nat.card ↥(centralizerOf x) : K) * ∑ j : J,
        (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)
          * generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
              ((wedderburnRepresentation eG j).character)
              (fun _ _ h => character_eq_of_isConj _ h) φ
      = ∑ j : J, ∑ z ∈ s, (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)
          * (algebraMap 𝒪 K
              (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ z)
            * (wedderburnRepresentation eG j).character
                (x * ((z⁻¹ : ↥(centralizerOf x)) : G))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, card_centralizerOf_mul_generalizedDecompositionNumber
          hpC hω hω' hπ hlin hkerJ e φ _ (fun _ _ h => character_eq_of_isConj _ h) s hs]
        ring
    _ = ∑ z ∈ s, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ z)
          * ∑ j : J, (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)
              * (wedderburnRepresentation eG j).character
                  (x * ((z⁻¹ : ↥(centralizerOf x)) : G)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ z ∈ s, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ z)
          * (if IsConj (x * (y : G)) (x * ((z⁻¹ : ↥(centralizerOf x)) : G)) then
              (Nat.card ↥(centralizerOf (x * (y : G))) : K) else 0) :=
        Finset.sum_congr rfl fun z _ => by
          rw [sum_character_inv_mul_character eG (x * (y : G))
            (x * ((z⁻¹ : ↥(centralizerOf x)) : G))]
    _ = (Nat.card ↥(centralizerOf (x * (y : G))) : K) * ∑ z ∈ t, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ z) := by
        rw [htdef, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> ring
    _ = (Nat.card ↥(centralizerOf x) : K) * algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ y⁻¹) := by
        rw [sum_eq_card_smul_of_forall_isConj _
          (fun a b h => congrArg (algebraMap 𝒪 K)
            (projectiveIndecomposableCharacter_eq_of_isConj hpC hω hω' hπ hlin hkerJ e φ h))
          y⁻¹ t ht, nsmul_eq_mul, ← mul_assoc, hcard]

/-! ### Navarro (5.13)(b) -/

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (5.13)(b)**: `∑_{χ ∈ Irr(G)} d^{x⁻¹}_{χμ} d^x_{χφ} = c_{μφ}`.

The numbers at `x⁻¹` are given as a family `dinv` satisfying the defining expansion read inside
`C_G(x)` — see the module docstring.  Substituting the inner-product form of `dinv` and then
`sum_character_mul_generalizedDecompositionNumber` turns the left-hand side into
`|C_G(x)|⁻¹ ∑_{y ∈ C_G(x)⁰} Φ_μ(y) Φ_φ(y⁻¹)`, and `[Φ_μ, Φ_φ]⁰ = c_{μφ}` finishes. -/
theorem sum_mul_generalizedDecompositionNumber_eq_cartanMatrix
    (hx : IsPElement p x) (μ φ : ι) (dinv : J → ι → K)
    (hdinv : ∀ (j : J) (y : ↥(centralizerOf x)), IsPRegular p y →
      ∑ τ, dinv j τ * algebraMap 𝒪 K
          (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹)
        = (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)) :
    (∑ j : J, dinv j μ * generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ h => character_eq_of_isConj _ h) φ)
      = (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ φ : K) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible ((Nat.card ↥(centralizerOf x) : K)) :=
    (isUnit_card_centralizer (K := K) x).invertible
  have hCne : (Nat.card ↥(centralizerOf x) : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  obtain ⟨s, hs⟩ : ∃ s : Finset ↥(centralizerOf x),
      ∀ z : ↥(centralizerOf x), z ∈ s ↔ IsPRegular p z :=
    ⟨Finset.univ.filter (fun z : ↥(centralizerOf x) => IsPRegular p z), by simp⟩
  refine mul_left_cancel₀ hCne ?_
  calc (Nat.card ↥(centralizerOf x) : K) * ∑ j : J, dinv j μ *
        generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h) φ
      = ∑ j : J, (∑ y ∈ s, algebraMap 𝒪 K
            (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
            * (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹)) *
          generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
            ((wedderburnRepresentation eG j).character)
            (fun _ _ h => character_eq_of_isConj _ h) φ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_projectiveIndecomposableCharacter_mul_eq hpC hω hω' hπ hlin hkerJ e μ
          (fun y : ↥(centralizerOf x) =>
            (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹))
          (dinv j) (hdinv j) s hs]
        ring
    _ = ∑ y ∈ s, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
          * ∑ j : J, (wedderburnRepresentation eG j).character ((x * (y : G))⁻¹) *
              generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
                ((wedderburnRepresentation eG j).character)
                (fun _ _ h => character_eq_of_isConj _ h) φ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ y ∈ s, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
          * algebraMap 𝒪 K
              (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ y⁻¹) :=
        Finset.sum_congr rfl fun y hy => by
          rw [sum_character_mul_generalizedDecompositionNumber hpC hω hω' hπ hlin hkerJ e eG
            hx φ ((hs y).mp hy)]
    _ = (Nat.card ↥(centralizerOf x) : K)
        * (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ φ : K) := by
        refine sum_projectiveIndecomposableCharacter_mul_eq hpC hω hω' hπ hlin hkerJ e μ
          (fun y : ↥(centralizerOf x) => algebraMap 𝒪 K
            (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e φ y⁻¹))
          (fun τ => (cartanMatrix hpC hω hω' hπ hlin hkerJ e τ φ : K)) ?_ s hs
        intro y hy
        rw [projectiveIndecomposableCharacter_eq_sum_cartanMatrix hpC hω hω' hπ hlin hkerJ e φ
          y⁻¹ hy.inv, map_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [map_mul, map_natCast]

end OddOrder.RepresentationTheory.Modular
