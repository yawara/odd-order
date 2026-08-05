/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSection
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSectionSum

/-!
# `Φ^x_μ`: a projective indecomposable character of `C_G(x)` spread over the `p`-section

**Navarro, proof of (5.13).**  For a `p`-element `x` and `μ ∈ IBr(C_G(x))`, define a class
function on `G` by

`Φ^x_μ(u) = Φ_μ(y)` if `u` is conjugate to `x y` with `y` a `p`-regular element of `C_G(x)`,
`Φ^x_μ(u) = 0` if `u ∉ S(x)`.

This is well defined: the `p`-section `S(x)` is parametrised by the `p`-regular classes of
`C_G(x)` (`mem_pSection_iff`) and the parametrisation is injective
(`isConj_centralizer_of_isConj_mul`), while `Φ_μ` is a class function of `C_G(x)`
(`projectiveIndecomposableCharacter_eq_of_isConj`).

Navarro's proof of (5.13) runs `Φ^x_μ` through the inner product twice: `[Φ^x_μ, χ]` recovers a
generalized decomposition number, and `[Φ^x_μ, Φ^x_φ]` is the Cartan invariant `c_{μφ}`.  This
file builds the class function and its defining properties; the two inner-product computations
come later.

⚠ The value at `u ∈ S(x)` is defined by choosing a witness `y`; `sectionProjectiveCharacter_mul`
is the interface — it says the choice does not matter — and no proof below should unfold the
definition.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.sectionProjectiveCharacter` — `Φ^x_μ`

## Main results

* `OddOrder.RepresentationTheory.Modular.sectionProjectiveCharacter_eq_zero` — it vanishes off
  `S(x)`
* `OddOrder.RepresentationTheory.Modular.sectionProjectiveCharacter_mul` — `Φ^x_μ(x y) = Φ_μ(y)`
* `OddOrder.RepresentationTheory.Modular.sectionProjectiveCharacter_eq_of_isConj` — it is a class
  function
* `OddOrder.RepresentationTheory.Modular.card_centralizerOf_smul_sum_sectionProjectiveCharacter` —
  the inner-product sum against `Φ^x_μ` collapses to a sum over `C_G(x)⁰`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]
variable (hpC : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-! ### The parametrisation is injective on values of `Φ_μ` -/

/-- **`Φ_μ` does not distinguish two parametrisations of the same `G`-class.**  If `x y₁` and
`x y₂` are `G`-conjugate then `y₁` and `y₂` are `C_G(x)`-conjugate, and `Φ_μ` is a class function
of `C_G(x)`. -/
theorem projectiveIndecomposableCharacter_eq_of_isConj_mul (hx : IsPElement p x) (μ : ι)
    {y₁ y₂ : ↥(centralizerOf x)} (h₁ : IsPRegular p (y₁ : G)) (h₂ : IsPRegular p (y₂ : G))
    (h : IsConj (x * (y₁ : G)) (x * (y₂ : G))) :
    projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y₁
      = projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y₂ := by
  obtain ⟨g, hg, hgy⟩ :=
    isConj_centralizer_of_isConj_mul hpC hx h₁ h₂ y₁.2 y₂.2 h
  refine projectiveIndecomposableCharacter_eq_of_isConj hpC hω hω' hπ hlin hkerJ e μ
    (isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext ?_⟩)
  push_cast
  exact hgy

/-! ### The class function `Φ^x_μ` -/

open scoped Classical in
/-- **`Φ^x_μ`**: the projective indecomposable character `Φ_μ` of `C_G(x)`, transported to the
`p`-section `S(x)` and extended by zero. -/
noncomputable def sectionProjectiveCharacter (hx : IsPElement p x) (μ : ι) (u : G) : 𝒪 :=
  if h : u ∈ pSection p x then
    projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ
      ⟨((mem_pSection_iff hpC hx).mp h).choose, ((mem_pSection_iff hpC hx).mp h).choose_spec.1⟩
  else 0

open scoped Classical in
/-- **`Φ^x_μ` vanishes off the `p`-section.** -/
theorem sectionProjectiveCharacter_eq_zero (hx : IsPElement p x) (μ : ι) {u : G}
    (hu : u ∉ pSection p x) :
    sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u = 0 :=
  dif_neg hu

open scoped Classical in
/-- **`Φ^x_μ(u) = Φ_μ(y)` whenever `u` is conjugate to `x y`** with `y` a `p`-regular element of
`C_G(x)`.  This is the interface to the definition: the choice of witness does not matter. -/
theorem sectionProjectiveCharacter_of_isConj_mul (hx : IsPElement p x) (μ : ι) {u : G}
    {y : ↥(centralizerOf x)} (hy : IsPRegular p (y : G)) (h : IsConj u (x * (y : G))) :
    sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u
      = projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y := by
  classical
  have hu : u ∈ pSection p x := (mem_pSection_iff hpC hx).mpr ⟨(y : G), y.2, hy, h⟩
  rw [sectionProjectiveCharacter, dif_pos hu]
  obtain ⟨hmem, hreg, hconj⟩ := ((mem_pSection_iff hpC hx).mp hu).choose_spec
  exact projectiveIndecomposableCharacter_eq_of_isConj_mul hpC hω hω' hπ hlin hkerJ e hx μ
    hreg hy (hconj.symm.trans h)

/-- **`Φ^x_μ(x y) = Φ_μ(y)`** for `p`-regular `y ∈ C_G(x)`. -/
theorem sectionProjectiveCharacter_mul (hx : IsPElement p x) (μ : ι)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p (y : G)) :
    sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ (x * (y : G))
      = projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y :=
  sectionProjectiveCharacter_of_isConj_mul hpC hω hω' hπ hlin hkerJ e hx μ hy (IsConj.refl _)

/-- **`Φ^x_μ` is a class function.** -/
theorem sectionProjectiveCharacter_eq_of_isConj (hx : IsPElement p x) (μ : ι) {u v : G}
    (huv : IsConj u v) :
    sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u
      = sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ v := by
  classical
  by_cases hu : u ∈ pSection p x
  · obtain ⟨y, hymem, hyreg, hconj⟩ := (mem_pSection_iff hpC hx).mp hu
    rw [sectionProjectiveCharacter_of_isConj_mul hpC hω hω' hπ hlin hkerJ e hx μ
        (y := ⟨y, hymem⟩) hyreg hconj,
      sectionProjectiveCharacter_of_isConj_mul hpC hω hω' hπ hlin hkerJ e hx μ
        (y := ⟨y, hymem⟩) hyreg (huv.symm.trans hconj)]
  · have hv : v ∉ pSection p x := fun hv =>
      hu (mem_pSection_iff_isConj_pPart.mpr
        ((isConj_pPart huv).trans (mem_pSection_iff_isConj_pPart.mp hv)))
    rw [sectionProjectiveCharacter_eq_zero hpC hω hω' hπ hlin hkerJ e hx μ hu,
      sectionProjectiveCharacter_eq_zero hpC hω hω' hπ hlin hkerJ e hx μ hv]

/-! ### The inner-product sum -/

open scoped Classical in
/-- **The inner-product sum against `Φ^x_μ` collapses to `C_G(x)`.**

`Φ^x_μ(u) χ(u⁻¹)` is a class function vanishing off `S(x)`, so
`card_centralizerOf_smul_sum_pSection` rewrites its sum over `G` as a sum over the `p`-regular
elements of `C_G(x)`, where `Φ^x_μ(x y) = Φ_μ(y)`.

This is the first half of Navarro's computation of `[Φ^x_μ, χ]` in the proof of (5.13). -/
theorem card_centralizerOf_smul_sum_sectionProjectiveCharacter [Fintype G]
    (hx : IsPElement p x) (μ : ι)
    (χ : G → K) (hχ : ∀ a b : G, IsConj a b → χ a = χ b) :
    Nat.card ↥(centralizerOf x)
        • (∑ u : G, algebraMap 𝒪 K
            (sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u) * χ u⁻¹)
      = Nat.card G
        • (∑ y ∈ Finset.univ.filter (fun y : ↥(centralizerOf x) => IsPRegular p ((y : G))),
            algebraMap 𝒪 K (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
              * χ ((x * (y : G))⁻¹)) := by
  classical
  set F : G → K := fun u => algebraMap 𝒪 K
    (sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u) * χ u⁻¹ with hF
  have hinv : ∀ a b : G, IsConj a b → IsConj a⁻¹ b⁻¹ := by
    intro a b h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact isConj_iff.mpr ⟨c, by rw [← hc]; group⟩
  have hclass : ∀ a b : G, IsConj a b → F a = F b := fun a b h => by
    simp only [hF]
    rw [sectionProjectiveCharacter_eq_of_isConj hpC hω hω' hπ hlin hkerJ e hx μ h,
      hχ _ _ (hinv a b h)]
  -- the sum over `G` is the sum over `S(x)`
  have hrestrict : (∑ u : G, F u)
      = ∑ u ∈ Finset.univ.filter (fun u : G => u ∈ pSection p x), F u := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_).symm
    have hnot : u ∉ pSection p x := fun h =>
      hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp only [hF]
    rw [sectionProjectiveCharacter_eq_zero hpC hω hω' hπ hlin hkerJ e hx μ hnot,
      map_zero, zero_mul]
  rw [hrestrict, card_centralizerOf_smul_sum_pSection hpC hx F hclass]
  refine congrArg _ (Finset.sum_congr rfl fun y hy => ?_)
  simp only [hF]
  rw [sectionProjectiveCharacter_mul hpC hω hω' hπ hlin hkerJ e hx μ
    (Finset.mem_filter.mp hy).2]

/-! ### The inner product `[Φ^x_μ, χ]` -/

open scoped Classical in
/-- **`[Φ^x_μ, χ] = d^{x⁻¹}_{χμ}`** — the second half of Navarro's computation in the proof of
(5.13).

The coefficient family is not taken from a splitting datum at `x⁻¹`: it is passed as a plain
`d : IBr(C_G(x)) → K` characterised **inside `C_G(x)`** by

`∑_τ d_τ τ(y⁻¹) = χ((x y)⁻¹)`   for `p`-regular `y ∈ C_G(x)`.

That is the defining property of `d^{x⁻¹}_{χ·}` read at `z = y⁻¹`, legitimate because
`C_G(x⁻¹) = C_G(x)` (`centralizerOf_inv`); keeping `y⁻¹` inside the subgroup avoids transporting
the whole splitting datum along an equality of subgroups that is not an equality of types.

The computation is: `card_centralizerOf_smul_sum_sectionProjectiveCharacter` turns the sum over
`G` into a sum over the `p`-regular elements of `C_G(x)`, the hypothesis expands `χ((x y)⁻¹)` in
the irreducible Brauer characters of `C_G(x)`, and `[Φ_μ, τ]⁰ = δ_{τμ}`
(`pairingZero_projectiveIndecomposableCharacter`) collapses the resulting double sum. -/
theorem inner_sectionProjectiveCharacter_eq [Fintype G] [∀ i, Nonempty (m i)]
    [Invertible (Nat.card G : K)] (hx : IsPElement p x) (μ : ι)
    (χ : G → K) (hχ : ∀ a b : G, IsConj a b → χ a = χ b) (d : ι → K)
    (hd : ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ τ, d τ * algebraMap 𝒪 K
          (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹)
        = χ ((x * (y : G))⁻¹)) :
    (Nat.card G : K)⁻¹ * ∑ u : G, algebraMap 𝒪 K
        (sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u) * χ u⁻¹
      = d μ := by
  haveI : Invertible ((Nat.card ↥(centralizerOf x) : K)) :=
    (isUnit_card_centralizer (K := K) x).invertible
  have hGne : (Nat.card G : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  have hCne : (Nat.card ↥(centralizerOf x) : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  have step2 := card_centralizerOf_smul_sum_sectionProjectiveCharacter
    hpC hω hω' hπ hlin hkerJ e hx μ χ hχ
  rw [nsmul_eq_mul, nsmul_eq_mul] at step2
  set R : Finset ↥(centralizerOf x) :=
    Finset.univ.filter (fun y : ↥(centralizerOf x) => IsPRegular p ((y : G))) with hR
  -- `∑_{y ∈ C⁰} Φ_μ(y) τ(y⁻¹) = |C_G(x)| δ_{τμ}` — Navarro (2.13), with the filter of the
  -- `p`-section computation traded for the filter of `pairingZero`.
  have hpair : ∀ τ : ι,
      (∑ y ∈ R, algebraMap 𝒪 K
          (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹))
        = (Nat.card ↥(centralizerOf x) : K) * (if τ = μ then 1 else 0) := by
    intro τ
    rw [← pairingZero_projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e τ μ,
      pairingZero, ← mul_assoc, mul_inv_cancel₀ hCne, one_mul, hR]
    exact Finset.sum_congr (Finset.ext fun y => by simp [isPRegular_coe_iff]) fun _ _ => rfl
  -- the sum over `C_G(x)⁰` is `|C_G(x)| d_μ`
  have step1 : (∑ y ∈ R,
        algebraMap 𝒪 K (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
          * χ ((x * (y : G))⁻¹))
      = (Nat.card ↥(centralizerOf x) : K) * d μ := by
    have hterm : ∀ y ∈ R,
        algebraMap 𝒪 K (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y)
            * χ ((x * (y : G))⁻¹)
          = ∑ τ, d τ * algebraMap 𝒪 K
              (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y
                * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹) := by
      intro y hy
      rw [← hd y (isPRegular_coe_iff.mp (by rw [hR] at hy; exact (Finset.mem_filter.mp hy).2)),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by rw [map_mul]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    calc (∑ τ, ∑ y ∈ R, d τ * algebraMap 𝒪 K
            (projectiveIndecomposableCharacter hpC hω hω' hπ hlin hkerJ e μ y
              * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π τ y⁻¹))
        = ∑ τ, d τ * ((Nat.card ↥(centralizerOf x) : K) * (if τ = μ then 1 else 0)) :=
          Finset.sum_congr rfl fun τ _ => by rw [← Finset.mul_sum, hpair τ]
      _ = (Nat.card ↥(centralizerOf x) : K) * d μ := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' Finset.univ μ,
            Finset.mem_univ, if_true]
          ring
  rw [step1] at step2
  have hSu : (∑ u : G, algebraMap 𝒪 K
        (sectionProjectiveCharacter hpC hω hω' hπ hlin hkerJ e hx μ u) * χ u⁻¹)
      = (Nat.card G : K) * d μ :=
    mul_left_cancel₀ hCne (by linear_combination step2)
  rw [hSu, inv_mul_cancel_left₀ hGne]

end OddOrder.RepresentationTheory.Modular
