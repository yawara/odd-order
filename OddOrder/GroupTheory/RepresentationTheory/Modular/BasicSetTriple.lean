/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BasicSetDecomposition

/-!
# The basic set of Navarro (7.4) has exactly three members

In the situation of Navarro (7.2) the principal block has `|Irr(B_0)| = 4`
(`card_blockOfIrr_principal_eq_four_and_character_involution`) and the basic set of (7.4) is
`𝓑 = {ε_j χ_j⁰ : χ_j ∈ Irr(B_0), j ≠ j₀}` — one character of `Irr(B_0)` is dropped, so `𝓑` has
three members.  That is what turns the display of Navarro p. 141,

`χ(t u) = ∑_{φ ∈ 𝓑} d^t_{χφ} φ(u)`,

into the *three*-term expansion

`χ(t u) = D^t_0 + ψ_1(u) D^t_1 + ψ_2(u) D^t_2`

that the endgame consumes as its hypothesis `hT`
(`OddOrder.RepresentationTheory.Modular.exists_proper_normal_of_columns`).

Everything here is elementary: a four-element set with two distinguished members has exactly two
others, and a sum supported on `𝓑` collapses to those three terms.  The content is entirely in
naming the three members, which no other file does.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_pair_of_card_filter_eq_four` — names `ψ_1`, `ψ_2`
* `OddOrder.RepresentationTheory.Modular.sum_eq_add_add_of_enumeration`
* `OddOrder.RepresentationTheory.Modular.basicDecompositionNumber_add_add_eq_character` —
  the three-term form of the display on p. 141

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.2), (7.4), p. 141.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-! ### Naming the three members -/

section Enumeration

variable {κ : Type*} [Fintype κ]

/-- **A four-element `Irr(B_0)` with the dropped character `j₀` and the trivial character `l₀`
removed leaves exactly two more**, `ψ_1` and `ψ_2`.

This is the only place the count `|Irr(B_0)| = 4` of Navarro (7.2) is *used*: it is what makes the
basic set of (7.4) a three-element set, so that the expansion of `χ(t u)` has three terms. -/
theorem exists_pair_of_card_filter_eq_four {P : κ → Prop} [DecidablePred P]
    (h4 : (Finset.univ.filter P).card = 4) {j₀ l₀ : κ} (hj₀ : P j₀) (hl₀ : P l₀)
    (hne : l₀ ≠ j₀) :
    ∃ ψ₁ ψ₂ : κ, P ψ₁ ∧ P ψ₂ ∧ ψ₁ ≠ j₀ ∧ ψ₂ ≠ j₀ ∧ l₀ ≠ ψ₁ ∧ l₀ ≠ ψ₂ ∧ ψ₁ ≠ ψ₂ ∧
      ∀ l : κ, P l → l ≠ j₀ → l = l₀ ∨ l = ψ₁ ∨ l = ψ₂ := by
  classical
  set S : Finset κ := Finset.univ.filter P with hS
  have hmem : ∀ l : κ, l ∈ S ↔ P l := fun l => by
    rw [hS, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hj₀S : j₀ ∈ S := (hmem j₀).mpr hj₀
  have hl₀S : l₀ ∈ (S.erase j₀) := Finset.mem_erase.mpr ⟨hne, (hmem l₀).mpr hl₀⟩
  have hcard1 : (S.erase j₀).card = 3 := by
    rw [Finset.card_erase_of_mem hj₀S, h4]
  have hcard2 : ((S.erase j₀).erase l₀).card = 2 := by
    rw [Finset.card_erase_of_mem hl₀S, hcard1]
  obtain ⟨ψ₁, ψ₂, hψne, hTeq⟩ := Finset.card_eq_two.mp hcard2
  have hψ₁ : ψ₁ ∈ (S.erase j₀).erase l₀ := by rw [hTeq]; exact Finset.mem_insert_self _ _
  have hψ₂ : ψ₂ ∈ (S.erase j₀).erase l₀ := by
    rw [hTeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine ⟨ψ₁, ψ₂, (hmem _).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hψ₁)),
    (hmem _).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hψ₂)),
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hψ₁)).1,
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hψ₂)).1,
    fun h => (Finset.mem_erase.mp hψ₁).1 h.symm, fun h => (Finset.mem_erase.mp hψ₂).1 h.symm,
    hψne, fun l hl hlj => ?_⟩
  by_cases hll : l = l₀
  · exact Or.inl hll
  have : l ∈ (S.erase j₀).erase l₀ :=
    Finset.mem_erase.mpr ⟨hll, Finset.mem_erase.mpr ⟨hlj, (hmem l).mpr hl⟩⟩
  rw [hTeq, Finset.mem_insert, Finset.mem_singleton] at this
  exact Or.inr this

/-- **A sum supported on the three-element basic set collapses to three terms.** -/
theorem sum_eq_add_add_of_enumeration {M : Type*} [AddCommMonoid M] {P : κ → Prop}
    {f : κ → M} {j₀ l₀ ψ₁ ψ₂ : κ}
    (hsupp : ∀ l : κ, f l ≠ 0 → P l ∧ l ≠ j₀)
    (henum : ∀ l : κ, P l → l ≠ j₀ → l = l₀ ∨ l = ψ₁ ∨ l = ψ₂)
    (h01 : l₀ ≠ ψ₁) (h02 : l₀ ≠ ψ₂) (h12 : ψ₁ ≠ ψ₂) :
    (∑ l : κ, f l) = f l₀ + f ψ₁ + f ψ₂ := by
  classical
  have hzero : ∀ l ∈ (Finset.univ : Finset κ), l ∉ ({l₀, ψ₁, ψ₂} : Finset κ) → f l = 0 := by
    intro l _ hl
    by_contra hne
    obtain ⟨hP, hj⟩ := hsupp l hne
    rcases henum l hP hj with h | h | h <;>
      exact hl (by rw [h]; simp)
  rw [← Finset.sum_subset (Finset.subset_univ ({l₀, ψ₁, ψ₂} : Finset κ)) hzero,
    Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton, add_assoc]

end Enumeration

/-! ### The three-term expansion of `χ(t u)` -/

section Cartan

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable (hpC : p.Prime)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))

include hpC hω' hπ hlin hkerJ in
/-- **Navarro p. 141, the display in three terms**:
`χ(x w) = D_{l₀}(χ) η_{l₀}(w) + D_{ψ_1}(χ) η_{ψ_1}(w) + D_{ψ_2}(χ) η_{ψ_2}(w)`.

The basic set `η` vanishes off `𝓑 = {l : B l ∧ l ≠ j₀}` (that is how `principalBasicSet` is
defined), and `𝓑 = {l₀, ψ_1, ψ_2}` by `exists_pair_of_card_filter_eq_four`; so the sum over the
whole index type in `sum_basicDecompositionNumber_eq_character_of_support` has three terms.

The hypothesis `hu` is only imposed on the support `P` of the column `d^x_{χ ·}`, since the basic
set of the principal block expresses `φ_μ` only for `μ ∈ IBr(B_0(C_G(x)/N))`; `hd` is what the
second main theorem supplies there
(`generalizedDecompositionNumber_eq_zero_of_quotient_ne`). -/
theorem basicDecompositionNumber_add_add_eq_character {ι₂ : Type*} [Fintype ι₂]
    (u : ι → ι₂ → K) (η : ι₂ → ↥(centralizerOf x) → K)
    (χ : G → K) (hχ : ∀ g h : G, IsConj g h → χ g = χ h) {P : ι → Prop}
    (hd : ∀ μ : ι, ¬ P μ →
      generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ μ = 0)
    (hu : ∀ μ : ι, P μ → ∀ w : ↥(centralizerOf x), IsPRegular p w →
      algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ w)
        = ∑ φ : ι₂, u μ φ * η φ w)
    {w : ↥(centralizerOf x)} (hw : IsPRegular p w)
    {B : ι₂ → Prop} {j₀ l₀ ψ₁ ψ₂ : ι₂}
    (hη : ∀ φ : ι₂, ¬ (B φ ∧ φ ≠ j₀) → η φ w = 0)
    (henum : ∀ φ : ι₂, B φ → φ ≠ j₀ → φ = l₀ ∨ φ = ψ₁ ∨ φ = ψ₂)
    (h01 : l₀ ≠ ψ₁) (h02 : l₀ ≠ ψ₂) (h12 : ψ₁ ≠ ψ₂) :
    basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ) u l₀ * η l₀ w
      + basicDecompositionNumber
          (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ) u ψ₁ * η ψ₁ w
      + basicDecompositionNumber
          (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ) u ψ₂ * η ψ₂ w
      = χ (x * (w : G)) := by
  classical
  rw [← sum_eq_add_add_of_enumeration (P := B) (j₀ := j₀)
    (f := fun φ => basicDecompositionNumber
      (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ) u φ * η φ w)
    (fun φ hφ => by
      by_contra hc
      exact hφ (by rw [hη φ hc, mul_zero])) henum h01 h02 h12]
  exact sum_basicDecompositionNumber_eq_character_of_support hpC hω' hπ hlin hkerJ u η χ hχ hd hu hw

end Cartan

end OddOrder.RepresentationTheory.Modular
