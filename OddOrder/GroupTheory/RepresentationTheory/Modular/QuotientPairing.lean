/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularQuotient
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse

/-!
# Navarro's pairing under a quotient by a normal `p`-subgroup

Third step of Navarro (7.6).  With `N ⊴ G` a `p`-subgroup centralised by every `p`-regular
element, `x ↦ xN` is a bijection `G⁰ → (G/N)⁰` (`bijOn_mk_isPRegular`), so two class functions
that correspond under it have the *same* sum

`∑_{g ∈ G⁰} a(g) b(g⁻¹) = ∑_{ḡ ∈ Ḡ⁰} ā(ḡ) b̄(ḡ⁻¹)`.

Only the normalising factor differs, and `|G| = |Ḡ| · |N|` turns that into Navarro's

`[a, b]⁰_G = (1/|N|) [ā, b̄]⁰_Ḡ`.

Since `([φ,θ]⁰)` is the inverse of the Cartan matrix (`sum_cartanMatrix_mul_pairingZero`), this is
the displayed computation on p. 137 behind `C_B = |P| C_B̄`.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_pRegular_quotient`
* `OddOrder.RepresentationTheory.Modular.card_mul_pairingZero_quotient`
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [Field K] [Algebra 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype (G ⧸ N)]

open scoped Classical in
/-- **The `p`-regular sums agree.**  Reindexing along the bijection `G⁰ → Ḡ⁰` of (7.6). -/
theorem sum_pRegular_quotient (hp : p.Prime) (hN : IsPGroup p ↥N)
    (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z) (F : G → K) (F' : (G ⧸ N) → K)
    (hF : ∀ g : G, IsPRegular p g → F g = F' (QuotientGroup.mk g)) :
    (∑ g ∈ Finset.univ.filter fun g : G => IsPRegular p g, F g)
      = ∑ y ∈ Finset.univ.filter fun y : G ⧸ N => IsPRegular p y, F' y := by
  obtain ⟨hmaps, hinj, hsurj⟩ := bijOn_mk_isPRegular (N := N) hp hN hcent
  refine Finset.sum_bij (fun g _ => (QuotientGroup.mk g : G ⧸ N)) (fun g hg => ?_)
    (fun g₁ hg₁ g₂ hg₂ h => ?_) (fun y hy => ?_) fun g hg => ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hmaps (Finset.mem_filter.mp hg).2⟩
  · exact hinj (Finset.mem_filter.mp hg₁).2 (Finset.mem_filter.mp hg₂).2 h
  · obtain ⟨g, hg, hgy⟩ := hsurj (Finset.mem_filter.mp hy).2
    exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, hgy⟩
  · exact hF g (Finset.mem_filter.mp hg).2

open scoped Classical in
/-- **Navarro (7.6), the pairing identity**: `|N| · [a,b]⁰_G = [ā,b̄]⁰_Ḡ`.  The two `p`-regular
sums coincide and `|G| = |Ḡ| · |N|`. -/
theorem card_mul_pairingZero_quotient [Invertible (Nat.card G : K)]
    [Invertible (Nat.card (G ⧸ N) : K)] (hp : p.Prime) (hN : IsPGroup p ↥N)
    (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z) (a b : G → 𝒪)
    (a' b' : (G ⧸ N) → 𝒪) (ha : ∀ g : G, IsPRegular p g → a g = a' (QuotientGroup.mk g))
    (hb : ∀ g : G, IsPRegular p g → b g = b' (QuotientGroup.mk g)) :
    (Nat.card ↥N : K) * pairingZero (𝒪 := 𝒪) p K a b
      = pairingZero (𝒪 := 𝒪) p K a' b' := by
  have hsum := sum_pRegular_quotient (K := K) hp hN hcent
    (fun g => algebraMap 𝒪 K (a g * b g⁻¹))
    (fun y => algebraMap 𝒪 K (a' y * b' y⁻¹)) fun g hg => by
      rw [ha g hg, hb g⁻¹ hg.inv]
      rfl
  -- `|G| = |Ḡ| · |N|`
  have hcard : (Nat.card G : K) = (Nat.card (G ⧸ N) : K) * (Nat.card ↥N : K) := by
    rw [← Nat.cast_mul, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hGne : (Nat.card G : K) ≠ 0 := (isUnit_of_invertible _).ne_zero
  have hNne : (Nat.card ↥N : K) ≠ 0 := by
    intro h
    rw [hcard, h, mul_zero] at hGne
    exact hGne rfl
  rw [pairingZero, pairingZero, hsum, ← mul_assoc, hcard, mul_inv,
    mul_comm ((Nat.card (G ⧸ N) : K))⁻¹, ← mul_assoc, mul_inv_cancel₀ hNne, one_mul]

end OddOrder.RepresentationTheory.Modular
