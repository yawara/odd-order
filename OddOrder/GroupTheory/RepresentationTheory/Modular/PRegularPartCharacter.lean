/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularProjection
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerInductionTheorem

/-!
# Navarro (2.15): `θ̂(x) = θ(x_{p'})` is a virtual character

Given a class function `θ` on `G` whose restriction to every `p'`-subgroup is a virtual character,
the function `θ̂(x) = θ(x_{p'})` is a virtual character of `G` — indeed a `ℤ`-combination of
characters induced from the subgroups `⟨u⟩ P`.

This is the assembly step.  Brauer's characterization
(`mem_inducedVirtualCharacters_of_restrict`) reduces the claim to the members of the family, and
the members of `elementarySubgroups G` are exactly the `E = ⟨u⟩ P`.  On such an `E` the `p'`-part
map is a group homomorphism `f : E →* G` (`exists_pRegularPart_hom`) whose image is a `p'`-group
(`not_dvd_card_of_forall_isPRegular`), and

`θ̂|_E = (θ|_{f.range}) ∘ f`,

so `comp_mem_virtualCharacters` closes it.

⚠ The hypothesis is about `p'`-*subgroups*, not about `E` itself: `θ|_E` is emphatically **not** a
virtual character in the intended application (`θ` is a Brauer character there, which only becomes
ordinary after the `p`-part has been projected away).

## Main results

* `OddOrder.RepresentationTheory.Modular.pRegularPart_mem_inducedVirtualCharacters` —
  **Navarro (2.15)**
* `OddOrder.RepresentationTheory.Modular.exists_int_sum_wedderburnRepresentation` —
  **Navarro (2.16)**

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.15) (p. 28).
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Finite ι'] [Invertible (Nat.card G : K)]
  {N : ℕ} {ω : K} {p : ℕ}

include e in
/-- **Navarro (2.15)** for `θ̂`.  A class function whose restrictions to the `p'`-subgroups are
virtual characters has `θ̂ : x ↦ θ(x_{p'})` a `ℤ`-combination of characters induced from the
elementary subgroups. -/
theorem pRegularPart_mem_inducedVirtualCharacters (hN : N ≠ 0) (hgN : ∀ g : G, g ^ N = 1)
    (hωN : IsPrimitiveRoot ω N) (hp : p.Prime) {θ : G → K}
    (hcl : ∀ g h : G, θ (h * g * h⁻¹) = θ g)
    (hsub : ∀ Q : Subgroup G, ¬ p ∣ Nat.card ↥Q → θ ∘ Q.subtype ∈ virtualCharacters K ↥Q) :
    (fun g => θ (pRegularPart p g)) ∈ inducedVirtualCharacters K (elementarySubgroups G) := by
  classical
  refine mem_inducedVirtualCharacters_of_restrict e isElementaryFamily_elementarySubgroups hN hgN
    hωN (fun g h => ?_) (fun E hE => ?_)
  · rw [pRegularPart_conj]
    exact hcl _ h
  -- a member of the family is a `⟨u⟩ P`, and there the `p'`-part map is a homomorphism
  obtain ⟨q, u, P, hq, -, hPq, hcomm, rfl⟩ := hE
  obtain ⟨f, hf⟩ := exists_pRegularPart_hom (p := p) hp hq hPq hcomm
  have hrange : ¬ p ∣ Nat.card ↥(f.range) := by
    refine not_dvd_card_of_forall_isPRegular hp fun y => ?_
    obtain ⟨x, hx⟩ := y.2
    rw [← isPRegular_coe_iff, ← hx, hf x]
    exact isPRegular_pRegularPart hp (isOfFinOrder_of_finite _)
  have hcomp : (fun g => θ (pRegularPart p g)) ∘ (pRegularProd u P hcomm).subtype
      = (θ ∘ (f.range).subtype) ∘ f.rangeRestrict := by
    funext x
    simp only [Function.comp_apply, Subgroup.coe_subtype, MonoidHom.coe_rangeRestrict, hf x]
  rw [hcomp]
  exact comp_mem_virtualCharacters _ (hsub f.range hrange)

-- `[Fintype G]` runs the pairing in the proof; the conclusion only mentions `θ` and the block
-- characters, so it does not surface in the type.
set_option linter.unusedFintypeInType false in
include e in
/-- **Navarro (2.16)**, in the shape the decomposition matrix needs: on the `p`-regular classes
`θ` is a `ℤ`-combination of the ordinary irreducible characters.

`θ̂` is a virtual character (`pRegularPart_mem_inducedVirtualCharacters` and `v(G) = ch(G)`), so it
expands as `∑_i (θ̂, χ_i) χ_i` with rational-integer coefficients; and `θ̂ = θ` on `G⁰`. -/
theorem exists_int_sum_wedderburnRepresentation (hN : N ≠ 0) (hgN : ∀ g : G, g ^ N = 1)
    (hωN : IsPrimitiveRoot ω N) (hp : p.Prime) [Fintype ι'] {θ : G → K}
    (hcl : ∀ g h : G, θ (h * g * h⁻¹) = θ g)
    (hsub : ∀ Q : Subgroup G, ¬ p ∣ Nat.card ↥Q → θ ∘ Q.subtype ∈ virtualCharacters K ↥Q) :
    ∃ a : ι' → ℤ, ∀ g : G, IsPRegular p g →
      θ g = ∑ i : ι', (a i : K) * (wedderburnRepresentation e i).character g := by
  classical
  -- `θ̂` is a virtual character
  have hhat : (fun g => θ (pRegularPart p g)) ∈ virtualCharacters K G :=
    inducedVirtualCharacters_le_virtualCharacters e _
      (pRegularPart_mem_inducedVirtualCharacters e hN hgN hωN hp hcl hsub)
  have hhatcl : ∀ g h : G, (fun g => θ (pRegularPart p g)) (h * g * h⁻¹)
      = (fun g => θ (pRegularPart p g)) g := fun g h => by
    simp only
    rw [pRegularPart_conj]
    exact hcl _ h
  -- expand it in the block characters, with integer coefficients
  choose a ha using fun i : ι' => charPairing_mem_intRange hhat
    (mem_virtualCharacters_wedderburnRepresentation e i)
  refine ⟨a, fun g hg => ?_⟩
  have hexp := congrFun (eq_sum_charPairing_wedderburnRepresentation
    (θ := fun g => θ (pRegularPart p g)) e hhatcl) g
  simp only [pRegularPart_eq_self_of_isPRegular hp hg] at hexp
  rw [hexp]
  exact Finset.sum_congr rfl fun i _ => by rw [← ha i]; rfl

end OddOrder.RepresentationTheory.Modular
