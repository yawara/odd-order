/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusConjIndex
import OddOrder.Peterfalvi.S09_ParityPrimitive

/-!
# Peterfalvi (7.9): the parity step `⟨Δ₁, Δ₂⟩` is even, at Hypothesis (7.9) generality

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §7.

The (7.9) conclusion `⟨β₁, ζ₂^{ν₂}⟩ ≠ 0 ∨ ⟨β₂, ζ₁^{ν₁}⟩ ≠ 0` is already proved over an
arbitrary `Hypothesis79` (`conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity`,
`S09_NonexistenceCertain/TwoFamilies.lean`).  Its one remaining input — that `⟨Δ₁, Δ₂⟩` is an
**even** integer — existed only in the Frobenius-family layer
(`FrobeniusFamily.hypothesis79_delta_even`), which was the last thing tying (7.9) to
`FrobeniusFamily`.

This leaf supplies that step at `Hypothesis79` generality.  Every ingredient was already
generic:

* `delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent` —
  `Δ₁, Δ₂ ∈ ℤ[Irr G]` from the two coherences.
* `cfdot_real_vchar_even` (`S09_ParityPrimitive`) — the odd-order parity primitive
  `⟨φ, ψ⟩ ≡ ⟨φ, 1_G⟩·⟨ψ, 1_G⟩ (mod 2)` for real virtual characters.
* `Hypothesis78.delta_orth_one` (`S09_NonexistenceCertain/CoherenceFormula`) —
  `⟨Δ, 1_G⟩ = 0` from a (7.8.a) beta decomposition.

Reality of the two residuals is taken as an input rather than re-derived, so that both
producers can feed it: the generic `delta_isReal` (`S09_FrobeniusConjIndex`, from the two
conjugation identities) and the Frobenius layer's `hypothesis78_delta_isReal`.

## Main results

- `OddOrder.Peterfalvi.S09.Hypothesis79.delta_even`: **Peterfalvi (7.9), parity step**.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]
variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]
variable [Invertible (Nat.card L₁ : ℂ)]
variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]
variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (7.9), parity step** at Hypothesis (7.9) generality: `⟨Δ₁, Δ₂⟩` is an even
integer.

`H79.odd_card` makes the ambient group odd, so the parity primitive `cfdot_real_vchar_even`
applies to the two real virtual characters `Δ₁, Δ₂` and gives
`⟨Δ₁, Δ₂⟩ ≡ ⟨Δ₁, 1_G⟩ · ⟨Δ₂, 1_G⟩ (mod 2)`.  The (7.8.a) beta decomposition of the first
member forces `⟨Δ₁, 1_G⟩ = 0` (`delta_orth_one`), so the product vanishes and `⟨Δ₁, Δ₂⟩` is
even.

The coherence data `hcoh₁`/`hnu₁`/`hcoh₂`/`hnu₂` together with `hind₁Z`/`hzeta₁_irr`/
`hind₂Z`/`hzeta₂_irr` are exactly the premises that place `Δ₁, Δ₂` in `ℤ[Irr G]`; they are the
book's "both families are coherent" hypothesis, not a specialization. -/
theorem delta_even
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hreal₁ : ClassFunction.IsReal H79.first.delta)
    (hreal₂ : ClassFunction.IsReal H79.second.delta)
    (hBD₁ : H79.first.BetaDecomp) :
    ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z := by
  classical
  -- `Δ ∈ ℤ[Irr G]` for both members, off the two coherences.
  obtain ⟨hδ₁Z, hδ₂Z, -, -⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  -- Parity primitive on the two real virtual characters.
  obtain ⟨m, a, b, hm, ha, hb, heven⟩ :=
    cfdot_real_vchar_even H79.odd_card hδ₁Z hreal₁ hδ₂Z hreal₂
  -- `a = ⟨Δ₁, 1_G⟩ = 0` (`constOne` and the trivial character coincide definitionally).
  have horth : ClassFunction.inner H79.first.delta
      ((trivialIrreducibleCharacter G : IrreducibleCharacter G) : ClassFunction G ℂ) = 0 :=
    H79.first.delta_orth_one hBD₁
  have ha0 : a = 0 := by exact_mod_cast ha.trans horth
  exact ⟨m, hm.symm, by simpa [ha0] using heven⟩

end Hypothesis79

end OddOrder.Peterfalvi.S09
