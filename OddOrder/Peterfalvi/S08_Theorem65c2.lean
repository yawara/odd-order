/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_Theorem63
import OddOrder.Peterfalvi.S08_CaseBAssembly

/-!
# Peterfalvi (6.2)/(6.3)/(6.5) for case (c2): the certain-type `p`-group reduction chain

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.2)/(6.3)/(6.5).

This leaf assembles the **case-(c2)** (certain-type) analogue of the Frobenius (c1) chain
`six_two_index_bound → six_two_central → six_three_index_bound → six_three →
isPGroup_of_not_coherent` (`S08_CoherenceCorePart2`), which produces the index bound
`hbound : |Abelianization H| ≤ 4|W₁|² + 1` consumed by the `(6.5)(b)` reduction
`exists_isPGroup_H_of_c2_of_card_le` (`S08_PGroupReduction`).

The c2 chain mirrors c1 with a three-brick swap (Frobenius → `h46`):
* `exists_coherentBreakPair` → `exists_coherentBreakPair_general` (members need not be irreducible),
* `SsubFiltration_hasNoRealCharacters hF` → `S_hasNoRealCharacters_caseB`,
* `sMember_index_le_two_psi hF` → `sSubFiltration_sum_le_two_psi_caseB` (the norm-weighted (5.6) (6.2)
  bound, `S08_Theorem63`).

The only genuinely new ingredient is **break-irreducibility**: the (5.6) brick demands the break `ψ`
be irreducible.  The reducible members of `S` are exactly the `w₂ − 1` certain-type columns, all of
which lie *outside* `S(A)` once `W₂ ≤ A` (`columnSum_notMem_SsubFiltration_of_le`); so on any such
`S(A)` every member is irreducible.  `member_isIrreducible_of_W2_le` packages this.

Reference note: `notes/peterfalvi/s08_6_8_resume_roadmap.md` (cont.¹⁷).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Break-irreducibility on a filtration level `W₂ ≤ A`** (case (c2)).

Every member of the filtration set `S(A)` is irreducible once `W₂ ≤ A`.  Indeed an `S`-member is, by
`caseB_S_member_column_or_irreducible`, either an irreducible character or one of the `w₂ − 1`
certain-type columns `columnSum h46 χ₂` (`χ₂ ≠ 1`); but the latter is excluded from `S(A)` by
`columnSum_notMem_SsubFiltration_of_le` (since `W₂ ≤ A`).  This supplies the `hψirr` hypothesis that
the norm-weighted (5.6) bound `sSubFiltration_sum_le_two_psi_caseB` demands of the break character in
the (6.2)/(6.3) certain-type chain. -/
theorem SibleyDadeHypothesis.member_isIrreducible_of_W2_le
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {A : Subgroup ↥L} (hAW2 : h46.W2 ≤ A)
    {ψ : ClassFunction ↥L ℂ} (hψ : ψ ∈ hyp.SsubFiltration A) :
    IsIrreducibleCharacter ψ := by
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.SsubFiltration_subset_S hψ) with
    ⟨χ₂, hχ₂, hcol⟩ | hirr
  · rw [← hcol] at hψ
    exact absurd hψ (hyp.columnSum_notMem_SsubFiltration_of_le h46 hHK hAW2 hχ₂)
  · exact hirr

end OddOrder.Peterfalvi.S08
