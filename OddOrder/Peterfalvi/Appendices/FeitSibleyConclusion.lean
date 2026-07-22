/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyUnionCoherence
import OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem

/-!
# Peterfalvi Appendix IV: the (8) conclusion (p. 150)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, p. 150 (campaign issue 1054, step (8)).  This leaf sits downstream of
both endgame branches — the coherence machinery (`FeitSibleyUnionCoherence` →
`FeitSibleyEndgame`) and the `𝒮`/`τ` support (`FeitSibleyTheorem`) — where the
final assembly of step (8) is built: the central-character congruence
`peterfalvi_67_hall_of_odd` applied to the `𝒴`-witness `e'₁`, combined with the
regular-character evaluation `∑_{χ ∈ 𝒳} χ(1)·χ(z) = -|H ⧸ Z|`, forces `a ∣ λ`
(`dvd_of_isIntegral_ratio`), closing (6) and hence the Feit–Sibley Theorem.

This file first records the **regular-character evaluation over `𝒳`**: with
`𝒳 = XsetOf ⊥ Z = {χ ∈ Irr H | Z ⊄ Ker χ}` (`mem_XsetOf_bot_iff`), reindexing to
the `IrreducibleCharacter H` filter and applying the (6.8.1) identity
`sumNonInflatedDegreeMulChar_of_mem` gives the off-identity value `-|H ⧸ Z|` — the
`(8)` input showing `Res_H e'₁` is constant on `Z^#`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

open scoped Classical in
/-- **(6.8.1) regular-character value over `𝒳`** (Peterfalvi (8), mmd 04.8 L168).  For
`𝒳 = XsetOf ⊥ Z` with `Z ≤ Q₁` and `z ∈ Z^#`, `∑_{χ ∈ 𝒳} χ(1)·χ(z) = -|H ⧸ Z|` — the
off-identity value of the regular-character difference `∑_{Z ⊄ Ker χ} χ(1)·χ = ρ_H − ρ_{H/Z}`.

By `mem_XsetOf_bot_iff` the members of `𝒳` are exactly the irreducibles with `Z ⊄ Ker`, so
(via `leKer_iff_subset_characterKernel`) the sum reindexes to the `IrreducibleCharacter H`
filter `Z ⊄ characterKernel`, where `sumNonInflatedDegreeMulChar_of_mem` evaluates it.  This is
the `(8)` step showing `Res_H e'₁` is constant on `Z^#`. -/
theorem sum_degree_mul_charValue_XsetOf_bot [Finite G] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    [(Z.subgroupOf hyp.H).Normal]
    {T : Finset (ClassFunction ↥hyp.H ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.XsetOf ⊥ Z)
    {z : ↥hyp.H} (hz : z ∈ Z.subgroupOf hyp.H) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, ((φ : ClassFunction ↥hyp.H ℂ) 1) * ((φ : ClassFunction ↥hyp.H ℂ) z)
      = -(Nat.card (↥hyp.H ⧸ Z.subgroupOf hyp.H) : ℂ) := by
  classical
  -- `𝒳 = {χ | Irr χ ∧ Z ⊄ characterKernel χ}` (drop the redundant `Q₁ ⊄ Ker`, `⊥ ⊆ Ker`).
  have hchar : ∀ φ : ClassFunction ↥hyp.H ℂ, φ ∈ hyp.XsetOf ⊥ Z ↔
      IsIrreducibleCharacter φ ∧
        ¬ ((Z.subgroupOf hyp.H : Set ↥hyp.H) ⊆ OddOrder.Peterfalvi.S03.characterKernel φ) := by
    intro φ
    rw [hyp.mem_XsetOf_bot_iff hZQ1, hyp.leKer_iff_subset_characterKernel]
  -- reindex the sum from `T` (class functions) to the `IrreducibleCharacter` filter.
  rw [show ∑ φ ∈ T, ((φ : ClassFunction ↥hyp.H ℂ) 1) * ((φ : ClassFunction ↥hyp.H ℂ) z)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : IrreducibleCharacter ↥hyp.H =>
          ¬ ((Z.subgroupOf hyp.H : Set ↥hyp.H) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥hyp.H ℂ))),
          ((ψ : ClassFunction ↥hyp.H ℂ) 1) * ((ψ : ClassFunction ↥hyp.H ℂ) z) from ?_]
  · exact OddOrder.RepresentationTheory.sumNonInflatedDegreeMulChar_of_mem
      (N := Z.subgroupOf hyp.H) hz hz1
  · refine Finset.sum_bij'
      (fun φ hφ => (⟨φ, ((hchar φ).mp ((hT φ).mp hφ)).1⟩ : IrreducibleCharacter ↥hyp.H))
      (fun ψ _ => (ψ : ClassFunction ↥hyp.H ℂ))
      (fun φ hφ => ?_) (fun ψ hψ => ?_) (fun φ hφ => rfl) (fun ψ hψ => ?_) (fun φ hφ => rfl)
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ((hchar φ).mp ((hT φ).mp hφ)).2⟩
    · rw [Finset.mem_filter] at hψ
      rw [hT, hchar]; exact ⟨ψ.2, hψ.2⟩
    · apply IrreducibleCharacter.ext; rfl

open scoped Classical in
/-- **Degree-square value over `𝒳`** (Peterfalvi (8), the `z = 1` companion of
`sum_degree_mul_charValue_XsetOf_bot`).  For `𝒳 = XsetOf ⊥ Z` with `Z ≤ Q₁`,
`∑_{χ ∈ 𝒳} χ(1)² = |H| − |H ⧸ Z|` — the identity value of `ρ_H − ρ_{H/Z}`
(`sumNonInflatedDegreeSq`).  Together with the off-identity value `-|H ⧸ Z|` this gives the
`(8)` difference `ρ_H − ρ_{H/Z}` evaluated at `z ∈ Z^#` minus at `1`, namely `-|H|`. -/
theorem sum_degreeSq_XsetOf_bot [Finite G] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    [(Z.subgroupOf hyp.H).Normal]
    {T : Finset (ClassFunction ↥hyp.H ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.XsetOf ⊥ Z) :
    ∑ φ ∈ T, ((φ : ClassFunction ↥hyp.H ℂ) 1) ^ 2
      = (Nat.card ↥hyp.H : ℂ) - (Nat.card (↥hyp.H ⧸ Z.subgroupOf hyp.H) : ℂ) := by
  classical
  have hchar : ∀ φ : ClassFunction ↥hyp.H ℂ, φ ∈ hyp.XsetOf ⊥ Z ↔
      IsIrreducibleCharacter φ ∧
        ¬ ((Z.subgroupOf hyp.H : Set ↥hyp.H) ⊆ OddOrder.Peterfalvi.S03.characterKernel φ) := by
    intro φ
    rw [hyp.mem_XsetOf_bot_iff hZQ1, hyp.leKer_iff_subset_characterKernel]
  rw [show ∑ φ ∈ T, ((φ : ClassFunction ↥hyp.H ℂ) 1) ^ 2
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : IrreducibleCharacter ↥hyp.H =>
          ¬ ((Z.subgroupOf hyp.H : Set ↥hyp.H) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥hyp.H ℂ))),
          ((ψ : ClassFunction ↥hyp.H ℂ) 1) ^ 2 from ?_]
  · exact OddOrder.RepresentationTheory.sumNonInflatedDegreeSq (N := Z.subgroupOf hyp.H)
  · refine Finset.sum_bij'
      (fun φ hφ => (⟨φ, ((hchar φ).mp ((hT φ).mp hφ)).1⟩ : IrreducibleCharacter ↥hyp.H))
      (fun ψ _ => (ψ : ClassFunction ↥hyp.H ℂ))
      (fun φ hφ => ?_) (fun ψ hψ => ?_) (fun φ hφ => rfl) (fun ψ hψ => ?_) (fun φ hφ => rfl)
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ((hchar φ).mp ((hT φ).mp hφ)).2⟩
    · rw [Finset.mem_filter] at hψ
      rw [hT, hchar]; exact ⟨ψ.2, hψ.2⟩
    · apply IrreducibleCharacter.ext; rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
