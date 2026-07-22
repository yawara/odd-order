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

open scoped Classical in
/-- **(8) Fourier evaluation split** (Peterfalvi (8), p. 150).  A virtual character
`θ ∈ ℤ[Irr H]` evaluated on `z ∈ Z` minus at `1` picks up only its `𝒳 = XsetOf ⊥ Z`
components: `θ(z) − θ(1) = ∑_{χ ∈ 𝒳} ⟨θ, χ⟩·(χ(z) − χ(1))`.  Writing `θ = ∑_a c_a·a`
(`mem_ZIrr_repr`) and evaluating, the `Z ⊆ Ker a` (i.e. `LeKer a Z`) components are constant
on `Z` (`a(z) = a(1)`) and drop out; the surviving irreducibles are exactly `𝒳`, on which the
coefficient is the Fourier inner product `⟨θ, a⟩ = c_a` (`inner_eq_coeff_of_repr`). -/
theorem apply_sub_apply_eq_sum_XsetOf_bot [Finite G] [Fintype ↥hyp.H]
    [Invertible (Nat.card ↥hyp.H : ℂ)] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    {T : Finset (ClassFunction ↥hyp.H ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.XsetOf ⊥ Z)
    {θ : ClassFunction ↥hyp.H ℂ} (hθ : θ ∈ ZIrr ↥hyp.H)
    {z : ↥hyp.H} (hz : (z : G) ∈ Z) :
    θ z - θ 1 = ∑ χ ∈ T, ClassFunction.inner θ (χ : ClassFunction ↥hyp.H ℂ) * (χ z - χ 1) := by
  classical
  obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hθ
  have hinner : ∀ χ ∈ T, ClassFunction.inner θ χ = (c χ : ℂ) := by
    intro χ hχ
    have hirr : IsIrreducibleCharacter χ := ((hyp.mem_XsetOf_bot_iff hZQ1).mp ((hT χ).mp hχ)).1
    have h := inner_eq_coeff_of_repr (⟨χ, hirr⟩ : IrreducibleCharacter ↥hyp.H) hsupp
    rw [show ((⟨χ, hirr⟩ : IrreducibleCharacter ↥hyp.H) : ClassFunction ↥hyp.H ℂ) = χ from rfl,
      ← hrepr] at h
    exact h
  rw [Finset.sum_congr rfl (fun χ hχ => by rw [hinner χ hχ])]
  have hval : θ z - θ 1 = ∑ a ∈ c.support, (c a : ℂ) * (a z - a 1) := by
    rw [hrepr, ClassFunction.sum_apply, ClassFunction.sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval]
  have hLeKer_vanish : ∀ a : ClassFunction ↥hyp.H ℂ, hyp.LeKer a Z → (a z - a 1) = 0 := by
    intro a ha; rw [ha z hz, sub_self]
  have hL : ∑ a ∈ c.support, (c a : ℂ) * (a z - a 1)
      = ∑ a ∈ c.support.filter (fun a => ¬ hyp.LeKer a Z), (c a : ℂ) * (a z - a 1) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro a ha hnot
    rw [Finset.mem_filter, not_and_or, not_not] at hnot
    rcases hnot with h | h
    · exact absurd ha h
    · rw [hLeKer_vanish a h, mul_zero]
  have hR : ∑ a ∈ c.support.filter (fun a => ¬ hyp.LeKer a Z), (c a : ℂ) * (a z - a 1)
      = ∑ χ ∈ T, (c χ : ℂ) * (χ z - χ 1) := by
    refine Finset.sum_subset ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [hT, hyp.mem_XsetOf_bot_iff hZQ1]
      exact ⟨mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha.1)), ha.2⟩
    · intro χ hχT hχnot
      have hχT' := (hyp.mem_XsetOf_bot_iff hZQ1).mp ((hT χ).mp hχT)
      rw [Finset.mem_filter, not_and_or] at hχnot
      rcases hχnot with h | h
      · rw [Finsupp.notMem_support_iff.mp h, Int.cast_zero, zero_mul]
      · exact absurd (not_not.mp h) hχT'.2
  rw [hL, hR]

open scoped Classical in
/-- **(8) coefficient relation** (Peterfalvi (8), p. 150).  For the restriction `Res_H e'`
of a `𝒴`-witness `e'` and a member `χ` of the coherent `𝒳`-family with `χ − b·χ₁` supported,
the Fourier coefficient scales with `b`: `⟨Res_H e', χ⟩ = b·⟨Res_H e', χ₁⟩`.

By Frobenius reciprocity `⟨Res_H e', χ − b·χ₁⟩ = conj⟨Ind(χ − b·χ₁), e'⟩`, and
`Ind(χ − b·χ₁) = τ(χ − b·χ₁) = E(χ − b·χ₁) = E χ − b·E χ₁` (coherence on the supported
difference), which is orthogonal to `e'` by the cross-orthogonality `⟨E φ, e'⟩ = 0`
(`cross_extension_inner_eq_zero`).  Hence `⟨Res_H e', χ − b·χ₁⟩ = 0`. -/
theorem restrict_extension_inner_eq_nsmul [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {X : Set (ClassFunction ↥hyp.H ℂ)}
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    {χ₁ χ : ClassFunction ↥hyp.H ℂ} {e' : ClassFunction G ℂ}
    (hcross : ∀ φ ∈ X, ClassFunction.inner (hcohX.extension φ) e' = 0)
    {b : ℕ} (hsupp : χ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) :
    ClassFunction.inner (ClassFunction.restrict hyp.H e') χ
      = (b : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ := by
  have htau : ClassFunction.induce hyp.H (χ - b • χ₁) = hcohX.extension (χ - b • χ₁) := by
    rw [← hyp.tau_apply, ← hcohX.extends_on_supported _ hsupp]
  have hkey : ClassFunction.inner (ClassFunction.restrict hyp.H e') (χ - b • χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ← ClassFunction.inner_induce_eq_inner_restrict hyp.H (χ - b • χ₁) e',
      htau, map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ b (hcohX.extension χ₁),
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hcross χ hχX, hcross χ₁ hχ₁X,
      mul_zero, sub_zero, star_zero]
  rw [ClassFunction.inner_sub_right, ← Nat.cast_smul_eq_nsmul ℂ b χ₁,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at hkey
  linear_combination hkey

/-- **(8) keystone relation** (Peterfalvi (8), p. 150).  The keystone pairing
`⟨Res_H e', χ₁⟩ − a·⟨Res_H e', η₁⟩ = λ − a`, where `e'` is the `𝒴`-witness for `η₁` and
`⟨τ(χ₁ − a·η₁), e'⟩ = λ − a` is the `(6)` norm-identity coefficient.  By Frobenius reciprocity
`⟨Res_H e', χ₁ − a·η₁⟩ = conj⟨Ind(χ₁ − a·η₁), e'⟩ = conj⟨τ(χ₁ − a·η₁), e'⟩ = λ − a`.  Combined
with the `𝒳`-coefficient relation this fixes `c₀ = ⟨Res_H e', χ₁⟩ = λ + a·μ` with
`μ = ⟨Res_H e', η₁⟩ − 1`. -/
theorem restrict_inner_keystone [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {χ₁ η₁ : ClassFunction ↥hyp.H ℂ} {e' : ClassFunction G ℂ} {a : ℕ} {lam : ℤ}
    (hlam1 : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) e' = (lam : ℂ) - a) :
    ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁
      - (a : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H e') η₁ = (lam : ℂ) - a := by
  have hks : ClassFunction.inner (ClassFunction.restrict hyp.H e') (χ₁ - a • η₁)
      = (lam : ℂ) - a := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ← ClassFunction.inner_induce_eq_inner_restrict hyp.H (χ₁ - a • η₁) e',
      ← hyp.tau_apply, hlam1, star_sub, star_intCast, star_natCast]
  rw [ClassFunction.inner_sub_right, ← Nat.cast_smul_eq_nsmul ℂ a η₁,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at hks
  linear_combination hks

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
