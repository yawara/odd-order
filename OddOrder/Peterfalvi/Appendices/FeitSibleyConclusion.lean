/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyUnionCoherence
import OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem
import OddOrder.GroupTheory.RepresentationTheory.HallTICongruence

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

open scoped Classical in
/-- **(8) composition + evaluation** (Peterfalvi (8), p. 150).  Combining the Fourier split
(`apply_sub_apply_eq_sum_XsetOf_bot`), the `𝒳`-coefficient relation
(`restrict_extension_inner_eq_nsmul`) and the two regular-character evaluations
(`sum_degree_mul_charValue_XsetOf_bot`, `sum_degreeSq_XsetOf_bot`) gives, for the `𝒴`-witness
`e'` (with cross-orthogonality `⟨E φ, e'⟩ = 0` on `𝒳`) and `z ∈ Z^#`,
`χ₁(1)·(e'(z) − e'(1)) = −|H|·⟨Res_H e', χ₁⟩`.

Set `θ = Res_H e' ∈ ℤ[Irr H]` (`restrict_mem_ZIrr`) and `c₀ = ⟨θ, χ₁⟩`.  The split gives
`θ(z) − θ(1) = ∑_{χ ∈ 𝒳} ⟨θ, χ⟩·(χ(z) − χ(1))`.  Each `χ ∈ 𝒳` has a supported difference
`χ − b·χ₁` (P1-X data), so `⟨θ, χ⟩ = b·c₀` and — since the difference vanishes at `1` (support
`⊆ A`, `1 ∉ A`) — `χ(1) = b·χ₁(1)`; hence `χ₁(1)·⟨θ, χ⟩ = c₀·χ(1)`.  Multiplying the split by
`χ₁(1)` and evaluating `∑ χ(1)·χ(z) = −|H ⧸ Z|` and `∑ χ(1)² = |H| − |H ⧸ Z|` collapses the sum
to `−|H|·c₀`.  This is the `(8)` value feeding the central-character congruence: dividing by
`χ₁(1) = a·d` and `|H| = d·|Q|` yields `e'(z) − e'(1) = −|Q|·(λ/a + μ)`. -/
theorem restrict_apply_sub_eq_neg_card_mul_inner [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) [(Z.subgroupOf hyp.H).Normal]
    {T : Finset (ClassFunction ↥hyp.H ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.XsetOf ⊥ Z)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.XsetOf ⊥ Z) hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁ : χ₁ ∈ hyp.XsetOf ⊥ Z)
    {e' : ClassFunction G ℂ} (he' : e' ∈ ZIrr G)
    (hcross : ∀ φ ∈ hyp.XsetOf ⊥ Z, ClassFunction.inner (hcohX.extension φ) e' = 0)
    (hXdiff : ∀ χ ∈ hyp.XsetOf ⊥ Z, ∃ b : ℕ,
      χ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (hyp.XsetOf ⊥ Z) hyp.A)
    {z : ↥hyp.H} (hz : (z : G) ∈ Z) (hz1 : z ≠ 1) :
    χ₁ 1 * (e' (z : G) - e' 1)
      = -(Nat.card ↥hyp.H : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ := by
  classical
  have hθZIrr : ClassFunction.restrict hyp.H e' ∈ ZIrr ↥hyp.H :=
    ClassFunction.restrict_mem_ZIrr hyp.H he'
  -- piece 1: Fourier split of `θ(z) − θ(1)` over `𝒳`
  have hsplit := hyp.apply_sub_apply_eq_sum_XsetOf_bot hZQ1 hT hθZIrr hz
  -- multiply the split by `χ₁(1)`, rewriting each coefficient `χ₁(1)·⟨θ, χ⟩ = c₀·χ(1)`
  have hkey : χ₁ 1 * (ClassFunction.restrict hyp.H e' z - ClassFunction.restrict hyp.H e' 1)
      = ∑ χ ∈ T, (ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ * (χ 1 * χ z)
          - ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ * (χ 1) ^ 2) := by
    rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    obtain ⟨b, hsupp⟩ := hXdiff χ ((hT χ).mp hχ)
    -- coefficient: `⟨θ, χ⟩ = b·c₀`
    have hinner : ClassFunction.inner (ClassFunction.restrict hyp.H e') χ
        = (b : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ :=
      hyp.restrict_extension_inner_eq_nsmul hcohX hcross hsupp ((hT χ).mp hχ) hχ₁
    -- degree: `χ(1) = b·χ₁(1)` from `(χ − b·χ₁)(1) = 0` (support `⊆ A`, `1 ∉ A`)
    have hbdeg : χ 1 = (b : ℂ) * χ₁ 1 := by
      have hval0 : (χ - b • χ₁) 1 = 0 := by
        by_contra h
        exact hyp.one_notMem_A
          (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hsupp
            (ClassFunction.mem_support.mpr h))
      have happ : (χ - b • χ₁) 1 = χ 1 - (b : ℂ) * χ₁ 1 := by
        rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ b χ₁, ClassFunction.smul_apply]
      rw [happ] at hval0
      exact eq_of_sub_eq_zero hval0
    rw [hinner, hbdeg]; ring
  -- evaluate the two regular-character sums over `𝒳`
  have hsum1 := hyp.sum_degree_mul_charValue_XsetOf_bot hZQ1 hT
    (Subgroup.mem_subgroupOf.mpr hz) hz1
  have hsum2 := hyp.sum_degreeSq_XsetOf_bot hZQ1 hT
  have hval : χ₁ 1 * (ClassFunction.restrict hyp.H e' z - ClassFunction.restrict hyp.H e' 1)
      = -(Nat.card ↥hyp.H : ℂ)
          * ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ := by
    rw [hkey, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hsum2]
    ring
  simpa only [ClassFunction.restrict_apply, OneMemClass.coe_one] using hval

set_option linter.unusedFintypeInType false in
open scoped OddOrder.AlgInt in
/-- **(8) step-(7) applied to a `𝒴`-witness** (Peterfalvi (8), p. 150).  For the `𝒴`-witness
`e' = ε·ξ` (`ε ≠ 0`, `ξ ∈ Irr G`) — which is constant on `Z^#` by the `(8)` evaluation
(`restrict_apply_sub_eq_neg_card_mul_inner`) — the central-character congruence (7)
`peterfalvi_67_hall_of_odd` gives `e'(z) ≡ e'(1) (mod |Q|)`.

The structural inputs of `peterfalvi_67_hall_of_odd` are discharged from the `Hypothesis` block
(`Q ≤ H`, `Q ⊴ H`, `Q^#` is a `TI`-subset of `G`); the remaining inputs — `G` of odd order, `Q`
a Hall subgroup of `H` and of `G`, `Z ⊴ H` central with `Q ≤ C_G(z)`, and the constancy of `ρ`
and of the normalizer–centralizer cardinality on `Z^#` — are supplied by the reduction context.
Writing `ξ = ρ.character` (`ξ.isIrreducible`), the `e'`-constancy transfers to `ρ.character`
(cancel `ε`), feeding (7); scaling the resulting `ξ`-congruence by the integer `ε`
(`Cong.smul_left`) returns the congruence for `e'`. -/
theorem witness_charValue_cong [Fintype G]
    {Z : Subgroup G} (hZQ : Z ≤ hyp.Q) [(Z.subgroupOf hyp.H).Normal]
    (hoddG : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card (↥hyp.H ⧸ hyp.Q.subgroupOf hyp.H)))
    (hHallG : Nat.Coprime (Nat.card ↥hyp.Q) hyp.Q.index)
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hQz : hyp.Q ≤ Subgroup.centralizer ({z} : Set G))
    {e' : ClassFunction G ℂ} {ε : ℤ} {ξ : IrreducibleCharacter G} (hεne : ε ≠ 0)
    (he' : e' = ε • (ξ : ClassFunction G ℂ))
    (he'const : ∀ w ∈ Z, w ≠ 1 → e' w = e' z)
    (hcard_const : ∀ w ∈ Z, w ≠ 1 →
      Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({z} : Set G))) :
    e' z ≡ e' 1 [ALGMOD (Nat.card ↥hyp.Q : ℤ)] := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  haveI : ρ.IsIrreducible := hρ
  have hεceo : (ε : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hεne
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  have hsmul : ∀ g : G, e' g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [he', ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  -- `hconst` for (7): character constancy (cancel `ε` from `e'`-constancy) + card constancy
  have hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({z} : Set G)) := by
    intro w hwZ hw1
    refine ⟨?_, hcard_const w hwZ hw1⟩
    rw [← congrFun hξρ w, ← congrFun hξρ z]
    apply mul_left_cancel₀ hεceo
    rw [← hsmul w, ← hsmul z]
    exact he'const w hwZ hw1
  have hcong := OddOrder.RepresentationTheory.peterfalvi_67_hall_of_odd ρ hyp.Q_le_H hZQ
    hyp.Q_subgroupOf_H_normal inferInstance hyp.isTISubset_Q_sdiff_one hHall hoddG hzZ hz1 hQz
    hHallG hconst
  rw [← congrFun hξρ z, ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  rw [← hsmul z, ← hsmul 1] at hcong2
  exact hcong2

open scoped Classical in
/-- **(8) full assembly: `a ∣ λ`** (Peterfalvi (8), p. 150).  The keystone divisibility closing
step (6): from the endgame `(4)` data — the coherent `𝒳 = XsetOf ⊥ Z` with anchor `χ₁` of degree
`χ₁(1) = a·d`, `p`-power degree differences `χ − b·χ₁` supported, the `𝒴`-witness `e' = ε·ξ`
cross-orthogonal to the `𝒳`-extensions, and the `(6)` coefficient `λ` from
`⟨τ(χ₁ − a·η₁), e'⟩ = λ − a` — one gets `a ∣ λ`.

Assembly of the five `(8)`-core pieces: `restrict_apply_sub_eq_neg_card_mul_inner` (piece 4) gives
`χ₁(1)·(e'(w) − e'(1)) = −|H|·⟨Res_H e', χ₁⟩` for every `w ∈ Z^#`, a value independent of `w`, so
`e'` is constant on `Z^#`; `witness_charValue_cong` (the step-(7) application) then gives
`e'(z) ≡ e'(1) (mod |Q|)`.  `restrict_inner_keystone` (piece 3) fixes
`⟨Res_H e', χ₁⟩ = λ + a·μ` (`μ = ⟨Res_H e', η₁⟩ − 1 ∈ ℤ`); substituting `χ₁(1) = a·d`,
`|H| = d·|Q|` into piece 4 gives `(a·d)·(e'(z) − e'(1)) = −(d·|Q|)·(λ + a·μ)`, whence
`dvd_lam_of_evaluation_cong` (piece 5) yields `a ∣ λ`. -/
theorem dvd_lam_of_endgame_data [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H]
    [Invertible (Nat.card ↥hyp.H : ℂ)]
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) [(Z.subgroupOf hyp.H).Normal]
    (hoddG : Odd (Nat.card G)) (hHallG : Nat.Coprime (Nat.card ↥hyp.Q) hyp.Q.index)
    {T : Finset (ClassFunction ↥hyp.H ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.XsetOf ⊥ Z)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.XsetOf ⊥ Z) hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁ : χ₁ ∈ hyp.XsetOf ⊥ Z)
    {a : ℕ} (ha : 0 < a) (hχ₁deg : χ₁ 1 = (a : ℂ) * (hyp.d : ℂ))
    (hXdiff : ∀ χ ∈ hyp.XsetOf ⊥ Z, ∃ b : ℕ,
      χ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (hyp.XsetOf ⊥ Z) hyp.A)
    {e' : ClassFunction G ℂ} (he'ZIrr : e' ∈ ZIrr G)
    {ε : ℤ} {ξ : IrreducibleCharacter G} (hεne : ε ≠ 0)
    (he'eq : e' = ε • (ξ : ClassFunction G ℂ))
    (hcross : ∀ φ ∈ hyp.XsetOf ⊥ Z, ClassFunction.inner (hcohX.extension φ) e' = 0)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁ZIrr : η₁ ∈ ZIrr ↥hyp.H) {lam : ℤ}
    (hlam1 : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) e' = (lam : ℂ) - a)
    {z : ↥hyp.H} (hzZ : (z : G) ∈ Z) (hz1 : z ≠ 1)
    (hQz : hyp.Q ≤ Subgroup.centralizer ({(z : G)} : Set G))
    (hcard_const : ∀ w ∈ Z, w ≠ 1 →
      Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(hyp.H ⊓ Subgroup.centralizer ({(z : G)} : Set G))) :
    (a : ℤ) ∣ lam := by
  classical
  have hZQ : Z ≤ hyp.Q := hZQ1.trans hyp.Q1_le_Q
  -- `d ≠ 0` and `|H| = d·|Q|`
  have hd0 : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have hHcard : (Nat.card ↥hyp.H : ℂ) = (hyp.d : ℂ) * (Nat.card ↥hyp.Q : ℂ) := by
    have h := hyp.card_Q_mul_card_D
    change (Nat.card ↥hyp.H : ℂ) = (Nat.card ↥hyp.D : ℂ) * (Nat.card ↥hyp.Q : ℂ)
    rw [← h]; push_cast; ring
  -- `χ₁(1) ≠ 0`
  have hχ0 : χ₁ 1 ≠ 0 := by
    rw [hχ₁deg]; exact mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne') hd0
  -- piece 4, universally in `w ∈ Z^#`: RHS is `w`-independent
  have hpiece4 : ∀ w : ↥hyp.H, (w : G) ∈ Z → w ≠ 1 →
      χ₁ 1 * (e' (w : G) - e' 1)
        = -(Nat.card ↥hyp.H : ℂ) * ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁ :=
    fun w hwZ hw1 =>
      hyp.restrict_apply_sub_eq_neg_card_mul_inner hZQ1 hT hcohX hχ₁ he'ZIrr hcross hXdiff hwZ hw1
  -- `e'` is constant on `Z^#`
  have he'const : ∀ w : G, w ∈ Z → w ≠ 1 → e' w = e' (z : G) := by
    intro w hwZ hw1
    have hwH : w ∈ hyp.H := hyp.Q_le_H (hZQ hwZ)
    have hwne : (⟨w, hwH⟩ : ↥hyp.H) ≠ 1 := fun h => hw1 (by simpa using congrArg (Subtype.val) h)
    have p4w := hpiece4 ⟨w, hwH⟩ hwZ hwne
    have p4z := hpiece4 z hzZ hz1
    have hcancel : χ₁ 1 * (e' w - e' 1) = χ₁ 1 * (e' (z : G) - e' 1) := by
      rw [show ((⟨w, hwH⟩ : ↥hyp.H) : G) = w from rfl] at p4w; rw [p4w, p4z]
    have hsub := mul_left_cancel₀ hχ0 hcancel
    linear_combination hsub
  -- step (7): `e'(z) ≡ e'(1) (mod |Q|)`
  have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (by simpa using h))
  have hHall : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card (↥hyp.H ⧸ hyp.Q.subgroupOf hyp.H)) := by
    have hidx : Nat.card (↥hyp.H ⧸ hyp.Q.subgroupOf hyp.H) = hyp.d := hyp.index_Q_subgroupOf_eq_d
    rw [hidx]; exact hyp.coprime_Q_D
  have halg := hyp.witness_charValue_cong hZQ hoddG hHall hHallG hzZ hz1G hQz hεne he'eq
    he'const hcard_const
  -- keystone: `c₀ = λ + a·μ` with `μ = ⟨Res_H e', η₁⟩ − 1`
  obtain ⟨mu', hmu'⟩ :=
    ClassFunction.inner_mem_ZIrr_int (ClassFunction.restrict_mem_ZIrr hyp.H he'ZIrr) hη₁ZIrr
  have hkey := hyp.restrict_inner_keystone hlam1
  rw [hmu'] at hkey
  -- combine piece 4 (at `z`) with the degree substitutions into `dvd_lam_of_evaluation_cong`
  have heval : (a : ℂ) * (hyp.d : ℂ) * (e' (z : G) - e' 1)
      = -((hyp.d : ℂ) * (Nat.card ↥hyp.Q : ℂ)) * ((lam : ℂ) + (a : ℂ) * ((mu' : ℂ) - 1)) := by
    have p4z := hpiece4 z hzZ hz1
    rw [hχ₁deg, hHcard] at p4z
    rw [p4z]
    -- `⟨Res_H e', χ₁⟩ = λ + a·(μ' − 1)` from the keystone
    have hc₀ : ClassFunction.inner (ClassFunction.restrict hyp.H e') χ₁
        = (lam : ℂ) + (a : ℂ) * ((mu' : ℂ) - 1) := by linear_combination hkey
    rw [hc₀]
  have hΔ : IsIntegral ℤ ((e' (z : G) - e' 1) / (Nat.card ↥hyp.Q : ℂ)) := halg
  simpa using dvd_lam_of_evaluation_cong (a := a) (lam := lam) (mu := mu' - 1) ha hd0
    (by exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥hyp.Q)).ne' :
      (Nat.card ↥hyp.Q : ℂ) ≠ 0)) (by push_cast; linear_combination heval) hΔ

open scoped Classical in
/-- **(4)–(8) endgame assembly: `𝒳 ∪ 𝒴` is coherent** (Peterfalvi (4)–(6)+(8), p. 148–150).
With the endgame `(4)` data set up — the coherent `𝒳 = XsetOf ⊥ Z` (anchor `χ₁`, degree
`χ₁(1) = a·d`, `p`-power integral differences) and a coherent `𝒴 ⊆ 𝒮` disjoint from `𝒳`
(anchor `η₁`, `|𝒴| ≥ 2`, `A`-supported differences), the supported keystone `χ₁ − a·η₁`, and a
central `Z ≤ Z(Q₁)` with `z ∈ Z^#` — the union `𝒳 ∪ 𝒴` is coherent.

This wires the four endgame lemmas: `cross_extension_inner_eq_zero` (step (5),
`⟨E_𝒳 φ, e'⟩ = 0`), `coherent_extension_eq_zsmul_irr` (the `𝒴`-witness `e' = ε·ξ`),
`exists_lambda_norm_identity` (the `(6)` coefficient `λ` and norm identity), and
`dvd_lam_of_endgame_data` (the `(8)` divisibility `a ∣ λ`, with `hQz`/`hcard_const` discharged
via `Q_le_centralizer_of_mem_central`/`inf_centralizer_card_const_of_central`), feeding
`union_coherent_of_lambda_dvd`. -/
theorem xset_qder_union_coherent [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.H]
    [Invertible (Nat.card ↥hyp.H : ℂ)] [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) [(Z.subgroupOf hyp.H).Normal]
    (hZcent : ∀ w ∈ Z, ∀ y ∈ hyp.Q1, ⁅w, y⁆ = 1)
    (hoddG : Odd (Nat.card G)) (hHallG : Nat.Coprime (Nat.card ↥hyp.Q) hyp.Q.index)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.XsetOf ⊥ Z) hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ hyp.XsetOf ⊥ Z)
    {a : ℕ} (ha : 2 ≤ a) (hχ₁deg : χ₁ 1 = (a : ℂ) * (hyp.d : ℂ))
    (hXdiff : ∀ φ ∈ hyp.XsetOf ⊥ Z, ∃ b : ℕ, 0 < b ∧
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (hyp.XsetOf ⊥ Z) hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ hyp.XsetOf ⊥ Z) (hχ₂ne : χ₂ ≠ χ₁)
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hdisj : ∀ φ ∈ hyp.XsetOf ⊥ Z, φ ∉ Y)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁) (hm : 2 ≤ Y.ncard)
    (hsupp : χ₁ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A)
    {z : ↥hyp.H} (hzZ : (z : G) ∈ Z) (hz1 : z ≠ 1) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.XsetOf ⊥ Z ∪ Y) hyp.A) := by
  classical
  have hXS : hyp.XsetOf ⊥ Z ⊆ hyp.Sset := hyp.XsetOf_subset_Sset ⊥ Z
  have hχ₁S : χ₁ ∈ hyp.Sset := hXS hχ₁X
  have hχ₁Y : χ₁ ∉ Y := hdisj χ₁ hχ₁X
  -- the `𝒴`-witness `e'` for `η₁`
  set e' : ClassFunction G ℂ := hcohY.extension η₁ with he'def
  have he'ZIrr : e' ∈ ZIrr G := hcohY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁Y)
  -- (5) cross-orthogonality `⟨E_𝒳 φ, e'⟩ = 0`
  have hcross : ∀ φ ∈ hyp.XsetOf ⊥ Z, ClassFunction.inner (hcohX.extension φ) e' = 0 :=
    fun φ hφ => hyp.cross_extension_inner_eq_zero hXS hYS hdisj hcohX hcohY hχ₁X hXdiff hχ₂X
      hχ₂ne hη₁Y hYdiff hη₂Y hη₂ne hφ hη₁Y
  -- the `𝒴`-witness is `±Irr`
  obtain ⟨ε, ξ, hε, hEeq⟩ :=
    hyp.coherent_extension_eq_zsmul_irr hcohY hη₁Y (hYS hη₁Y).1
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> omega
  -- (6) the coefficient `λ` and norm identity
  obtain ⟨lam, hlam_ne, hlam_1, nvv, hnvv, hident⟩ :=
    hyp.exists_lambda_norm_identity hYS hcohY hχ₁S hχ₁Y hη₁Y hsupp hYdiff
  -- (8) divisibility `a ∣ λ`
  have hη₁ZIrr : η₁ ∈ ZIrr ↥hyp.H := (hYS hη₁Y).1.mem_ZIrr
  have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (by simpa using h))
  have hdvd : (a : ℤ) ∣ lam :=
    hyp.dvd_lam_of_endgame_data hZQ1 hoddG hHallG
      (T := (hyp.XsetOf_finite ⊥ Z).toFinset) (fun φ => Set.Finite.mem_toFinset _)
      hcohX hχ₁X (by omega) hχ₁deg
      (fun φ hφ => (hXdiff φ hφ).imp fun b hb => hb.2)
      he'ZIrr hεne hEeq hcross hη₁ZIrr hlam_1 hzZ hz1
      (hyp.Q_le_centralizer_of_mem_central hZQ1 hZcent hzZ)
      (fun w hwZ hw1 => hyp.inf_centralizer_card_const_of_central hZQ1 hZcent hwZ hw1 hzZ hz1G)
  -- (6) assembly: `a ∣ λ ⟹ 𝒳 ∪ 𝒴` coherent
  exact ⟨hyp.union_coherent_of_lambda_dvd hXS hYS hdisj hcohX hcohY hχ₁X
    (fun φ hφ => (hXdiff φ hφ).imp fun b hb => hb) hχ₂X hχ₂ne hη₁Y hYdiff hη₂Y hη₂ne ha hm hsupp
    hlam_ne hlam_1 hnvv hident hdvd⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
