/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Props109To1011

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S12_MaximalIII_IV_V` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S12
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), dichotomy form.**  Under the (11.8) contradiction hypothesis — the
residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to every `ω_{ij}^σ` — the Dade image
`(μ₀ − ζ)^τ` differs from `∑_r ω_{r0}^σ` by a **single signed coherent extension**: either
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}` (the normalized (11.8.4) form), or the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` and `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ + ζ̄^{τ₁}`.

Textbook proof (p. 66): write `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − χ`.  The orthogonality hypothesis pins
`⟨(μ₀ − ζ)^τ, ω_{r0}^σ⟩ = 1`, so `‖χ‖² = ‖μ₀ − ζ‖² − w₁ = 1` (Dade isometry on the `A₀`-supported
lattice, `‖μ₀ − ζ‖² = w₁ + 1` from `inner_muColumnZero_sub_zeta_self`).  Computing
`⟨(μ₀ − ζ)^τ, (ζ − ζ̄)^τ⟩ = ⟨μ₀ − ζ, ζ − ζ̄⟩ = −1` against the supported split
`(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` and the (5.3.b) orthogonalities `⟨λ^{τ₁}, ∑_r ω_{r0}^σ⟩ = 0` gives
`⟨χ, ζ^{τ₁}⟩ − ⟨χ, ζ̄^{τ₁}⟩ = 1`, with both inner products integers (`ZIrr` pairing) of square
`≤ 1` (Cauchy–Schwarz in the unit-norm integral lattice), whence `⟨χ, ζ^{τ₁}⟩ = 1` (then
`χ = ζ^{τ₁}` by positive definiteness) or `⟨χ, ζ̄^{τ₁}⟩ = −1` (then `χ = −ζ̄^{τ₁}`).  In the second
case any third family member `λ ∈ S₁ − {ζ, ζ̄}` would give
`1 = ⟨μ₀ − ζ, λ − ζ⟩ = ⟨(μ₀ − ζ)^τ, λ^{τ₁} − ζ^{τ₁}⟩ = 0`, so `S₁ = {ζ, ζ̄}`.

The textbook's "we may assume" is the replacement of `τ₁` by its negated conjugate-swap
`λ ↦ −(λ̄)^{τ₁}` in the second branch — deferred to the consumer, since the swap is again a
coherent extension of `τ` on `ℤ[S₁]` precisely because `S₁ = {ζ, ζ̄}` (every `A₀`-supported lattice
element is then an integer multiple of `ζ − ζ̄`). -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_isCoherent hG).extension ζ
    ∨ ((∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
          lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) ∧
        hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
          = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
            + (hyp.SHC_isCoherent hG).extension ζ.conj) := by
  haveI := hyp.finiteG
  classical
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  -- generic unit-norm integral-lattice toolkit: the Cauchy–Schwarz bound `m² ≤ 1` and the
  -- positive-definiteness equalities `⟨A, θ⟩ = ±1 → A = ±θ` for unit-norm `A`, `θ`.
  have hbound : ∀ (A θ : ClassFunction G ℂ) (m : ℤ),
      ClassFunction.inner A A = 1 → ClassFunction.inner A θ = (m : ℂ) →
      ClassFunction.inner θ θ = 1 → m * m ≤ 1 := by
    intro A θ m hA hm hθ
    have hθA : ClassFunction.inner θ A = (m : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hm, star_intCast]
    have hval : ClassFunction.inner (A - (m : ℂ) • θ) (A - (m : ℂ) • θ)
        = ((1 - m * m : ℤ) : ℂ) := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hA, hm, hθA, hθ,
        star_intCast]
      push_cast
      ring
    have hre := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - (m : ℂ) • θ)
    rw [hval] at hre
    have h1 : (0 : ℝ) ≤ ((1 - m * m : ℤ) : ℝ) := by simpa using hre
    have h2 : (0 : ℤ) ≤ 1 - m * m := by exact_mod_cast h1
    linarith
  have heq : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = 1 → ClassFunction.inner θ θ = 1 → A = θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ, star_one]
    have hz : ClassFunction.inner (A - θ) (A - θ) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A - θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact sub_eq_zero.mp h0
  have heqneg : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = -1 → ClassFunction.inner θ θ = 1 → A = -θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = -1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ]
      simp
    have hz : ClassFunction.inner (A + θ) (A + θ) = 0 := by
      rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_add_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A + θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact add_eq_zero_iff_eq_neg.mp h0
  -- conjugate-family facts for `ζ`
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
  have hζcmem : ζ.conj ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζcirr
  -- supports
  have hsupp : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hsuppd : (ζ - ζ.conj).support ⊆ hyp.A0 := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  -- `ψ = (μ₀ − ζ)^τ ∈ ZIrr G`
  have hμ0Z : (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr
  have hψZ : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp hdiffZ
  have heζZ : (hyp.SHC_isCoherent hG).extension ζ ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have heζcZ : (hyp.SHC_isCoherent hG).extension ζ.conj ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ.conj
      (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  -- `M`-side orthogonality facts
  have hμζ : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζ1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hμζc : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ.conj = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζcirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζc1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [irr_cf_inner hζmem hζmem, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [irr_cf_inner hζmem hζcmem, if_neg hζne.symm]
  -- `G`-side norm bookkeeping under the orthogonality hypothesis
  have hΩr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (∑ r' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    rw [inner_sum_left, Finset.sum_eq_single r]
    · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r r 0 0, if_pos ⟨rfl, rfl⟩]
    · intro r' _ hne
      rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r' r 0 0, if_neg fun h => hne h.1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hψr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    have h := horth r 0
    rw [ClassFunction.inner_sub_left, sub_eq_zero] at h
    exact h.trans (hΩr r)
  have hψΩ : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hψr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hΩψ : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩnorm : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hΩr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψnorm : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- `χ = ∑_r ω_{r0}^σ − (μ₀ − ζ)^τ` has norm `1`
  have hχnorm : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hΩnorm, hΩψ, hψΩ, hψnorm]
    push_cast
    ring
  -- the (5.3.b) orthogonalities `⟨∑_r ω_{r0}^σ, λ^{τ₁}⟩ = 0`
  have heΩ : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1 hζne
  have hΩe : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩ, star_zero]
  have hζcne : (ζ.conj).conj ≠ ζ.conj := by
    rw [ClassFunction.conj_conj]
    exact hζne.symm
  have heΩc : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hζcS hζcirr hζc1 hζcne
  have hΩec : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩc, star_zero]
  -- the integer coefficients `s = ⟨ψ, ζ^{τ₁}⟩`, `t = ⟨ψ, ζ̄^{τ₁}⟩` with `s − t = −1`
  obtain ⟨s, hs⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζZ
  obtain ⟨t, ht⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζcZ
  have hGside : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau (ζ - ζ.conj)) = -1 := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsuppd, ClassFunction.inner_sub_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hμζ, hμζc, hζζ, hζζc]
    ring
  rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1,
    ClassFunction.inner_sub_right, hs, ht] at hGside
  have hstz : s - t = -1 := by exact_mod_cast hGside
  -- Cauchy–Schwarz bounds and the integer dichotomy `s = −1 ∨ t = 1`
  have hee : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      ((hyp.SHC_isCoherent hG).extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζS hζirr hζ1
  have heec : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1
  have hmA : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ) = ((-s : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩe, hs]
    push_cast
    ring
  have hmAc : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = ((-t : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩec, ht]
    push_cast
    ring
  have hs2 : s * s ≤ 1 := by
    have h := hbound _ _ (-s) hχnorm hmA hee
    have h' : s * s = -s * -s := by ring
    rw [h']
    exact h
  have ht2 : t * t ≤ 1 := by
    have h := hbound _ _ (-t) hχnorm hmAc heec
    have h' : t * t = -t * -t := by ring
    rw [h']
    exact h
  have hsle : s ≤ 1 := by nlinarith [mul_self_nonneg (s - 1)]
  have hsge : -1 ≤ s := by nlinarith [mul_self_nonneg (s + 1)]
  have htle : t ≤ 1 := by nlinarith [mul_self_nonneg (t - 1)]
  have htge : -1 ≤ t := by nlinarith [mul_self_nonneg (t + 1)]
  have hcase : s = -1 ∨ t = 1 := by omega
  rcases hcase with hsval | htval
  · -- `⟨χ, ζ^{τ₁}⟩ = 1`: `χ = ζ^{τ₁}`, the normalized (11.8.4) form
    left
    have hAe : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ) = 1 := by
      rw [ClassFunction.inner_sub_left, hΩe, hs, hsval]
      push_cast
      ring
    have hχe := heq _ _ hχnorm hAe hee
    rw [← hχe]
    abel
  · -- `⟨χ, ζ̄^{τ₁}⟩ = −1`: `χ = −ζ̄^{τ₁}` and `S₁ = {ζ, ζ̄}`
    right
    have hAec : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ.conj) = -1 := by
      rw [ClassFunction.inner_sub_left, hΩec, ht, htval]
      push_cast
      ring
    have hχec := heqneg _ _ hχnorm hAec heec
    have hψeq : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [sub_eq_iff_eq_add] at hχec
      rw [hχec]
      abel
    refine ⟨fun lam hlamS hlamirr hlam1 => ?_, hψeq⟩
    by_contra hboth
    rw [not_or] at hboth
    obtain ⟨hlamzeta, hlamzetac⟩ := hboth
    have hlamne : lam.conj ≠ lam := hyp.inducedFamily_degree_w1_conj_ne hG hlamirr hlam1
    have hmulam : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) lam = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hlamirr ?_
      rw [hyp.muGrid_zero_column_apply_one hG hodd i, hlam1]
      intro he
      have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
      omega
    have hlammem : lam ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hlamirr
    have hzetalam : ClassFunction.inner ζ lam = 0 := by
      rw [irr_cf_inner hζmem hlammem, if_neg (Ne.symm hlamzeta)]
    have hsupplam : (lam - ζ).support ⊆ hyp.A0 :=
      hyp.inducedFamily_sub_support hlamS hζS (by rw [hlam1, hζ1])
    have hGlam : ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.tau (lam - ζ)) = 1 := by
      rw [hyp.tau_inner_eq_of_supported hsupp hsupplam, ClassFunction.inner_sub_left,
        ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hmulam, hμζ, hzetalam, hζζ]
      ring
    have hspanlam : lam ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hlamS, hlamirr, hlam1⟩
    have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
    have hmemsupp : (lam - ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
      ⟨Submodule.sub_mem _ hspanlam hspanζ, hsupplam⟩
    have htaulam : hyp.tau (lam - ζ) = (hyp.SHC_isCoherent hG).extension lam
        - (hyp.SHC_isCoherent hG).extension ζ := by
      rw [← (hyp.SHC_isCoherent hG).extends_on_supported _ hmemsupp, map_sub]
    have heOmegalam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hlamS hlamirr hlam1 hlamne
    have hOmegalam : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, heOmegalam, star_zero]
    have heclam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hlamS hlamirr hlam1 (Ne.symm hlamzetac)
    have hece : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension ζ) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hζS hζirr hζ1 hζne
    rw [htaulam, ClassFunction.inner_sub_right, hψeq, ClassFunction.inner_add_left,
      ClassFunction.inner_add_left, hOmegalam, heclam, hΩe, hece] at hGlam
    norm_num at hGlam

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the branch-2 "we may assume" swap.**  When the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` (the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`), the map `φ ↦ −(ζ̄-side extension of φ̄)`, i.e.
`SHC_swap.extension φ = −(SHC_isCoherent.extension φ.conj)`, is again a **coherent extension of `τ`
to `ℤ[S(HC)]`** — the textbook's replacement of `ζ^{τ₁}, ζ̄^{τ₁}` by `−ζ̄^{τ₁}, −ζ^{τ₁}` (p. 66).

The four `IsCoherent` fields:
* **isometry on `ℤ[S(HC)]`**: `S(HC)` is closed under conjugation (`inducedFamily` is, degrees are
  preserved), so `φ̄, ψ̄ ∈ ℤ[S(HC)]`; `⟨SHC(φ̄), SHC(ψ̄)⟩ = ⟨φ̄, ψ̄⟩ = star⟨φ,ψ⟩ = ⟨φ,ψ⟩`
  (`inner_conj_conj` and the reality of a `ZIrr` pairing);
* **agrees with `τ` on `ℤ[S(HC), A₀]`**: this is where `S(HC) = {ζ, ζ̄}` is used — every
  `A₀`-supported element of `span{ζ, ζ̄}` is a multiple `a(ζ − ζ̄)` (value at `1` is `(a+b)w₁ = 0`), on which
  `SHC_swap` and `SHC` both send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁} = τ(ζ − ζ̄)`;
* **maps into `ZIrr`** and **nonzero-supported witness `ζ − ζ̄`**: inherited from `SHC`.

Combined with the dichotomy this gives the h114-producing extension in *both* branches (branch 1:
`SHC_isCoherent`; branch 2: this swap), i.e. Peterfalvi's "we may assume `(μ₀−ζ)^τ = ∑ω − ζ^{τ₁}`"
holds for a canonical choice of coherent `τ₁`. -/
noncomputable def Hypothesis.SHC_swap [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  set SHCset : Set (ClassFunction ↥M ℂ) :=
    {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} with hSHCset
  -- the `ζ̄`-side degree-`w₁` conjugate facts
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ SHCset := ⟨hζS, hζirr, hζ1⟩
  have hζcmem : ζ.conj ∈ SHCset := ⟨hζcS, hζcirr, hζc1⟩
  -- `SHCset` is closed under conjugation.
  have hconj_closed : ∀ φ ∈ SHCset, φ.conj ∈ SHCset := by
    rintro φ ⟨hφS, hφirr, hφ1⟩
    exact ⟨inducedFamily_closedUnderConjugate M hφS, hφirr.conj, by
      rw [ClassFunction.conj_apply, hφ1, star_natCast]⟩
  -- the swap extension `φ ↦ −SHC(φ̄)`, packaged as an integral character map.
  set ext' : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
    -((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv)) with hext'def
  have hconjbridge : ∀ φ : ClassFunction ↥M ℂ,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj := fun φ => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hext'apply : ∀ φ : ClassFunction ↥M ℂ,
      ext' φ = -((hyp.SHC_isCoherent hG).extension φ.conj) := by
    intro φ
    rw [hext'def, LinearMap.neg_apply, LinearMap.comp_apply,
      ClassFunction.mapRingEquivLinear_apply, hconjbridge]
  have hconj_zsmul : ∀ (n : ℤ) (x : ClassFunction ↥M ℂ), (n • x).conj = n • x.conj := by
    intro n x
    rw [← hconjbridge (n • x), ClassFunction.mapRingEquiv_zsmul, hconjbridge x]
  -- span-level conjugation closure.
  have hspan_conj : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ.conj ∈ OddOrder.Peterfalvi.S07.zSpan SHCset := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hconj_closed x hx)
    | zero => rw [ClassFunction.conj_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [ClassFunction.conj_add]; exact Submodule.add_mem _ hx hy
    | smul n x _ hx => rw [hconj_zsmul]; exact Submodule.smul_mem _ n hx
  -- span elements are `ZIrr`-members (so pairings are integers, hence real).
  have hspan_ZIrr : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ ∈ ZIrr ↥M := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.2.1.mem_ZIrr
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul n x _ hx => exact Submodule.smul_mem _ n hx
  refine ⟨⟨ζ - ζ.conj, ⟨?_, ?_⟩, ?_⟩, ext', ?_, ?_, ?_⟩
  · -- `ζ − ζ̄ ∈ ℤ[S(HC)]`
    exact Submodule.sub_mem _ (Submodule.subset_span hζmem) (Submodule.subset_span hζcmem)
  · -- `ζ − ζ̄` is `A₀`-supported
    exact hyp.zeta_sub_conj_support hG hodd hζS hζirr
  · -- `ζ − ζ̄ ≠ 0`
    intro h
    exact hζne (sub_eq_zero.mp h).symm
  · -- **isometry on `ℤ[S(HC)]`**
    intro φ ψ hφ hψ
    have hφc := hspan_conj φ hφ
    have hψc := hspan_conj ψ hψ
    rw [hext'apply φ, hext'apply ψ, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
      neg_neg, (hyp.SHC_isCoherent hG).extension_inner_eq _ _ hφc hψc,
      OddOrder.RepresentationTheory.inner_conj_conj]
    obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int (hspan_ZIrr φ hφ) (hspan_ZIrr ψ hψ)
    rw [hm, star_intCast]
  · -- **agrees with `τ` on `ℤ[S(HC), A₀]`** — uses `S(HC) = {ζ, ζ̄}`
    rintro φ ⟨hφspan, hφsupp⟩
    -- `S(HC) = {ζ, ζ̄}` as sets, so `ℤ[S(HC)] = span{ζ, ζ̄}`.
    have hset_eq : SHCset = {ζ, ζ.conj} := by
      apply Set.eq_of_subset_of_subset
      · rintro x ⟨hxS, hxirr, hx1⟩
        exact htwo x hxS hxirr hx1
      · rintro x (rfl | rfl)
        · exact hζmem
        · exact hζcmem
    have hφpair : φ ∈ Submodule.span ℤ ({ζ, ζ.conj} : Set (ClassFunction ↥M ℂ)) := by
      rwa [OddOrder.Peterfalvi.S07.zSpan, hset_eq] at hφspan
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hφpair
    -- support in `A₀` (which excludes `1`) forces the value at `1` to vanish, so `a + b = 0`.
    have h1notA : (1 : ↥M) ∉ hyp.A0 := by
      intro h1
      have hg : ((1 : ↥M) : G) ∈ typePA0 M hyp.typeP := h1
      rw [OneMemClass.coe_one] at hg
      exact hyp.dadeData.dade.ne_one hg rfl
    have hφ1 : φ 1 = 0 := by
      by_contra hne
      exact h1notA (hφsupp (Function.mem_support.mpr hne))
    have hval1 : (a : ℂ) * (hyp.w1 : ℂ) + (b : ℂ) * (hyp.w1 : ℂ) = 0 := by
      have hc := congrArg (fun f : ClassFunction ↥M ℂ => (f : ↥M → ℂ) 1) hab
      simp only [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.add_apply,
        ClassFunction.smul_apply] at hc
      rw [hζ1, hζc1] at hc
      rw [hc]; exact hφ1
    have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
      have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
      exact_mod_cast (by omega : hyp.w1 ≠ 0)
    have hab0 : a + b = 0 := by
      have hfac : ((a : ℂ) + (b : ℂ)) * (hyp.w1 : ℂ) = 0 := by linear_combination hval1
      have hz : (a : ℂ) + (b : ℂ) = 0 := (mul_eq_zero.mp hfac).resolve_right hw1ne
      exact_mod_cast hz
    have hb : b = -a := by omega
    -- so `φ = a(ζ − ζ̄)`.
    have hφeq : φ = (a : ℤ) • (ζ - ζ.conj) := by
      rw [← hab, hb]; module
    -- both `SHC_swap` and `τ` send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁}`.
    have hswapdiff : ext' (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [map_sub, hext'apply ζ, hext'apply ζ.conj, ClassFunction.conj_conj]
      abel
    have htaudiff : hyp.tau (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj :=
      hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1
    rw [hφeq, map_zsmul, map_zsmul, hswapdiff, htaudiff]
  · -- **maps into `ZIrr`**
    intro φ hφ
    rw [hext'apply φ]
    exact neg_mem ((hyp.SHC_isCoherent hG).extension_mem_ZIrr φ.conj (hspan_conj φ hφ))

open scoped FiniteInduce in
/-- **h114 for the branch-2 swap.**  In the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal` (`S(HC) = {ζ, ζ̄}` and
`(μ₀−ζ)^τ = ∑ω_{r0}^σ + ζ̄^{τ₁}`), the swapped coherent extension `SHC_swap` satisfies the
normalized (11.8.4) identity `(μ₀−ζ)^τ = ∑ω_{r0}^σ − SHC_swap.extension ζ`: indeed
`SHC_swap.extension ζ = −ζ̄^{τ₁}`, so `∑ω − SHC_swap(ζ) = ∑ω + ζ̄^{τ₁} = (μ₀−ζ)^τ`.  This is the
h114-form the (11.8.5) capstone consumes, now available in branch 2 with the swapped `τ₁`. -/
theorem Hypothesis.SHC_swap_h114 [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    (hbranch2 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ := by
  haveI := hyp.finiteG
  classical
  have hswapζ : (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ
      = -((hyp.SHC_isCoherent hG).extension ζ.conj) := by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) ζ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ = ζ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswapζ, sub_neg_eq_add, hbranch2]

open scoped FiniteInduce in
/-- **The branch-2 swap commutes with complex conjugation** (the `hconj` P4 input the (11.8.5)
capstone `residualCoeff_eq_zero` needs for the swap branch).  For a degree-`w₁` irreducible
`χ ∈ S(HC)`, `(SHC_swap.extension χ)‾ = SHC_swap.extension χ‾`.  Both sides equal `−SHC(χ‾‾)`:
`SHC_swap.extension φ = −SHC(φ‾)`, so `(SHC_swap χ)‾ = (−SHC(χ‾))‾ = −(SHC(χ‾))‾ = −SHC(χ‾‾)`
(the last by `SHC_extension_conj` at `χ‾`), while `SHC_swap χ‾ = −SHC(χ‾‾)` directly. -/
theorem Hypothesis.SHC_swap_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    ((hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ).conj
      = (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ.conj := by
  haveI := hyp.finiteG
  classical
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hχc1 : χ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hχ1, star_natCast]
  have hswap : ∀ φ : ClassFunction ↥M ℂ, (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension φ
      = -((hyp.SHC_isCoherent hG).extension φ.conj) := fun φ => by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) φ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswap χ, hswap χ.conj, ClassFunction.conj_neg,
    hyp.SHC_extension_conj hG hχcS hχcirr hχc1]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the h114-producing coherent extension.**  Under the (11.8) contradiction
hypothesis (the residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to `(Irr W)^σ`), there is a
coherent extension `ν` of `τ` to `ℤ[S(HC)]` for which the normalized (11.8.4) identity
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ν.extension ζ` holds.  In the generic (first-branch) case `ν` is the
canonical `SHC_isCoherent`; in the degenerate `S(HC) = {ζ, ζ̄}` case `ν` is the conjugate-swap
`SHC_swap` — Peterfalvi's "we may assume `(μ₀ − ζ)^τ = ∑ω_{i0}^σ − ζ^{τ₁}`" (p. 66), now a clean
`∃`-statement with no residual sorry.  This is the interface the (11.8.5) capstone consumes once its
`τ₁`-machinery is taken over an arbitrary coherent extension. -/
theorem Hypothesis.exists_coherent_extension_h114_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0,
      (∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
        χ 1 = (hyp.w1 : ℂ) → (ν.extension χ).conj = ν.extension χ.conj) ∧
      hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - ν.extension ζ := by
  rcases hyp.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal hG hodd hζS hζirr hζ1 horth with
    h1 | ⟨htwo, h2⟩
  · exact ⟨hyp.SHC_isCoherent hG,
      (fun hχS hχirr hχ1 => hyp.SHC_extension_conj hG hχS hχirr hχ1), h1⟩
  · exact ⟨hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo,
      (fun hχS hχirr hχ1 => hyp.SHC_swap_conj hG hodd hζS hζirr hζ1 htwo hχS hχirr hχ1),
      hyp.SHC_swap_h114 hG hodd hζS hζirr hζ1 htwo h2⟩

open scoped Classical in
/-- **Cross-Parseval for a virtual character.**  For `Δ ∈ ZIrr G` and any `φ`,
`⟨φ, Δ⟩ = ∑_{χ : Irr} ⟨φ, χ⟩ · ⟨Δ, χ⟩`.  From the Fourier reconstruction `Δ = ∑_χ ⟨Δ,χ⟩·χ`
(`sum_inner_irreducibleCharacter_smul`) and `inner_smul_right`; the `star` from conjugate-linearity
vanishes because `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`). -/
theorem mem_ZIrr_inner_eq_sum_over_irr [Finite G] [Fintype G] [Fintype (IrreducibleCharacter G)]
    [Invertible (Nat.card G : ℂ)] {φ Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) :
    ClassFunction.inner φ Δ
      = ∑ χ : IrreducibleCharacter G,
          ClassFunction.inner φ (χ : ClassFunction G ℂ)
            * ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  conv_lhs => rw [← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul Δ]
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast, mul_comm]

/-- **Parity of a sum over a fixed-point-free involution** with an involution-invariant integer
weight.  If `g` is a fixed-point-free involution on `s` and `f (g a) = f a` for all `a ∈ s`, then
`∑_{a ∈ s} f a` is even — each orbit `{a, g a}` contributes `2·f a`.  (Proof via `ZMod 2`:
`(f a : ZMod 2) + (f (g a) : ZMod 2) = 2·(f a) = 0`, so `Finset.sum_involution` kills the sum mod 2.)
This is the combinatorial core of the Peterfalvi (11.8.5) "`a` even from `β` real" parity — the
conjugation involution `χ ↦ χ̄` on `Irr G ∖ {1}` is fixed-point-free by Peterfalvi (1.1). -/
theorem even_sum_of_involution {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℤ}
    (g : ∀ a ∈ s, α) (g_mem : ∀ a ha, g a ha ∈ s) (g_ne : ∀ a ha, g a ha ≠ a)
    (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a) (hf : ∀ a ha, f (g a ha) = f a) :
    Even (∑ a ∈ s, f a) := by
  suffices h : ((∑ a ∈ s, f a : ℤ) : ZMod 2) = 0 by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by push_cast at hk; omega⟩
  rw [Int.cast_sum]
  refine Finset.sum_involution g ?_ (fun a ha _ => g_ne a ha) g_mem g_inv
  intro a ha
  rw [hf a ha]
  exact CharTwo.add_self_eq_zero _

/-- **Inner product of two conjugated class functions** `⟨φ̄, ψ̄⟩ = conj ⟨φ, ψ⟩`.  Pointwise:
`∑_g star(φ g)·ψ g = conj (∑_g φ g · star(ψ g))`, and `⅟|G|` is real. -/
theorem inner_conj_conj [Fintype G] [Invertible (Nat.card G : ℂ)] (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ.conj ψ.conj = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum φ.conj ψ.conj = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply, star_mul, star_star, mul_comm]
  have hcard : (Nat.card G : ℂ) ≠ 0 := (isUnit_of_invertible (Nat.card G : ℂ)).ne_zero
  refine mul_left_cancel₀ hcard ?_
  rw [ClassFunction.card_mul_inner, hsum, ← ClassFunction.card_mul_inner, star_mul, star_natCast,
    mul_comm]

/-- For a **real** `Δ ∈ ZIrr G`, the Fourier coefficient is `conjPerm`-symmetric:
`⟨Δ, χ̄⟩ = ⟨Δ, χ⟩`.  Since `Δ̄ = Δ` (`IsReal`), `⟨Δ, χ̄⟩ = ⟨Δ̄, χ̄⟩ = conj⟨Δ,χ⟩` (`inner_conj_conj`),
and `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`), so the `conj` is inert. -/
theorem inner_conjPerm_eq_of_isReal [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) (hr : ClassFunction.IsReal Δ)
    (χ : IrreducibleCharacter G) :
    ClassFunction.inner Δ
        ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ)
      = ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  rw [IrreducibleCharacter.conjPerm_apply_coe]
  have key : ClassFunction.inner Δ ((χ : ClassFunction G ℂ).conj)
      = ClassFunction.inner Δ.conj ((χ : ClassFunction G ℂ).conj) := by rw [hr]
  rw [key, inner_conj_conj]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast]

open scoped Classical in
/-- **Parity of the inner product of two real virtual characters orthogonal to `1`** (Peterfalvi
(11.8.5) "`a` even from `β` real").  For `Δ₁, Δ₂ ∈ ZIrr G` (odd `G`) that are real (`IsReal`) — hence
with `conjPerm`-symmetric Fourier coefficients `⟨Δᵢ, χ̄⟩ = ⟨Δᵢ, χ⟩` — with `⟨Δ₂, 1⟩ = 0` (only one
factor need be orthogonal to `1`, since the `χ = 1` term `c₁(1)·c₂(1)` vanishes), the integer
`⟨Δ₁, Δ₂⟩` is even.  Cross-Parseval (`mem_ZIrr_inner_eq_sum_over_irr`) gives
`⟨Δ₁,Δ₂⟩ = ∑_χ c₁(χ)c₂(χ)` with `cᵢ(χ) = ⟨Δᵢ,χ⟩ ∈ ℤ`; the `χ = 1` term vanishes, and on `Irr ∖ {1}`
the conjugation involution `conjPerm` is fixed-point-free (`conjPerm_eq_self_iff` +
`not_isReal_of_ne_trivial_of_odd_card'`) with `cᵢ` invariant, so `even_sum_of_involution` applies. -/
theorem even_inner_of_conjPerm_symmetric [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hodd : Odd (Nat.card G))
    {Δ₁ Δ₂ : ClassFunction G ℂ} (h₁ : Δ₁ ∈ ZIrr G) (h₂ : Δ₂ ∈ ZIrr G)
    (hr₁ : ClassFunction.IsReal Δ₁) (hr₂ : ClassFunction.IsReal Δ₂)
    (htriv₂ : ClassFunction.inner Δ₂ (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0) :
    ∃ z : ℤ, ClassFunction.inner Δ₁ Δ₂ = (z : ℂ) ∧ Even z := by
  have hsym₁ := fun χ => inner_conjPerm_eq_of_isReal h₁ hr₁ χ
  have hsym₂ := fun χ => inner_conjPerm_eq_of_isReal h₂ hr₂ χ
  choose c₁ hc₁ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₁
  choose c₂ hc₂ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₂
  have hz : ClassFunction.inner Δ₁ Δ₂
      = ((∑ χ : IrreducibleCharacter G, c₁ χ * c₂ χ : ℤ) : ℂ) := by
    rw [mem_ZIrr_inner_eq_sum_over_irr h₂]
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by rw [hc₁ χ, hc₂ χ]
  refine ⟨_, hz, ?_⟩
  have hc2t : c₂ (trivialIrreducibleCharacter G) = 0 := by
    have hh := hc₂ (trivialIrreducibleCharacter G); rw [htriv₂] at hh; exact_mod_cast hh.symm
  have hsymc₁ : ∀ χ, c₁ (IrreducibleCharacter.conjPerm G χ) = c₁ χ := fun χ => by
    have hh := ((hc₁ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₁ χ)).trans (hc₁ χ)
    exact_mod_cast hh
  have hsymc₂ : ∀ χ, c₂ (IrreducibleCharacter.conjPerm G χ) = c₂ χ := fun χ => by
    have hh := ((hc₂ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₂ χ)).trans (hc₂ χ)
    exact_mod_cast hh
  have htrivfix : IrreducibleCharacter.conjPerm G (trivialIrreducibleCharacter G)
      = trivialIrreducibleCharacter G :=
    (IrreducibleCharacter.conjPerm_eq_self_iff (trivialIrreducibleCharacter G)).mpr (by simp)
  rw [← Finset.add_sum_erase Finset.univ (fun χ => c₁ χ * c₂ χ)
      (Finset.mem_univ (trivialIrreducibleCharacter G)),
    hc2t, mul_zero, zero_add]
  refine even_sum_of_involution (fun χ _ => IrreducibleCharacter.conjPerm G χ)
    (fun χ hχ => ?_) (fun χ hχ => ?_) (fun χ _ => (IrreducibleCharacter.conjPerm G).left_inv χ)
    (fun χ _ => by rw [hsymc₁, hsymc₂])
  · rw [Finset.mem_erase] at hχ ⊢
    refine ⟨fun h => hχ.1 ?_, Finset.mem_univ _⟩
    exact (IrreducibleCharacter.conjPerm G).injective (h.trans htrivfix.symm)
  · rw [Finset.mem_erase] at hχ
    intro h
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hχ.1
      ((IrreducibleCharacter.conjPerm_eq_self_iff χ).mp h)

open scoped Classical FiniteInduce in
/-- **The `σ`-column sum `∑_r ω_{r0}^σ` is real** (Peterfalvi (3.9)(a)).  The column-`0` `σ`-images
are permuted by the row-conjugation involution `σ` (`exists_rowInv_alignedOmegaSigma_conj`:
`conj ω_{r0}^σ = ω_{σr,0}^σ`), so the sum is conjugation-invariant.  This is the `M`-side reality
feeding the (11.8.5) `a = ⟨∑ω_{r0}^σ, β⟩` parity (`even_inner_of_conjPerm_symmetric`). -/
theorem Hypothesis.sum_alignedOmegaSigma_zeroColumn_isReal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ClassFunction.IsReal (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) := by
  haveI := hyp.finiteG
  classical
  choose σ hσ using fun i => hyp.exists_rowInv_alignedOmegaSigma_conj hG hodd i
  have hbridge : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hgridinj : ∀ a b : Fin hyp.w1,
      hyp.alignedOmegaSigmaGrid hG hodd a 0 = hyp.alignedOmegaSigmaGrid hG hodd b 0 → a = b := by
    intro a b hab
    by_contra hne
    have hii := hyp.alignedOmegaSigmaGrid_inner hG hodd a b 0 0
    rw [← hab, hyp.alignedOmegaSigmaGrid_inner hG hodd a a 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun h => hne h.1)] at hii
    exact one_ne_zero hii
  have hσinv : Function.Involutive σ := fun r => by
    apply hgridinj
    calc hyp.alignedOmegaSigmaGrid hG hodd (σ (σ r)) 0
        = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0) := ((hσ (σ r)).1).symm
      _ = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd r 0)) := by rw [(hσ r).1]
      _ = hyp.alignedOmegaSigmaGrid hG hodd r 0 := by
            rw [← hbridge, ← hbridge, ClassFunction.conj_conj]
  have hconjsum : ∀ s : Finset (Fin hyp.w1),
      (∑ r ∈ s, hyp.alignedOmegaSigmaGrid hG hodd r 0).conj
        = ∑ r ∈ s, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, ClassFunction.conj_add, ih, Finset.sum_insert ha]
  rw [ClassFunction.IsReal, hconjsum Finset.univ,
    show (∑ r : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj)
        = ∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0 from
      Finset.sum_congr rfl fun r _ => by rw [hbridge]; exact (hσ r).1]
  exact Equiv.sum_comp (Equiv.ofBijective σ hσinv.bijective)
    (fun r => hyp.alignedOmegaSigmaGrid hG hodd r 0)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), the "`a` even" step** (assembled).  If `a = ⟨∑_r ω_{r0}^σ, β⟩` with `β` a
real virtual character orthogonal to `1_G` (Peterfalvi (11.8.3): `β` is `i,j`-independent and real),
then `a` is even.  Both factors are real (`∑ω_{r0}^σ` via `sum_alignedOmegaSigma_zeroColumn_isReal`,
`β` by hypothesis) and lie in `ℤ[Irr G]`, and `β ⊥ 1`, so `even_inner_of_conjPerm_symmetric` gives
the parity.  This excludes `a = 1` (odd), so with `a ∈ {0,1,2}` (11.8.2) it forces `a ∈ {0,2}`, the
input to `charParam_a_eq_zero_of_residualEq`. -/
theorem Hypothesis.a_even_of_eq_inner_sumOmegaSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {β : ClassFunction G ℂ} (hβZ : β ∈ ZIrr G)
    (hβr : ClassFunction.IsReal β)
    (hβ1 : ClassFunction.inner β (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0)
    {a : ℤ} (ha : (a : ℂ)
      = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) β) :
    Even a := by
  haveI := hyp.finiteG
  have hωZ : (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) ∈ ZIrr G :=
    Submodule.sum_mem _ fun r _ => hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd r 0
  have hωr := hyp.sum_alignedOmegaSigma_zeroColumn_isReal hG hodd
  obtain ⟨z, hz, hev⟩ := even_inner_of_conjPerm_symmetric hodd hωZ hβZ hωr hβr hβ1
  have haz : a = z := by
    have hcast : (a : ℂ) = (z : ℂ) := ha.trans hz
    exact_mod_cast hcast
  rw [haz]; exact hev

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ⊥ 1_G`** (`i ≠ 0`): `⟨α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁},
1_G⟩ = 0`.  Via the Dade adjoint `tau_inner_trivial` (`⟨α_{ij}^τ, 1_G⟩ = ⟨α_{ij}, 1_M⟩ = 0`, `hα1M`);
`1_G = ω_{00}^σ` (`alignedOmegaSigmaGrid_zero_zero`), so `⟨ω_{ij}^σ − ω_{i0}^σ, 1_G⟩ = 0`
(`alignedOmegaSigmaGrid_inner`, using `i ≠ 0`); and `⟨ζ^{τ₁}, 1_G⟩ = 0`
(Peterfalvi (5.3.b), `SHC_extension_inner_alignedOmegaSigma_eq_zero`).  This is the `β ⊥ 1` input to
the `a`-even parity `a_even_of_eq_inner_sumOmegaSigma`. -/
theorem Hypothesis.beta_inner_trivial [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hα1M : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      (trivialClassFunction ↥M) = 0) :
    ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialClassFunction G) = 0 := by
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hατ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (trivialClassFunction G) = 0 := by
    rw [hyp.tau_inner_trivial hsupp]; exact hα1M
  have hωdiff1 : ClassFunction.inner
      (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, ClassFunction.inner_sub_left,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 j 0,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 0 0,
      if_neg (fun h => hi0 h.1), if_neg (fun h => hi0 h.1), sub_zero]
  have hζτ1 : ClassFunction.inner (coh.extension ζ)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd]
    exact hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne 0 0
  rw [ClassFunction.inner_add_left, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hατ1, hωdiff1, hζτ1, mul_zero, mul_zero, sub_zero, add_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ∈ ℤ[Irr G]`**: the (11.8.3) residual `β = α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ) + nζ^{τ₁}` is a virtual character.  `α_{ij}^τ ∈ ZIrr` (`muGridAlpha_tau_mem_ZIrr`), the
aligned `σ`-grid entries `∈ ZIrr` (`alignedOmegaSigmaGrid_mem_ZIrr`), and `ζ^{τ₁} ∈ ZIrr`
(`SHC_isCoherent.extension_mem_ZIrr`); `ZIrr G` is closed under `ℤ`/`ℕ`-linear combinations. -/
theorem Hypothesis.beta_mem_ZIrr [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ) ∈ ZIrr G := by
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζτZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hωZ : (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      ∈ ZIrr G :=
    Submodule.sub_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j)
      (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i 0)
  refine Submodule.add_mem _ (Submodule.sub_mem _ hαZ ?_) ?_
  · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hωZ δ
  · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζτZ n

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `⟨α_{ij}, 1_M⟩ = 0` for `i ≠ 0`**: the pre-Dade residual
`α_{ij} = μ_{ij} − δμ_{i0} − nζ` is orthogonal to the principal character of `M`.  The principal
character sits at the grid origin `μ_{00} = 1_M` (`muGrid_zero_zero_eq_trivial`), so for `i ≠ 0`,
`j ≠ 0` all three constituents avoid it: `⟨μ_{ij}, 1_M⟩ = ⟨μ_{ij}, μ_{00}⟩ = 0` (cross-column,
`j ≠ 0`), `⟨μ_{i0}, 1_M⟩ = ⟨μ_{i0}, μ_{00}⟩ = 0` (within-column, `i ≠ 0`), and `⟨ζ, 1_M⟩ = 0`
(`ζ(1) = w₁ > 1 ≠ 1`).  This discharges the `hα1M` hypothesis of `beta_inner_trivial`, making
`β ⊥ 1_G` unconditional for `i ≠ 0`. -/
theorem Hypothesis.muGridAlpha_inner_trivial_M [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} (hi0 : i ≠ 0) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {δ : ℤ} {n : ℕ} :
    ClassFunction.inner
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (trivialClassFunction (↥M)) = 0 := by
  have hμij : ClassFunction.inner (hyp.muGrid hG hodd i j) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_cross_column hG hodd i 0 hj0
  have hμi0 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_within_column hG hodd 0 hi0
  have hζ : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hζ1, trivialClassFunction_apply] at h1
    have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hμij, hμi0, hζ,
    mul_zero, mul_zero, sub_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), the parity anchor `a = (∑_r ω_{r0}^σ, β)`**: the residual coefficient `a`
(defined by `(α_{ij}^τ, ζ^{τ₁}) = a − n`, `hinner`) equals the `σ`-grid inner product of the (11.8.3)
residual `β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}`.  This is the identity feeding the parity
assembly `a_even_of_eq_inner_sumOmegaSigma` (β real virtual character ⊥ 1 ⇒ `a` even), the input
that excludes `a = 1` unconditionally.  Computation: `(α_{ij}^τ, ∑_r ω_{r0}^σ) = a − δ` (from
`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta` `= n − δ`, the (11.8.4) rewrite `h114`, and `hinner`);
`(ω^σ diff, ∑ω) = −1` (`alignedOmegaSigma_diff_inner_zeroColumnSum`); `(ζ^{τ₁}, ∑ω) = 0`
(`SHC_extension_inner_zeroColumnOmegaSigma_sum`, (5.3.b)) — so `(β, ∑ω) = (a − δ) − δ·(−1) + 0 = a`,
and conjugate-symmetry gives `(∑ω, β) = a`.  The `δ` in `β`'s coefficient cancels the `δ` from the
`α^τ` term, so this holds for **all** `δ` (not only `δ = 1`). -/
theorem Hypothesis.muGridAlpha_a_eq_inner_sumOmegaSigma_beta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {a : ℤ}
    (hinner : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ))
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    (a : ℂ) = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
          + (n : ℂ) • coh.extension ζ) := by
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) - (δ : ℂ) := by
    have h := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1 hdeg hμ0
      hnf hδj hdζ h0ζ
    rw [h114, ClassFunction.inner_sub_right, hinner] at h
    linear_combination h
  have hβω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, hαω,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne,
      star_natCast, star_intCast]
    ring
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hβω, star_intCast]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `a = 0` under the (11.8.4) hypothesis** (the residual-orthogonal case).
Given the (11.8.4) by-contradiction consequence `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}` (`μ₀ = ∑ μ_{i'0}`),
the two-way computation of `(α_{ij}^τ, (μ₀ − ζ)^τ)` forces `a = 0` when `a ∈ {0, 2}`:
* `M`-side (via the Dade isometry, `muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`): `= n − δ`;
* `G`-side (via (11.8.4) + the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`
  for `a ∈ {0, 2}`, `SHC_residual_eq_omegaSigma_diff`, with `(ω^σ diff, ∑ω_{r0}^σ) = −1`
  (`alignedOmegaSigma_diff_inner_zeroColumnSum`) and the (5.3.b) orthogonalities
  `(ζ^{τ₁}, ∑ω) = (∑β, ∑ω) = 0`): `= −δ − (a − n) = n − δ − a`.
Equating gives `a = 0`.  With the parity `a` even (Peterfalvi (11.8.3), `β` real, excluding `a = 1`)
this is the full (11.8.5): under the residual-orthogonality assumption every column coefficient
`a = 0`, the key input to (11.8.6)'s `μ_j^{τ₂} = ∑ ω_{ij}^σ` coherence contradiction. -/
theorem Hypothesis.charParam_a_eq_zero_of_residualEq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      (Even a → a = 0) := by
  obtain ⟨a, Y, hbound, hinner, hYeq, hdecompA⟩ :=
    hyp.SHC_residual_eq_omegaSigma_diff hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm
      hn2 hRn hZ horth hRmem hRrev
  refine ⟨a, hbound, hinner, ?_⟩
  intro heven
  -- `a` even and `a ∈ {0,1,2}` gives `a ∈ {0,2}` (Peterfalvi (11.8.3)/(11.8.5): the parity `a` even
  -- from `β` real excludes `a = 1`).
  have ha02 : a = 0 ∨ a = 2 := by
    rcases hbound with h | h | h
    · exact Or.inl h
    · obtain ⟨k, hk⟩ := heven; omega
    · exact Or.inr h
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hYd := hYeq ha02
  have htrans := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1
    hdeg hμ0 hnf hδj hdζ h0ζ
  rw [h114] at htrans
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = -(δ : ℂ) := by
    rw [hdecompA, hYd]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne,
      hyp.R_sum_inner_zeroColumnOmegaSigma_sum hG coh hodd hRrev,
      star_natCast, star_intCast]
    ring
  rw [ClassFunction.inner_sub_right, hαω, hinner] at htrans
  have ha0 : (a : ℂ) = 0 := by linear_combination -htrans
  exact_mod_cast ha0

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), unconditional `a = 0`**.  Combines the conditional (11.8.5)
`charParam_a_eq_zero_of_residualEq` (which gives `a ∈ {0,1,2}` and the implication
`Even a → a = 0`) with the parity assembly: the (11.8.3) residual
`β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` is a virtual character (`beta_mem_ZIrr`) orthogonal
to `1_G` (`beta_inner_trivial`, its `hα1M` discharged by `muGridAlpha_inner_trivial_M` for `i ≠ 0`),
**real** (`beta_isReal`, the (11.8.3) reality), and `a = (∑_r ω_{r0}^σ, β)`
(`muGridAlpha_a_eq_inner_sumOmegaSigma_beta`); so `a` is even
(`a_even_of_eq_inner_sumOmegaSigma`, the general reality-parity of an integer inner product of
real virtual characters one of which is `⊥ 1_G` in odd order), which excludes `a = 1`.  Hence
`a = 0` unconditionally, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.  This is the full (11.8.5).

The formerly-threaded row-`0` (4.8)/(4.10) Dade identities `h48`/`h410` are now **discharged**
from the §10 instantiation of Hypothesis (4.6) (`tau_muGrid_zeroRow_diff` /
`tau_muGrid_fourCorner` via `toHypothesis46`, issue 9004); the residual input is the
`w₂`-primality `hw2` they need for the (10.3) cross-column degree constancy. -/
theorem Hypothesis.residualCoeff_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ} (hw2 : (hyp.w2).Prime)
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ) := by
  -- the (4.8)/(4.10) Dade identities, discharged from the §10 instantiation of (4.6)
  have hdeg0 : hyp.muGrid hG hodd 0 j 1 = (d : ℂ) :=
    (hyp.muGrid_apply_one_eq hG hodd hw2 0 i hj0 hj0).trans hdeg
  have h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
    have := hyp.tau_muGrid_fourCorner hG hodd i j
    rwa [hδj] at this
  have h48 : ∀ k : Fin hyp.w2, k ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := fun k hk => by
    have := hyp.tau_muGrid_zeroRow_diff hG hodd hw2 hj0 hk
    rwa [hδj] at this
  have hβr := hyp.beta_isReal hG coh hconj hodd i hj0 hζS hζirr hζ1 hdeg0
    (hyp.muGrid_zero_column_apply_one hG hodd 0) hnf hδj h410 h48
  obtain ⟨a, hbound, hinner, heven_imp⟩ := hyp.charParam_a_eq_zero_of_residualEq hG coh hodd i hj0 hζS
    hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev h114
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have ha := hyp.muGridAlpha_a_eq_inner_sumOmegaSigma_beta hG coh hodd i hj0 hζS hζirr hζ1 hζne hdeg hμ0
    hnf hδj hdζ h0ζ hinner h114
  have hβZ := hyp.beta_mem_ZIrr hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj
  have hβ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 :=
    hyp.beta_inner_trivial hG coh hodd i hj0 hi0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj
      (hyp.muGridAlpha_inner_trivial_M hG hodd hi0 hj0 hζirr hζ1)
  have heven := hyp.a_even_of_eq_inner_sumOmegaSigma hG hodd hβZ hβr hβ1 ha
  have ha0 : a = 0 := heven_imp heven
  rw [ha0] at hinner
  rw [hinner]; ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.6) opening identity** `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, `δ = 1`).
Given the `a = 0` Dade images `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for all `i` (`halpha`,
Peterfalvi (11.8.2)+(11.8.5), `SHC_tau_muGridAlpha_eq` at `δ = 1`) and the (11.8.4) value
`(μ₀ − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`h114`), the `M`-level identity `μ_j − dζ = (μ₀ − ζ) + ∑_i α_{ij}`
(needs `d = w₁·n + 1`, i.e. `δ = 1`) maps through the linear Dade isometry `τ` (`map_add`, `map_sum`)
to `∑_i ω_{i0}^σ − ζ^{τ₁} + ∑_i (ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}) = ∑_i ω_{ij}^σ − dζ^{τ₁}`.  This is the
key step of (11.8.6): with `μ_j^{τ₂} = ∑_i ω_{ij}^σ` (via (4.9)/(5.8)) it makes `S(C) = S₁ ∪ S₂`
coherent, contradicting (11.3). -/
theorem Hypothesis.tau_muColumnSum_sub_zeta_eq_of_alphaImage [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (j : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {d n : ℕ} (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hMlevel : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        + ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) := by
    have hαe : (∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (n : ℂ)) • ζ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
    rw [hαe, hd]; module
  rw [hMlevel, map_add, h114, map_sum, Finset.sum_congr rfl (fun i _ => halpha i)]
  have hsum : (∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0
        - (n : ℂ) • coh.extension ζ))
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension ζ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
  rw [hsum, hd]; module

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5)+(11.8.6 opening), the assembled column identity**
`(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, `δ = 1`).  Assembles the (11.8.5) `a = 0` residual
coefficient into the full column Dade image: for every row `i ≠ 0`, `residualCoeff_eq_zero` gives
`(α_{ij}^τ, ζ^{τ₁}) = −n`, whence `SHC_tau_muGridAlpha_eq` gives the image
`α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}`; the `i = 0` image follows from any `i ≠ 0` one via the
four-corner (4.10) identity `tau_muGrid_fourCorner` (the `nζ` cancels in `α_{ij} − α_{0j}`, and
`μ_{0j} − μ_{00} − nζ = (α_{ij}) − (μ_{ij} − μ_{0j} − μ_{i0} + μ_{00})`).  With `δ = 1`
(`d = w₁·n + 1`) the (11.8.6) opening `tau_muColumnSum_sub_zeta_eq_of_alphaImage` then linearly
assembles the column sum.  The `S(HC)`-coherent extension `coh` and its orthonormal image data `R`
(`= coh.extension '' S(HC)`, `|R| = n`) are the (11.8.1)/(5.7) inputs; `h114` is the (11.8.4)
normalization; `δ = 1`, `n`, and the `R` cardinality `|S(HC)| = n` are the §9 (11.8.1) counts. -/
theorem Hypothesis.tau_muColumnSum_sub_dzeta_eq_of_residualData [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d n : ℕ} (hw2 : (hyp.w2).Prime)
    (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - 1)
    (hdegall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0all : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 = 1)
    (hδj : hyp.muColumnSign hG hodd j = 1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hdℕ : d = hyp.w1 * n + 1 := by exact_mod_cast hd
  have hw1le : hyp.w1 ≤ hyp.w1 * n := Nat.le_mul_of_pos_right _ (by omega)
  have hdgt : hyp.w1 < d := by omega
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hdζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 ≠ ζ 1 := fun i => by
    rw [hdegall i, hζ1]; exact_mod_cast (by omega : d ≠ hyp.w1)
  have h0ζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 ≠ ζ 1 := fun i => by
    rw [hμ0all i, hζ1]; exact_mod_cast (by omega : (1 : ℕ) ≠ hyp.w1)
  -- the row-`i` Dade image `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for `i ≠ 0`
  have halpha_ne : ∀ i : Fin hyp.w1, i ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i hi0
    have hα0 := hyp.residualCoeff_eq_zero hG coh hconj hodd i hj0 hi0 hζS hζirr hζ1 hw2
      (hdegall i) (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hn2 hRn hZ horth hRmem hRrev
      h114
    have himg := hyp.SHC_tau_muGridAlpha_eq hG coh hodd i hj0 hζS hζirr hζ1 hζne (hdegall i)
      (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hα0
    simpa only [Int.cast_one, one_smul] using himg
  -- the row-`0` image via the four-corner identity from row `i₁ = 1 ≠ 0`
  have halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      set i₁ : Fin hyp.w1 := ⟨1, by omega⟩ with hi1def
      have hi1 : i₁ ≠ 0 := by rw [hi1def]; simp [Fin.ext_iff]
      have h410 := hyp.tau_muGrid_fourCorner hG hodd i₁ j
      rw [hδj] at h410
      simp only [Int.cast_one, one_smul] at h410
      have key : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ
          = (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd i₁ 0 - (n : ℂ) • ζ)
            - (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd i₁ 0
                + hyp.muGrid hG hodd 0 0) := by module
      rw [key, map_sub, halpha_ne i₁ hi1, h410]; module
    · exact halpha_ne i hi0
  exact hyp.tau_muColumnSum_sub_zeta_eq_of_alphaImage hG hodd coh j hd halpha h114

open scoped Classical FiniteInduce in
/-- **The orthonormal coherent image `R = coh.extension '' S(HC)`** (Peterfalvi (11.8.1)/(5.7)):
the image of the degree-`w₁` irreducible subfamily `S(HC)` under an `S(HC)`-coherent extension `coh`
is a Finset of mutually orthonormal virtual characters in `ℤ[Irr G]`.  The `extension` isometry
(`extension_inner_eq`) carries the orthonormal irreducibles of `S(HC)` (`irr_cf_inner`) to an
orthonormal set — also giving injectivity, so `|R| = |S(HC)|` — and lands them in `ℤ[Irr G]`
(`extension_mem_ZIrr`).  This materializes the `R` data (`hZ`/`horth`/`hRmem`/`hRrev`) the (11.8.5)
`residualCoeff_eq_zero`/`tau_muColumnSum_sub_dzeta_eq_of_residualData` consume; only the cardinality
value `|S(HC)| = n` remains the §9 (11.8.1) count (`caseB_degree_qu` + Frobenius `(u−1)/q`). -/
theorem Hypothesis.exists_coherentImage_SHC [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) :
    ∃ R : Finset (ClassFunction G ℂ),
      (∀ β ∈ R, β ∈ ZIrr G) ∧
      (∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) ∧
      (∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
        φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R) ∧
      (∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
        φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) ∧
      R.card = (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
        (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
          ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card := by
  haveI := hyp.finiteG
  classical
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  -- each `χ ∈ s` is a member of `S(HC) = SHCSet`, hence lies in `zSpan SHCSet`
  have hspan : ∀ χ : IrreducibleCharacter ↥M, χ ∈ s →
      (χ : ClassFunction ↥M ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.SHCSet := fun χ hχ =>
    Submodule.subset_span ⟨((hmem_s χ).mp hχ).1, χ.2, ((hmem_s χ).mp hχ).2⟩
  set f : IrreducibleCharacter ↥M → ClassFunction G ℂ :=
    fun χ => coh.extension (χ : ClassFunction ↥M ℂ) with hf
  -- the extension isometry carries the orthonormal `χ ∈ s` to an orthonormal image
  have hiso : ∀ χ χ' : IrreducibleCharacter ↥M, χ ∈ s → χ' ∈ s →
      ClassFunction.inner (f χ) (f χ') = if χ = χ' then (1 : ℂ) else 0 := by
    intro χ χ' hχ hχ'
    rw [hf, coh.extension_inner_eq _ _ (hspan χ hχ) (hspan χ' hχ'),
      irr_cf_inner (mem_irreducibleCharacters.mpr χ.2) (mem_irreducibleCharacters.mpr χ'.2)]
    simp only [Subtype.coe_inj]
  have hinjOn : ∀ χ ∈ s, ∀ χ' ∈ s, f χ = f χ' → χ = χ' := by
    intro χ hχ χ' hχ' hfeq
    by_contra hne
    have h1 : ClassFunction.inner (f χ) (f χ') = 0 := by rw [hiso χ χ' hχ hχ', if_neg hne]
    have h2 : ClassFunction.inner (f χ) (f χ') = 1 := by
      rw [hfeq, hiso χ' χ' hχ' hχ', if_pos rfl]
    rw [h1] at h2; exact one_ne_zero h2.symm
  refine ⟨s.image f, ?_, ?_, ?_, ?_, ?_⟩
  · -- hZ
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    exact coh.extension_mem_ZIrr _ (hspan χ hχ)
  · -- horth
    intro α hα β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.mp hβ
    rw [hiso χ χ' hχ hχ']
    by_cases hc : χ = χ'
    · rw [if_pos hc, if_pos (by rw [hc])]
    · rw [if_neg hc, if_neg (fun h => hc (hinjOn χ hχ χ' hχ' h))]
  · -- hRmem
    intro φ hφS hφirr hφ1
    exact Finset.mem_image.mpr ⟨⟨φ, hφirr⟩, (hmem_s _).mpr ⟨hφS, hφ1⟩, rfl⟩
  · -- hRrev
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hφS, hφ1⟩ := (hmem_s χ).mp hχ
    exact ⟨(χ : ClassFunction ↥M ℂ), hφS, χ.2, hφ1, rfl⟩
  · -- cardinality: injective on `s`
    exact Finset.card_image_of_injOn hinjOn

open scoped Classical FiniteInduce in
/-- **`S(HC) = S₁` is orthonormal** (Peterfalvi (11.8), the `S₁` side of the (11.8.6) union).
Every member of `S(HC)` is an irreducible character of `M` (`SHCSet` filters `inducedFamily` by
`IsIrreducibleCharacter`), so `⟨φ, ψ⟩ = [φ = ψ]` by `irr_cf_inner`.  This is the orthonormal-`X`
input the (6.8.1) union glue `exists_integralCharacterMap_glue_of_orthonormal` takes for `S₁` in the
(11.8.6) τ₂ union (`coherent_Sset_of_column_identities`). -/
theorem Hypothesis.SHCSet_orthonormal [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ ∈ hyp.SHCSet) (hψ : ψ ∈ hyp.SHCSet) :
    ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 :=
  irr_cf_inner (mem_irreducibleCharacters.mpr hφ.2.1) (mem_irreducibleCharacters.mpr hψ.2.1)

open scoped FiniteInduce in
/-- **Degree of an `inducedFamily` member factors through `w₁`**: `Ind_{M'}^M θ (1) = w₁ · θ(1)`,
since `[M : M'] = w₁` (`TypePData.card_W1_eq_derived_index`; `M' = derivedInG M`).  This is the
foundational (11.8.1) degree-factoring for the world-bridge: the degree of any member `y = Ind θ`
of `S = inducedFamily M` is `w₁` times a source degree `θ(1)`, so the two-degree-class structure
`{w₁, qu = d·w₁}` of `𝒮(C)` reduces to `θ(1) ∈ {1, d}`.  (The reducible members' `θ(1) = d` is the
§9 `reducible_mem_sOf_H0_apply_one_eq_qu` content; this lemma supplies the `[M:M']`-factoring half.) -/
theorem Hypothesis.induce_derived_apply_one_eq_w1_mul [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M)) :
    (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) (1 : ↥M)
      = (hyp.w1 : ℂ) * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (1 : ↥((derivedInG M).subgroupOf M)) := by
  haveI := hyp.finiteG
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  rw [ClassFunction.induce_apply_one, hidx]

open scoped FiniteInduce in
/-- **(11.8.1) column degree**: for `k ≠ 0`, the μ-grid column sum `μ_k = ∑ᵢ μ_{ik}` has degree
`q·u` (= `w₁·|Ū| = qu`).  `muGrid_column_sum_mem_sOf_H0_and_reducible` (μ_k is a reducible
`𝒮(H₀)`-member) composed with `reducible_mem_sOf_H0_apply_one_eq_qu` (reducible `𝒮(H₀)`-members have
degree `q·u`, §9 (9.8.b)/(9.9.b)).  This is the concrete `ψ₀`-witness degree for the (11.8.6) `hgen`
bundled `S₂`-structure: a column `μ_k ∈ Sset \ SHCSet` (reducible → not in the irreducible `SHCSet`,
`muGrid_column_sum_mem_inducedFamily`) of degree `qu`. -/
theorem Hypothesis.muGrid_column_sum_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (k : Fin hyp.w2) (hk : k ≠ 0) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
      = (((hyp.toTypesIIIIIIVSetup htype hnt).q *
          (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  obtain ⟨hmem, hred⟩ :=
    hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk
  exact reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief)
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) hmem hred

open scoped FiniteInduce in
/-- **Peterfalvi (9.5)/(4.5.b): a reducible `S = inducedFamily M`-member is a nonzero μ-column.**
For `y = Ind_{M'}^M θ ∈ inducedFamily M` (`θ ∈ Irr(M')`, `θ ≠ 1`) with `Ind_{M'}^M θ` *reducible*,
there is a column index `k ≠ 0` with `y = ∑ᵢ μ_{ik}`.

This is the (9.5)/(11.5) family identification, closed via the §6 residue theory rather than a
prime-TI port.  Since `M' = HU = h.K` (`toCertainTypeHypothesis`), `θ` is an irreducible of `K`, and
the (4.5.b) reducibility criterion `induce_not_isIrreducible_iff` forces `θ = chiRestrict χ₂` (a
column `χ_j`, via the inertia computation `I_L(χ) = K`).  Then `induce_restrict_certainType_eq`
identifies `Ind_K^M (chiRestrict χ₂) = ∑ᵢ μ_{ik}` (the μ-grid column), where `k` is the column of
`χ₂`; `θ ≠ 1` excludes the trivial column (`chiRestrict_one_eq_trivial`, `finCardEquivCharacterGroup`
sends `0` to `1`), giving `k ≠ 0`. -/
theorem Hypothesis.exists_muGrid_column_eq_of_inducedFamily_reducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {y : ClassFunction ↥M ℂ} (hyS : y ∈ inducedFamily M)
    (hred : ¬ IsIrreducibleCharacter y) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ y = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- `y = Ind_{h.K} θ` (`h.K = M'` defeq), `θ ≠ 1`.
  obtain ⟨θ, hθne, hyeq⟩ := hyS
  rw [hyeq] at hred
  -- (4.5.b) reducibility criterion: `θ = chiRestrict χ₂` for some column `χ₂`.
  obtain ⟨χ₂, hχ₂⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  -- the column index of `χ₂`.
  set k : Fin hyp.w2 := finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂) with hkdef
  have hχ₂k : finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k) = χ₂ := by
    have hkk : finCongr hcardW2sub.symm k = (finCardEquivCharacterGroup _).symm χ₂ := by
      rw [hkdef]; ext; simp
    rw [hkk, Equiv.apply_symm_apply]
  refine ⟨k, ?_, ?_⟩
  · -- `k ≠ 0`: else `χ₂ = 1` and `θ = chiRestrict 1 = 1`, contradicting `θ ≠ 1`.
    intro hk0
    apply hθne
    have hχ₂1 : χ₂ = 1 := by
      rw [← hχ₂k, hk0]
      have h0 : finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 := by ext; simp
      rw [h0, finCardEquivCharacterGroup_zero]
    rw [← hχ₂, hχ₂1]
    -- `chiRestrict 1 = trivial ↥h.K`, defeq to `trivial ↥M'`.
    exact h.chiRestrict_one_eq_trivial
  · -- `y = ∑ᵢ μ_{ik}` via `Ind_K^M (chiRestrict χ₂) = ∑ᵢ μ_{ik}`.
    have h2 : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
        = ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) := by
      rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
        ← Equiv.sum_comp (finCongr hcardW1.symm)
          (fun i' => ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show hyp.muGrid hG hodd i k
        = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu
            (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl,
        hχ₂k]
    -- `y = Ind_{M'} θ = Ind_{h.K} (chiRestrict χ₂) = ∑ᵢ μ_{ik}` (last `induce` step defeq via `M' = h.K`).
    rw [h2, hχ₂]
    exact hyeq

open scoped FiniteInduce in
/-- **Reducible members of `S = inducedFamily M` have degree `q·u = qu`** — the reducible-side of the
(11.8.1) uniform-degree structure of `𝒮₂ = Sset \ SHCSet`.  A reducible `inducedFamily`-member is a
nonzero μ-column (`exists_muGrid_column_eq_of_inducedFamily_reducible`, the (9.5)/(4.5.b) family
identification), which lies in `𝒮(H₀) = sOf ... chief.H0` (`muGrid_column_sum_mem_sOf_H0_and_reducible`);
then `reducible_mem_sOf_H0_apply_one_eq_qu` gives degree `q·u`. -/
theorem Hypothesis.inducedFamily_reducible_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    {y : ClassFunction ↥M ℂ} (hyS : y ∈ inducedFamily M) (hred : ¬ IsIrreducibleCharacter y) :
    y (1 : ↥M) = (((hyp.toTypesIIIIIIVSetup htype hnt).q *
        (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  have hmem : y ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 := by
    -- (9.5)/(4.5.b) family identification: the reducible `inducedFamily`-member is a nonzero
    -- μ-column (`exists_muGrid_column_eq_of_inducedFamily_reducible`), which lies in `𝒮(H₀)`.
    obtain ⟨k, hk, hyk⟩ :=
      hyp.exists_muGrid_column_eq_of_inducedFamily_reducible hG hG.odd hyS hred
    rw [hyk]
    exact (hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk).1
  exact reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief) y hmem hred

open scoped FiniteInduce in
/-- **Degree of an `S₁ = S(HC)`-span element is an integer multiple of `w₁`.**  Every member of
`SHCSet` has degree `w₁` (by definition, third conjunct), so `ψ ∈ ℤ[S(HC)]` has `ψ(1) = s·w₁` with
`s ∈ ℤ` the coefficient sum (`span_induction`).  This is the `S₁`-side degree-ratio input of the
(11.8.6) generation `hgen` — the analogue of S08 `certainTypeSet_span_apply_one_eq_intMul`. -/
theorem Hypothesis.SHCSet_span_apply_one_eq_intMul [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {ψ : ClassFunction ↥M ℂ} (hψ : ψ ∈ Submodule.span ℤ hyp.SHCSet) :
    ∃ s : ℤ, ψ 1 = (s : ℂ) * (hyp.w1 : ℂ) := by
  classical
  induction hψ using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [hx.2.2]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      exact ⟨c * sx, by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring⟩

open scoped FiniteInduce in
/-- **Degree of an `S₂ = S(C) − S(HC)`-span element is an integer multiple of `qu`**, given that all
`S₂` members share degree `qu` (the (11.8.1) uniform reducible degree — supplied as a hypothesis,
§9-gated).  `span_induction`, as `SHCSet_span_apply_one_eq_intMul`.  The `S₂`-side degree-ratio input
of the (11.8.6) generation `hgen`. -/
theorem Hypothesis.Sset_diff_span_apply_one_eq_intMul [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {qu : ℕ}
    (hS2deg : ∀ y ∈ hyp.Sset \ hyp.SHCSet, (y : ↥M → ℂ) 1 = (qu : ℂ))
    {ψ : ClassFunction ↥M ℂ} (hψ : ψ ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet)) :
    ∃ s : ℤ, ψ 1 = (s : ℂ) * (qu : ℂ) := by
  classical
  induction hψ using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [hS2deg x hx]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      exact ⟨c * sx, by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring⟩

open scoped FiniteInduce in
/-- **`S(HC) ⊥ (S − S(HC))`** (the source-orthogonality `hsrc_ortho` input for the (11.8.6) union):
`S(HC)` and `S₂ = S(C) − S(HC)` are disjoint subsets of `S = inducedFamily M`, so a member of each
is a distinct pair of `inducedFamily` characters, orthogonal by `inducedFamily_pairwiseOrthogonal`.
This is the set-level `X ⊥ Y` the (6.8.1) union glue `exists_integralCharacterMap_glue_of_orthonormal`
takes (with `X = S(HC)`, `Y = S₂`). -/
theorem Hypothesis.SHCSet_inner_diff_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ} (hx : x ∈ hyp.SHCSet) (hy : y ∈ hyp.Sset \ hyp.SHCSet) :
    ClassFunction.inner x y = 0 := by
  haveI := hyp.finiteG
  have hne : x ≠ y := fun h => hy.2 (h ▸ hx)
  exact inducedFamily_pairwiseOrthogonal hx.1 hy.1 hne

open scoped FiniteInduce in
/-- **`ℤ[S(HC)] ⊥ ℤ[S₂]`** (span-level `hsrc_ortho` for the (11.8.6) union): the `ℤ`-lattices spanned
by `S(HC)` and `S₂ = S(C) − S(HC)` are orthogonal, lifted from the set-level
`SHCSet_inner_diff_eq_zero` by bi-additivity of the inner product (`span_induction` on both
arguments).  This is the exact `hsrc_ortho` hypothesis
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` takes for the τ₂ union. -/
theorem Hypothesis.span_inner_SHCSet_diff_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {u v : ClassFunction ↥M ℂ}
    (hu : u ∈ Submodule.span ℤ hyp.SHCSet) (hv : v ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet)) :
    ClassFunction.inner u v = 0 := by
  haveI := hyp.finiteG
  have hright : ∀ x ∈ hyp.SHCSet, ∀ w ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet),
      ClassFunction.inner x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact hyp.SHCSet_inner_diff_eq_zero hx hy
    | zero => rw [ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  induction hu using Submodule.span_induction with
  | mem x hx => exact hright x hx v hv
  | zero => rw [ClassFunction.inner_zero_left]
  | add x z _ _ ihx ihz => rw [ClassFunction.inner_add_left, ihx, ihz, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih, mul_zero]

open scoped FiniteInduce in
/-- **`S(HC) ⊆ S`** (the `X ⊆ X ∪ Y` inclusion for the (11.8.6) union): every member of
`S(HC) = {φ ∈ S | φ irreducible, φ(1) = w₁}` is in `S = inducedFamily M` by the first conjunct of
its defining comprehension.  Trivial, but named so the (11.8.6) set-decomposition
`Sset_eq_SHCSet_union_diff` and future gluing consumers can cite it. -/
theorem Hypothesis.SHCSet_subset_Sset [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SHCSet ⊆ hyp.Sset :=
  fun _ hφ => hφ.1

open scoped FiniteInduce in
/-- **`S(C) = S(HC) ∪ (S(C) − S(HC))`** (the set-level decomposition `S = S₁ ∪ S₂` of the (11.8.6)
union): `S(HC) ⊆ S` (`SHCSet_subset_Sset`), so `S = S(HC) ∪ (S ∖ S(HC))` by `Set.union_diff_cancel`.
This is the exact `rw` that turns the (11.8.6) goal `IsCoherent τ S A₀` into the union form
`IsCoherent τ (S(HC) ∪ S₂) A₀` the S07 gluing engine
(`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`) concludes — with `X = S(HC)`
(coherent by `coh`), `Y = S₂ = S ∖ S(HC)` (coherent by (9.11)/(11.7)). -/
theorem Hypothesis.Sset_eq_SHCSet_union_diff [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.Sset = hyp.SHCSet ∪ (hyp.Sset \ hyp.SHCSet) :=
  (Set.union_diff_cancel hyp.SHCSet_subset_Sset).symm

open scoped FiniteInduce in
/-- ⚠️ **Over-broad family, part of the uniform-degree route (issue 1019).**  Here `S₂` is taken as
`hyp.Sset \ hyp.SHCSet = inducedFamily M \ S(HC) = S_1 \ S(HC)`, but Peterfalvi's `S₂` is the narrower
`S(C) \ S(HC)` (with the `C`-kernel condition).  The coherence of the full `S_1 \ S(HC)` is not a
standalone fact — in Coq `S_1` is merely `subcoherent`, and its coherence is *derived* from `S(H₀C)`
coherence via `bounded_seqIndD_coherence`.  This obligation should be re-scoped in the redesign
(narrow to `S(C)` / `S(H₀C)`, then extend via bounded coherence).

**Peterfalvi (11.8.6) prerequisite: `S₂ = S(C) − S(HC)` is coherent** (the `hY` gluing input;
§9/§14-gated, named obligation).

This is Peterfalvi's "By (9.11), `𝒮(H₀C') − 𝒮(HC')` is coherent, whence `𝒮₂` is coherent by (11.7)"
(mmd 04.13 L67).  It is the `S₂`-side coherence `hY` that `coherent_Sset_of_glued` and the (11.8.6)
capstone `coherent_Sset_of_column_identities` consume — with `S₂ = hyp.Sset \ hyp.SHCSet` (the
`S(C) − S(HC)` difference of the pinned §10 induced family).

Reduction status (see `notes/peterfalvi/s13_11_8_orthogonality.md` update²⁶): the underlying content
is (9.11) `S11.coherent_H0C_commutator`, itself gated on `S11.sibleyTarget_H0C` (§14 Sibley setup +
lane-b (6.8)).  Three carrier obstructions block a direct sorry-free cite of (9.11) here:
(1) the `S11.Section11CharacterData` bridge `mkSection11CharacterData` sets `H0CprimeSupport := ∅`,
but `IsCoherent … ∅` is unconstructible (`zSupportedSpan S ∅ = {0}` kills `nonzero`);
(2) (9.11) is stated for the *difference* `𝒮(H₀C') − 𝒮(HC')`, whereas the repo's
`coherent_H0C_commutator` concludes on the *full* `chars.S = sSet data`;
(3) the world-bridge `sSet`/`sOf` (§9) ↔ `inducedFamily` (§10) `𝒮₂ = hyp.Sset ∖ hyp.SHCSet` is
unformalized.  Honest close = re-port (9.11) as `SOf`-difference coherence + (11.7) collapse, deep
char work coordinated with §14/lane-b.  Left as a single §14-gated `sorry` of the correct
difference-coherence signature (NOT a false-hypothesis hoist). -/
theorem Hypothesis.coherent_Sset_diff_SHCSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0) := by
  sorry

open scoped Classical FiniteInduce in
/-- **(11.8.6) gluing wrapper: `S(C) = S(HC) ∪ S₂` coherence from the glued `τ₃` data** (sorry-free).
The pure-algebra half of Peterfalvi (11.8.6): given the two coherences `coh` (`S(HC) = S₁`, `τ₁`) and
`hY` (`S₂ = S(C) − S(HC)`, `τ₂`), a glued integral map `ν` agreeing with `coh.extension` on `S₁` and
with `hY.extension` on `S₂` (`hagreeX`/`hagreeY` — Peterfalvi's `τ₃`), the mixed isometry `hmixed`,
and the supported cross-diagonal set `D` on which `ν = τ` (`hDτ`, the `hcol` column identities feed
this) with the enlarged generation hypothesis `hgen`, the full family `S = S(C)` is coherent.

This packages the S07 gluing engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`
for the (11.8.6) union: the source-orthogonality `hsrc_ortho` is discharged internally from the
landed `span_inner_SHCSet_diff_eq_zero` (`S₁ ⊥ S₂` at span level), and the conclusion is rewritten
from the union form to `hyp.Sset` via `Sset_eq_SHCSet_union_diff`.  What remains for the caller is
exactly the genuine (11.8.6) glue data: `hY` (the §9/§14-gated `S₂` coherence) and the `τ₃`
construction (`ν`, `hagreeX`, `hagreeY`, `hmixed`, `D`, `hDτ`, `hgen`) driven by `hcol`. -/
noncomputable def Hypothesis.coherent_Sset_of_glued [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (hagreeX : ∀ x ∈ hyp.SHCSet, ν x = coh.extension x)
    (hagreeY : ∀ y ∈ hyp.Sset \ hyp.SHCSet, ν y = hY.extension y)
    (hmixed : ∀ x ∈ hyp.SHCSet, ∀ y ∈ hyp.Sset \ hyp.SHCSet,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥M ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.SHCSet ∪ (hyp.Sset \ hyp.SHCSet)) hyp.A0 ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan hyp.SHCSet hyp.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Sset \ hyp.SHCSet) hyp.A0 ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0 := by
  haveI := hyp.finiteG
  rw [hyp.Sset_eq_SHCSet_union_diff]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    coh hY ν hagreeX hagreeY
    (fun _ hu _ hv => hyp.span_inner_SHCSet_diff_eq_zero hu hv) hmixed D hDτ hgen

/-- **Peterfalvi (10.10.1), pure arithmetic**: for the type-V case (c) parameters — `p = w₂` prime,
`w₁ ∣ p+1` (both odd, `w₁ > 1`), and the Huppert bound `|H:H'| = p² ≤ 4w₁²+1` (6.5.a) — one has
`p = 2w₁ − 1`, hence `w₁ < p = w₂`.

Writing `p+1 = 2k·w₁` (`m := (p+1)/w₁` is even, since `p+1` is even and `w₁` odd), the bound gives
`(2kw₁−1)² ≤ 4w₁²+1`, i.e. `w₁(k²−1) ≤ k`; with `w₁ ≥ 2`, `k ≥ 1` this forces `k = 1`.  Mirrors the
`typeII_noncoherence_arithmetic` pattern (the analytic/structural inputs are isolated). -/
theorem typeV_param_arithmetic {p w₁ : ℕ} (hpodd : Odd p) (hw1odd : Odd w₁) (hw1 : 1 < w₁)
    (hdvd : w₁ ∣ p + 1) (hbound : p ^ 2 ≤ 4 * w₁ ^ 2 + 1) :
    p = 2 * w₁ - 1 ∧ w₁ < p := by
  obtain ⟨m, hm⟩ := hdvd
  -- `m` is even: `p+1` is even (`p` odd) and `w₁` is odd.
  have hm_even : Even m := by
    have hp1even : Even (p + 1) := Odd.add_one hpodd
    rw [hm] at hp1even
    rcases Nat.even_mul.mp hp1even with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hw1odd)
    · exact h
  obtain ⟨k, hk⟩ := hm_even
  have hpk : p + 1 = 2 * w₁ * k := by rw [hm, hk]; ring
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · rw [h0, Nat.mul_zero] at hpk; omega
    · exact h1
  -- `k = 1` from the bound (over `ℤ` to avoid `ℕ`-subtraction).
  have hk1 : k = 1 := by
    have hpZ : (p : ℤ) = 2 * w₁ * k - 1 := by
      have : (p : ℤ) + 1 = 2 * (w₁ : ℤ) * k := by exact_mod_cast hpk
      linarith
    have hboundZ : (p : ℤ) ^ 2 ≤ 4 * (w₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hbound
    rw [hpZ] at hboundZ
    have hw1Z : (2 : ℤ) ≤ w₁ := by exact_mod_cast hw1
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hkpos
    have hkle : (k : ℤ) ≤ 1 := by
      nlinarith [hboundZ, hw1Z, hkZ, mul_nonneg (by linarith : (0:ℤ) ≤ (w₁:ℤ) - 2)
        (by nlinarith : (0:ℤ) ≤ (k:ℤ)^2 - 1), sq_nonneg ((k:ℤ) - 1)]
    omega
  subst hk1
  constructor
  · omega
  · omega

/-- **Peterfalvi (10.10.1)--(10.10.4)**: if Hypothesis (10.1) holds with `M` of type V, then the
type-V parameter calculation forces `S` to be coherent.

De-scaffolded: the conclusion is now the *genuine* coherence `Nonempty (IsCoherent τ S A₀)` only,
dropping the former opaque `typeV_parameter_formula`/`typeV_coherence_formula : Prop` conjuncts
(unprovable for generic `params`; producers set them `True`).  The remaining `sorry` is the honest
(10.10.1)–(10.10.4) coherence argument: case (a) of Def (8.7) gives coherence by (6.8); case (b) is
excluded by (6.5.c); case (c) (`|H| = p³`, `w₁ ∣ p+1`) runs the parameter calculation
(`typeV_param_arithmetic` gives `p = 2w₁−1`, then `d = p`, `δ = −1`, `n = 2`) and the σ-grid column
identities (reusing the (11.8) `muGrid`/`alignedOmegaSigmaGrid`/coherent-extension machinery).
Gated on the §6/§8 coherence inputs (6.5.a/6.8) and the type-V `|H| = p³` structure. -/
theorem typeV_forces_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} (hV : IsTypeV M) (params : CharacterParameters hyp) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (10.10)**: `G` has no maximal subgroup of type V.

By (10.8) (`S_not_coherent`) the family `S` of any type-III/IV/V maximal is not
coherent; but a type-V maximal forces `S` to be coherent by (10.10.1)–(10.10.4)
(`typeV_forces_coherence`).  These now refer to the *genuine* Dade isometry,
induced family, and support carried by the faithful (10.1) `Hypothesis` (built by
`exists_hypothesis_of_typeIIIorIVorV`), so the contradiction is honest. -/
theorem no_typeV_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M := by
  rintro ⟨M, hMmax, hMV⟩
  obtain ⟨hyp⟩ := exists_hypothesis_of_typeIIIorIVorV hG hMmax (Or.inr (Or.inr hMV))
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  exact S_not_coherent hG hyp (typeV_forces_coherence hG hMV params)

/-- The case-(b) data in Peterfalvi (8.8), used in the remark (10.11). -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- (8.8.b1): `W₁ ≤ S` and `S = [S,S] ⋊ W₁` (so `W₁` complements `S' = [S,S]` in `S`). -/
  W1_le_S : W1 ≤ S
  W2_le_T : W2 ≤ T
  S_compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)
  T_compl : Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)

/-- A non-type-I maximal subgroup that is not of type V (so of type II/III/IV) carries type-`P`
data whose `W₁` has prime order — Peterfalvi (8.6.a), via `TypePNontrivialCore`.  Type V is
excluded by Theorem (10.10) `no_typeV_maximal`. -/
private theorem caseB_typeP_prime_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    ∃ data : TypePData M, (Nat.card ↥data.W1).Prime := by
  rcases hnonI with h | h | h | h
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact absurd ⟨M, hM, h⟩ (no_typeV_maximal hG)

/-- **Peterfalvi (10.11), first assertion**: in case (b) of Theorem (8.8), the
orders of `W_1` and `W_2` are prime.

By Theorem (10.10) `no_typeV_maximal`, the non-type-I subgroups `S`, `T` are of type II/III/IV,
whose type-`P` `W₁` has prime order (8.6.a).  The case-(b) factors `W₁`, `W₂` complement the
derived subgroups of `S`, `T` (8.8.b1, `S_compl`/`T_compl`), so they share the orders
`|S : S'|`, `|T : T'|` with the respective type-`P` `W₁` (`card_W1_eq_derived_index`) — hence prime. -/
theorem theorem88_caseB_prime_orders [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseB : Theorem88CaseBData G) :
    (Nat.card ↥caseB.W1).Prime ∧ (Nat.card ↥caseB.W2).Prime := by
  have hW1 : Nat.card ↥caseB.W1 = ((derivedInG caseB.S).subgroupOf caseB.S).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W1_le_S).toEquiv,
      ← caseB.S_compl.symm.index_eq_card]
  have hW2 : Nat.card ↥caseB.W2 = ((derivedInG caseB.T).subgroupOf caseB.T).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W2_le_T).toEquiv,
      ← caseB.T_compl.symm.index_eq_card]
  refine ⟨?_, ?_⟩
  · obtain ⟨dataS, hSp⟩ := caseB_typeP_prime_W1 hG caseB.S_maximal caseB.S_nonI
    rw [hW1, ← dataS.card_W1_eq_derived_index]; exact hSp
  · obtain ⟨dataT, hTp⟩ := caseB_typeP_prime_W1 hG caseB.T_maximal caseB.T_nonI
    rw [hW2, ← dataT.card_W1_eq_derived_index]; exact hTp

/-- **Peterfalvi (10.11), Type II assertion**: for a type-II maximal subgroup,
the §11 family `S(H_0 C')` specializes to a coherent set. -/
theorem typeII_section11_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent chars.tau chars.S chars.H0CprimeSupport) := by
  exact ⟨OddOrder.Peterfalvi.S11.coherent_H0C_commutator chars⟩

end OddOrder.Peterfalvi.S12

