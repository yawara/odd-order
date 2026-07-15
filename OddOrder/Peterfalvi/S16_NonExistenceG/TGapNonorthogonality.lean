import OddOrder.Peterfalvi.S16_NonExistenceG.TGapMemberResidual

/-!
# Peterfalvi §§3, 11, 15 (pp. 5–9, 50–57, 75–86): grid rigidity and omega exhaustion

Arbitrary-grid dichotomy, eta-residual rigidity, and finite omega-grid
exhaustion used by the T-gap contradiction.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

end OddOrder.Peterfalvi.S16

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), arbitrary-grid dichotomy.**  The norm and integral-lattice
argument producing the normalized coherent extension uses only two properties of the chosen
`sigma`-grid: orthonormality and orthogonality of every degree-`w1` coherent image to its
zero-column sum.  Thus the canonical `alignedOmegaSigmaGrid` can be replaced by any grid with
those properties, in particular the independently constructed T-side grid.
This is the grid-parametric form of `tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`. -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_grid_orthogonal [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {lam : ClassFunction ↥M ℂ},
      lam ∈ inducedFamily M → IsIrreducibleCharacter lam → lam 1 = (hyp.w1 : ℂ) →
      lam.conj ≠ lam →
      ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, grid r 0) = 0)
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) -
          ∑ i' : Fin hyp.w1, grid i' 0)
        (grid i j) = 0) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) - (hyp.SHC_isCoherent hG).extension ζ ∨
      ((∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
          lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) ∧
        hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
          (∑ r : Fin hyp.w1, grid r 0) +
            (hyp.SHC_isCoherent hG).extension ζ.conj) := by
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
      ClassFunction.inner (∑ r' : Fin hyp.w1, grid r' 0)
        (grid r 0) = 1 := by
    intro r
    rw [inner_sum_left, Finset.sum_eq_single r]
    · rw [hgridInner r 0 r 0, if_pos ⟨rfl, rfl⟩]
    · intro r' _ hne
      rw [hgridInner r' 0 r 0, if_neg fun h => hne h.1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hψr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (grid r 0) = 1 := by
    intro r
    have h := horth r 0
    rw [ClassFunction.inner_sub_left, sub_eq_zero] at h
    exact h.trans (hΩr r)
  have hψΩ : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ r : Fin hyp.w1, grid r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hψr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hΩψ : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩnorm : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      (∑ r : Fin hyp.w1, grid r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hΩr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψnorm : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- `χ = ∑_r ω_{r0}^σ − (μ₀ − ζ)^τ` has norm `1`
  have hχnorm : ClassFunction.inner
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hΩnorm, hΩψ, hψΩ, hψnorm]
    push_cast
    ring
  -- the (5.3.b) orthogonalities `⟨∑_r ω_{r0}^σ, λ^{τ₁}⟩ = 0`
  have heΩ : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      (∑ r : Fin hyp.w1, grid r 0) = 0 :=
    hgridExtensionOrth hζS hζirr hζ1 hζne
  have hΩe : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
      ((hyp.SHC_isCoherent hG).extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩ, star_zero]
  have hζcne : (ζ.conj).conj ≠ ζ.conj := by
    rw [ClassFunction.conj_conj]
    exact hζne.symm
  have heΩc : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      (∑ r : Fin hyp.w1, grid r 0) = 0 :=
    hgridExtensionOrth hζcS hζcirr hζc1 hζcne
  have hΩec : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
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
      ((∑ r : Fin hyp.w1, grid r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ) = ((-s : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩe, hs]
    push_cast
    ring
  have hmAc : ClassFunction.inner
      ((∑ r : Fin hyp.w1, grid r 0)
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
        ((∑ r : Fin hyp.w1, grid r 0)
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
        ((∑ r : Fin hyp.w1, grid r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ.conj) = -1 := by
      rw [ClassFunction.inner_sub_left, hΩec, ht, htval]
      push_cast
      ring
    have hχec := heqneg _ _ hχnorm hAec heec
    have hψeq : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, grid r 0)
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
        (∑ r : Fin hyp.w1, grid r 0) = 0 :=
      hgridExtensionOrth hlamS hlamirr hlam1 hlamne
    have hOmegalam : ClassFunction.inner (∑ r : Fin hyp.w1, grid r 0)
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
/-- **Peterfalvi (11.8.4), arbitrary-grid branch-2 normalization.**
The conjugate-swap changes only the coherent extension, so the textbook's
`sum grid + extension zeta.conj` branch normalizes for every chosen grid. -/
theorem Hypothesis.SHC_swap_grid_h114 [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M →
      IsIrreducibleCharacter lam → lam 1 = (hyp.w1 : ℂ) →
      lam = ζ ∨ lam = ζ.conj)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hbranch2 :
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) +
          (hyp.SHC_isCoherent hG).extension ζ.conj) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
      (∑ r : Fin hyp.w1, grid r 0) -
        (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ := by
  haveI := hyp.finiteG
  classical
  have hswapζ :
      (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ =
        -((hyp.SHC_isCoherent hG).extension ζ.conj) := by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M)
        Complex.conjAe.toRingEquiv))) ζ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply,
      ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ = ζ.conj from by
        ext g
        rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
        rfl]
  rw [hswapζ, sub_neg_eq_add, hbranch2]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), arbitrary-grid h114 producer.**
Under the contradiction orthogonality for any orthonormal sigma-grid whose
zero column is orthogonal to the coherent family, one may choose a coherent
extension satisfying the normalized h114 identity for that same grid. -/
theorem Hypothesis.exists_coherent_extension_h114_of_grid_orthogonal [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {lam : ClassFunction ↥M ℂ},
      lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam.conj ≠ lam →
      ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, grid r 0) = 0)
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) -
          ∑ i' : Fin hyp.w1, grid i' 0)
        (grid i j) = 0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0,
      (∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M →
        IsIrreducibleCharacter χ → χ 1 = (hyp.w1 : ℂ) →
        (ν.extension χ).conj = ν.extension χ.conj) ∧
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) =
        (∑ r : Fin hyp.w1, grid r 0) - ν.extension ζ := by
  rcases hyp.tau_muColumnZero_sub_zeta_dichotomy_of_grid_orthogonal
      hG hodd hζS hζirr hζ1 grid hgridInner hgridExtensionOrth horth with
    h1 | ⟨htwo, h2⟩
  · exact ⟨hyp.SHC_isCoherent hG,
      (fun hχS hχirr hχ1 => hyp.SHC_extension_conj hG hχS hχirr hχ1), h1⟩
  · exact ⟨hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo,
      (fun hχS hχirr hχ1 =>
        hyp.SHC_swap_conj hG hodd hζS hζirr hζ1 htwo hχS hχirr hχ1),
      hyp.SHC_swap_grid_h114 hG hodd hζS hζirr hζ1 htwo grid h2⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), arbitrary-grid residual identification.**
The Parseval decomposition and coefficient bound are independent of sigma.
Only the norm-two residual classifier is grid-specific, so it is exposed as
`hclassify`; this is the exact input supplied by a concrete sigma-isometry. -/
theorem Hypothesis.SHC_residual_eq_grid_diff [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hclassify : ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 -
            (n : ℂ) • ζ) v) →
      Y = (δ : ℂ) • (grid i j - grid i 0)) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ((a = 0 ∨ a = 2) → Y = (δ : ℂ) • (grid i j - grid i 0)) ∧
      hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) =
        Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  obtain ⟨a, Y, hbound, _, hinner, _, hnorm2case, hYZ, hYV, hdecomp⟩ :=
    hyp.muGridAlpha_tau_residual_norm hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev
  exact ⟨a, Y, hbound, hinner,
    fun ha02 => hclassify hYZ (hnorm2case ha02) hYV, hdecomp⟩

open scoped FiniteInduce in
/-- A row difference in an orthonormal grid pairs to `-1` with the zero-column sum. -/
theorem grid_diff_inner_zeroColumnSum [Finite G] {w1 w2 : ℕ} [NeZero w2]
    (grid : Fin w1 → Fin w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (i : Fin w1) {j : Fin w2} (hj0 : j ≠ 0) :
    ClassFunction.inner (grid i j - grid i 0)
      (∑ r : Fin w1, grid r 0) = -1 := by
  classical
  rw [ClassFunction.inner_sub_left,
    OddOrder.RepresentationTheory.inner_sum_right,
    OddOrder.RepresentationTheory.inner_sum_right]
  have h1 : ∀ r : Fin w1, ClassFunction.inner (grid i j) (grid r 0) = 0 :=
    fun r => by
      rw [hgridInner i j r 0, if_neg]
      rintro ⟨_, h⟩
      exact hj0 h
  have h2 : ∀ r : Fin w1,
      ClassFunction.inner (grid i 0) (grid r 0) =
        if i = r then (1 : ℂ) else 0 := fun r => by
    rw [hgridInner i 0 r 0]
    simp
  rw [Finset.sum_congr rfl (fun r _ => h1 r),
    Finset.sum_congr rfl (fun r _ => h2 r), Finset.sum_const_zero,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- The sum of a coherent image family is orthogonal to an arbitrary grid's zero column
whenever each family member is. -/
theorem Hypothesis.R_sum_inner_grid_zeroColumnSum [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {R : Finset (ClassFunction G ℂ)}
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hext : ∀ {φ : ClassFunction ↥M ℂ}, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) →
      ClassFunction.inner (coh.extension φ) (∑ r : Fin hyp.w1, grid r 0) = 0) :
    ClassFunction.inner (∑ β ∈ R, β) (∑ r : Fin hyp.w1, grid r 0) = 0 := by
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβR => ?_
  obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
  exact hext hφS hφirr hφ1

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), arbitrary-grid conditional coefficient vanishing.**
Given the grid-parametric (11.8.2) residual classifier and h114 identity,
the two-way inner-product computation forces every even coefficient `a` to vanish. -/
theorem Hypothesis.charParam_a_eq_zero_of_grid_residualEq [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M →
      IsIrreducibleCharacter φ → φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (hgridInner : ∀ i j i' j',
      ClassFunction.inner (grid i j) (grid i' j') =
        if i = i' ∧ j = j' then 1 else 0)
    (hgridExtensionOrth : ∀ {φ : ClassFunction ↥M ℂ},
      φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) →
      ClassFunction.inner (coh.extension φ) (∑ r : Fin hyp.w1, grid r 0) = 0)
    (hclassify : ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 -
            (n : ℂ) • ζ) v) →
      Y = (δ : ℂ) • (grid i j - grid i 0))
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) =
      (∑ r : Fin hyp.w1, grid r 0) - coh.extension ζ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      (Even a → a = 0) := by
  obtain ⟨a, Y, hbound, hinner, hYeq, hdecomp⟩ :=
    hyp.SHC_residual_eq_grid_diff hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev grid hclassify
  refine ⟨a, hbound, hinner, ?_⟩
  intro heven
  have ha02 : a = 0 ∨ a = 2 := by
    rcases hbound with h | h | h
    · exact Or.inl h
    · obtain ⟨k, hk⟩ := heven
      omega
    · exact Or.inr h
  have hYd := hYeq ha02
  have htrans := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta
    hG hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ
  rw [h114] at htrans
  have hαgrid : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j -
        (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, grid r 0) = -(δ : ℂ) := by
    rw [hdecomp, hYd]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      grid_diff_inner_zeroColumnSum grid hgridInner i hj0,
      hgridExtensionOrth hζS hζirr hζ1,
      hyp.R_sum_inner_grid_zeroColumnSum coh hRrev grid hgridExtensionOrth]
    ring
  rw [ClassFunction.inner_sub_right, hαgrid, hinner] at htrans
  have ha0 : (a : ℂ) = 0 := by
    linear_combination -htrans
  exact_mod_cast ha0

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), arbitrary-grid regular-value pin.**
The S12 Dade image already equals the canonical aligned sigma-grid difference
on `typePV`.  Consequently it equals any other grid difference whose two
entries have the same values there.  This deliberately asks only for
regular-set value alignment, not a false global uniqueness/equality of sigma
isometries. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_of_grid_value_alignment [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2}
    (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (grid : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ)
    (halign : ∀ k : Fin hyp.w2, ∀ {v : G}, v ∈ typePV M hyp.typeP →
      hyp.alignedOmegaSigmaGrid hG hodd i k v = grid i k v) :
    ∀ v ∈ typePV M hyp.typeP,
      hyp.tau (hyp.muGrid hG hodd i j -
          (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v =
        ((δ : ℂ) • (grid i j - grid i 0)) v := by
  intro v hv
  rw [hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS
    hdeg hμ0 hζ1 hnf hδj hv, ClassFunction.smul_apply,
    ClassFunction.sub_apply, halign j hv, halign 0 hv,
    ← ClassFunction.sub_apply, ← ClassFunction.smul_apply]

open scoped FiniteInduce in
/-- The multiplicative character of the type-P subgroup `W` whose canonical
sigma-image is `alignedOmegaSigmaGrid i j`.  This exposes the source character
which was previously reconstructed only inside value-level proofs. -/
noncomputable def Hypothesis.alignedOmegaSourceCharacter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ↥(typePData_toTICyclicHypothesis hyp.typeP hodd).W →* ℂˣ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  exact (h.sdiffTICyclicHypothesis.omegaProdChar
    (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp e.toMonoidHom

open scoped FiniteInduce in
/-- On the type-P regular set, an aligned sigma-grid entry restores its
underlying multiplicative character.  This is the source-side counterpart of
S15's `tau3_apply_of_regular`. -/
theorem Hypothesis.alignedOmegaSigmaGrid_apply_eq_sourceCharacter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) {v : G}
    (hv : v ∈ typePV M hyp.typeP) :
    hyp.alignedOmegaSigmaGrid hG hodd i j v =
      ((hyp.alignedOmegaSourceCharacter hG hodd i j
        ⟨v, hv.1⟩ : ℂˣ) : ℂ) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _
        (fun _ => rfl))⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  have hvtic : v ∈ tic.V := hv
  have eaos : hyp.alignedOmegaSigmaGrid hG hodd i j v =
      (h.chiColumn χ₂ (finCongr hcardW1.symm i) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        (e ⟨v, tic.V_subset_W hvtic⟩) := by
    unfold Hypothesis.alignedOmegaSigmaGrid
    rw [tic.sigmaIntegral_apply_of_mem_V rfl app _ hvtic,
      ClassFunction.compHom_apply]
    rfl
  have hsource : hyp.alignedOmegaSourceCharacter hG hodd i j =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp e.toMonoidHom := by
    unfold Hypothesis.alignedOmegaSourceCharacter
    rfl
  rw [eaos, hsource]
  rfl

end OddOrder.Peterfalvi.S12

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8)/(11.8.2), eta residual classifier from regular values.**
Suppose the regular set of a type-P datum is the shared S15 regular set.  If a
norm-two virtual character agrees there with a signed eta row difference, then
it equals that difference globally.  Class-function invariance upgrades the
pointwise type-P equality to the conjugacy saturation consumed by
`eta_diff_rigidity`.

This is the concrete eta implementation of the `hclassify` input in
`S12.Hypothesis.SHC_residual_eq_grid_diff`; only the source's regular-value pin
remains for a particular T-side alpha. -/
theorem eta_diff_classifier_of_typePV_value [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (data : TypePData M)
    (hV : typePV M data =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i0 : Fin base.q) {j1 j2 : Fin base.p} (hj : j1 ≠ j2)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    {source : ClassFunction G ℂ}
    (hsource : ∀ v ∈ typePV M data,
      source v = ((s : ℂ) • (base.eta i0 j1 - base.eta i0 j2)) v) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M data, Y v = source v) →
      Y = (s : ℂ) • (base.eta i0 j1 - base.eta i0 j2) := by
  intro Y hYZ hY2 hYsource
  apply eta_diff_rigidity base hYZ hY2 i0 hj hs
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ typePV M data := hV.symm ▸ hw
  rw [ClassFunction.sub_apply,
    ← Y.of_isConj hconj,
    ← (((s : ℂ) • (base.eta i0 j1 - base.eta i0 j2)).of_isConj hconj),
    hYsource w hwV, hsource w hwV, sub_self]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8), eta column-difference rigidity.**
This is the transposed dual of `eta_diff_rigidity`: a norm-two virtual
character agreeing with `s * (eta i1 j0 - eta i2 j0)` on the shared regular
set equals that column difference globally.  The abstract grid-rigidity engine
already permits arbitrary distinct grid points; only the (3.7) separability
assembly is repeated here. -/
theorem eta_column_diff_rigidity [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G)
    (hX2 : ClassFunction.inner X X = 2)
    {i1 i2 : Fin base.q} (hi : i1 ≠ i2) (j0 : Fin base.p)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hvanish : ∀ x ∈ conjClassSet
      ((base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G))),
      (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)) x = 0) :
    X = (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0) := by
  classical
  have hcardq : Nat.card (Fin base.q) = base.q :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hcardp : Nat.card (Fin base.p) = base.p :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hsep : ∀ (i i' : Fin base.q) (j j' : Fin base.p),
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i j) +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i' j') =
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i j') +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0))
          (base.eta i' j) := by
    intro i i' j j'
    have h1 := inner_eta_grid_relation base hvanish i j
    have h2 := inner_eta_grid_relation base hvanish i' j'
    have h3 := inner_eta_grid_relation base hvanish i j'
    have h4 := inner_eta_grid_relation base hvanish i' j
    linear_combination h1 + h2 - h3 - h4
  have hmain := OddOrder.Peterfalvi.S05.orthonormalGrid_diff_rigidity
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    (fun pq => eta_mem_ZIrr base pq.1 pq.2)
    (fun a => by simpa using eta_orthonormal base a.1 a.1 a.2 a.2)
    (fun a b hab => by
      rw [eta_orthonormal base a.1 b.1 a.2 b.2, if_neg]
      rintro ⟨h1, h2⟩
      exact hab (Prod.ext h1 h2))
    (by rw [hcardq]; exact base.three_le_q)
    (by rw [hcardp]; exact base.three_le_p)
    (by rw [hcardq]; exact base.q_odd)
    (by rw [hcardp]; exact base.p_odd)
    (by
      rw [hcardq, hcardp]
      exact (Nat.coprime_primes base.q_prime base.p_prime).mpr
        (Ne.symm base.p_ne_q))
    hXZ hX2 (P1 := (i1, j0)) (P2 := (i2, j0))
    (by intro h; exact hi (Prod.ext_iff.mp h).1) hs hsep
  simpa using hmain

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8)/(11.8.2), transposed eta classifier from regular values.**
The type-P regular-value bridge specialized to an eta column difference, the
orientation required by the T-side transposition in (11.8). -/
theorem eta_column_diff_classifier_of_typePV_value [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (data : TypePData M)
    (hV : typePV M data =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    {i1 i2 : Fin base.q} (hi : i1 ≠ i2) (j0 : Fin base.p)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    {source : ClassFunction G ℂ}
    (hsource : ∀ v ∈ typePV M data,
      source v = ((s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)) v) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M data, Y v = source v) →
      Y = (s : ℂ) • (base.eta i1 j0 - base.eta i2 j0) := by
  intro Y hYZ hY2 hYsource
  apply eta_column_diff_rigidity base hYZ hY2 hi j0 hs
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ typePV M data := hV.symm ▸ hw
  rw [ClassFunction.sub_apply, ← Y.of_isConj hconj,
    ← (((s : ℂ) • (base.eta i1 j0 - base.eta i2 j0)).of_isConj hconj),
    hYsource w hwV, hsource w hwV, sub_self]

/-- The multiplicative character underlying an abstract S15 omega-grid entry.
Nonvanishing follows from multiplicativity and `omega i j 1 = 1`. -/
noncomputable def omegaMonoidHom
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) : ↥base.W →* ℂˣ where
  toFun w := Units.mk0 (base.omega i j w) (by
    intro hz
    have hmul := base.omega_mul i j w w⁻¹
    rw [mul_inv_cancel, base.omega_apply_one, hz, zero_mul] at hmul
    exact zero_ne_one hmul.symm)
  map_one' := Units.ext (base.omega_apply_one i j)
  map_mul' x y := Units.ext (base.omega_mul i j x y)

/-- The underlying omega-grid character has the original class-function value. -/
theorem omegaMonoidHom_coe
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) (w : ↥base.W) :
    ((omegaMonoidHom base i j w : ℂˣ) : ℂ) = base.omega i j w := rfl

/-- Two linear characters of `W = W₁ ⊔ W₂` are equal when their restrictions
to both factors are equal.  This is the factorwise extensionality used to
recover the two coordinate axes of the abstract omega-grid. -/
theorem monoidHom_eq_of_eq_on_W1_W2 [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {f g : ↥base.W →* ℂˣ}
    (hW1 : ∀ x : ↥(base.W1.subgroupOf base.W), f x = g x)
    (hW2 : ∀ y : ↥(base.W2.subgroupOf base.W), f y = g y) :
    f = g := by
  letI := base.W_cyclic
  letI : CommGroup ↥base.W := IsCyclic.commGroup
  have hW1le : base.W1 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_left
  have hW2le : base.W2 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_right
  ext w
  have hw : w ∈ (base.W1.subgroupOf base.W) ⊔
      (base.W2.subgroupOf base.W) := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← base.W_eq_join,
      Subgroup.subgroupOf_self]
    exact Subgroup.mem_top w
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp hw
  rw [← hxy, map_mul, map_mul, hW1 ⟨x, hx⟩, hW2 ⟨y, hy⟩]

/-- Restriction of the column-zero omega character `omega i 0` to `W₁`. -/
noncomputable def omegaW1Restriction
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) : ↥(base.W1.subgroupOf base.W) →* ℂˣ :=
  (omegaMonoidHom base i ⟨0, base.p_prime.pos⟩).comp
    (base.W1.subgroupOf base.W).subtype

/-- Restriction of the row-zero omega character `omega 0 j` to `W₂`. -/
noncomputable def omegaW2Restriction
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (j : Fin base.p) : ↥(base.W2.subgroupOf base.W) →* ℂˣ :=
  (omegaMonoidHom base ⟨0, base.q_prime.pos⟩ j).comp
    (base.W2.subgroupOf base.W).subtype

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.3), abstract omega-grid exhaustion.**
The `q*p` multiplicative characters underlying the S15 omega-grid are
pairwise distinct by orthonormality.  Since the cyclic group `W` has order
`p*q`, its complex linear-character group has the same cardinality; hence the
grid enumerates every `W →* ℂˣ` character. -/
theorem omegaMonoidHom_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
  classical
  have hinj : Function.Injective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
    intro ⟨i, j⟩ ⟨k, l⟩ hhom
    have hcf : base.omega i j = base.omega k l := by
      ext w
      have hw := DFunLike.congr_fun hhom w
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hw
    by_contra hne
    have h1 := eta_orthonormal base i k j l
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega,
      base.tau3_isometry.inner_eq, hcf] at h1
    have h2 := base.omega_orthonormal k k l l
    have hcond : ¬ (i = k ∧ j = l) := fun ⟨hi, hj⟩ => hne (by rw [hi, hj])
    rw [if_neg hcond] at h1
    rw [if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
    exact zero_ne_one (h1.symm.trans h2)
  haveI : Fintype (↥base.W →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ↥base.W := base.W_cyclic
  letI : CommGroup ↥base.W := IsCyclic.commGroup
  haveI : NeZero (Monoid.exponent ↥base.W) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero ((Monoid.exponent ↥base.W : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat : Nat.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥base.W ℂ,
      OddOrder.Peterfalvi.S15.card_W_eq_pq base, Nat.mul_comm]
  have hcardHom : Fintype.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

/-- Distinct column-zero omega characters remain distinct on `W₁`; on the
other factor they are all trivial. -/
theorem omegaW1Restriction_injective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Injective (omegaW1Restriction base) := by
  intro i k hik
  have hhom : omegaMonoidHom base i ⟨0, base.p_prime.pos⟩ =
      omegaMonoidHom base k ⟨0, base.p_prime.pos⟩ := by
    apply monoidHom_eq_of_eq_on_W1_W2 base
    · intro x
      exact DFunLike.congr_fun hik x
    · intro y
      apply Units.ext
      rw [omegaMonoidHom_coe, omegaMonoidHom_coe,
        base.omega_col_zero_apply_of_mem_W2 i y
          (Subgroup.mem_subgroupOf.mp y.property),
        base.omega_col_zero_apply_of_mem_W2 k y
          (Subgroup.mem_subgroupOf.mp y.property)]
  have hp : ((i, ⟨0, base.p_prime.pos⟩) : Fin base.q × Fin base.p) =
      (k, ⟨0, base.p_prime.pos⟩) :=
    (omegaMonoidHom_bijective base).injective hhom
  exact congrArg Prod.fst hp

/-- Distinct row-zero omega characters remain distinct on `W₂`; on the
other factor they are all trivial. -/
theorem omegaW2Restriction_injective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Injective (omegaW2Restriction base) := by
  intro j l hjl
  have hhom : omegaMonoidHom base ⟨0, base.q_prime.pos⟩ j =
      omegaMonoidHom base ⟨0, base.q_prime.pos⟩ l := by
    apply monoidHom_eq_of_eq_on_W1_W2 base
    · intro x
      apply Units.ext
      rw [omegaMonoidHom_coe, omegaMonoidHom_coe,
        base.omega_row_zero_apply_of_mem_W1 j x
          (Subgroup.mem_subgroupOf.mp x.property),
        base.omega_row_zero_apply_of_mem_W1 l x
          (Subgroup.mem_subgroupOf.mp x.property)]
    · intro y
      exact DFunLike.congr_fun hjl y
  have hp : ((⟨0, base.q_prime.pos⟩, j) : Fin base.q × Fin base.p) =
      (⟨0, base.q_prime.pos⟩, l) :=
    (omegaMonoidHom_bijective base).injective hhom
  exact congrArg Prod.snd hp

open scoped Classical in
/-- **Peterfalvi (3.3), `W₁` axis exhaustion.**  The column-zero omega
characters restrict bijectively to all complex linear characters of `W₁`.
The injectivity is factorwise rigidity; surjectivity follows because both
sides have cardinality `q`. -/
theorem omegaW1Restriction_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective (omegaW1Restriction base) := by
  classical
  have hinj := omegaW1Restriction_injective base
  have hW1le : base.W1 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_left
  haveI : IsCyclic ↥base.W := base.W_cyclic
  letI : CommGroup ↥base.W := IsCyclic.commGroup
  haveI : Fintype (↥(base.W1.subgroupOf base.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : NeZero (Monoid.exponent ↥(base.W1.subgroupOf base.W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero ((Monoid.exponent ↥(base.W1.subgroupOf base.W) : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat :
      Nat.card (↥(base.W1.subgroupOf base.W) →* ℂˣ) = base.q := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      ↥(base.W1.subgroupOf base.W) ℂ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv,
      ← base.q_eq_card_W1]
  have hcardHom :
      Fintype.card (↥(base.W1.subgroupOf base.W) →* ℂˣ) = base.q := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

open scoped Classical in
/-- **Peterfalvi (3.3), `W₂` axis exhaustion.**  The row-zero omega
characters restrict bijectively to all complex linear characters of `W₂`.
The injectivity is factorwise rigidity; surjectivity follows because both
sides have cardinality `p`. -/
theorem omegaW2Restriction_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective (omegaW2Restriction base) := by
  classical
  have hinj := omegaW2Restriction_injective base
  have hW2le : base.W2 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_right
  haveI : IsCyclic ↥base.W := base.W_cyclic
  letI : CommGroup ↥base.W := IsCyclic.commGroup
  haveI : Fintype (↥(base.W2.subgroupOf base.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : NeZero (Monoid.exponent ↥(base.W2.subgroupOf base.W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero ((Monoid.exponent ↥(base.W2.subgroupOf base.W) : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat :
      Nat.card (↥(base.W2.subgroupOf base.W) →* ℂˣ) = base.p := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      ↥(base.W2.subgroupOf base.W) ℂ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv,
      ← base.p_eq_card_W2]
  have hcardHom :
      Fintype.card (↥(base.W2.subgroupOf base.W) →* ℂˣ) = base.p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

/-- The zero-column indices as an explicit enumeration of `W₁`'s linear
characters. -/
noncomputable def omegaW1RestrictionEquiv [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Fin base.q ≃ (↥(base.W1.subgroupOf base.W) →* ℂˣ) :=
  Equiv.ofBijective (omegaW1Restriction base)
    (omegaW1Restriction_bijective base)

/-- The zero-row indices as an explicit enumeration of `W₂`'s linear
characters. -/
noncomputable def omegaW2RestrictionEquiv [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Fin base.p ≃ (↥(base.W2.subgroupOf base.W) →* ℂˣ) :=
  Equiv.ofBijective (omegaW2Restriction base)
    (omegaW2Restriction_bijective base)

/-- The zero index on the `W₁` axis is the trivial linear character. -/
theorem omegaW1Restriction_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
  omegaW1Restriction base ⟨0, base.q_prime.pos⟩ = 1 := by
  ext x
  change base.omega ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ x = 1
  exact base.omega_row_zero_apply_of_mem_W1 ⟨0, base.p_prime.pos⟩ x
    (Subgroup.mem_subgroupOf.mp x.property)

/-- The zero index on the `W₂` axis is the trivial linear character. -/
theorem omegaW2Restriction_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
  omegaW2Restriction base ⟨0, base.p_prime.pos⟩ = 1 := by
  ext y
  change base.omega ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ y = 1
  exact base.omega_col_zero_apply_of_mem_W2 ⟨0, base.q_prime.pos⟩ y
    (Subgroup.mem_subgroupOf.mp y.property)

/-- The inverse `W₁`-axis enumeration sends the trivial character back to
the distinguished zero index. -/
theorem omegaW1RestrictionEquiv_symm_one [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (omegaW1RestrictionEquiv base).symm 1 = ⟨0, base.q_prime.pos⟩ := by
  apply (omegaW1RestrictionEquiv base).injective
  rw [Equiv.apply_symm_apply]
  change 1 = omegaW1Restriction base ⟨0, base.q_prime.pos⟩
  exact (omegaW1Restriction_zero base).symm

/-- The inverse `W₂`-axis enumeration sends the trivial character back to
the distinguished zero index. -/
theorem omegaW2RestrictionEquiv_symm_one [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (omegaW2RestrictionEquiv base).symm 1 = ⟨0, base.p_prime.pos⟩ := by
  apply (omegaW2RestrictionEquiv base).injective
  rw [Equiv.apply_symm_apply]
  change 1 = omegaW2Restriction base ⟨0, base.p_prime.pos⟩
  exact (omegaW2Restriction_zero base).symm

open scoped Classical in
/-- Every complex linear character of the shared cyclic `W` is one omega-grid entry. -/
theorem exists_omegaMonoidHom_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (ξ : ↥base.W →* ℂˣ) :
    ∃ (i : Fin base.q) (j : Fin base.p), omegaMonoidHom base i j = ξ := by
  obtain ⟨ij, hij⟩ := (omegaMonoidHom_bijective base).surjective ξ
  exact ⟨ij.1, ij.2, hij⟩

end OddOrder.Peterfalvi.S16
