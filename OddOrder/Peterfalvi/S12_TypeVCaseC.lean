/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core
import OddOrder.Peterfalvi.S12_Props109To1011

/-!
# Peterfalvi (10.10.2)–(10.10.4): type-V case (c) — column characters

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§10, pp. 58-63, Theorem (10.10) proof, case (c) of Definition (8.7).

Case-(c) cluster of `typeV_forces_coherence` (issue 1021): the column characters
`μ_j = ∑_{0≤i<w₁} μ_{ij}` of the (10.3) grid — Peterfalvi's reducible members of
`S` in case (c) — their degree `μ_j(1) = d·w₁` ((10.10.2)), and the (10.10.4)
column identity `∑_i α_{ij} = μ_j − δ·μ_0 − (d−δ)·ζ`, the source-side algebra of
the coherent-extension glue `(μ_j − d·ζ)^τ = δ·(μ_0 − ζ)^τ + ∑_i α_{ij}^τ`.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {M : Subgroup G}

namespace CharacterParameters

variable {hyp : Hypothesis M}

/-- The **column character** `μ_j = ∑_{0≤i<w₁} μ_{ij}` of the (10.3) grid — Peterfalvi's
`μ_j`, the (reducible) members of `S − S₁` in case (c) of the (10.10) proof. -/
noncomputable def muColumn (params : CharacterParameters hyp) (j : Fin hyp.w2) :
    ClassFunction ↥M ℂ :=
  ∑ i : Fin hyp.w1, params.mu i j

/-- **`μ_j(1) = d·w₁`** for `j ≠ 0` — the degree of the column character, the degree half of
(10.10.2)'s "the elements of `S − S₁` have degree `p·w₁`" (with `d = p` in case (c)).  Each
grid entry has degree `d` (`degree_independent`), and there are `w₁` rows. -/
theorem muColumn_apply_one (params : CharacterParameters hyp) {j : Fin hyp.w2}
    (hj : j ≠ 0) :
    params.muColumn j 1 = (params.d : ℂ) * (hyp.w1 : ℂ) := by
  rw [muColumn, ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun i _ => params.degree_independent i j hj),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **The (10.10.4) column identity**: `∑_i α_{ij} = μ_j − δ·μ_0 − (d−δ)·ζ`.  Summing the
(10.5) definition `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` over the `w₁` rows collapses the
`ζ`-coefficient to `n·w₁ = d − δ` (`n_formula`).  This is the source-side identity behind
`(μ_j − d·ζ)^τ = δ·(μ_0 − ζ)^τ + ∑_i α_{ij}^τ` in the (10.10.4) coherence computation. -/
theorem sum_alpha_eq (params : CharacterParameters hyp) (j : Fin hyp.w2) :
    ∑ i : Fin hyp.w1, params.alpha i j
      = params.muColumn j - (params.delta : ℂ) • params.muColumn 0
        - (((params.d : ℤ) - params.delta : ℤ) : ℂ) • params.zeta := by
  have hcast : ((params.n : ℂ)) * (hyp.w1 : ℂ) = (((params.d : ℤ) - params.delta : ℤ) : ℂ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) params.n_formula
  calc ∑ i : Fin hyp.w1, params.alpha i j
      = ∑ i : Fin hyp.w1,
          (params.mu i j - (params.delta : ℂ) • params.mu i 0 - (params.n : ℂ) • params.zeta) :=
        Finset.sum_congr rfl (fun i _ => params.alpha_def i j)
    _ = (∑ i : Fin hyp.w1, params.mu i j)
          - (params.delta : ℂ) • (∑ i : Fin hyp.w1, params.mu i 0)
          - ((params.n : ℂ) * (hyp.w1 : ℂ)) • params.zeta := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
    _ = params.muColumn j - (params.delta : ℂ) • params.muColumn 0
          - (((params.d : ℤ) - params.delta : ℤ) : ℂ) • params.zeta := by
        rw [hcast, muColumn, muColumn]

end CharacterParameters

/-- **The (10.10.3) coefficient vanishing, pure arithmetic**: if `c·a² − 4a − 2 ≤ 0` with
`c ≥ 8` (book: `c = |S₁| = 4(w₁−1) ≥ 8` and `n = 2`, so the norm inequality reads
`|S₁|a² − 2an − 2 ≤ 0`), then the integer coefficient `a` is `0`. -/
theorem alpha_coefficient_eq_zero {c a : ℤ} (hc : 8 ≤ c)
    (h : c * a ^ 2 - 4 * a - 2 ≤ 0) : a = 0 := by
  by_contra ha
  have h1 : 1 ≤ a ∨ a ≤ -1 := by omega
  rcases h1 with h1 | h1
  · nlinarith [sq_nonneg a, sq_nonneg (a - 1)]
  · nlinarith [sq_nonneg a, sq_nonneg (a + 1)]

namespace CharacterParameters

variable {hyp : Hypothesis M}

/-- **The (10.10.2) index pin `n = 2`**: with `d = p = 2w₁ − 1` and `δ = −1`, the (10.3)
relation `n·w₁ = d − δ = 2w₁` forces `n = 2`. -/
theorem n_eq_two (params : CharacterParameters hyp) (hw1 : 0 < hyp.w1)
    (hd : (params.d : ℤ) = 2 * (hyp.w1 : ℤ) - 1) (hδ : params.delta = -1) :
    params.n = 2 := by
  have h := params.n_formula
  rw [hd, hδ] at h
  have hw1' : (0 : ℤ) < (hyp.w1 : ℤ) := by exact_mod_cast hw1
  have h2 : (params.n : ℤ) * (hyp.w1 : ℤ) = 2 * (hyp.w1 : ℤ) := by linarith
  have : (params.n : ℤ) = 2 := mul_right_cancel₀ hw1'.ne' h2
  exact_mod_cast this

/-- **The (10.10.2) sign pin `δ = −1`**: with `d = p = 2w₁ − 1` and `w₁ ≥ 3`, the sign
`δ = +1` is impossible — `n·w₁ = d − 1 = 2w₁ − 2` would give `w₁ ∣ 2`.  (The `δ = ±1`
dichotomy is Peterfalvi (10.3), `muColumnSign_eq_one_or_neg_one`.) -/
theorem delta_eq_neg_one (params : CharacterParameters hyp) (hw1 : 3 ≤ hyp.w1)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hd : (params.d : ℤ) = 2 * (hyp.w1 : ℤ) - 1) :
    params.delta = -1 := by
  rcases hδpm with h1 | h
  · exfalso
    have h := params.n_formula
    rw [hd, h1] at h
    have hdvd : (hyp.w1 : ℤ) ∣ 2 := by
      have h2 : ((params.n : ℤ) - 2) * (hyp.w1 : ℤ) = -2 := by linear_combination h
      have : (hyp.w1 : ℤ) ∣ -2 := Dvd.intro_left _ h2
      exact (dvd_neg.mp this)
    have hle : (hyp.w1 : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    have : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    omega
  · exact h

end CharacterParameters

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3), the `a = 0` coefficient computation** — the type-V case-(c)
counterpart of the (11.8.2) `muGridAlpha_tau_residual_norm`: projecting `α_{ij}^τ` onto the
orthonormal `S₁^{τ₁} = R` gives a constant coefficient `a` off `ζ^{τ₁}`
(`muGridAlpha_tau_inner_SHC_extension_sub`) and `a − n` at `ζ^{τ₁}`; Parseval + the norm
`‖α_{ij}^τ‖² = 2 + n²` give `(a−n)² + (|R|−1)a² ≤ 2 + n²`, i.e. `|R|·a² − 2an − 2 ≤ 0`.
In the (10.10.3) regime `n = 2` and `|R| = |S₁| = 4(w₁−1) ≥ 8` — as opposed to the
(11.8.1) regime `|R| = n` — this forces `a = 0` (`alpha_coefficient_eq_zero`), so
`⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n`: exactly the `hα0` input of `SHC_tau_muGridAlpha_eq`, whence
`α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` ((10.10.3)). -/
theorem Hypothesis.muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    {R : Finset (ClassFunction G ℂ)} (hR8 : 8 ≤ R.card)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (coh.extension ζ) = -(n : ℂ) := by
  classical
  have hζR : coh.extension ζ ∈ R := hRmem ζ hζS hζirr hζ1
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  obtain ⟨c, Y, hcoeff, hnorm, hYorth, hdecomp, hYZ⟩ :=
    inner_self_eq_sum_sq_add_of_intProjection hαZ hZ horth
  set a : ℤ := c (coh.extension ζ) + (n : ℤ) with hadef
  have hcζ : c (coh.extension ζ) = a - (n : ℤ) := by rw [hadef]; ring
  have hcη : ∀ β ∈ R, β ≠ coh.extension ζ → c β = a := by
    intro β hβR hβne
    obtain ⟨η, hηS, hηirr, hη1, rfl⟩ := hRrev β hβR
    have hηζ : η ≠ ζ := fun h => hβne (by rw [h])
    have hsub := hyp.muGridAlpha_tau_inner_SHC_extension_sub hG coh hodd i hj0 hζS hζirr hζ1
      hηS hηirr hη1 hηζ hdeg hμ0 hnf hδj hdζ h0ζ
    rw [hcoeff _ hζR, hcoeff _ (hRmem η hηS hηirr hη1)] at hsub
    have hcast : ((c (coh.extension η) : ℤ) : ℂ) = ((a : ℤ) : ℂ) := by
      rw [hadef]; push_cast; linear_combination -hsub
    exact_mod_cast hcast
  have hsplit := sum_sq_eq_of_split hζR hcζ hcη
  have hnorm2 := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  rw [hnorm2, hsplit] at hnorm
  have hineq : (a - (n : ℤ)) ^ 2 + ((R.card : ℤ) - 1) * a ^ 2 ≤ 2 + (n : ℤ) ^ 2 := by
    apply int_le_of_add_inner_self_eq (Y := Y)
    push_cast at hnorm ⊢
    linear_combination -hnorm
  have hc8 : (8 : ℤ) ≤ (R.card : ℤ) := by exact_mod_cast hR8
  have ha0 : a = 0 := by
    refine alpha_coefficient_eq_zero hc8 ?_
    subst hneq
    push_cast at hineq
    nlinarith [hineq]
  have hval := hcoeff _ hζR
  rw [hcζ, ha0] at hval
  rw [hval]
  push_cast
  ring

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3)** (grid form): in the (10.10.3) regime — `n = 2` and an orthonormal
`S₁^{τ₁} = R` with `|R| ≥ 8` — the Dade image of the (10.5) difference is
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` with `ζ^{τ₁}` the `S₁`-coherent extension.
Composition of the `a = 0` coefficient computation
(`muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card`) with the SHC (10.5) endgame
(`SHC_tau_muGridAlpha_eq`). -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_card [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    {R : Finset (ClassFunction G ℂ)} (hR8 : 8 ≤ R.card)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ :=
  hyp.SHC_tau_muGridAlpha_eq hG coh hodd i hj0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj hdζ h0ζ hδpm
    (hyp.muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hneq hR8 hZ horth hRmem hRrev)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3), count form** (R-free): with `n = 2` and at least `8` degree-`w₁`
irreducible members of `S` — the (10.10.2) count is `|S₁| = 4(w₁−1) ≥ 8` for `w₁ ≥ 3` —
the (10.5) difference maps to `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.  The
orthonormal family `S₁^{τ₁}` and its cardinality are supplied by
`exists_SHC_extension_orthonormal`. -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ := by
  obtain ⟨R, hZ, horth, hRmem, hRrev, hcard⟩ := hyp.exists_SHC_extension_orthonormal hG coh
  exact hyp.SHC_tau_muGridAlpha_eq_of_eight_le_card hG coh hodd i hj0 hζS hζirr hζ1 hζne
    hdeg hμ0 hnf hδj hdζ h0ζ hδpm hneq (by rw [hcard]; exact h8) hZ horth hRmem hRrev

end OddOrder.Peterfalvi.S12
