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

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.4), the column computation**: summing the (10.10.3) images
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` over the `w₁` rows and pinning the first
column by (10.9) gives the coherent-extension glue for the column character
`μ_j = ∑_i μ_{ij}`:

`(μ_j − d·ζ)^τ = δ·(μ_0 − ζ)^τ + ∑_i α_{ij}^τ = δ·∑_i ω_{ij}^σ − d·ζ^{τ₁}`.

The `ζ`-coefficient collapses through `n·w₁ = d − δ` (`hnf`): on the source side
`−δ − n·w₁ = −d` (so `μ_j − d·ζ = δ·(μ_0 − ζ) + ∑_i α_{ij}` is exact), and on the image side
`δ + n·w₁ = d` reassembles the `−d·ζ^{τ₁}` tail.  The (10.9) pin
`(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}` is supplied separately as `hpin`. -/
theorem Hypothesis.SHC_tau_muColumn_sub_smul_zeta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : ∀ i, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : ∀ i, hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : ∀ i, hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : ∀ i, hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card)
    (hpin : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (δ : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  -- the (10.3) index relation, cast to `ℂ`: `d = δ + w₁·n`
  have hd' : (d : ℂ) = (δ : ℂ) + (hyp.w1 : ℂ) * (n : ℂ) := by
    have h := congrArg (Int.cast : ℤ → ℂ) hnf
    push_cast at h
    linear_combination -h
  -- the per-row (10.10.3) images `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`
  have htau_i : ∀ i : Fin hyp.w1, hyp.tau (hyp.muGrid hG hodd i j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (n : ℂ) • coh.extension ζ := fun i =>
    hyp.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount hG coh hodd i hj0 hζS hζirr hζ1 hζne
      (hdeg i) (hμ0 i) hnf hδj (hdζ i) (h0ζ i) hδpm hneq h8
  -- the `δ`-scaled (10.9) pin `(δ·(μ_0 − ζ))^τ = δ·(∑_i ω_{i0}^σ − ζ^{τ₁})`
  have hpinδ : hyp.tau ((δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.extension ζ) := by
    rw [Int.cast_smul_eq_zsmul ℂ δ ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ),
      map_zsmul, hpin, Int.cast_smul_eq_zsmul ℂ δ]
  -- source-side regrouping `μ_j − d·ζ = δ·(μ_0 − ζ) + ∑_i α_{ij}` (ζ-coefficient `−δ − n·w₁ = −d`)
  have hsum_mu : ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        - (δ : ℂ) • (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (n : ℂ)) • ζ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hsrc : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        + ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j
            - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) := by
    rw [hsum_mu, hd']
    module
  -- image-side collapse of the `α`-sum
  have hsum_om : ∑ i : Fin hyp.w1, ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (n : ℂ) • coh.extension ζ)
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
          - (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0))
        - ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension ζ := by
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum (r := (δ : ℂ)), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
  rw [hsrc, map_add, map_sum, hpinδ]
  simp only [htau_i]
  rw [hsum_om, hd']
  module

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.9)/(10.10.4), the column-`0` pin**: `(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}`,
where `ζ^{τ₁} = coh.extension ζ` is the `S₁ = S(HC)`-coherent extension — the residual `χ` of the
(10.9) decomposition **identified** with `ζ^{τ₁}` (book: "As `(α_{ij}, μ_0 − ζ) = −δ + n`, it
follows from (10.9), (10.10.1) and (10.10.3) that `(μ_0 − ζ)^τ = ∑_{0≤i<w₁} ω_{i0}^σ − ζ^{τ₁}`").

The coherence-free (10.9) σ-coefficient form
(`inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2`, hence the hypothesis `w₁ < w₂`)
pins `⟨ψ, ω_{ij}^σ⟩ = [j = 0]` for `ψ = (μ_0 − ζ)^τ`, and the Dade isometry gives
`‖ψ‖² = ‖μ_0 − ζ‖² = w₁ + 1` (`inner_muColumnZero_sub_zeta_self`), so the residual
`χ = ∑_i ω_{i0}^σ − ψ` has `‖χ‖² = w₁ − w₁ − w₁ + (w₁ + 1) = 1`.  The identification is the
(10.10.4) pairing: transporting `(α_{0j}, μ_0 − ζ) = n − δ` through the Dade isometry
(`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`) and expanding `α_{0j}^τ` by (10.10.3)
(`SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount`) forces `⟨ζ^{τ₁}, ψ⟩ = −1` (using `n = 2 ≠ 0`);
with `⟨ζ^{τ₁}, ∑_i ω_{i0}^σ⟩ = 0` (`SHC_extension_inner_zeroColumnOmegaSigma_sum`, (5.3.b)) this
gives `⟨ζ^{τ₁}, χ⟩ = 1`, and `‖ζ^{τ₁}‖² = 1 = ‖χ‖²` collapses
`‖ζ^{τ₁} − χ‖² = 1 − 1 − 1 + 1 = 0`, i.e. `χ = ζ^{τ₁}` (positive-definiteness).  This discharges
the `hpin` input of `SHC_tau_muColumn_sub_smul_zeta`. -/
theorem Hypothesis.SHC_tau_muColumnZero_sub_zeta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : ∀ i, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : ∀ i, hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : ∀ i, hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : ∀ i, hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card)
    (hw12 : hyp.w1 < hyp.w2) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.extension ζ := by
  classical
  -- `w₁ ≥ 3`, so the row `0` for the (10.10.4) α-pairing exists
  have h3 : (3 : ℕ) ≤ hyp.w1 :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  haveI : NeZero hyp.w1 := ⟨by omega⟩
  -- the (10.9) coherence-free σ-coefficients: `⟨ψ, ω_{ij'}^σ⟩ = [j' = 0]`
  have hψω : ∀ (i : Fin hyp.w1) (j' : Fin hyp.w2),
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd i j') = (if j' = 0 then (1 : ℂ) else 0) :=
    fun i j' =>
      inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 hG hyp hζS hζirr hζ1 hw12 i j'
  have hωψ : ∀ (i : Fin hyp.w1) (j' : Fin hyp.w2),
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j')
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        = (if j' = 0 then (1 : ℂ) else 0) := by
    intro i j'
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψω i j']
    by_cases hj' : j' = 0 <;> simp [hj']
  -- the (10.10.4) pairing: `⟨ζ^{τ₁}, ψ⟩ = −1`
  have hzψ : ClassFunction.inner (coh.extension ζ)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = -1 := by
    have hpair := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd 0 hj0 hζS hζirr hζ1
      (hdeg 0) (hμ0 0) hnf hδj (hdζ 0) (h0ζ 0)
    rw [hyp.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount hG coh hodd 0 hj0 hζS hζirr hζ1 hζne
      (hdeg 0) (hμ0 0) hnf hδj (hdζ 0) (h0ζ 0) hδpm hneq h8] at hpair
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left] at hpair
    rw [hωψ 0 j, hωψ 0 0, if_neg hj0, if_pos rfl] at hpair
    have hn : ((n : ℕ) : ℂ) = 2 := by rw [hneq]; norm_num
    rw [hn] at hpair
    linear_combination (-1 / 2 : ℂ) * hpair
  -- (5.3.b): `⟨ζ^{τ₁}, ∑_i ω_{i0}^σ⟩ = 0`, and `‖ζ^{τ₁}‖² = 1`
  have hzΩ : ClassFunction.inner (coh.extension ζ)
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne
  have hzz : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  -- the (10.9) norm data: `⟨ψ, Ω⟩ = ⟨Ω, ψ⟩ = ⟨Ω, Ω⟩ = w₁` and `⟨ψ, ψ⟩ = w₁ + 1`
  have hsum1 : ∑ _i : Fin hyp.w1, (1 : ℂ) = (hyp.w1 : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψΩ : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = (hyp.w1 : ℂ) := by
    have h1 : ∀ i : Fin hyp.w1, ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd i 0) = 1 := fun i => by
      rw [hψω i 0, if_pos rfl]
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl (fun i _ => h1 i), hsum1]
  have hΩψ : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩΩ : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = (hyp.w1 : ℂ) := by
    have h1 : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i 0)
        (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0) = 1 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single i]
      · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 0, if_pos ⟨rfl, rfl⟩]
      · intro i' _ hi'
        rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i' 0 0,
          if_neg (fun hh => hi' hh.1.symm)]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [inner_sum_left, Finset.sum_congr rfl (fun i _ => h1 i), hsum1]
  have hψψ : ClassFunction.inner
      (hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))
      (hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    have hsupp : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 :=
      hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- transposed values (conjugate symmetry; all values are real)
  have hψz : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) (coh.extension ζ) = -1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hzψ]
    simp
  have hΩz : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (coh.extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hzΩ, star_zero]
  -- Cauchy–Schwarz equality: `‖ζ^{τ₁} − (Ω − ψ)‖² = 1 − 1 − 1 + 1 = 0`, so `ζ^{τ₁} = Ω − ψ`
  have hzero : ClassFunction.inner
      (coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)))
      (coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, hzz, hzΩ, hzψ,
      hΩz, hΩΩ, hΩψ, hψz, hψΩ, hψψ]
    push_cast
    ring
  have heq : coh.extension ζ
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) :=
    sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero
      (φ := coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)))
      (by rw [hzero]; exact Complex.zero_re))
  rw [heq, sub_sub_cancel]

end OddOrder.Peterfalvi.S12
