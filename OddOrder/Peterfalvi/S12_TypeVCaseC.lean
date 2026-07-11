/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core

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

end OddOrder.Peterfalvi.S12
