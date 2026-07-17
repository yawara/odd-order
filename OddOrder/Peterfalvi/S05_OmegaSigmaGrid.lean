/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_IntegralSigma
import OddOrder.Peterfalvi.S05_OmegaGrid

/-!
# Peterfalvi §5: the `ω^σ`-grid (the σ-image of the ω-grid)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§3 (repo chunk 04.3), result (3.6).

This is a **signature-bridge leaf** for the FT critical path
(`notes/meta/ft_path_policy.md` §4, endpoint **E**, the `ω^σ` part).  It names the
composite `ω_{ij}^σ = σ(ω_{ij})` of the integral (3.2) σ-map (`sigmaIntegral`,
endpoint C) and the (3.3) ω-grid (`omegaGrid`, endpoint B): the virtual characters
`ω_{ij}^σ ∈ ZIrr(G)` that appear throughout §10–16.

This grid is what `S15.Hypothesis.eta` is pinned to (so `S15`'s (13.1.d)
`eta_eq_tau_omega` is `rfl`).  `S12.CharacterParameters.omegaSigma` is pinned to the
sibling *aligned* `σ`-image `S12.Hypothesis.alignedOmegaSigmaGrid` (the σ-image of the
*same* `ω` that `muGrid` is built from) — the per-`(i,j)` alignment that the (10.5)
Dade-image identity `tau_muGridAlpha_eq`/`alpha_tau_image` requires.

**Scope note (endpoint E)**: `ω^σ` is the only part of `S12.CharacterParameters`
supplied by §3–9 character theory.  The remaining `CharacterParameters` fields
(`zeta` of degree `w₁` (10.2), the arithmetic `d`/`δ`/`n` (10.3), the certain-type
`mu`/`alpha` of `M`, and the coherent extension) are §10-level analysis gated on
`IsMinimalSimpleOdd` and the §10–16 maximal-subgroup structure — *not* a §3–9
signature gap.  They belong to the §12 analysis owner, not to signature
pre-staging.  Pure §5 character theory — **not** gated on the §10–16 structure.
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G) [Fintype hyp.W]
  [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
  (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
  [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)]

/-- **Peterfalvi (3.6) `ω^σ`-grid** = `σ(ω)`: the integral-σ image of the (3.3)
ω-grid, the virtual characters `ω_{ij}^σ` of `G`.  This is the family that
`S15.Hypothesis.eta` is pinned to (`S12.CharacterParameters.omegaSigma` uses the
aligned sibling `S12.Hypothesis.alignedOmegaSigmaGrid`). -/
noncomputable def omegaSigmaGrid :
    Fin (Nat.card hyp.W1) → Fin (Nat.card hyp.W2) → ClassFunction G ℂ :=
  fun i j => hyp.sigmaIntegral hVeq app (hyp.omegaGrid i j)

@[simp] theorem omegaSigmaGrid_apply (i : Fin (Nat.card hyp.W1))
    (j : Fin (Nat.card hyp.W2)) :
    hyp.omegaSigmaGrid hVeq app i j = hyp.sigmaIntegral hVeq app (hyp.omegaGrid i j) :=
  rfl

omit [Fintype ↥hyp.W] in
/-- The (3.3) ω-grid entries are virtual characters of `W` (each is irreducible). -/
theorem omegaGrid_mem_ZIrr (i : Fin (Nat.card hyp.W1)) (j : Fin (Nat.card hyp.W2)) :
    hyp.omegaGrid i j ∈ ZIrr hyp.W := by
  simp only [omegaGrid]
  exact (hyp.omega _).mem_ZIrr

/-- **`ω^σ` are virtual characters of `G`** (the integral σ-map sends `ZIrr W` to
`ZIrr G`). -/
theorem omegaSigmaGrid_mem_ZIrr (i : Fin (Nat.card hyp.W1))
    (j : Fin (Nat.card hyp.W2)) :
    hyp.omegaSigmaGrid hVeq app i j ∈ ZIrr G :=
  hyp.sigmaIntegral_mem_ZIrr hVeq app (hyp.omegaGrid_mem_ZIrr i j)

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
