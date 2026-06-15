/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_SigmaIsometry

/-!
# Peterfalvi §5: the (3.3) ω-grid indexed by `Fin |W₁| × Fin |W₂|`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§3 (repo chunk 04.3), result (3.3).

This is a **signature-bridge leaf** for the FT critical path
(`notes/meta/ft_path_policy.md` §4, endpoint **B**).  It exposes the (3.3)
ω-grid — the linear characters `ω_{ij}` of `W = W₁W₂` indexed by the duals
`Ĉ₁ × Ĉ₂` (`TICyclicHypothesis.omegaIrrEquiv`) — re-indexed by
`Fin |W₁| × Fin |W₂|` with the distinguished index `0 ↦ 1` (trivial dual), so
that `ω_{00} = 1_W`.  This is the exact shape of the §13 `S,T`-grid field
`S15.Hypothesis.omega : Fin q → Fin p → ClassFunction ↥W ℂ` (`q = |W₁|`,
`p = |W₂|`), whose anchored differences `ω_{ij} − ω_{0j}` / `ω_{ij} − ω_{i0}`
drive `mu_definition`/`nu_definition`.

The reindex `charEquiv` generalizes `S06.…w1CharEquiv` (which only covers the
`W₁` direction, on the certain-type structure) to either coprime cyclic factor
of any `TICyclicHypothesis`.  Pure §5 character theory — **not** gated on the
§10–16 maximal-subgroup structure.  Pinning the consumer side
(`S15.Hypothesis.omega := …`) is the §13-spine owner's wiring step.
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G)

/-- An arbitrary reindexing `Fin |H| ≃ Ĥ` of a subgroup-dual, from the cardinality
match `|Ĥ| = |H|` (`card_charGroup_subgroupOf`, Pontryagin self-duality). -/
noncomputable def charBaseEquiv {H : Subgroup G} (hHW : H ≤ hyp.W) :
    Fin (Nat.card H) ≃ ((H.subgroupOf hyp.W) →* ℂˣ) :=
  haveI : Fintype ((H.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  (Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact hyp.card_charGroup_subgroupOf hHW)).symm

/-- The reindexing `Fin |H| ≃ Ĥ` pinned at `0 ↦ 1` (trivial character), by composing
`charBaseEquiv` with the transposition moving the trivial character to index `0`.
Generalizes `S06.…w1CharEquiv` to any subgroup `H ≤ W`. -/
noncomputable def charEquiv {H : Subgroup G} (hHW : H ≤ hyp.W) [NeZero (Nat.card H)] :
    Fin (Nat.card H) ≃ ((H.subgroupOf hyp.W) →* ℂˣ) :=
  (Equiv.swap (0 : Fin (Nat.card H)) ((hyp.charBaseEquiv hHW).symm 1)).trans
    (hyp.charBaseEquiv hHW)

@[simp] theorem charEquiv_zero {H : Subgroup G} (hHW : H ≤ hyp.W) [NeZero (Nat.card H)] :
    hyp.charEquiv hHW 0 = 1 := by
  rw [charEquiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- **Peterfalvi (3.3) ω-grid**, indexed by `Fin |W₁| × Fin |W₂|` with the
distinguished `0`-indices = trivial duals.  This is the family
`S15.Hypothesis.omega` is pinned to. -/
noncomputable def omegaGrid [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)] :
    Fin (Nat.card hyp.W1) → Fin (Nat.card hyp.W2) → ClassFunction hyp.W ℂ :=
  fun i j =>
    (hyp.omega (hyp.omegaProdChar
      (hyp.charEquiv hyp.W1_le_W i) (hyp.charEquiv hyp.W2_le_W j)) :
        ClassFunction hyp.W ℂ)

/-- **Peterfalvi (3.3) anchor**: `ω_{00} = 1_W` (the trivial class function). -/
@[simp] theorem omegaGrid_zero_zero [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)] :
    hyp.omegaGrid 0 0 = trivialClassFunction hyp.W := by
  rw [omegaGrid, hyp.charEquiv_zero hyp.W1_le_W, hyp.charEquiv_zero hyp.W2_le_W,
    hyp.omegaProdChar_one_one]
  ext w
  simp

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
