/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E

/-!
# BG §12: Lemma 12.18 — `τ₁`-elements against `M_α`

**スコープ**: BG Chapter III §12, Lemma 12.18 (pp. 89-90, mmd L3454-3508)。
`p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, `Q` a nontrivial `P`-invariant `q`-subgroup of `M` (`q ≠ p`) with
`C_Q(P) = 1` and `ℳ(N_G(Q)) ≠ {M}`:

- **(a)** `M_α ≠ 1` and `q ∉ α(M)` imply `C_{M_α}(P) ≠ 1` and `C_{M_α}(PQ) = 1`;
- **(b)** if moreover `Q` is a Sylow `q`-subgroup of `M`, then `α(M) = β(M)` and all the
  hypotheses and conclusions of (a) hold.

Building blocks (Helper A `maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1`,
BB2 `exists_charSubgroup_exponent_not_centralized`, BB3
`exists_invariant_sylow_Malpha_rank_three`, the fixed-point-free decomposition
`inf_centralizer_sup_eq_bot_of_le_normalizer`, and the first conjunct of (a)
`tau1_Malpha_centralizer_P_ne_bot`) are in `S12_E.lean`. This file contains the second
conjunct of (a) (the hard core), the part (b) reduction, and the assembled
`tau1_Malpha_interaction`.

## 主要結果

- `isNilpotent_derived_of_Malpha_eq_bot` (BB4): `M_α = 1 ⇒ M'` nilpotent
  (the degenerate case of BG Theorem 10.2(d), used contrapositively in (b))
- `tau1_Malpha_centralizer_PQ_eq_bot`: (a) second conjunct `C_{M_α}(PQ) = 1`
- `tau1_Malpha_interaction`: **BG Lemma 12.18**
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BB4 — degenerate case of BG Theorem 10.2(d)**: if `M_α = 1` then `M'` is nilpotent.
By `S10.derived_quotient_Malpha_le_fitting`, `(M/M_α)' ≤ F(M/M_α)` unconditionally; with
`M_α = 1` the quotient is by `⊥`, so `M' ≤ F(M)`-type nilpotency transports back to `↥M`
along `QuotientGroup.quotientBot`. Used contrapositively in Lemma 12.18(b) to produce
`M_α ≠ 1` from the non-nilpotence of `M'`. -/
theorem isNilpotent_derived_of_Malpha_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hα : S10.Malpha M = ⊥) :
    Group.IsNilpotent ↥(derivedInG M) := by
  classical
  have h102 := S10.derived_quotient_Malpha_le_fitting hG hM
  -- the quotient is by `⊥`, so it is isomorphic to `↥M` itself.
  have hbot : (S10.Malpha M).subgroupOf M = ⊥ := by rw [hα, Subgroup.bot_subgroupOf]
  have e2 : (↥M ⧸ (S10.Malpha M).subgroupOf M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  -- the commutator of the quotient is nilpotent: subgroup of the nilpotent Fitting subgroup.
  haveI hnil1 : Group.IsNilpotent ↥(commutator (↥M ⧸ (S10.Malpha M).subgroupOf M)) :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h102)
  have hcomm_eq :
      (commutator (↥M ⧸ (S10.Malpha M).subgroupOf M)).map e2.toMonoidHom = commutator ↥M := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e2.surjective, ← _root_.commutator_def]
  haveI hnil2 : Group.IsNilpotent ↥(commutator ↥M) := by
    rw [← hcomm_eq]
    exact nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ e2.injective)
  -- `derivedInG M = (commutator ↥M).map M.subtype`.
  exact nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)

/-- **BG Lemma 12.18** (mmd L3454): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, `q ∈ p'`, `Q` を `M` の非自明
`P`-不変 `q`-部分群で `C_Q(P)=1`, `ℳ(N_G(Q))≠{M}` とすると
(a) `M_α≠1` かつ `q∉α(M)` なら `C_{M_α}(P)≠1` かつ `C_{M_α}(PQ)=1`;
(b) `Q` が `M` の Sylow `q` なら `α(M)=β(M)` で (a) の状況が成立。 -/
theorem tau1_Malpha_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M}) :
    (S10.Malpha M ≠ ⊥ → q ∉ S10.alpha M →
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) ∧
    ((∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T) →
      S10.alpha M = S10.beta M ∧ S10.Malpha M ≠ ⊥ ∧ q ∉ S10.alpha M ∧
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) := by
  sorry

end OddOrder.BG.Ch3.S12
