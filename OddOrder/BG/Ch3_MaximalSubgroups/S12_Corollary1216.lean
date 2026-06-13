/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Proposition1215

/-!
# BG §12 Corollary 12.16 — `σ(M)`-subgroup ↔ maximal-subgroup interaction (downstream leaf)

**Bender–Glauberman, _Local Analysis for the Odd Order Theorem_, §12, Corollary 12.16**
(mmd L3453–3476, PDF pp.95–96).

For a nonidentity `σ(M)`-subgroup `Y` of `G`, every prime `p ∈ π(E) ∩ β(G)'`, and every
`H ∈ ℳ(Y)` not conjugate to `M`:

* (a) `r_p(N_H(Y)) ≤ 1` (`pRank_normalizer_le_one`);
* (b) if `p ∈ τ₁(M)` then `p ∉ π(N_H(Y)')` (`not_mem_primeFactors_derived_of_tau1`).

## なぜ downstream leaf か (architecture)

12.16 の証明は **BG Proposition 12.15** (`S12_Proposition1215.sigma_subgroup_maximal_interaction`)
を本質的に要する (BG L3466-3476: 「By Proposition 12.15(a),(e) … `M* = (M ∩ M*)K`」)。ところが
`S12_Proposition1215` は `S12_E` を推移 import している (S12_Theorem125 → S12_ExceptionalBridge →
… → S12_Lemma1218 → S12_E)。よって `S12_E` は 12.15 を import できず (循環)、12.16 を S12_E 内で
in-place 証明できない。Thm 12.13 / Prop 12.15 と同じく **downstream leaf** 化が解。

Lane G の `S13_Lemma131` は S12_E の sorry'd `sigma_subgroup_pRank_normalizer_le_one` /
`sigma_subgroup_not_mem_primeFactors_derived_of_tau1` を cite 済み。本 leaf の証明完成後、
**HUB が merge 時に Lane G の cite を本 leaf (`S12.Cor1216.*`) へ re-point** する (de-axiom;
確立済パターン)。Lane F は lane 規約に従い S13 を編集しない。

## 証明スケッチ (BG L3458-3476)

`Y` solvable ⟹ 非自明 characteristic `q`-部分群 `X` (`q ∈ σ(M)`)。`q ∈ σ(M)` ゆえ `M_σ` は `G` の
Sylow `q` を含む ⟹ `X` を共役で `M_σ` へ (rank 不変ゆえ結論を transport)。
- `N_G(X) ⊆ M` の場合: `N_G(Y) ⊆ N_G(X) ⊆ M` ⟹ `(N_H(Y))' ⊆ M'`、direct。
- `N_G(X) ⊄ M` の場合: `M* ∈ ℳ(N_G(X))`。Prop 12.15(a)(e) で `M*` は `M` に非共役 + (12.3)。
  `K = M*_β`/`M*_σ` (`q ∈ σ(M*)`/`τ₂(M*)`)、Lem 10.12(a)+Cor 12.6(f) で `K` は `σ(M)'`-群、
  (12.4) `M* = (M ∩ M*)K`。`p ∉ β(G)` ゆえ `K` は `p'`-群。WLOG `H = M*`。
  - (a): rank-2 `A ∈ ℰ_p²(N_H(Y))` を仮定 → `K` が `p'` ゆえ `A` は `M ∩ H ⊆ M` に共役 →
    `A ∈ ℰ_p²(M)`、`p ∉ σ(M)` ゆえ `p ∈ τ₂(M)` → Thm 12.5(e) で `M_σ ∩ H = 1`、
    `1 ⊂ X ⊆ M_σ ∩ H` に矛盾。
  - (b): `p ∈ τ₁(M)` ⟹ `p ∉ π(M')`。`(M ∩ H)'K` は `H = (M ∩ H)K` の正規 `p'`-部分群で `H'` を含む
    ⟹ `p ∉ π(H')` ⟹ `p ∉ π(N_H(Y)')`。
-/

namespace OddOrder.BG.Ch3.S12.Cor1216

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Corollary 12.16(a)** (mmd L3453-3456): `r_p(N_H(Y)) ≤ 1`. 実証明版 (S12_E の forward-decl
`sigma_subgroup_pRank_normalizer_le_one` を置換; HUB が Lane G を re-point)。 -/
theorem pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  sorry

/-- **BG Corollary 12.16(b)** (mmd L3453, 3456): `p ∈ τ₁(M)` ⟹ `p ∉ π(N_H(Y)')`. 実証明版。 -/
theorem not_mem_primeFactors_derived_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors := by
  sorry

end OddOrder.BG.Ch3.S12.Cor1216
