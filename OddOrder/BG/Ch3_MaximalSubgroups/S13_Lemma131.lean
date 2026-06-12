/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E

/-!
# BG §13: Lemma 13.1 (異 maximal `M*` との `p`-相互作用)

**スコープ**: Bender–Glauberman §13, mmd `references/bg/local-analysis.mmd` L3528-3546。

`M* ∈ ℳ`, `p ∈ π(E)∩π(M*)`, `p ∉ τ₁(M*)`, `[M_σ∩M*, M∩M*] ≠ 1`, `M*` が `M` と非共役なら
(a) `M∩M*` の全 `p`-部分群が `M_σ∩M*` を中心化; (b) `p ∉ τ₂(M*)`; (c) `p ∈ τ₁(M)` なら `p ∈ β(G)`。

§13 は **Lemma 13.1 を根とする DAG** (Cor 13.2 が「follows directly from Lemma 13.1」、以降全結果が
13.2/13.4 経由)。本 leaf がその根。

## ⚠ Forward axioms: BG Corollary 12.16(a)(b) (issue 8000)

着工前 STATEMENT AUDIT (2026-06-12, Lane G session 1) で、Lemma 13.1 が要する **BG Cor 12.16(a)(b)**
(rank bound `r_p(N_H(Y)) ≤ 1` / π-bound `p∈τ₁(M) ⟹ p∉π(N_H(Y)')`) が repo に未露出と判明
(`S12_E.lean:64` `sigma_subgroup_conj_into_Msigma` は前置節「Y conj into M_σ」のみで誤ラベル)。

ユーザー裁可 (2026-06-12) のもと、両者を下記 **provisional forward axiom** として宣言し、その上で
§13 を実証明する。Lane F が S12_E 側に faithful な statement (drop-in 署名は issue 8000) を入れ次第、
本 axiom は de-axiom され、cite 先を S12_E へ差し替える。本 axiom を使う §13 定理は
`AxiomsCheck.lean` の `#assert_axioms_island … expecting [cor1216_…]` で pin する。

→ 詳細・解消パス: `issues/8000-s13-blocked-cor1216ab.md`,
  `notes/bg/s13_prime_action.md`「2026-06-12 Lane G session 1」。
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Forward axioms — BG Corollary 12.16(a)(b) (provisional; issue 8000) -/

/-- **[FORWARD AXIOM] BG Corollary 12.16(a)** (mmd L3453-3456): for a nonidentity `σ(M)`-subgroup
`Y` of `G`, a prime `p ∈ π(E) ∩ β(G)'`, and a maximal subgroup `H ∈ ℳ(Y)` not conjugate to `M`,
the `p`-rank of `N_H(Y) = H ⊓ N_G(Y)` is at most `1`.

**Provisional** (user-approved 2026-06-12, issue 8000): de-axiom when Lane F exposes the faithful
statement in `S12_E`. -/
axiom cor1216_pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1

/-- **[FORWARD AXIOM] BG Corollary 12.16(b)** (mmd L3453, 3456): same setting, and additionally
`p ∈ τ₁(M)`; then `p` does not divide `|N_H(Y)'|`, i.e. `p ∉ π(N_H(Y)')`.

**Provisional** (user-approved 2026-06-12, issue 8000): de-axiom when Lane F exposes the faithful
statement in `S12_E`. -/
axiom cor1216_not_mem_primeFactors_derived_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors

end OddOrder.BG.Ch3.S13
