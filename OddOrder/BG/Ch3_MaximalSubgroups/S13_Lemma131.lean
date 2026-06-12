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

/-! ## Lemma 13.1 — structural steps (mmd L3534-3546) -/

/-- `⁅M_σ, M⁆ ≤ M_σ`: the radical `M_σ` is normal in `M`. (Reusable; via the normality of
`(M_σ).subgroupOf M` inside `↥M`.) -/
theorem Msigma_commutator_M_le (M : Subgroup G) :
    ⁅S10.Msigma M, M⁆ ≤ S10.Msigma M := by
  classical
  haveI : ((S10.Msigma M).subgroupOf M).Normal := by rw [S10.Msigma_subgroupOf]; infer_instance
  have h1 : ⁅(S10.Msigma M).subgroupOf M, (⊤ : Subgroup ↥M)⁆ ≤ (S10.Msigma M).subgroupOf M :=
    Subgroup.commutator_le_left _ _
  have h2 := Subgroup.map_mono (f := M.subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (S10.Msigma_le M),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

/-- **Lemma 13.1, step 1** (mmd L3534): from `⁅M_σ∩M*, M∩M*⁆ ≠ 1`, the commutator lies in
`M_σ ⊓ M*'`, so there is a prime `q ∈ σ(M)` dividing `|M*'|`. -/
theorem exists_sigma_prime_dvd_derived_Mstar [Finite G] {M Mstar : Subgroup G}
    (hcomm : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ q ∈ S10.sigma M ∧
      q ∈ (Nat.card ↥(derivedInG Mstar)).primeFactors := by
  classical
  have hMsig : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≤ S10.Msigma M :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans (Msigma_commutator_M_le M)
  have hderiv : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≤ derivedInG Mstar := by
    have hmono := Subgroup.commutator_mono (H₁ := S10.Msigma M ⊓ Mstar) (H₂ := M ⊓ Mstar)
      (K₁ := Mstar) (K₂ := Mstar) inf_le_right inf_le_right
    rwa [show ⁅Mstar, Mstar⁆ = derivedInG Mstar from (Subgroup.map_subtype_commutator Mstar).symm]
      at hmono
  have hne : S10.Msigma M ⊓ derivedInG Mstar ≠ ⊥ := fun hbot =>
    hcomm (le_bot_iff.mp ((le_inf hMsig hderiv).trans hbot.le))
  have hcardne : Nat.card ↥(S10.Msigma M ⊓ derivedInG Mstar) ≠ 1 := by
    have hnt : Nontrivial ↥(S10.Msigma M ⊓ derivedInG Mstar) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hcardne
  have hcardpos : ∀ K : Subgroup G, Nat.card ↥K ≠ 0 := fun K => Nat.card_pos.ne'
  refine ⟨q, hqp, ?_, ?_⟩
  · refine S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr ⟨hqp, ?_, hcardpos _⟩)
    exact hqdvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  · exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd.trans (Subgroup.card_dvd_of_le inf_le_right),
      hcardpos _⟩

/-- `M_β ≤ M'` (= `derivedInG M`): via `M_β ≤ M_σ ≤ M'` (`β(M) ⊆ σ(M)` + `Msigma_le_derived`).
Reusable; mirrors the `hMβD` step inside `S10.derivedQuotientMbeta_isNilpotent`. -/
theorem Mbeta_le_derived [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) : S10.Mbeta M ≤ derivedInG M :=
  le_trans (Subgroup.map_mono (Ch03.oPiCore_mono
    (fun r hr => S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M hr)) ↥M))
    (S10.Msigma_le_derived hG hM)

end OddOrder.BG.Ch3.S13
