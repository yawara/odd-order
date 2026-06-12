/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211

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

/-! ## `pRank` transfer helpers (reusable) -/

/-- `p`-rank is invariant under group isomorphism. -/
theorem pRank_eq_of_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {p : ℕ} (e : A ≃* B) : pRank A p = pRank B p :=
  le_antisymm (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

/-- If `N ≤ H` are subgroups whose orders have the same `p`-adic valuation (equivalently, `N`
contains a Sylow `p`-subgroup of `H`), then `pRank ↥H p ≤ pRank ↥N p`. A Sylow `p`-subgroup of
`N` then has order `p ^ v_p(|H|)`, so it is a Sylow `p`-subgroup of `H`, and `pRank` is realised
on Sylow subgroups (`pRank_sylow_eq`). Reusable. -/
theorem pRank_le_of_factorization_card_eq [Finite G] {p : ℕ} [Fact p.Prime]
    {N H : Subgroup G} (hNH : N ≤ H)
    (hfact : (Nat.card ↥H).factorization p = (Nat.card ↥N).factorization p) :
    pRank ↥H p ≤ pRank ↥N p := by
  classical
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥N) := inferInstance
  set Pn : Subgroup G := (Q : Subgroup ↥N).map N.subtype with hPndef
  have hPnN : Pn ≤ N := Subgroup.map_subtype_le _
  have hPnH : Pn ≤ H := hPnN.trans hNH
  have hPncard : Nat.card ↥Pn = p ^ (Nat.card ↥N).factorization p := by
    rw [hPndef, Subgroup.card_map_of_injective N.subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  have hPnHcard : Nat.card ↥(Pn.subgroupOf H) = p ^ (Nat.card ↥H).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPnH).toEquiv, hPncard, hfact]
  set S : Sylow p ↥H := Sylow.ofCard (Pn.subgroupOf H) hPnHcard with hSdef
  calc pRank ↥H p
      = pRank ↥(S : Subgroup ↥H) p := (pRank_sylow_eq S).symm
    _ = pRank ↥(Pn.subgroupOf H) p := by rw [hSdef, Sylow.coe_ofCard]
    _ = pRank ↥Pn p := pRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPnH)
    _ = pRank ↥(Pn.subgroupOf N) p :=
        (pRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPnN)).symm
    _ ≤ pRank ↥N p := pRank_mono_of_le (Pn.subgroupOf N)

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
    (fun _r hr => S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M hr)) ↥M))
    (S10.Msigma_le_derived hG hM)

/-- **Lemma 13.1, step 2** (mmd L3534): for `q ∉ β(M*)` dividing `|M*'|`, there is a Sylow
`q`-subgroup `Y` of `M*'` with the Frattini decomposition `M* = O_{β(M*)∪{q}}(M*') ⊔ N_{M*}(Y)`.
The `{β∪{q}}`-core `K := O_{β(M*)∪{q}}(M*')` is normal in `M*` (characteristic in `M*' ⊴ M*`) and a
`{β(M*)∪{q}}`-group, so `[M* : N_{M*}(Y)]` is prime to every `p ∉ β(M*) ∪ {q}` — the input that
places a Sylow `p` of `M*` inside `N_{M*}(Y)` in step 3. Adapts the Cor 10.9 Frattini machinery of
`S10_BetaRadical`. -/
theorem exists_sylow_frattini_decomp [Finite G] (hG : IsMinimalSimpleOdd G)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hqβ : q ∉ S10.beta Mstar) (hq_dvd : q ∣ Nat.card ↥(derivedInG Mstar)) :
    ∃ Y : Subgroup G, Y ≠ ⊥ ∧ IsPGroup q ↥Y ∧ Y ≤ derivedInG Mstar ∧
      Mstar = opiCoreInG (S10.beta Mstar ∪ {q}) (derivedInG Mstar) ⊔
        (Mstar ⊓ Subgroup.normalizer (Y : Set G)) := by
  classical
  set D := derivedInG Mstar with hDdef
  have hDM : D ≤ Mstar := Subgroup.map_subtype_le _
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥D) := inferInstance
  set Y : Subgroup G := (Q : Subgroup ↥D).map D.subtype with hYdef
  have hYD : Y ≤ D := Subgroup.map_subtype_le _
  have hYq : IsPGroup q ↥Y :=
    Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective)
  -- `|Y| = q ^ v_q(|D|)`: `Y` is a Sylow `q`-subgroup of `D`.
  have hYcard : Nat.card ↥Y = q ^ (Nat.card ↥D).factorization q := by
    rw [hYdef, Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  have hvpos : 0 < (Nat.card ↥D).factorization q :=
    (Fact.out : q.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hq_dvd
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hYcard
    have h1lt : 1 < q ^ (Nat.card ↥D).factorization q :=
      Nat.one_lt_pow hvpos.ne' (Fact.out : q.Prime).one_lt
    omega
  -- `M*_β ≤ D`, normal in `↥D`, and a `q′`-group.
  have hMβD : S10.Mbeta Mstar ≤ D := Mbeta_le_derived hG hMstar
  haveI hMβnorm : ((S10.Mbeta Mstar).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMβD).mpr
      (hDM.trans (le_normalizer_opiCoreInG (S10.beta Mstar) Mstar))
  have hNq' : ¬ q ∣ Nat.card ↥((S10.Mbeta Mstar).subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv]
    intro hdvd
    exact hqβ (isPiSubgroup_opiCoreInG (S10.beta Mstar) Mstar q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  -- `M*_β ⊔ Q ◁ D` (nilpotent quotient `D/M*_β`).
  haveI hMβQnorm : ((S10.Mbeta Mstar).subgroupOf D ⊔ (Q : Subgroup ↥D)).Normal :=
    S10.normal_sup_sylow_of_quotient_nilpotent
      (S10.derivedQuotientMbeta_isNilpotent hG hMstar) hNq' Q
  set K : Subgroup G := opiCoreInG (S10.beta Mstar ∪ {q}) D with hKdef
  have hKD : K ≤ D := Subgroup.map_subtype_le _
  set MβQ : Subgroup G := ((S10.Mbeta Mstar).subgroupOf D ⊔ (Q : Subgroup ↥D)).map D.subtype
    with hMβQdef
  have hMβQ_le_D : MβQ ≤ D := Subgroup.map_subtype_le _
  have hMβQ_pi : Subgroup.IsPiSubgroup (S10.beta Mstar ∪ {q}) MβQ := by
    intro r hr
    rw [hMβQdef, Subgroup.card_map_of_injective D.subtype_injective] at hr
    have hdvd : Nat.card ↥((S10.Mbeta Mstar).subgroupOf D ⊔ (Q : Subgroup ↥D)) ∣
        Nat.card ↥((S10.Mbeta Mstar).subgroupOf D) * Nat.card ↥(Q : Subgroup ↥D) := by
      have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
        ((S10.Mbeta Mstar).subgroupOf D) (Q : Subgroup ↥D)
      rw [show (↑((S10.Mbeta Mstar).subgroupOf D) * ↑(Q : Subgroup ↥D) : Set ↥D)
          = ↑((S10.Mbeta Mstar).subgroupOf D ⊔ (Q : Subgroup ↥D) : Subgroup ↥D) from
          (Subgroup.normal_mul ((S10.Mbeta Mstar).subgroupOf D) (Q : Subgroup ↥D)).symm] at hform
      exact ⟨_, hform.symm⟩
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    rcases (Nat.Prime.dvd_mul hr_prime).mp ((Nat.mem_primeFactors.mp hr).2.1.trans hdvd) with h | h
    · exact Or.inl (isPiSubgroup_opiCoreInG (S10.beta Mstar) Mstar r
        (Nat.mem_primeFactors.mpr ⟨hr_prime,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv) ▸ h, Nat.card_pos.ne'⟩))
    · refine Or.inr ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
      exact (Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow (hk ▸ h))
  have hMβQ_le_K : MβQ ≤ K := by
    refine le_opiCoreInG_of_normal_of_isPiSubgroup hMβQ_le_D ?_ hMβQ_pi
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
    exact hMβQnorm
  have hY_le_K : Y ≤ K :=
    le_trans (hYdef ▸ Subgroup.map_mono (le_sup_right : (Q : Subgroup ↥D) ≤ _))
      (hMβQdef ▸ hMβQ_le_K)
  -- `|K|_q = |D|_q`, so `Y` is a Sylow `q`-subgroup of `K`.
  have hKq_card : (Nat.card ↥K).factorization q = (Nat.card ↥D).factorization q := by
    refine le_antisymm
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hKD) q) ?_
    have hdvd : q ^ (Nat.card ↥D).factorization q ∣ Nat.card ↥K :=
      hYcard ▸ Subgroup.card_dvd_of_le hY_le_K
    exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
  haveI hKnorm : (K.subgroupOf Mstar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKD.trans hDM)).mpr
      (le_normalizer_opiCoreInG_of_le_normalizer (S10.beta Mstar ∪ {q})
        (S10.le_normalizer_derivedInG Mstar))
  -- **Frattini** in `↥M*`: `M* = K ⊔ N_{M*}(Y)`.
  have hYK_card : Nat.card ↥((Y.subgroupOf Mstar).subgroupOf (K.subgroupOf Mstar)) =
      q ^ (Nat.card ↥(K.subgroupOf Mstar)).factorization q := by
    have hYM : Y ≤ Mstar := hYD.trans hDM
    have hle : Y.subgroupOf Mstar ≤ K.subgroupOf Mstar := Subgroup.subgroupOf_mono Mstar hY_le_K
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKD.trans hDM)).toEquiv,
      hYcard, hKq_card]
  set P : Sylow q ↥(K.subgroupOf Mstar) :=
    Sylow.ofCard ((Y.subgroupOf Mstar).subgroupOf (K.subgroupOf Mstar)) hYK_card with hP
  have hPmap : (P : Subgroup ↥(K.subgroupOf Mstar)).map (K.subgroupOf Mstar).subtype =
      Y.subgroupOf Mstar := by
    rw [hP, Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Subgroup.subgroupOf_mono Mstar hY_le_K)]
  have hFrattini := Sylow.normalizer_sup_eq_top P
  rw [hPmap, ← Subgroup.subgroupOf_normalizer_eq (hYD.trans hDM)] at hFrattini
  -- transport `⊤ = N_{M*}(Y).subgroupOf M* ⊔ K.subgroupOf M*` to `M* = K ⊔ N_{M*}(Y)`.
  refine ⟨Y, hYne, hYq, hYD, ?_⟩
  have hmap := congrArg (Subgroup.map Mstar.subtype) hFrattini
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.mpr (hKD.trans hDM),
    inf_comm, sup_comm] at hmap
  exact hmap.symm

/-- **Lemma 13.1, step 3 = conclusion (b)** (mmd L3538): under the Lemma 13.1 hypotheses,
`p ∉ τ₂(M*)`. Assume `p ∈ τ₂(M*)`. Step 1 gives `q ∈ σ(M) ∩ π(M*')`; step 2 the Frattini
decomposition `M* = K ⊔ N_{M*}(Y)` with `K = O_{β(M*)∪{q}}(M*') ⊴ M*` and `Y` a Sylow `q` of
`M*'`. Since `p ∉ β(M*)` (`τ₂ ∩ σ = ∅ ⊇ β`) and `p ≠ q` (`p ∈ π(E)`, `q ∈ σ(M)`,
`π(E) ∩ σ(M) = ∅`), the `{β(M*)∪{q}}`-group `K` has order prime to `p`, so `[M* : N_{M*}(Y)]`
is prime to `p` and `r_p(N_{M*}(Y)) = r_p(M*) = 2`. But Lemma 12.1(g) gives `p ∉ β(G)`, so
Corollary 12.16(a) forces `r_p(N_{M*}(Y)) ≤ 1` — a contradiction. First use of the forward
axiom `cor1216_pRank_normalizer_le_one`. -/
theorem not_mem_tau2_of_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G)
    (hpE : p ∈ (Nat.card ↥E).primeFactors)
    (hcomm : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    p ∉ tau2 Mstar := by
  classical
  intro hpτ2
  -- step 1: a prime `q ∈ σ(M) ∩ π(M*')`.
  obtain ⟨q, hqp, hqσ, hqπ⟩ := exists_sigma_prime_dvd_derived_Mstar hcomm
  haveI : Fact q.Prime := ⟨hqp⟩
  -- conjugacy is symmetric (inlined `not_conj_symm`).
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  -- `q ∉ β(M*)` from `σ(M) ∩ α(M*) = ∅` (Lemma 10.12(a), swapped) + `β ⊆ α`.
  have hqα : q ∉ S10.alpha Mstar := fun ha =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG hMstar h.mem_maximal hnc').1.2) q ⟨ha, hqσ⟩
  have hqβ : q ∉ S10.beta Mstar := fun hb => hqα (S10.beta_subset_alpha Mstar hb)
  -- step 2: Frattini decomposition `M* = K ⊔ N`, `Y` a Sylow `q` of `M*'`.
  obtain ⟨Y, hYne, hYq, hYD, hdecomp⟩ :=
    exists_sylow_frattini_decomp hG hMstar hqβ (Nat.dvd_of_mem_primeFactors hqπ)
  have hDM : derivedInG Mstar ≤ Mstar := Subgroup.map_subtype_le _
  set K : Subgroup G := opiCoreInG (S10.beta Mstar ∪ {q}) (derivedInG Mstar) with hKdef
  set N : Subgroup G := Mstar ⊓ Subgroup.normalizer (Y : Set G) with hNdef
  have hKD : K ≤ derivedInG Mstar := Subgroup.map_subtype_le _
  have hKM : K ≤ Mstar := hKD.trans hDM
  have hNM : N ≤ Mstar := inf_le_left
  -- `K ⊴ M*` (characteristic in `M*' ⊴ M*`).
  haveI hKnorm : (K.subgroupOf Mstar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr
      (le_normalizer_opiCoreInG_of_le_normalizer (S10.beta Mstar ∪ {q})
        (S10.le_normalizer_derivedInG Mstar))
  -- `p ∤ |K|`: `p ∉ β(M*)` (`τ₂ ∩ σ = ∅ ⊇ β`) and `p ≠ q` (`π(E) ∩ σ(M) = ∅`).
  have hpσMstar : p ∉ S10.sigma Mstar := ((mem_tau2_iff Mstar p).mp hpτ2).1
  have hpβMstar : p ∉ S10.beta Mstar := fun hb =>
    hpσMstar (S10.alpha_subset_sigma hG hMstar (S10.beta_subset_alpha Mstar hb))
  have hpq : p ≠ q := fun he => (h.not_mem_sigma_of_mem_primeFactors hG hpE) (he ▸ hqσ)
  have hpK : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    have hmem : p ∈ (Nat.card ↥K).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    rcases isPiSubgroup_opiCoreInG (S10.beta Mstar ∪ {q}) (derivedInG Mstar) p hmem with hβ | hq'
    · exact hpβMstar hβ
    · exact hpq (Set.mem_singleton_iff.mp hq')
  -- product formula in `↥M*`: `|M*| · |K ⊓ N| = |K| · |N|`.
  have hsupTop : K.subgroupOf Mstar ⊔ N.subgroupOf Mstar = ⊤ := by
    apply Subgroup.map_injective Mstar.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKM, inf_eq_left.mpr hNM, ← hdecomp,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have eTop : Nat.card ↥(↑(K.subgroupOf Mstar) * ↑(N.subgroupOf Mstar) : Set ↥Mstar)
            = Nat.card ↥Mstar := by
    rw [(Subgroup.normal_mul (K.subgroupOf Mstar) (N.subgroupOf Mstar)).symm, hsupTop,
      SetLike.coe_sort_coe, Subgroup.card_top]
  have hcardId : Nat.card ↥Mstar * Nat.card ↥(K ⊓ N) = Nat.card ↥K * Nat.card ↥N := by
    have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
      (K.subgroupOf Mstar) (N.subgroupOf Mstar)
    have e2 : Nat.card ↥(K.subgroupOf Mstar) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e3 : Nat.card ↥(N.subgroupOf Mstar) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    have e4 : Nat.card ↥(K.subgroupOf Mstar ⊓ N.subgroupOf Mstar) = Nat.card ↥(K ⊓ N) := by
      have hinf : K.subgroupOf Mstar ⊓ N.subgroupOf Mstar = (K ⊓ N).subgroupOf Mstar :=
        (Subgroup.comap_inf K N Mstar.subtype).symm
      rw [hinf]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hKM)).toEquiv
    rw [eTop, e4, e2, e3] at hform
    exact hform
  -- `v_p(|M*|) = v_p(|N|)` (since `v_p(|K|) = v_p(|K ⊓ N|) = 0`).
  have hfact : (Nat.card ↥Mstar).factorization p = (Nat.card ↥N).factorization p := by
    have happ : (Nat.card ↥Mstar).factorization p + (Nat.card ↥(K ⊓ N)).factorization p
              = (Nat.card ↥K).factorization p + (Nat.card ↥N).factorization p := by
      have hcong := congrArg (fun n => n.factorization p) hcardId
      simpa only [Nat.factorization_mul (Nat.card_pos (α := ↥Mstar)).ne' Nat.card_pos.ne',
        Nat.factorization_mul (Nat.card_pos (α := ↥K)).ne' Nat.card_pos.ne',
        Finsupp.add_apply] using hcong
    have hfK0 : (Nat.card ↥K).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpK
    have hfKN0 : (Nat.card ↥(K ⊓ N)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hpK (hd.trans (Subgroup.card_dvd_of_le inf_le_left)))
    omega
  -- `2 ≤ r_p(N_{M*}(Y))`.
  have h2N : 2 ≤ pRank ↥N p := by
    have hr2 : pRank ↥Mstar p = 2 := tau2_pRank_eq_two hpτ2
    have hle := pRank_le_of_factorization_card_eq hNM hfact
    omega
  -- `p ∉ β(G)` (Lemma 12.1(g)).
  obtain ⟨A, hA, hAM⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 (Fact.out : p.Prime) hpτ2
  have hpβG : ¬ S10.idealPrime p G :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG hMstar (Fact.out : p.Prime) hpτ2 hAM hA).2
  -- Corollary 12.16(a): `r_p(N_{M*}(Y)) ≤ 1` (forward axiom).
  have hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y := by
    intro r hr
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYq
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hqp).mp
      (hr_prime.dvd_of_dvd_pow (hk ▸ Nat.dvd_of_mem_primeFactors hr))
    rw [hrq]; exact hqσ
  have hYM : Y ≤ Mstar := hYD.trans hDM
  have hHY : Mstar ∈ maximalSubgroupsContaining Y :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar, hYM⟩
  have hle1 := cor1216_pRank_normalizer_le_one hG h hYne hYpi hpE hpβG hHY hnc
  rw [← hNdef] at hle1
  omega

end OddOrder.BG.Ch3.S13
