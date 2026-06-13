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

/-- `2 ≤ pRank H q` (`q` prime) yields a rank-2 elementary abelian `A ∈ ℰ_q²(G)` with `A ≤ H`.
(Replicated from the private helper in `S12_Proposition1215`; the underlying PRank lemmas are
base-level.) -/
private theorem exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank [Finite G] {H : Subgroup G}
    {q : ℕ} (hq_prime : q.Prime) (hpr : 2 ≤ pRank ↥H q) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ H := by
  obtain ⟨B, hB_ea, hB_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥H) (p := q) (n := 2) two_pos hpr
  have hB_card : q ^ 2 ≤ Nat.card ↥B :=
    le_trans (Nat.pow_le_pow_right hq_prime.one_lt.le hB_log)
      (Nat.pow_log_le_self q Nat.card_pos.ne')
  obtain ⟨K, hK_ea, hK_card⟩ :=
    IsElementaryAbelian.exists_subgroup_card_prime_sq hq_prime hB_ea hB_card
  refine ⟨(K.map B.subtype).map H.subtype, mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩,
    Subgroup.map_subtype_le _⟩
  · exact Subgroup.IsElementaryAbelian.map H.subtype_injective
      (Subgroup.IsElementaryAbelian.map B.subtype_injective hK_ea)
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective B.subtype_injective]
    exact hK_card

/-- If `A ⊔ N = ⊤` with `N ⊴` and `r ∤ |N|`, then `r ∤ [⊤:A]`. (Replicated from S12_Proposition1215.) -/
private theorem not_dvd_index_of_sup_top_normal {K' : Type*} [Group K'] [Finite K'] {r : ℕ}
    {A N : Subgroup K'} [N.Normal] (htop : A ⊔ N = ⊤) (hrN : ¬ r ∣ Nat.card ↥N) :
    ¬ r ∣ A.index := by
  have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card A N
  rw [show (↑A * ↑N : Set K') = ↑(A ⊔ N : Subgroup K') from (Subgroup.mul_normal A N).symm] at hform
  have hsup_dvd : Nat.card ↥(A ⊔ N : Subgroup K') ∣ Nat.card ↥A * Nat.card ↥N := ⟨_, hform.symm⟩
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv] at hsup_dvd
  have hidx_dvd : A.index ∣ Nat.card ↥N := by
    have h2 : Nat.card ↥A * A.index ∣ Nat.card ↥A * Nat.card ↥N := by
      rw [A.card_mul_index]; exact hsup_dvd
    exact (Nat.mul_dvd_mul_iff_left (Nat.card_pos)).mp h2
  exact fun h => hrN (h.trans hidx_dvd)

/-- `pRank` is preserved by a subgroup of `r`-coprime index (`r` prime). (Replicated from
S12_Proposition1215.) -/
private theorem pRank_eq_of_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] {H K : Subgroup G} (hHK : H ≤ K)
    (hidx : ¬ r ∣ (H.subgroupOf K).index) : pRank ↥H r = pRank ↥K r := by
  obtain ⟨R⟩ : Nonempty (Sylow r ↥H) := inferInstance
  set Rincl : Subgroup ↥K := (R : Subgroup ↥H).map (Subgroup.inclusion hHK) with hRincl
  have hcardRincl : Nat.card ↥Rincl = r ^ (Nat.card ↥K).factorization r := by
    have hidxcard : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact (H.subgroupOf K).card_mul_index
    have hidx_ne : (H.subgroupOf K).index ≠ 0 := by
      intro h; rw [h, mul_zero] at hidxcard; exact (Nat.card_pos).ne' hidxcard.symm
    have hfact : (Nat.card ↥K).factorization r = (Nat.card ↥H).factorization r := by
      rw [← hidxcard, Nat.factorization_mul (Nat.card_pos).ne' hidx_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    rw [hRincl, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK),
      R.card_eq_multiplicity, hfact]
  have eR : ↥(R : Subgroup ↥H) ≃* ↥Rincl :=
    hRincl ▸ Subgroup.equivMapOfInjective _ (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hSylK : pRank ↥Rincl r = pRank ↥K r := by
    have h := pRank_sylow_eq (Sylow.ofCard Rincl hcardRincl)
    rwa [Sylow.coe_ofCard] at h
  rw [← pRank_sylow_eq R, ← hSylK]
  exact le_antisymm (pRank_le_of_injective (f := eR.toMonoidHom) eR.injective)
    (pRank_le_of_injective (f := eR.symm.toMonoidHom) eR.symm.injective)

/-- **Core of 12.16(a)** with the extra hypothesis `Y ⊆ M_σ` (the conjugated setup). If
`r_p(N_H(Y)) ≥ 2`, a rank-2 `A ∈ ℰ_p²(N_H(Y))` (after moving into `M`) makes `p ∈ τ₂(M)`, and
Thm 12.5(e) gives `M_σ ∩ H* = ⊥` for a maximal `H* ⊇ A` (`≠ M`) — but `1 ⊂ Y ⊆ M_σ ∩ H*`. -/
private theorem pRank_normalizer_le_one_core [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M) (hYMσ : Y ≤ S10.Msigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  have hM := h.mem_maximal
  have hHmax := mem_maximalSubgroupsContaining.mp hHY
  have hYH : Y ≤ H := hHmax.2
  have hHM : H ≠ M := fun he => hHnc ⟨1, by rw [map_one, one_smul]; exact he.symm⟩
  have hpσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hpE
  by_contra hge
  obtain ⟨A, hAea, hAN⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
    (Fact.out : p.Prime) (not_le.mp hge)
  have hAH : A ≤ H := hAN.trans inf_le_left
  have hANY : A ≤ Subgroup.normalizer (Y : Set G) := hAN.trans inf_le_right
  -- **Generic contradiction**: any rank-2 `B ≤ M` inside a maximal `H* ≠ M` with `Y ≤ H*` fails —
  -- `B` makes `p ∈ τ₂(M)` (`p ∉ σ(M)` so `p ∉ α(M)`, rank `≤ 2`; `B` gives rank `≥ 2`), then Thm
  -- 12.5(e) yields `M_σ ∩ H* = ⊥`, contradicting `1 ⊂ Y ⊆ M_σ ∩ H*`.
  have hcontra : ∀ (B : Subgroup G), B ∈ elemAbelianOfRank G p 2 → B ≤ M →
      ∀ (Hstar : Subgroup G), Hstar ∈ maximalSubgroupsContaining B → Hstar ≠ M → Y ≤ Hstar →
      False := by
    intro B hBea hBM Hstar hHstar hHstarM hYHstar
    have hpτ2 : p ∈ tau2 M := by
      refine ⟨hpσ, le_antisymm ?_ ?_⟩
      · by_contra h3
        have h3' : 3 ≤ pRank ↥M p := by omega
        exact hpσ (S10.alpha_subset_sigma hG hM ((S10.mem_alpha_iff M p).mpr
          ⟨OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (H := ↥M) (p := p) (by omega),
            h3'⟩))
      · have hBsubM : (B.subgroupOf M).IsElementaryAbelian p :=
          IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBM).symm
            (mem_elemAbelianOfRank.mp hBea).1
        have hle := le_pRank (B.subgroupOf M) hBsubM
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv,
          (mem_elemAbelianOfRank.mp hBea).2, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    exact hYne (le_bot_iff.mp
      ((Msigma_nilpotent_of_tau2 hG hM hpτ2 hBea hBM).2.2.2.2.1 Hstar hHstar hHstarM ▸
        le_inf hYMσ hYHstar))
  by_cases hNYM : Subgroup.normalizer (Y : Set G) ≤ M
  · -- **Case 1**: `N_G(Y) ⊆ M`, so `A ≤ N_H(Y) ⊆ M` directly; take `H* = H`, `B = A`.
    exact hcontra A hAea (hANY.trans hNYM) H
      (mem_maximalSubgroupsContaining.mpr ⟨hHmax.1, hAH⟩) hHM hYH
  · -- **Case 2** (BG L3466-3476): `N_G(Y) ⊄ M`. A maximal `M* ⊇ N_G(Y)` exists; `M* ≠ M`.
    have hYM_le : Y ≤ M := hYMσ.trans (S10.Msigma_le M)
    obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
      OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
        hG hM hYne hYM_le
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Y : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
    have hMstarne : Mstar ≠ M := fun he => hNYM (he ▸ hMstar_ge)
    have hYMstar : Y ≤ Mstar := Subgroup.le_normalizer.trans hMstar_ge
    have hYMM : Y ≤ M ⊓ Mstar := le_inf hYM_le hYMstar
    -- Build `S = Syl_q(M ∩ M*) ⊇ Y` (extend `Y` to a Sylow `q` of `↥(M ∩ M*)`, map to `G`).
    have hYsub_pg : IsPGroup q ↥(Y.subgroupOf (M ⊓ Mstar)) :=
      hYq.of_equiv (Subgroup.subgroupOfEquivOfLe hYMM).symm
    obtain ⟨Psub, hPsub⟩ := hYsub_pg.exists_le_sylow
    set S : Subgroup G := (Psub : Subgroup ↥(M ⊓ Mstar)).map (M ⊓ Mstar).subtype with hSdef
    have hSle : S ≤ M ⊓ Mstar := Subgroup.map_subtype_le _
    have hSq : IsPGroup q ↥S :=
      Psub.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M ⊓ Mstar).subtype_injective)
    have hYS : Y ≤ S := by
      rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hYMM]; exact Subgroup.map_mono hPsub
    have hPsubeq : S.subgroupOf (M ⊓ Mstar) = Psub := by
      rw [hSdef]; exact Subgroup.comap_map_eq_self_of_injective (M ⊓ Mstar).subtype_injective _
    have hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T := by
      intro T hTle hTq hST
      have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M ⊓ Mstar)) :=
        hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
      have hTeq := Psub.3 hTsub_pg (by rw [← hPsubeq]; exact Subgroup.comap_mono hST)
      rw [hSdef, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
    -- Prop 12.15: `M*` not conjugate to `M`, plus the `(M ∩ M*)`-factorization (d)/(e).
    have h1215 := sigma_subgroup_maximal_interaction hG hM hqσ hYM_le hYne hYq hMstarMem hMstarne
      hSle hYS hSq hSmax
    -- `M* = (M ∩ M*)K` with `K = M*_β` (if `q ∈ σ(M*)`) or `K = M*_σ` (if `q ∉ σ(M*)`), `K ⊴ M*`,
    -- and `K` a `p'`-group: `M*_β`-primes ⊆ `β(M*)` and `p ∉ β(M*)` (`¬idealPrime p`); for `M*_σ`,
    -- `p ∈ π(M) ∩ σ(M*) ⊆ β(M*)` by (12.3), contradiction.
    obtain ⟨K, hKnorm, hMstarFact, hpK⟩ :
        ∃ K : Subgroup G, (K.subgroupOf Mstar).Normal ∧ Mstar = (M ⊓ Mstar) ⊔ K ∧
          ¬ p ∣ Nat.card ↥K := by
      by_cases hqσMstar : q ∈ S10.sigma Mstar
      · refine ⟨S10.Mbeta Mstar, by rw [S10.Mbeta_subgroupOf]; infer_instance,
          (h1215.2.2.2.1 hqσMstar).1, fun hdvd => hpβ ?_⟩
        exact ((S10.mem_beta_iff Mstar p).mp (S10.Mbeta_isPiGroup Mstar p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))).2
      · refine ⟨S10.Msigma Mstar, by rw [S10.Msigma_subgroupOf]; infer_instance, ?_,
          fun hdvd => hpβ ?_⟩
        · rw [sup_comm]; exact (h1215.2.2.2.2 hqσMstar).2.2.2.symm
        · have hp_πM : p ∈ (Nat.card ↥M).primeFactors :=
            Nat.primeFactors_mono (Subgroup.card_dvd_of_le h.E_le) Nat.card_pos.ne' hpE
          have hp_σMstar : p ∈ S10.sigma Mstar := S10.Msigma_isPiGroup Mstar p
            (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
          exact ((S10.mem_beta_iff Mstar p).mp ((h1215.2.2.2.2 hqσMstar).2.1 p hp_πM hp_σMstar)).2
    -- `[M* : M ∩ M*] ∣ |K|` is `p'`, so `pRank(M ∩ M*) p = pRank(M*) p ≥ 2` (`A ≤ M*` rank-2); thus
    -- `M ∩ M*` contains a rank-2 `B ∈ ℰ_p²`, and `hcontra B … M*` (with `M* ≠ M`, `Y ≤ M*`) closes.
    have hKle : K ≤ Mstar := hMstarFact ▸ le_sup_right
    have hidx : ¬ p ∣ ((M ⊓ Mstar).subgroupOf Mstar).index := by
      haveI := hKnorm
      have htop : (M ⊓ Mstar).subgroupOf Mstar ⊔ K.subgroupOf Mstar = ⊤ := by
        rw [← Subgroup.subgroupOf_sup inf_le_right hKle, ← hMstarFact, Subgroup.subgroupOf_self]
      exact not_dvd_index_of_sup_top_normal htop
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]; exact hpK)
    have hAMstar : A ≤ Mstar := hANY.trans hMstar_ge
    have hpRankMstar : 2 ≤ pRank ↥Mstar p := by
      have hAsubMstar : (A.subgroupOf Mstar).IsElementaryAbelian p :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAMstar).symm
          (mem_elemAbelianOfRank.mp hAea).1
      have hle := le_pRank (A.subgroupOf Mstar) hAsubMstar
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMstar).toEquiv,
        (mem_elemAbelianOfRank.mp hAea).2, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    have hpRankMM : 2 ≤ pRank ↥(M ⊓ Mstar) p := by
      rw [pRank_eq_of_le_of_not_dvd_index inf_le_right hidx]; exact hpRankMstar
    obtain ⟨B, hBea, hBMM⟩ :=
      exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank (Fact.out : p.Prime) hpRankMM
    exact hcontra B hBea (hBMM.trans inf_le_left) Mstar
      (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hBMM.trans inf_le_right⟩)
      hMstarne (Subgroup.le_normalizer.trans hMstar_ge)

/-- **BG Corollary 12.16(a)** (mmd L3453-3456), **`q`-group specialization**: for a nonidentity
`q`-group `Y` with `q ∈ σ(M)`, `r_p(N_H(Y)) ≤ 1`. This is what Lane G needs (S13_Lemma131 supplies
`Y` as a `q`-group via `IsPGroup q Y`); the general `σ(M)`-subgroup form of S12_E's forward-decl
`sigma_subgroup_pRank_normalizer_le_one` reduces to this via a characteristic `q`-subgroup `X ⊆ Y`
(deferred wrapper). HUB が Lane G の cite を本 lemma へ re-point (G は `hYq`/`hqσ` を保持)。 -/
theorem pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  -- **Step 1 — conjugate `Y` into `M_σ`**: `Y` is a `q`-group, `q ∈ σ(M)`, and `M_σ` contains a
  -- Sylow `q` of `G` (BG 10.2), so `Y` is `G`-conjugate into `M_σ`.
  obtain ⟨g, hgY⟩ : ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
    obtain ⟨_, P, _⟩ := (S10.mem_sigma_iff M q).mp hqσ
    obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
    have hPpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
      intro s hs
      have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
        (Nat.mem_primeFactors.mp hs).2.1
      rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
      obtain ⟨n, hn⟩ := (P.2).exists_card_eq
      rw [hn] at hs_dvd
      rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) Fact.out).mp
        ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hs_dvd)]
    have hPMσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
      S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG h.mem_maximal)
        (Subgroup.map_subtype_le _) hPpi
    obtain ⟨Q, hYQ⟩ := hYq.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG Q
    refine ⟨g⁻¹, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
    have hQconj : MulAut.conj g⁻¹ • (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
      have hQ : (Q : Subgroup G) = MulAut.conj g • (SG : Subgroup G) := by
        rw [← hg]; exact Sylow.coe_subgroup_smul
      rw [hQ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hSG]
    rw [hQconj]; exact hPMσ
  -- **Step 2** (TODO, BG L3466-3476): reduce to the conjugated setup `Y' = Y^g ⊆ M_σ` (rank is
  -- conjugation-invariant); apply Prop 12.15 to get `M* = (M ∩ M*)K`, `K` a `p'`-group; a rank-2
  -- `A ∈ ℰ_p²(N_{M*}(Y'))` lands in `M`, so `p ∈ τ₂(M)`, and Thm 12.5(e) gives `M_σ ∩ M* = ⊥`,
  -- contradicting `1 ⊂ Y' ⊆ M_σ ∩ M*`.
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
