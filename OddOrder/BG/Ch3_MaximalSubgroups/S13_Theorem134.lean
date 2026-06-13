/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Corollary132
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1218

/-!
# BG §13: Theorem 13.4 (the main step — `C_{M_σ}(P) ⊆ C_{M_σ}(R)`)

**スコープ**: Bender–Glauberman §13, mmd `references/bg/local-analysis.mmd` L3576-3597.

`p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `r ∈ π(E)`, `R ∈ ℰ_r¹(C_E(P))` なら `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。
prime action 解析の中心。

**証明梗概** (mmd L3580-3597; 詳細プラン = `notes/bg/s13_prime_action.md`「Thm 13.4 着手」):
- **outer**: `C_{M_σ}(P)` は σ(M)-群ゆえ、各 `q ∈ σ(M)` の `PR`-不変 Sylow `q` `S` で生成
  (`PR = P × R` abelian, `R ≤ C_E(P)`)。各 `S` を `R` が中心化すれば `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。
- **per-q (核)**: `S` = `PR`-不変 Sylow `q` of `C_{M_σ}(P)`、`[S,R]=1` を示す。`Q := [S,R] ≠ 1` と仮定:
  1. `M* ∈ ℳ(N_G(P))`。`1 ⊂ Q = [S,R] ⊆ [M_σ ∩ M*, R]` ⟹ Cor 13.2 で `p ∈ β(M*)`, `r ∈ τ₁(M*)`。
  2. `1 ⊂ P ⊆ C_{M_α(M*)}(RQ)`、`S = C_S(R) × Q` (`S` abelian by Thm 12.13)。
  3. Lem 12.18(a) (`tau1_Malpha_interaction`) を `(r,R,M*) ↦ (p,P,M)` で適用 →
     `C_{M_α}(P) = C_{M_α}(R)` (両包含; `r ∈ τ₁(M)` で逆向き)。
  4. `S ⊆ C_M(P)` ゆえ `C_{M_α}(P)=C_{M_α}(R)` を正規化 → `Q=[S,R]` で中心化 → `C_{M_α}(R)=C_{M_α}(RQ)`。
  5. `ℳ(N_G(Q)) ≠ {M}` ⟹ Lem 12.18(a) が `C_{M_α}(R) ≠ C_{M_α}(RQ)` → 矛盾。

**🚧 WIP** (2026-06-13, Lane G loop): leaf scaffold。proof は `sorry` (scaffold stub は
`S13_PrimeAction.centralizer_le_centralizer_of_tau1` のまま; 本 leaf は完成時に差し替え予定)。
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Thm 13.4 per-q core** (mmd L3576-3597): for a `(P ⊔ R)`-invariant `q`-subgroup `S` of
`C_{M_σ}(P)`, `R` centralizes `S` (i.e. `⁅S, R⁆ = ⊥`). Assume `Q := ⁅S, R⁆ ≠ ⊥`; then via
Cor 13.2(b)(c) `r ∈ τ₁(M*)` and `p ∈ β(M*)` for `M* ∈ ℳ(N_G(P))`, and Prop 12.15 / Lemma 12.18
yield `C_{M_α}(P) = C_{M_α}(R) = C_{M_α}(RQ)` against `ℳ(N_G(Q)) ≠ {M}` — contradiction.
**🚧 WIP**: setup + Cor 13.2 steps + step 4 (`S` abelian, FPF) + **step 5** (`ℳ(N_G(Q)) = {M*}`
via Lemma 12.18(a) role-swap); steps 6-9 (Prop 12.15 / Lemma 12.18 contradiction) `sorry`. -/
theorem per_q_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hp : p ∈ tau1 M) (hr : r ∈ (Nat.card ↥E).primeFactors)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRC : R ≤ E ⊓ Subgroup.centralizer (P : Set G))
    {q : ℕ} (hq : q.Prime) {S : Subgroup G}
    (hSN : S ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)) (hSpg : IsPGroup q ↥S)
    (hSinv : (P ⊔ R) ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.centralizer (R : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hQne
  -- `P`, `R` basics.
  obtain ⟨hPea, hPcard⟩ := mem_elemAbelianOfRank.mp hP
  obtain ⟨hRea, hRcard⟩ := mem_elemAbelianOfRank.mp hR
  have hPM : P ≤ M := hPE.trans h.E_le
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot, pow_one] at hPcard
    exact (Fact.out : p.Prime).ne_one hPcard.symm
  have hRr : IsPGroup r ↥R := hRea.isPGroup
  have hRne : R ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot, pow_one] at hRcard
    exact (Fact.out : r.Prime).ne_one hRcard.symm
  have hRE : R ≤ E := hRC.trans inf_le_left
  have hRCP : R ≤ Subgroup.centralizer (P : Set G) := hRC.trans inf_le_right
  -- `M* ∈ ℳ(N_G(P))`: `N_G(P) ≠ ⊤` (else `P ⊴ G`), so a coatom lies above it.
  have hNPne : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    haveI : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal P inferInstance with hb | ht
    · exact hPne hb
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hPM))
  obtain ⟨Mstar, hMstarCo, hNP⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (P : Set G))).resolve_left hNPne
  have hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNP⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  have hPMstar : P ≤ Mstar := Subgroup.le_normalizer.trans hNP
  have hRMstar : R ≤ Mstar := hRCP.trans ((Subgroup.centralizer_le_normalizer _).trans hNP)
  have hSMsig : S ≤ S10.Msigma M := hSN.trans inf_le_left
  have hSMstar : S ≤ Mstar :=
    (hSN.trans inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans hNP)
  have hSMsigMstar : S ≤ S10.Msigma M ⊓ Mstar := le_inf hSMsig hSMstar
  -- `⁅S, R⁆ ⊆ ⁅M_σ ⊓ M*, R⁆ ⊆ ⁅M_σ ⊓ M*, M ⊓ M*⁆`.
  have hRMMstar : R ≤ M ⊓ Mstar := le_inf (hRE.trans h.E_le) hRMstar
  have hQsub : ⁅S, R⁆ ≤ ⁅S10.Msigma M ⊓ Mstar, R⁆ :=
    Subgroup.commutator_mono hSMsigMstar le_rfl
  -- Cor 13.2 for `p ∈ τ₁(M)`, `P`, `M*`.
  have hcor132 := tau13_pSubgroup_centralizes hG h (Or.inl hp) hPM hPne hPp hMstar
  -- step 2: `r ∈ τ₁(M*)` (else Cor 13.2(b) makes `R` centralize `M_σ ⊓ M*`, killing `⁅S,R⁆`).
  have hrτ1 : r ∈ tau1 Mstar := by
    by_contra hrnot
    have hRpi : Subgroup.IsPiSubgroup (tau1 Mstar)ᶜ R := by
      intro s hs
      have hsr : s = r := by
        have hsd := (Nat.mem_primeFactors.mp hs).2.1
        rw [hRcard, pow_one] at hsd
        exact (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hs).1 (Fact.out : r.Prime)).mp hsd
      rw [hsr]; exact hrnot
    have hRcent := hcor132.2.1 R (le_inf hRE hRMstar) hRpi
    have hcomm0 : ⁅S10.Msigma M ⊓ Mstar, R⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcent
    exact hQne (le_bot_iff.mp (hQsub.trans hcomm0.le))
  -- step 3: `p ∈ β(M*)`.
  have hint : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := fun hb =>
    hQne (le_bot_iff.mp (hQsub.trans (Subgroup.commutator_mono le_rfl hRMMstar |>.trans hb.le)))
  have hpβ : p ∈ S10.beta Mstar := (hcor132.2.2 hint).2 hp
  -- `M* ≠ M` (else `M*` is conjugate to `M` via `g = 1`).
  have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar :=
    not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal (Or.inl hp) hPM hPne hPp hNP
  have hMstarNe : Mstar ≠ M := fun heq => hnc ⟨1, by rw [map_one, one_smul]; exact heq.symm⟩
  -- step 4a: `S` is abelian (Theorem 12.13: a nonabelian `q`-subgroup would be uniquely maximal,
  -- contradicting `S ≤ M` and `S ≤ M*` with `M ≠ M*`).
  have hSab : IsMulCommutative ↥S := by
    by_contra hnab
    exact hMstarNe ((nonabelian_pgroup_isUniquelyMaximal hG hSpg hnab).eq_of_isCoatom_of_le
      (mem_maximalSubgroups.mp h.mem_maximal) (hSMsig.trans (S10.Msigma_le M))
      hMstarCo hSMstar).symm
  -- step 4b: `C_⁅S,R⁆(R) = 1` (coprime FPF on the abelian `S`).
  have hSne : S ≠ ⊥ := fun hb => hQne (by rw [hb, Subgroup.commutator_bot_left])
  have hqσ : q ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M q (mem_primeFactors_of_isPGroup_le hq hSMsig hSne hSpg)
  have hrq : r ≠ q := fun heq =>
    h.not_mem_sigma_of_mem_primeFactors hG hr (heq.symm ▸ hqσ)
  have hcop_SR : Nat.Coprime (Nat.card ↥R) (Nat.card ↥S) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne'
      (fun s hs => h.isPiGroup_sigma_compl hG s (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hs).1,
          (Nat.mem_primeFactors.mp hs).2.1.trans (Subgroup.card_dvd_of_le hRE), Nat.card_pos.ne'⟩))
      (fun s hs hsc => hsc (S10.Msigma_isPiGroup M s (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hs).1,
          (Nat.mem_primeFactors.mp hs).2.1.trans (Subgroup.card_dvd_of_le hSMsig), Nat.card_pos.ne'⟩)))
  have hRS_norm : R ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hSinv
  have hCQR : ⁅S, R⁆ ⊓ Subgroup.centralizer (R : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot_of_isCommutative
      (fun a ha b hb => congrArg Subtype.val (hSab.is_comm.comm (⟨a, ha⟩ : ↥S) ⟨b, hb⟩))
      hRS_norm hcop_SR
  -- ===== structural facts for `Q := ⁅S, R⁆` (step 5 prep) =====
  -- `Q ≤ S` (`R` normalizes `S`), so `Q` is a `q`-group and `Q ≤ M*`.
  have hQS : ⁅S, R⁆ ≤ S := Ch04.commutator_le_of_le_normalizer hRS_norm
  have hQq : IsPGroup q ↥(⁅S, R⁆ : Subgroup G) := hSpg.to_le hQS
  have hQMstar : (⁅S, R⁆ : Subgroup G) ≤ Mstar := hQS.trans hSMstar
  -- `R` normalizes `Q` since `⁅Q, R⁆ ≤ ⁅S, R⁆ = Q`.
  have hRNQ : R ≤ Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G) :=
    Ch04.le_normalizer_of_commutator_le (Subgroup.commutator_mono hQS le_rfl)
  -- `P` centralizes `R ⊔ Q` (both `R ≤ C(P)` and `Q ≤ S ≤ C(P)`, then symmetry).
  have hSCP : S ≤ Subgroup.centralizer (P : Set G) := hSN.trans inf_le_right
  have hPcRQ : P ≤ Subgroup.centralizer ((R ⊔ ⁅S, R⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hRCP (hQS.trans hSCP))
  -- `q ∉ α(M*)`: Lemma 10.12(a) gives `σ(M) ∩ α(M*) = ∅` as `M*` is not conjugate to `M`.
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hqαstar : q ∉ S10.alpha Mstar := fun ha =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG hMstarMax h.mem_maximal hnc').1.2) q ⟨ha, hqσ⟩
  -- `p ∈ α(M*)` (from `p ∈ β(M*)`): `P ≤ M*_α`, hence `M*_α ≠ ⊥`.
  have hpαstar : p ∈ S10.alpha Mstar := S10.beta_subset_alpha Mstar hpβ
  have hPα : Ch03.Subgroup.IsPiGroup (S10.alpha Mstar) P := by
    intro s hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hpαstar
  have hPMα : P ≤ S10.Malpha Mstar :=
    S10.alpha_subgroup_le_Malpha_of_isHall (S10.Malpha_isHall hG hMstarMax) hPMstar hPα
  have hMαstar_ne : S10.Malpha Mstar ≠ ⊥ := fun hb => hPne (le_bot_iff.mp (hb ▸ hPMα))
  -- ===== step 5: `ℳ(N_G(Q)) = {M*}` (Lemma 12.18(a) with `(r, R, M*)` for `(p, P, M)`) =====
  -- If `ℳ(N_G(Q)) ≠ {M*}`, Lemma 12.18(a) forces `M*_α ⊓ C(R ⊔ Q) = ⊥`; but `1 ⊂ P` lies there.
  have hMNQstar :
      maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G)) = {Mstar} := by
    by_contra hne
    obtain ⟨_, hCRQ⟩ :=
      (tau1_Malpha_interaction hG hMstarMax hrq.symm hrτ1 hR hRMstar hQMstar hQne hQq hRNQ hCQR
        hne).1 hMαstar_ne hqαstar
    exact hPne (le_bot_iff.mp (hCRQ ▸ le_inf hPMα hPcRQ))
  -- steps 6-9: Prop 12.15 (`X = Q`) → `q ∈ σ(M*)`; `C_{M_α}(P) = C_{M_α}(R) = C_{M_α}(RQ)`;
  -- Lemma 12.18(a) (on `M`) contradiction since `ℳ(N_G(Q)) ≠ {M}`. 🚧
  sorry

/-- **BG Theorem 13.4** (mmd L3576): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `r ∈ π(E)`, `R ∈ ℰ_r¹(C_E(P))`
なら `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。outer reduction `msigma_centralizer_le_of_invariant_sylow_centralized`
(完全証明) + per-q core `per_q_centralizes`。後者の steps 4-9 (Lemma 12.18/Prop 12.15 入れ子
contradiction) は §12 の sorry'd scaffold に bottom-out する scaffold sorry (plan = notes)。 -/
theorem centralizer_le_centralizer_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hp : p ∈ tau1 M) (hr : r ∈ (Nat.card ↥E).primeFactors)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRC : R ≤ E ⊓ Subgroup.centralizer (P : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (R : Set G) :=
  msigma_centralizer_le_of_invariant_sylow_centralized hG h hPE hRC
    (fun q hq S hSN hSpg hSinv => per_q_centralizes hG h hp hr hP hPE hR hRC hq hSN hSpg hSinv)

end OddOrder.BG.Ch3.S13
