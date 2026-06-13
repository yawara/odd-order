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

/-- Extend a `q`-subgroup `Q ≤ H` to a maximal `q`-subgroup `S` of `H` (a Sylow `q` of `↥H`,
pulled back to `G`). Supplies the `S` and Sylow-maximality hypotheses of Proposition 12.15. -/
theorem exists_maximal_pSubgroup_le_of_le {q : ℕ} [Fact q.Prime] [Finite G]
    {Q H : Subgroup G} (hQH : Q ≤ H) (hQq : IsPGroup q ↥Q) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup q ↥S ∧ Q ≤ S ∧
      ∀ T : Subgroup G, T ≤ H → IsPGroup q ↥T → S ≤ T → S = T := by
  -- `Q.subgroupOf H` is a `q`-group inside `↥H`; extend to a Sylow `P` of `↥H`.
  have hpg : IsPGroup q ↥(Q.subgroupOf H) := by
    obtain ⟨n, hn⟩ := hQq.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]; exact hn)
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  refine ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hQH]; exact Subgroup.map_mono hP
  · intro T hTH hTq hST
    have hTHpg : IsPGroup q ↥(T.subgroupOf H) := by
      obtain ⟨n, hn⟩ := hTq.exists_card_eq
      exact IsPGroup.of_card
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]; exact hn)
    have hPT : (P : Subgroup ↥H) ≤ T.subgroupOf H := Subgroup.map_le_iff_le_comap.mp hST
    have e : (P : Subgroup ↥H) = T.subgroupOf H := by
      have hm := P.is_maximal' hTHpg hPT
      first | exact hm | exact hm.symm
    rw [e]
    exact Subgroup.map_subgroupOf_eq_of_le hTH

/-- **Thm 13.4 per-q core** (mmd L3576-3597): for a `(P ⊔ R)`-invariant `q`-subgroup `S` of
`C_{M_σ}(P)`, `R` centralizes `S` (i.e. `⁅S, R⁆ = ⊥`). Assume `Q := ⁅S, R⁆ ≠ ⊥`; then via
Cor 13.2(b)(c) `r ∈ τ₁(M*)` and `p ∈ β(M*)` for `M* ∈ ℳ(N_G(P))`, and Prop 12.15 / Lemma 12.18
yield `C_{M_α}(P) = C_{M_α}(R) = C_{M_α}(RQ)` against `ℳ(N_G(Q)) ≠ {M}` — contradiction.
**🚧 WIP**: steps 1-6 + **steps 8-9** (three-subgroups + Lemma 12.18(a) on `(r,R,q,Q)` contradiction)
all proven; the whole 9-step contradiction now reduces to the **single equality** `C_{M_α}(P) = C_{M_α}(R)`
(step 7, the rank-≤1 / cyclic argument that BG elides) which is the sole remaining `sorry`. -/
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
  -- ===== step 6: Prop 12.15 (`X = Q`) → `q ∈ σ(M*)`, `τ₁(M*) ⊆ τ₁(M) ∪ α(M)`, `M_α ≠ ⊥` =====
  have hQM : (⁅S, R⁆ : Subgroup G) ≤ M := hQS.trans (hSMsig.trans (S10.Msigma_le M))
  obtain ⟨S', hS'le, hS'q, hQS', hS'max⟩ :=
    exists_maximal_pSubgroup_le_of_le (le_inf hQM hQMstar) hQq
  have hMstarMem :
      Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G)) := by
    rw [hMNQstar]; rfl
  have hprop := sigma_subgroup_maximal_interaction hG h.mem_maximal hqσ hQM hQne hQq
    hMstarMem hMstarNe hS'le hQS' hS'q hS'max
  -- `P ≤ M*_σ` (since `p ∈ β(M*) ⊆ σ(M*)`), used to exclude case (e).
  have hpσstar : p ∈ S10.sigma Mstar := S10.alpha_subset_sigma hG hMstarMax hpαstar
  have hPσ : Ch03.Subgroup.IsPiGroup (S10.sigma Mstar) P := by
    intro s hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hpσstar
  have hPMσstar : P ≤ S10.Msigma Mstar :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMstarMax) hPMstar hPσ
  -- case (e) `q ∉ σ(M*)` is impossible: `1 ⊂ P ⊆ M*_σ ⊓ (M ⊓ M*) = ⊥`.
  have hqσstar : q ∈ S10.sigma Mstar := by
    by_contra hqns
    have he := hprop.2.2.2.2 hqns
    have hPbot : P ≤ S10.Msigma Mstar ⊓ (M ⊓ Mstar) := le_inf hPMσstar (le_inf hPM hPMstar)
    rw [he.2.2.1] at hPbot
    exact hPne (le_bot_iff.mp hPbot)
  -- Prop 12.15(d): `τ₁(M*) ⊆ τ₁(M) ∪ α(M)` and `M_α ≠ ⊥`.
  obtain ⟨_, hτ1sub, _, hMαne⟩ := hprop.2.2.2.1 hqσstar
  -- `q ∉ α(M)`: Lemma 10.12(a) gives `α(M) ∩ σ(M*) = ∅` and `q ∈ σ(M*)`.
  have hqαM : q ∉ S10.alpha M := fun ha =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG h.mem_maximal hMstarMax hnc).1.2) q ⟨ha, hqσstar⟩
  -- ===== steps 7-9: `C_{M_α}(P) = C_{M_α}(R)` → three-subgroups → Lemma 12.18(a) contradiction =====
  -- `r ∈ τ₁(M)`: `τ₁(M*) ⊆ τ₁(M) ∪ α(M)`, `r ∈ π(E) ⟹ r ∉ σ(M) ⊇ α(M)`.
  have hrτ1M : r ∈ tau1 M := by
    rcases hτ1sub hrτ1 with h1 | h1
    · exact h1
    · exact absurd (S10.alpha_subset_sigma hG h.mem_maximal h1)
        (h.not_mem_sigma_of_mem_primeFactors hG hr)
  -- `ℳ(N_G(Q)) ≠ {M}` (since `M* ≠ M`).
  have hMNQne :
      maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G)) ≠ {M} := by
    rw [hMNQstar]; intro heq; exact hMstarNe (Set.singleton_injective heq)
  -- Lemma 12.18(a) on `(r, R, q, Q)`: `C_{M_α}(R) ≠ 1` and `C_{M_α}(RQ) = 1`.
  obtain ⟨hCR_ne, hCRQ_bot⟩ :=
    (tau1_Malpha_interaction hG h.mem_maximal hrq.symm hrτ1M hR (hRE.trans h.E_le) hQM hQne hQq
      hRNQ hCQR hMNQne).1 hMαne hqαM
  -- step 7 (2nd BG gap, original derivation): `C_{M_α}(P) = C_{M_α}(R)`. BG elides the rank-≤1 /
  -- Thompson / Thm 3.7 argument; built incrementally. Framework: both centralizers have rank ≤ 1.
  have hCeq : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      = S10.Malpha M ⊓ Subgroup.centralizer (R : Set G) := by
    -- `P`, `R` are `α(M)'`-subgroups (`p, r ∈ τ₁(M) ⟹ p, r ∉ σ(M) ⊇ α(M)`).
    have hpnotσ : p ∉ S10.sigma M := hp.1
    have hPpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ P := by
      intro s hs
      obtain ⟨n, hn⟩ := hPp.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hs
      rw [Set.mem_compl_iff,
        (Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)]
      exact fun ha => hpnotσ (S10.alpha_subset_sigma hG h.mem_maximal ha)
    have hRpi : Subgroup.IsPiSubgroup (S10.alpha M)ᶜ R := by
      intro s hs
      obtain ⟨n, hn⟩ := hRr.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hs
      rw [Set.mem_compl_iff,
        (Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)]
      exact fun ha => h.not_mem_sigma_of_mem_primeFactors hG hr (S10.alpha_subset_sigma hG
        h.mem_maximal ha)
    -- `(12.6)`-style rank bounds (rank lemma + `ℳ(N_G(·)) ≠ {M}` for `τ₁` primes).
    have hrankP : rank ↥(Subgroup.centralizer (P : Set G) ⊓ S10.Malpha M) ≤ 1 :=
      rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG h.mem_maximal hPM hPne hPpi
        (maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1 hG h.mem_maximal hp hPM
          hPne hPp)
    have hrankR : rank ↥(Subgroup.centralizer (R : Set G) ⊓ S10.Malpha M) ≤ 1 :=
      rank_centralizer_Malpha_le_one_of_not_uniqueMaximal hG h.mem_maximal (hRE.trans h.E_le) hRne
        hRpi (maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1 hG h.mem_maximal hrτ1M
          (hRE.trans h.E_le) hRne hRr)
    -- 🚧 remaining: Thompson critical + Thm 3.7 FPF argument for the equality.
    sorry
  -- step 8: `A := C_{M_α}(P)` is `S`-invariant (`S ⊆ C(P)`, `M_α ⊴ M`) and `⊆ C(R)` (`= C_{M_α}(R)`),
  -- so by three-subgroups it is centralized by `Q = ⁅S, R⁆`.
  have hMNMα : M ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (S10.alpha M) M
  have hSNA : S ≤ Subgroup.normalizer
      ((S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf ((hSMsig.trans (S10.Msigma_le M)).trans hMNMα)
      (hSCP.trans Subgroup.le_normalizer)
  have hAleCR : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ Subgroup.centralizer (R : Set G) := by rw [hCeq]; exact inf_le_right
  have hAcQ : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ Subgroup.centralizer ((⁅S, R⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    refine commutator_commutator_eq_bot_of_le_of_commutator_bot
      (Ch04.commutator_le_of_le_normalizer hSNA) ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hAleCR
  -- step 9: `A ⊆ M_α ⊓ C(R ⊔ Q) = ⊥`, but `A = C_{M_α}(R) ≠ ⊥`. Contradiction.
  have hRQcA : (R ⊔ ⁅S, R⁆ : Subgroup G) ≤ Subgroup.centralizer
      ((S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_ <;>
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
    · exact hAleCR
    · exact hAcQ
  have hAbot : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ S10.Malpha M ⊓ Subgroup.centralizer ((R ⊔ ⁅S, R⁆ : Subgroup G) : Set G) := by
    refine le_inf inf_le_left ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hRQcA
  rw [hCRQ_bot, le_bot_iff, hCeq] at hAbot
  exact hCR_ne hAbot

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
