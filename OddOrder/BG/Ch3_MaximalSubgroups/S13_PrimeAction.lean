/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Lemma131
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Corollary132
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Theorem134

/-!
# BG §13: Prime Action

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §13 (pp. 97-104), mmd `references/bg/local-analysis.mmd`
L3484-3699, **11 結果 + 2 定義** (Lem 13.1/13.6/13.7/13.8 + Cor 13.2/13.3/13.11 +
Thm 13.4/13.5/13.9/13.10)。

§13 は maximal subgroup `M` 内で `M_σ` の補群 `E` がどのように `M_σ` に作用するかを解析する。
中心概念は **prime action** (`C_{M_σ}(g)=C_{M_σ}(X)` ∀g∈X#) と **regular action** (`C_{M_σ}(g)=1`)。
`E₁`/`E₃` (cyclic Hall τ₁/τ₃-部分群) が `M_σ` に prime 作用すること (13.5, 13.3) が主結果。

## 定義 (BG → repo, mmd L3486/L3494)

- `ActsPrimeOn N X`: `X` が `N` に prime 作用 (`C_N(g)=C_N(X)` ∀g∈X#)。
- `ActsRegularlyOn N X`: `X` が `N` に regular 作用 (`C_N(g)=1` ∀g∈X#)。
- `M_σ`/σ/τ_i 等は §10/§12 を再利用 (`S10.*`, `tau1/tau2/tau3`, `SubgroupESetup`)。
- 固定 G `(hG : IsMinimalSimpleOdd G)` を明示 thread。proof は全て `sorry` (scaffold)。

**注**: Thm 13.10/Cor 13.11 の結論 bullet は Nougat が脱落 → PDF p.102-103 を画像読みで復元
(`notes/meta/nougat_missing_page_recovery.md`)。

## Lane C dependency gates

- Import boundary: §13 imports §12 only. The §11 exceptional-maximal input is carried by
  §12, because Prop 12.4 and Thm 12.5 are the first places using Hypothesis 11.1.
- Lemma 13.1 uses Lemma 10.8 and Corollary 12.16(a) (mmd L3504/L3508).
  This is the first §13 gate back into the β-radical and τ₂ exclusion machinery.
- Corollary 13.2 uses Lemma 12.2(a) plus Lemma 13.1 (mmd L3524).
- Theorem 13.4 uses Theorem 12.13 and Lemma 12.18 (mmd L3552/L3568);
  these are centralizer-control interfaces, not new assumptions on `ActsPrimeOn`.
- Lemma 13.8 and Theorem 13.10 use `S10.normalizer_le_of_nontrivial_beta_subgroup`
  (BG Prop 10.14(d)) and Lemma 12.18 (mmd L3646/L3656/L3692). This gate is now
  exposed in §10 as a theorem with `sorry`, not as a downstream hypothesis or setup field.
- The §12 path into §13 also depends on the newly exposed §10 surfaces
  `S10.beta_complement_normalizer_derived_contains_sylow` (Cor 10.9(a)(3)),
  `S10.beta_factorization_of_sylow_normalizer_in_intersection` (Cor 10.9(b)), and
  `S10.sigma_complement_commutator_cyclic_normal` (Prop 10.11(d)). Keep those as
  upstream proof gates when filling Lemma 13.8 / Theorem 13.10.
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## prime / regular action の定義 (mmd L3486, L3494) -/

/-- `C_N(X)` in BG §13: elements of `N` centralizing the subgroup `X`. -/
def fixedBy (N X : Subgroup G) : Subgroup G :=
  N ⊓ Subgroup.centralizer (X : Set G)

/-- `C_N(g)` in BG §13: elements of `N` centralizing the element `g`. -/
def fixedByElement (N : Subgroup G) (g : G) : Subgroup G :=
  N ⊓ Subgroup.centralizer ({g} : Set G)

/-- **BG "X acts in a prime manner on N"** (mmd L3486): `X` の `N` への共役作用が
`C_N(g) = C_N(X)` を満たす (全 `g ∈ X#`)。ここで `C_N(·) = N ⊓ C_G(·)`。
同値な形 `C_N(P) ⊆ C_N(X)` (∀P∈ℰ¹(X)) も原典にある。 -/
def ActsPrimeOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 →
    fixedByElement N g = fixedBy N X

/-- **BG "X acts regularly on N"** (mmd L3494): `C_N(g) = 1` を満たす (全 `g ∈ X#`)。 -/
def ActsRegularlyOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 → fixedByElement N g = ⊥

@[simp] theorem fixedBy_def (N X : Subgroup G) :
    fixedBy N X = N ⊓ Subgroup.centralizer (X : Set G) :=
  rfl

@[simp] theorem fixedByElement_def (N : Subgroup G) (g : G) :
    fixedByElement N g = N ⊓ Subgroup.centralizer ({g} : Set G) :=
  rfl

@[simp] theorem actsPrimeOn_iff (N X : Subgroup G) :
    ActsPrimeOn N X ↔ ∀ g ∈ X, g ≠ 1 → fixedByElement N g = fixedBy N X :=
  Iff.rfl

@[simp] theorem actsRegularlyOn_iff (N X : Subgroup G) :
    ActsRegularlyOn N X ↔ ∀ g ∈ X, g ≠ 1 → fixedByElement N g = ⊥ :=
  Iff.rfl

theorem fixedBy_le_fixedByElement {N X : Subgroup G} {g : G} (hg : g ∈ X) :
    fixedBy N X ≤ fixedByElement N g := by
  refine inf_le_inf_left N ?_
  refine Subgroup.centralizer_le ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact hg

theorem ActsRegularlyOn.toActsPrimeOn {N X : Subgroup G} (h : ActsRegularlyOn N X) :
    ActsPrimeOn N X := by
  intro g hg hgne
  have hpoint : fixedByElement N g = ⊥ := h g hg hgne
  have hfixed : fixedBy N X = ⊥ := by
    exact le_bot_iff.mp ((fixedBy_le_fixedByElement (N := N) (X := X) hg).trans (by rw [hpoint]))
  rw [hpoint, hfixed]

theorem ActsRegularlyOn.mono_left {N₀ N X : Subgroup G} (hN₀ : N₀ ≤ N)
    (h : ActsRegularlyOn N X) : ActsRegularlyOn N₀ X := by
  intro g hg hgne
  have hle : fixedByElement N₀ g ≤ fixedByElement N g := by
    intro y hy
    exact ⟨hN₀ hy.1, hy.2⟩
  exact le_antisymm (hle.trans (by rw [h g hg hgne])) bot_le

theorem ActsPrimeOn.mono_left {N₀ N X : Subgroup G} (hN₀ : N₀ ≤ N)
    (h : ActsPrimeOn N X) : ActsPrimeOn N₀ X := by
  intro g hg hgne
  refine le_antisymm ?_ (fixedBy_le_fixedByElement (N := N₀) (X := X) hg)
  intro y hy
  have hy_big : y ∈ fixedByElement N g := ⟨hN₀ hy.1, hy.2⟩
  have hy_fixed : y ∈ fixedBy N X := by
    rwa [h g hg hgne] at hy_big
  exact ⟨hy.1, hy_fixed.2⟩

theorem actsPrimeOn_bot_left (X : Subgroup G) : ActsPrimeOn (⊥ : Subgroup G) X := by
  simp [ActsPrimeOn, fixedByElement, fixedBy]

theorem actsRegularlyOn_bot_left (X : Subgroup G) : ActsRegularlyOn (⊥ : Subgroup G) X := by
  simp [ActsRegularlyOn, fixedByElement]

/-! ## §13 初等的 prime action (mmd L3498-3572) -/

/-- **BG Lemma 13.1** (mmd L3498): `M* ∈ ℳ`, `p ∈ π(E)∩π(M*)`, `p ∉ τ₁(M*)`,
`[M_σ∩M*, M∩M*] ≠ 1`, `M*` が `M` と非共役なら
(a) `M∩M*` の全 `p`-部分群が `M_σ∩M*` を中心化; (b) `p ∉ τ₂(M*)`; (c) `p ∈ τ₁(M)` なら `p ∈ β(G)`。 -/
theorem pSubgroup_centralizes_of_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G)
    (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpMstar : p ∈ (Nat.card ↥Mstar).primeFactors)
    (hpτ1 : p ∉ tau1 Mstar) (hcomm : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    (∀ P : Subgroup G, P ≤ M ⊓ Mstar → IsPGroup p ↥P →
      P ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G)) ∧
    p ∉ tau2 Mstar ∧
    (p ∈ tau1 M → S10.idealPrime p G) := by
  have hb : p ∉ tau2 Mstar := not_mem_tau2_of_interaction hG h hMstar hpE hcomm hnc
  exact ⟨fun P hP hPp =>
      pSubgroup_centralizes_Msigma_inf hG h hMstar hpE hpMstar hpτ1 hb hnc hP hPp,
    hb, fun hpτ1M =>
      mem_idealPrime_of_tau1_of_interaction hG h hMstar hpE hpMstar hpτ1 hb hcomm hnc hpτ1M⟩

-- **BG Corollary 13.2** (`tau13_pSubgroup_centralizes`) は leaf
-- `S13_Corollary132.lean` で完全証明済 (上で import)。本ファイルからは再 export される。

/-- **Core of BG Corollary 13.3(a)**: an abelian `p`-subgroup `P ≤ M` with `p ∈ τ₁(M) ∪ τ₃(M)`
acts in a prime manner on `M_σ`. For `g ∈ P#`, pick `M* ∈ ℳ(N_G(⟨g⟩))`; then `P ≤ M ⊓ M*`
(`P` abelian centralizes `g`), so Corollary 13.2(a) makes `P` centralize `M_σ ⊓ M*`, while
`C_{M_σ}(g) ≤ M_σ ⊓ M*` (since `C(g) ⊆ M*`); hence `C_{M_σ}(g) = C_{M_σ}(P)`. -/
theorem actsPrimeOn_Msigma_of_mem_tau13 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M ∪ tau3 M) {P : Subgroup G} (hPM : P ≤ M) (hPab : IsMulCommutative ↥P)
    (hPp : IsPGroup p ↥P) : ActsPrimeOn (S10.Msigma M) P := by
  classical
  intro g hgP hg1
  have hMcoatom : IsCoatom M := mem_maximalSubgroups.mp h.mem_maximal
  -- `Z := ⟨g⟩`, a nontrivial `p`-subgroup of `M`.
  have hZle : Subgroup.zpowers g ≤ P := by rw [Subgroup.zpowers_le]; exact hgP
  have hZM : Subgroup.zpowers g ≤ M := hZle.trans hPM
  have hZne : Subgroup.zpowers g ≠ ⊥ := fun hb => hg1 (Subgroup.zpowers_eq_bot.mp hb)
  have hZp : IsPGroup p ↥(Subgroup.zpowers g) := hPp.to_le hZle
  -- `N_G(Z) ≠ ⊤`, so some coatom `M*` lies above it.
  have hNZne : Subgroup.normalizer (Subgroup.zpowers g : Set G) ≠ ⊤ := by
    intro htop
    haveI : (Subgroup.zpowers g).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) inferInstance with hb | ht
    · exact hZne hb
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hZM))
  obtain ⟨Mstar, hMstarCo, hNZM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Subgroup.zpowers g : Set G))).resolve_left
      hNZne
  have hMstarMem : Mstar ∈
      maximalSubgroupsContaining (Subgroup.normalizer (Subgroup.zpowers g : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNZM⟩
  -- `C({g}) ≤ C(Z) ≤ N(Z) ≤ M*` (centralizing `g` ⟹ centralizing `⟨g⟩`).
  have hCg_CZ : Subgroup.centralizer ({g} : Set G)
      ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm : Commute x g := (hx g rfl).symm
    exact ((hcomm.zpow_right k).eq).symm
  have hCg_Mstar : Subgroup.centralizer ({g} : Set G) ≤ Mstar :=
    hCg_CZ.trans ((Subgroup.centralizer_le_normalizer _).trans hNZM)
  -- `P ≤ M ⊓ M*` (P abelian ∋ g, so `P ≤ C(P) ≤ C(Z) ≤ N(Z) ≤ M*`).
  have hPCZ : P ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hPab).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZle))
  have hPMstar : P ≤ Mstar :=
    hPCZ.trans ((Subgroup.centralizer_le_normalizer _).trans hNZM)
  -- Corollary 13.2(a): `P` centralizes `M_σ ⊓ M*`.
  have hPcent : P ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
    (tau13_pSubgroup_centralizes hG h hp hZM hZne hZp hMstarMem).1 P (le_inf hPM hPMstar) hPp
  have hMMcP : (S10.Msigma M ⊓ Mstar : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPcent
  -- conclude: `M_σ ⊓ C(g) ≤ M_σ ⊓ M* ≤ C(P)`, so `C_{M_σ}(g) = C_{M_σ}(P)`.
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hgP)
  rw [fixedByElement_def, fixedBy_def]
  exact le_inf inf_le_left ((inf_le_inf_left _ hCg_Mstar).trans hMMcP)

/-- A nontrivial cyclic Sylow `p`-subgroup `P` of `E` has `p ∈ τ₁(M) ∪ τ₃(M)`: as `P` is a Sylow
`p` of `E` and `p ∤ |M_σ|` (since `p ∈ π(E) ⊆ σ(M)'`), `P` is a Sylow `p` of `M`, so
`r_p(M) = r_p(P) ≤ 1`; with `p ∉ σ(M)` this places `p` in `τ₁ ∪ τ₃` (which is `{p ∉ σ(M), r_p(M)=1}`).
Excludes `τ₂` (which needs `r_p(M)=2`) and supplies the `τ₁ ∪ τ₃` hypothesis of the core lemma. -/
theorem mem_tau1_union_tau3_of_isCyclic_sylow_E [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hPE : P ≤ E) (hPp : IsPGroup p ↥P) (hPcyc : IsCyclic ↥P) (hPne : P ≠ ⊥)
    (hPmax : ∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) :
    p ∈ tau1 M ∪ tau3 M := by
  classical
  -- `p ∈ π(P) ⊆ π(E) ⊆ π(M)`.
  have hpdvdP : p ∣ Nat.card ↥P := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl; rw [pow_zero] at hk; exact hPne (Subgroup.card_eq_one.mp hk)
    exact hk ▸ dvd_pow_self p hk0
  have hpdvdE : p ∣ Nat.card ↥E := hpdvdP.trans (Subgroup.card_dvd_of_le hPE)
  have hpπE : p ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdE, Nat.card_pos.ne'⟩
  have hpσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hpπE
  have hpπM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdE.trans (Subgroup.card_dvd_of_le h.E_le),
      Nat.card_pos.ne'⟩
  -- `P.subgroupOf E` is a Sylow `p` of `↥E`, so `|P| = p ^ (|E|).factorization p`.
  have hPEpg : IsPGroup p ↥(P.subgroupOf E) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv]; exact hk)
  obtain ⟨SylE, hSylE⟩ := hPEpg.exists_le_sylow
  have hPeqSyl : P = (SylE : Subgroup ↥E).map E.subtype := by
    refine hPmax _ (Subgroup.map_subtype_le _) (SylE.isPGroup'.map E.subtype) ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hPE]; exact Subgroup.map_mono hSylE
  have hPcardEq : Nat.card ↥P = p ^ (Nat.card ↥E).factorization p := by
    rw [hPeqSyl, Subgroup.card_map_of_injective E.subtype_injective]
    exact SylE.card_eq_multiplicity
  -- `|M|.factorization p = |E|.factorization p` (since `p ∤ |M_σ|`).
  have hpMσ : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun hd =>
    hpσ (S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))
  have hfactEq : (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
    rw [← h.card_Msigma_mul_card_E,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpMσ, zero_add]
  -- `P.subgroupOf M` is a Sylow `p` of `↥M`; hence `r_p(M) = r_p(P) ≤ 1`.
  have hPMcardEq : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPE.trans h.E_le)).toEquiv, hPcardEq, hfactEq]
  let SylM : Sylow p ↥M := Sylow.ofCard (P.subgroupOf M) hPMcardEq
  haveI hcyc : IsCyclic ↥(P.subgroupOf M) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe (hPE.trans h.E_le)).symm.surjective
  have hpr : pRank ↥(P.subgroupOf M) p ≤ 1 := by
    by_contra hc
    obtain ⟨A, _, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank
        (G := ↥(P.subgroupOf M)) (p := p) (by omega)
    exact hAnc inferInstance
  have hpRankM : pRank ↥M p ≤ 1 :=
    (pRank_sylow_eq SylM).symm.trans_le hpr
  have hpRank1 : pRank ↥M p = 1 :=
    le_antisymm hpRankM (one_le_pRank_of_mem_primeFactors hpπM)
  -- assemble `τ₁ ∪ τ₃`.
  by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
  · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hpRank1⟩)
  · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hpRank1⟩)

/-- **BG Corollary 13.3** (mmd L3526): (a) `E` の非自明 cyclic Sylow 部分群は `M_σ` に prime 作用;
(b) `E₃` は `M_σ` に prime 作用。 -/
theorem cyclicSylow_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ E → IsPGroup p ↥P → IsCyclic ↥P → P ≠ ⊥ →
      (∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) →
      ActsPrimeOn (S10.Msigma M) P) ∧
    ActsPrimeOn (S10.Msigma M) E₃ := by
  refine ⟨fun p hp_prime P hPE hPp hPcyc hPne hPmax => ?_, ?_⟩
  · -- (a): cyclic Sylow `P` has `p ∈ τ₁ ∪ τ₃`, then the core lemma applies (`P` abelian).
    haveI : Fact p.Prime := ⟨hp_prime⟩
    haveI := hPcyc
    letI : CommGroup ↥P := IsCyclic.commGroup
    haveI : IsMulCommutative ↥P := ⟨⟨mul_comm⟩⟩
    exact actsPrimeOn_Msigma_of_mem_tau13 hG h
      (mem_tau1_union_tau3_of_isCyclic_sylow_E hG h hPE hPp hPcyc hPne hPmax)
      (hPE.trans h.E_le) inferInstance hPp
  · -- (b) `E₃` acts in a prime manner on `M_σ`.
    haveI hE3cyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
    intro g hgE3 hg1
    refine le_antisymm ?_ (fixedBy_le_fixedByElement hgE3)
    -- pick a prime `p ∣ ord(g)` and the order-`p` element `x := g ^ (ord g / p) ∈ ⟨g⟩ ⊆ E₃`.
    have hord1 : orderOf g ≠ 1 := fun hh => hg1 (orderOf_eq_one_iff.mp hh)
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hord1
    haveI : Fact p.Prime := ⟨hp_prime⟩
    set x : G := g ^ (orderOf g / p) with hx_def
    have hxE3 : x ∈ E₃ := pow_mem hgE3 _
    have hxp1 : x ^ p = 1 := by
      rw [hx_def, ← pow_mul, Nat.div_mul_cancel hp_dvd, pow_orderOf_eq_one]
    have hx1 : x ≠ 1 := by
      intro hh
      have hdvd := orderOf_dvd_of_pow_eq_one hh
      have hpos : 0 < orderOf g / p :=
        Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hp_dvd) hp_prime.pos
      have hlt : orderOf g / p < orderOf g :=
        Nat.div_lt_self (orderOf_pos g) hp_prime.one_lt
      exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
    have hx_ord : orderOf x = p := by
      rcases (Nat.dvd_prime hp_prime).mp (orderOf_dvd_of_pow_eq_one hxp1) with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hx1
      · exact hh
    -- `⟨x⟩` is characteristic in cyclic `E₃`, hence `E`-normal.
    have hZle : Subgroup.zpowers x ≤ E₃ := Subgroup.zpowers_le.mpr hxE3
    haveI : ((Subgroup.zpowers x).subgroupOf E₃).Characteristic :=
      Ch04.characteristic_of_subgroup_of_isCyclic _
    have hENx : E ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro e he
      have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₃)
        (C := (Subgroup.zpowers x).subgroupOf E₃) (h.E3_normal hG he)
      rwa [Subgroup.map_subgroupOf_eq_of_le hZle] at hmem
    -- `M* ∈ ℳ(N_G(⟨x⟩))`, so `E ⊆ M*` and `E₃ ⊆ E' ⊆ M*'`.
    have hxne : Subgroup.zpowers x ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1
    have hxM : Subgroup.zpowers x ≤ M := hZle.trans h.E3_le_M
    have hNxne : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ := by
      intro htop
      haveI : (Subgroup.zpowers x).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) inferInstance with hb | ht
      · exact hxne hb
      · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hxM))
    obtain ⟨Mstar, hMstarCo, hNxM⟩ :=
      (eq_top_or_exists_le_coatom
        (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G))).resolve_left hNxne
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining
        (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNxM⟩
    have hEMstar : E ≤ Mstar := hENx.trans hNxM
    -- `p ∈ τ₃(M)`; `IsPiSubgroup (τ₁ M*)ᶜ E₃`.
    have hpπE3 : p ∈ (Nat.card ↥E₃).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
      have hzc : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx_ord]
      rw [← hzc]; exact Subgroup.card_dvd_of_le hZle
    have hpτ3 : p ∈ tau3 M := h.isPiGroup_tau3 p hpπE3
    have hE3M'star : E₃ ≤ derivedInG Mstar :=
      (h.E3_le_derived hG).trans (derivedInG_le_derivedInG hEMstar)
    have hE3pi : Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) E₃ := by
      intro q hq
      rw [Set.mem_compl_iff, mem_tau1_iff]
      rintro ⟨_, hqM', _⟩
      exact hqM' (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
        (Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le hE3M'star), Nat.card_pos.ne'⟩)
    -- Corollary 13.2(b): `E₃` centralizes `M_σ ⊓ M*`.
    have hxp : IsPGroup p ↥(Subgroup.zpowers x) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hx_ord, pow_one])
    have hE3cent : E₃ ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
      (tau13_pSubgroup_centralizes hG h (Or.inr hpτ3) hxM hxne hxp hMstarMem).2.1 E₃
        (le_inf h.E₃_le (h.E₃_le.trans hEMstar)) hE3pi
    have hMMcE3 : (S10.Msigma M ⊓ Mstar : Subgroup G) ≤ Subgroup.centralizer (E₃ : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hE3cent
    -- `C({x}) ⊆ N(⟨x⟩) ⊆ M*`, and `C({g}) ⊆ C({x})` (since `x ∈ ⟨g⟩`).
    have hCx_Mstar : Subgroup.centralizer ({x} : Set G) ≤ Mstar := by
      refine le_trans ?_ ((Subgroup.centralizer_le_normalizer _).trans hNxM)
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc : Commute y x := (hy x rfl).symm
      exact ((hc.zpow_right k).eq).symm
    have hCgCx : Subgroup.centralizer ({g} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz; subst hz
      have hc : Commute y g := (hy g rfl).symm
      exact ((hc.pow_right (orderOf g / p)).eq).symm
    -- assemble: `M_σ ⊓ C(g) ≤ M_σ ⊓ C(x) ≤ M_σ ⊓ M* ≤ C(E₃)`.
    rw [fixedByElement_def, fixedBy_def]
    refine le_inf inf_le_left ?_
    calc S10.Msigma M ⊓ Subgroup.centralizer ({g} : Set G)
        ≤ S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) := inf_le_inf_left _ hCgCx
      _ ≤ S10.Msigma M ⊓ Mstar := inf_le_inf_left _ hCx_Mstar
      _ ≤ Subgroup.centralizer (E₃ : Set G) := hMMcE3

-- **BG Theorem 13.4** (`centralizer_le_centralizer_of_tau1`) は leaf `S13_Theorem134.lean` へ
-- 移動 (上で import)。outer reduction は完全証明、per-q core steps 4-9 は scaffold sorry。

/-- **BG Theorem 13.5** (mmd L3570): `E₁ ≠ 1` なら `E₁` は `M_σ` に prime 作用。

`E₁` is cyclic (Lemma 12.1(d)). The crux is a *cross-prime* fact: for any prime-order element
`x ∈ E₁`, `C_{M_σ}(x) = C_{M_σ}(E₁)`. `C_{M_σ}(E₁) ⊆ C_{M_σ}(x)` is free; for the reverse,
`le_centralizer_of_forall_prime_isPGroup` reduces `E₁ ≤ C(C_{M_σ}(x))` to: every prime-power
subgroup `R ≤ E₁` is centralized by `C_{M_σ}(x)`. Picking an order-`r` element `y ∈ R`,
Theorem 13.4 (with `⟨x⟩ ∈ ℰ_p¹(E)` and `⟨y⟩ ∈ ℰ_r¹(C_E(⟨x⟩))`, valid since `E₁` is abelian) gives
`C_{M_σ}(x) ⊆ C_{M_σ}(y) = C_{M_σ}(R)` (last equality is `R`'s prime action, Corollary 13.3(a) core),
so `C_{M_σ}(x) ≤ C(R)`. A general `g ∈ E₁#` reduces to its prime-power `x = g^{ord g / p}` via
`C(g) ⊆ C(x)`. No explicit Sylow decomposition of `E₁` is needed: the prime-power induction in
`le_centralizer_of_forall_prime_isPGroup` carries it. -/
theorem E1_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥) :
    ActsPrimeOn (S10.Msigma M) E₁ := by
  classical
  haveI hcyc : IsCyclic ↥E₁ := h.E1_isCyclic hG
  letI : CommGroup ↥E₁ := IsCyclic.commGroup
  -- `C({z}) = C(⟨z⟩)`: centralizing an element is the same as centralizing the cyclic subgroup.
  have hcent_zpowers : ∀ z : G,
      Subgroup.centralizer ({z} : Set G)
        = Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro z
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hcm : Commute z w := hw z rfl
      exact ((hcm.symm.zpow_right k).eq).symm
    · exact Subgroup.centralizer_le (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; rw [hu]; exact Subgroup.mem_zpowers z)
  -- Elements of `E₁` commute (E₁ abelian).
  have hE1comm : ∀ a ∈ E₁, ∀ b ∈ E₁, Commute a b := by
    intro a ha b hb
    exact Subtype.ext_iff.mp (mul_comm (⟨a, ha⟩ : ↥E₁) ⟨b, hb⟩)
  -- `⟨z⟩ ∈ ℰ_s¹` for a prime-order element `z`.
  have hzp_mem : ∀ (s : ℕ) (z : G), s.Prime → orderOf z = s →
      Subgroup.zpowers z ∈ elemAbelianOfRank G s 1 := by
    intro s z hs hzord
    haveI : Fact s.Prime := ⟨hs⟩
    refine mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩
    · exact Subgroup.IsElementaryAbelian.of_card_prime (by rw [Nat.card_zpowers]; exact hzord)
    · rw [pow_one, Nat.card_zpowers]; exact hzord
  -- Sub-claim A: a prime-order element `x ∈ E₁` has `C_{M_σ}(x) = C_{M_σ}(E₁)`.
  have key : ∀ (p : ℕ) (x : G), x ∈ E₁ → p.Prime → orderOf x = p →
      fixedByElement (S10.Msigma M) x = fixedBy (S10.Msigma M) E₁ := by
    intro p x hxE1 hp hxord
    haveI : Fact p.Prime := ⟨hp⟩
    have hxmem : Subgroup.zpowers x ∈ elemAbelianOfRank G p 1 := hzp_mem p x hp hxord
    have hxE : (Subgroup.zpowers x : Subgroup G) ≤ E :=
      (Subgroup.zpowers_le.mpr hxE1).trans h.E₁_le
    have hpπE1 : p ∈ (Nat.card ↥E₁).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      rw [← hxord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxE1)
    have hpτ1 : p ∈ tau1 M := h.isPiGroup_tau1 p hpπE1
    refine le_antisymm ?_ (fixedBy_le_fixedByElement hxE1)
    -- `C_{M_σ}(x) ≤ C_{M_σ}(E₁)`; reduce to `C_{M_σ}(x) ≤ C(↑E₁)`.
    rw [fixedBy_def]
    refine le_inf (by rw [fixedByElement_def]; exact inf_le_left) ?_
    rw [← Subgroup.le_centralizer_iff]
    apply le_centralizer_of_forall_prime_isPGroup
    intro r hr R hRE1 hRr
    rcases eq_or_ne R ⊥ with rfl | hRne
    · exact bot_le
    · haveI : Fact r.Prime := ⟨hr⟩
      rw [← Subgroup.le_centralizer_iff]
      -- `R` is abelian (≤ E₁) and nontrivial; extract an order-`r` element `y ∈ R`.
      haveI hRab : IsMulCommutative ↥R := ⟨⟨fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]; exact hE1comm (a : G) (hRE1 a.2) (b : G) (hRE1 b.2))⟩⟩
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hRr) a
      have hak0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk; exact ha1 (orderOf_eq_one_iff.mp hk)
      have haR : (a : G) ∈ R := a.2
      have haord : orderOf (a : G) = r ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      have hrdvd : r ∣ orderOf (a : G) := by rw [haord]; exact dvd_pow_self r hak0
      have hyr1 : ((a : G) ^ (orderOf (a : G) / r)) ^ r = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel hrdvd, pow_orderOf_eq_one]
      have hy1 : (a : G) ^ (orderOf (a : G) / r) ≠ 1 := by
        intro hh
        have hdvd := orderOf_dvd_of_pow_eq_one hh
        have hpos : 0 < orderOf (a : G) / r :=
          Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hrdvd) hr.pos
        have hlt : orderOf (a : G) / r < orderOf (a : G) :=
          Nat.div_lt_self (orderOf_pos _) hr.one_lt
        exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
      have hyord : orderOf ((a : G) ^ (orderOf (a : G) / r)) = r := by
        rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hyr1) with hh | hh
        · exact absurd (orderOf_eq_one_iff.mp hh) hy1
        · exact hh
      have hyR : (a : G) ^ (orderOf (a : G) / r) ∈ R := pow_mem haR _
      set y : G := (a : G) ^ (orderOf (a : G) / r) with hydef
      have hyE1 : y ∈ E₁ := hRE1 hyR
      have hyE : y ∈ E := h.E₁_le hyE1
      -- `⟨y⟩ ∈ ℰ_r¹`, `r ∈ π(E)`, `r ∈ τ₁(M)`.
      have hymem : Subgroup.zpowers y ∈ elemAbelianOfRank G r 1 := hzp_mem r y hr hyord
      have hrπE : r ∈ (Nat.card ↥E).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hr, hyord ▸ E.orderOf_dvd_natCard hyE, Nat.card_pos.ne'⟩
      have hrτ1 : r ∈ tau1 M :=
        h.isPiGroup_tau1 r (Nat.mem_primeFactors.mpr
          ⟨hr, hyord ▸ E₁.orderOf_dvd_natCard hyE1, Nat.card_pos.ne'⟩)
      -- `⟨y⟩ ≤ E ⊓ C(↑⟨x⟩)` (y commutes with x).
      have hyRC : (Subgroup.zpowers y : Subgroup G) ≤
          E ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        refine le_inf ((Subgroup.zpowers_le.mpr hyE1).trans h.E₁_le) ?_
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro u hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact ((hE1comm x hxE1 y hyE1).zpow_left j).eq
      -- Theorem 13.4 and the prime action of `R`.
      have hT134 := centralizer_le_centralizer_of_tau1 hG h hpτ1 hrπE hxmem hxE hymem hyRC
      have hRact : ActsPrimeOn (S10.Msigma M) R :=
        actsPrimeOn_Msigma_of_mem_tau13 hG h (Or.inl hrτ1) (hRE1.trans h.E1_le_M) hRab hRr
      have hRy : fixedByElement (S10.Msigma M) y = fixedBy (S10.Msigma M) R := hRact y hyR hy1
      calc fixedByElement (S10.Msigma M) x
          = S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
            rw [fixedByElement_def, hcent_zpowers x]
        _ ≤ S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := hT134
        _ = fixedByElement (S10.Msigma M) y := by rw [fixedByElement_def, hcent_zpowers y]
        _ = fixedBy (S10.Msigma M) R := hRy
        _ ≤ Subgroup.centralizer ((R : Subgroup G) : Set G) := by
            rw [fixedBy_def]; exact inf_le_right
  -- Main: reduce a general `g ∈ E₁#` to its prime-power part `x = g^{ord g / p}`.
  intro g hgE1 hg1
  have hord1 : orderOf g ≠ 1 := fun hh => hg1 (orderOf_eq_one_iff.mp hh)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hord1
  have hxp1 : (g ^ (orderOf g / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hp_dvd, pow_orderOf_eq_one]
  have hx1 : g ^ (orderOf g / p) ≠ 1 := by
    intro hh
    have hdvd := orderOf_dvd_of_pow_eq_one hh
    have hpos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hp_dvd) hp_prime.pos
    have hlt : orderOf g / p < orderOf g := Nat.div_lt_self (orderOf_pos g) hp_prime.one_lt
    exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  have hxord : orderOf (g ^ (orderOf g / p)) = p := by
    rcases (Nat.dvd_prime hp_prime).mp (orderOf_dvd_of_pow_eq_one hxp1) with hh | hh
    · exact absurd (orderOf_eq_one_iff.mp hh) hx1
    · exact hh
  have hxE1 : g ^ (orderOf g / p) ∈ E₁ := pow_mem hgE1 _
  -- `C(g) ≤ C(x)` since `x = g^(ord g / p)`.
  have hCgx : Subgroup.centralizer ({g} : Set G)
      ≤ Subgroup.centralizer ({g ^ (orderOf g / p)} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    intro u hu
    rw [Set.mem_singleton_iff] at hu; subst hu
    have hcm : Commute g w := hw g rfl
    exact (hcm.pow_left (orderOf g / p)).eq
  have hkey := key p (g ^ (orderOf g / p)) hxE1 hp_prime hxord
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hgE1)
  calc fixedByElement (S10.Msigma M) g
      ≤ fixedByElement (S10.Msigma M) (g ^ (orderOf g / p)) := by
        rw [fixedByElement_def, fixedByElement_def]; exact inf_le_inf_left _ hCgx
    _ = fixedBy (S10.Msigma M) E₁ := hkey

/-! ## §13 prime action の拡張解析 (mmd L3574-3628) -/

/-- **BG Lemma 13.6** (mmd L3574): `1⊂P⊆E₁`, `q∈σ(M)`, `X∈ℰ_q¹(C_{M_σ}(P))`, `S` を `M_σ` の
Sylow `q`-部分群とすると `ℳ(C_G(X))=ℳ(S)={M}`。 -/
theorem maximalContaining_eq_singleton_of_E1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {P : Subgroup G} (hPE1 : P ≤ E₁) (hPne : P ≠ ⊥)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G q 1)
    (hXC : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G))
    {S : Subgroup G} (hSle : S ≤ S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
    maximalSubgroupsContaining S = {M} := by
  sorry

/-- **BG Lemma 13.7** (mmd L3596): `E₁≠1` かつ `E₁` が `E₃` に regular 作用しないなら、`E₁E₃` は
`M_σ` に prime 作用。 -/
theorem E1E3_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ActsPrimeOn (S10.Msigma M) (E₁ ⊔ E₃) := by
  sorry

/-! ## §13 相互制約と transition (mmd L3630-3699) -/

/-- **BG Lemma 13.8** (mmd L3630): 次の配置は不可能 — `M*∈ℳ` (`M`と非共役),
`p∈τ₁(M)∩τ₁(M*)`, `P∈ℰ_p¹(M∩M*)`, `Q,Q*` を `M∩M*` の `P`-不変 Sylow 部分群
(素数は異なってよい), `C_Q(P)=C_{Q*}(P)=1`, `N_G(Q)⊆M*`, `N_G(Q*)⊆M`。

§10 gates visible for proof-fill: Theorem 10.2's `M'/M_α` nilpotence tail,
`S10.disjoint_of_not_conj` (Lemma 10.12), and
`S10.normalizer_le_of_nontrivial_beta_subgroup` (Prop 10.14(d)). The Hall/Frattini pieces
used through §12 must remain upstream theorem calls, not new hypotheses on this statement. -/
theorem forbidden_config_impossible [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M) (hpstar : p ∈ tau1 Mstar)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPM : P ≤ M ⊓ Mstar)
    {q qstar : ℕ} [Fact q.Prime] [Fact qstar.Prime] {Q Qstar : Subgroup G}
    (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQstarle : Qstar ≤ M ⊓ Mstar) (hQstarq : IsPGroup qstar ↥Qstar)
    (hQstarmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup qstar ↥T → Qstar ≤ T → Qstar = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hQstarinv : P ≤ Subgroup.normalizer (Qstar : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hCQstar : Qstar ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hNQstar : Subgroup.normalizer (Qstar : Set G) ≤ M) :
    False := by
  sorry

/-- **BG Theorem 13.9** (mmd L3662): `M*∈ℳ` が `M` と非共役なら `σ(M)` と `σ(M*)` は disjoint。 -/
theorem sigma_disjoint_of_nonconjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    Disjoint (S10.sigma M) (S10.sigma Mstar) := by
  sorry

/-- **BG Theorem 13.10** (mmd L3672; 結論は PDF p.102 から画像読みで復元):
ある `P∈ℰ_p¹(E₁)` が `E₃` を中心化しないなら (a) `E₁` は `E₃` に regular 作用;
(b) `E₃` は `M_σ` に regular 作用; (c) その `P` について `C_{M_σ}(P) ≠ 1`。

§10 gates visible for proof-fill: `S10.normalizer_le_of_nontrivial_beta_subgroup`
(Prop 10.14(d)) supplies `N_G(Q*)⊆M` in the `q*∈β(M)` branch; the remaining branch uses
`σ(M)` by definition. Lemma 12.18 / Lemma 12.19 carry the Cor 10.9 β-complement input. -/
theorem E1_regular_on_E3_of_noncentralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hP : ∃ p : ℕ, ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ E₁ ∧
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G))) :
    ActsRegularlyOn E₃ E₁ ∧ ActsRegularlyOn (S10.Msigma M) E₃ ∧
    (∀ p : ℕ, ∀ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 → P ≤ E₁ →
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G)) →
      S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) := by
  sorry

/-- **BG Corollary 13.11** (mmd L3696; 結論は PDF p.103 から画像読みで復元): `E₃≠1` かつ `E₃` が
`M_σ` に regular 作用しないなら (a) `E₁≠1`; (b) `E=E₁E₃`; (c) `E` は `M_σ` に prime 作用;
(d) すべての `X∈ℰ¹(E)` は `E` で正規。 -/
theorem E3_not_regular_consequences [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE3 : E₃ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn (S10.Msigma M) E₃) :
    E₁ ≠ ⊥ ∧ E = E₁ ⊔ E₃ ∧ ActsPrimeOn (S10.Msigma M) E ∧
    (∀ q : ℕ, ∀ X : Subgroup G, X ∈ elemAbelianOfRank G q 1 → X ≤ E →
      E ≤ Subgroup.normalizer (X : Set G)) := by
  sorry

end OddOrder.BG.Ch3.S13
