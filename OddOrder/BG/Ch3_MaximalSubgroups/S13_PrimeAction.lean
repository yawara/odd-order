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

/-- **BG Corollary 13.3** (mmd L3526): (a) `E` の非自明 cyclic Sylow 部分群は `M_σ` に prime 作用;
(b) `E₃` は `M_σ` に prime 作用。 -/
theorem cyclicSylow_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ p : ℕ, ∀ P : Subgroup G, P ≤ E → IsPGroup p ↥P → IsCyclic ↥P → P ≠ ⊥ →
      (∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) →
      ActsPrimeOn (S10.Msigma M) P) ∧
    ActsPrimeOn (S10.Msigma M) E₃ := by
  sorry

-- **BG Theorem 13.4** (`centralizer_le_centralizer_of_tau1`) は leaf `S13_Theorem134.lean` へ
-- 移動 (上で import)。outer reduction は完全証明、per-q core steps 4-9 は scaffold sorry。

/-- **BG Theorem 13.5** (mmd L3570): `E₁ ≠ 1` なら `E₁` は `M_σ` に prime 作用。 -/
theorem E1_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥) :
    ActsPrimeOn (S10.Msigma M) E₁ := by
  sorry

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
