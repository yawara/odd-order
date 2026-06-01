/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E

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
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## prime / regular action の定義 (mmd L3486, L3494) -/

/-- **BG "X acts in a prime manner on N"** (mmd L3486): `X` の `N` への共役作用が
`C_N(g) = C_N(X)` を満たす (全 `g ∈ X#`)。ここで `C_N(·) = N ⊓ C_G(·)`。
同値な形 `C_N(P) ⊆ C_N(X)` (∀P∈ℰ¹(X)) も原典にある。 -/
def ActsPrimeOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 →
    N ⊓ Subgroup.centralizer ({g} : Set G) = N ⊓ Subgroup.centralizer (X : Set G)

/-- **BG "X acts regularly on N"** (mmd L3494): `C_N(g) = 1` を満たす (全 `g ∈ X#`)。 -/
def ActsRegularlyOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 → N ⊓ Subgroup.centralizer ({g} : Set G) = ⊥

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
  sorry

/-- **BG Corollary 13.2** (mmd L3518): `p ∈ τ₁(M)∪τ₃(M)`, `P` 非自明 `p`-部分群 of `M`,
`M* ∈ ℳ(N_G(P))` なら (a) `M∩M*` の全 `p`-部分群が `M_σ∩M*` を中心化; (b) `E∩M*` の全
`τ₁(M*)'`-部分群が `M_σ∩M*` を中心化; (c) `[M_σ∩M*,M∩M*]≠1` なら `p ∈ σ(M*)`、かつ
`p ∈ τ₁(M)` なら `p ∈ β(M*)`。 -/
theorem tau13_pSubgroup_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M ∪ tau3 M) {P : Subgroup G} (hPM : P ≤ M) (hPne : P ≠ ⊥) (hPp : IsPGroup p ↥P)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))) :
    (∀ Q : Subgroup G, Q ≤ M ⊓ Mstar → IsPGroup p ↥Q →
      Q ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G)) ∧
    (∀ Q : Subgroup G, Q ≤ E ⊓ Mstar → Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) Q →
      Q ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G)) ∧
    (⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ →
      p ∈ S10.sigma Mstar ∧ (p ∈ tau1 M → p ∈ S10.beta Mstar)) := by
  sorry

/-- **BG Corollary 13.3** (mmd L3526): (a) `E` の非自明 cyclic Sylow 部分群は `M_σ` に prime 作用;
(b) `E₃` は `M_σ` に prime 作用。 -/
theorem cyclicSylow_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ p : ℕ, ∀ P : Subgroup G, P ≤ E → IsPGroup p ↥P → IsCyclic ↥P → P ≠ ⊥ →
      (∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) →
      ActsPrimeOn (S10.Msigma M) P) ∧
    ActsPrimeOn (S10.Msigma M) E₃ := by
  sorry

/-- **BG Theorem 13.4** (mmd L3538): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `r ∈ π(E)`, `R ∈ ℰ_r¹(C_E(P))`
なら `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。(prime action 解析の主ステップ。) -/
theorem centralizer_le_centralizer_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hp : p ∈ tau1 M) (hr : r ∈ (Nat.card ↥E).primeFactors)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRC : R ≤ E ⊓ Subgroup.centralizer (P : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (R : Set G) := by
  sorry

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

/-- **BG Lemma 13.8** (mmd L3630): 次の配置は不可能 — `M*∈ℳ` (`M`と非共役), `p∈τ₁(M)∩τ₁(M*)`,
`P∈ℰ_p¹(M∩M*)`, `Q,Q*` を `M∩M*` の `P`-不変 Sylow 部分群 (素数は異なってよい),
`C_Q(P)=C_{Q*}(P)=1`, `N_G(Q)⊆M*`, `N_G(Q*)⊆M`。 -/
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

/-- **BG Theorem 13.10** (mmd L3672; 結論は PDF p.102 から画像読みで復元): ある `P∈ℰ_p¹(E₁)` が
`E₃` を中心化しないなら (a) `E₁` は `E₃` に regular 作用; (b) `E₃` は `M_σ` に regular 作用;
(c) その `P` について `C_{M_σ}(P) ≠ 1`。 -/
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
