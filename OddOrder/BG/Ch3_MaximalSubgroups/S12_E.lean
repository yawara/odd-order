/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma
import OddOrder.BG.Ch3_MaximalSubgroups.S11_ExceptionalMaximal
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# BG §12: The Subgroup `E`

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §12 (pp. 79-90), mmd `references/bg/local-analysis.mmd`
L3023-3483, **19 結果** (Lem 12.1/12.2/12.11/12.17/12.18/12.19 + Prop 12.4/12.15 +
Thm 12.5/12.7/12.13 + Cor 12.6/12.8/12.9/12.10/12.14/12.16 + Lem 12.3)。

§12 は maximal subgroup `M` の **複合体 `E`** (= `M_σ` の補群、`E ≅ M/M_σ`) の構造を解析する大規模節。
`r(E) ≤ 2`, `E'` nilpotent, 各 Sylow abelian 等。本ファイルは §12 全 19 結果の **faithful な
statement + `sorry`** scaffold (定義層 + Lem 12.1 / Lem 12.2(a) / Lem 12.3 / Prop 12.4(a) /
τ₂-case Thm 12.5–12.12 / Thm 12.13 / Cor 12.14 / Prop 12.15 / Cor 12.16(a) / Lem 12.17 /
Lem 12.18 / Lem 12.19)。clean core を述べ、`Ω₁(P)=A`・内部直積の commuting・商型 nilpotent/rank
等の fragile sub-clause は各 docstring で defer。proof は別フェーズ。

Import boundary: §12 mathematically sits after §11. Prop 12.4 activates the
exceptional-maximal setup, and Thm 12.5 uses the §11 consequences under Hypothesis 11.1.
This file imports `S11_ExceptionalMaximal` even when an individual scaffolded statement only
mentions §10 notation, keeping the BG §16 endpoint closure honest.

## 定義 (BG → repo, mmd L3029)

- `tau1/tau2/tau3 M` (`Set ℕ`): `σ(M)'` を rank と `π(M')` で 3 分割 (mmd L3029)。
- `SubgroupESetup M E E₁ E₂ E₃`: `E` は `M_σ` の `M` 内補群、`Eᵢ` は `E` の Hall `τᵢ(M)`-部分群。
- `M'` = `derivedInG M`; `M_σ` = `S10.Msigma M`; `r_p` = `pRank ↥· p`。
- 固定 G `(hG : IsMinimalSimpleOdd G)` を明示 thread。残り 18 結果 (12.2–12.19) は後続。

## Lane C proof-gate notes

- Import boundary: §12 imports §11. This is intentional even when a theorem statement
  only mentions §10 notation; Proposition 12.4 and Theorem 12.5 activate the
  exceptional-maximal interface and must remain on the BG spine.
- Lemma 12.1 gates on Theorem 10.2, Lemma 4.5, Proposition 1.6(d), and
  Lemma 10.4(c) (mmd L3035-L3060). These are proof obligations, not fields of
  `SubgroupESetup`.
- Lemma 12.2 uses Lemma 10.5 and Theorem 10.1(b) (mmd L3062-L3069). The Lean
  surface currently records part (a); part (b) is a deferred nonconjugacy clause.
- Proposition 12.4 uses the Uniqueness Theorem, Lemma 12.3, Proposition 1.16,
  Proposition 10.11(b), and Theorem 10.2 (mmd L3095-L3126).
- Theorem 12.5 is the bridge from §11 into §12: Proposition 12.4 supplies
  Hypothesis 11.1, then Theorems 11.3, 11.5, 11.7, Corollary 11.6, and
  Lemma 12.3 give the six conclusions (mmd L3129-L3148).
- Theorem 12.12 packages the Frobenius-complement endpoint from Theorem 12.7,
  Lemma 12.8, Corollary 12.6, and Lemma 12.11 (mmd L3306-L3344). The internal
  cyclic `Z_p` construction remains deferred.
- Proposition 12.15, Corollary 12.16, and Lemma 12.17 are the direct §13--§14
  gates (mmd L3385-L3453). The Lean surfaces intentionally keep only the clauses
  currently consumed downstream; Corollary 12.16(b) and the cyclic `β(M)'`/derived
  intersection tail of Lemma 12.17 remain deferred proof obligations.
- Lemmas 12.18 and 12.19 use Theorem 1.13, Theorem 3.7, Corollary 10.9(a), and
  the Uniqueness Theorem (mmd L3454-L3482). Do not replace them by downstream
  prime-action assumptions in §13.
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §12 prime 分割 τ₁/τ₂/τ₃ (mmd L3029) -/

/-- **BG `τ₁(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∉ π(M') ∧ r_p(M)=1}`。 -/
def tau1 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∉ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

/-- **BG `τ₂(M)`** (mmd L3029): `{p ∈ σ(M)' | r_p(M)=2}`。 -/
def tau2 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ pRank ↥M p = 2}

/-- **BG `τ₃(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∈ π(M') ∧ r_p(M)=1}`。 -/
def tau3 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∈ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

/-! ### Basic API for the τ-partition -/

@[simp] theorem mem_tau1_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau1 M ↔
      p ∉ S10.sigma M ∧ p ∉ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1 :=
  Iff.rfl

@[simp] theorem mem_tau2_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau2 M ↔ p ∉ S10.sigma M ∧ pRank ↥M p = 2 :=
  Iff.rfl

@[simp] theorem mem_tau3_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau3 M ↔
      p ∉ S10.sigma M ∧ p ∈ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1 :=
  Iff.rfl

theorem tau1_subset_sigma_compl (M : Subgroup G) : tau1 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau2_subset_sigma_compl (M : Subgroup G) : tau2 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau3_subset_sigma_compl (M : Subgroup G) : tau3 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau1_not_mem_derived_primeFactors {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    p ∉ (Nat.card ↥(derivedInG M)).primeFactors :=
  hp.2.1

theorem tau3_mem_derived_primeFactors {M : Subgroup G} {p : ℕ} (hp : p ∈ tau3 M) :
    p ∈ (Nat.card ↥(derivedInG M)).primeFactors :=
  hp.2.1

theorem tau1_pRank_eq_one {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    pRank ↥M p = 1 :=
  hp.2.2

theorem tau2_pRank_eq_two {M : Subgroup G} {p : ℕ} (hp : p ∈ tau2 M) :
    pRank ↥M p = 2 :=
  hp.2

theorem tau3_pRank_eq_one {M : Subgroup G} {p : ℕ} (hp : p ∈ tau3 M) :
    pRank ↥M p = 1 :=
  hp.2.2

theorem not_mem_tau3_of_mem_tau1 {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    p ∉ tau3 M :=
  fun hp3 => hp.2.1 hp3.2.1

theorem not_mem_tau1_of_mem_tau3 {M : Subgroup G} {p : ℕ} (hp : p ∈ tau3 M) :
    p ∉ tau1 M :=
  fun hp1 => hp1.2.1 hp.2.1

/-- A prime divisor of `|H|` forces `pRank H p ≥ 1` (Cauchy: an order-`p` element
generates an elementary abelian subgroup of order `p`). -/
theorem one_le_pRank_of_mem_primeFactors {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p ∈ (Nat.card H).primeFactors) : 1 ≤ pRank H p := by
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨x, hx⟩ := Ch01.cauchy hdvd
  have hcard : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have helem : (Subgroup.zpowers x).IsElementaryAbelian p := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · intro a
      have h1 : orderOf a ∣ p := hcard ▸ orderOf_dvd_natCard a
      exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hle := le_pRank (Subgroup.zpowers x) helem
  rw [hcard] at hle
  have hlog : Nat.log p p = 1 := by
    nth_rewrite 2 [show p = p ^ 1 from (pow_one p).symm]
    exact Nat.log_pow hprime.one_lt 1
  rwa [hlog] at hle

/-- `E₁E₂` in BG §12, represented as the subgroup join. -/
def E12 (E₁ E₂ : Subgroup G) : Subgroup G :=
  E₁ ⊔ E₂

/-- `E₂E₃` in BG §12, represented as the subgroup join. -/
def E23 (E₂ E₃ : Subgroup G) : Subgroup G :=
  E₂ ⊔ E₃

/-- `E₁E₂E₃` in BG §12, represented as iterated subgroup join. -/
def E123 (E₁ E₂ E₃ : Subgroup G) : Subgroup G :=
  E₁ ⊔ E₂ ⊔ E₃

/-- **BG §12 setup**: `E` は `M_σ` の `M` 内補群 (`M_σ ⊓ E = 1`, `M_σ ⊔ E = M`)、`E₁/E₂/E₃` は
`E` の Hall `τ₁/τ₂/τ₃(M)`-部分群。

原文 (mmd L3029) は **`E₁₂` を `E` の Hall `τ₁(M)∪τ₂(M)`-部分群として固定し、`E₁`,`E₂` を
その内部の Hall** に取る。この入れ子を field `E₁₂_hall` (`E₁ ⊔ E₂` が Hall `τ₁∪τ₂`) で表現する。
`E₁`,`E₂` を `E` の独立な Hall として取るだけでは `E₁ ⊔ E₂` は Hall `τ₁∪τ₂` にならず
(`E₁` だけ共役でずれた取り方が可能)、Lemma 12.1(e) の `E₂ ⊴ E₁E₂` が反例を持つ
(notes/bg/s12_subgroup_e.md 2026-06-10 節)。 -/
structure SubgroupESetup (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  E_le : E ≤ M
  E_compl_inf : S10.Msigma M ⊓ E = ⊥
  E_compl_sup : S10.Msigma M ⊔ E = M
  E₁_le : E₁ ≤ E
  E₂_le : E₂ ≤ E
  E₃_le : E₃ ≤ E
  E₁_hall : Ch03.IsHallSubgroup (tau1 M) (E₁.subgroupOf E)
  E₂_hall : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf E)
  E₃_hall : Ch03.IsHallSubgroup (tau3 M) (E₃.subgroupOf E)
  E₁₂_hall : Ch03.IsHallSubgroup (tau1 M ∪ tau2 M) ((E₁ ⊔ E₂).subgroupOf E)

namespace SubgroupESetup

variable {M E E₁ E₂ E₃ : Subgroup G}

theorem E_complement (h : SubgroupESetup M E E₁ E₂ E₃) :
    S10.Msigma M ⊓ E = ⊥ ∧ S10.Msigma M ⊔ E = M :=
  ⟨h.E_compl_inf, h.E_compl_sup⟩

theorem E1_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₁ ≤ M :=
  h.E₁_le.trans h.E_le

theorem E2_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₂ ≤ M :=
  h.E₂_le.trans h.E_le

theorem E3_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₃ ≤ M :=
  h.E₃_le.trans h.E_le

theorem E12_le_E (h : SubgroupESetup M E E₁ E₂ E₃) : E12 E₁ E₂ ≤ E :=
  sup_le h.E₁_le h.E₂_le

theorem E23_le_E (h : SubgroupESetup M E E₁ E₂ E₃) : E23 E₂ E₃ ≤ E :=
  sup_le h.E₂_le h.E₃_le

theorem E123_le_E (h : SubgroupESetup M E E₁ E₂ E₃) : E123 E₁ E₂ E₃ ≤ E :=
  sup_le (sup_le h.E₁_le h.E₂_le) h.E₃_le

theorem E12_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E12 E₁ E₂ ≤ M :=
  (h.E12_le_E).trans h.E_le

theorem E23_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E23 E₂ E₃ ≤ M :=
  (h.E23_le_E).trans h.E_le

/-! ### Complement bookkeeping: `E ≅ M/M_σ`, `π(E) ⊆ σ(M)'`, `r(E) ≤ 2` -/

section Basic

variable [Finite G]

omit [Finite G] in
/-- `M_σ` and `E` are complements inside `↥M` (internal form of `M = M_σ E`,
`M_σ ∩ E = 1`; `M_σ ⊴ M` makes the disjoint join a genuine complement). -/
theorem isComplement'_subgroupOf (h : SubgroupESetup M E E₁ E₂ E₃) :
    ((S10.Msigma M).subgroupOf M).IsComplement' (E.subgroupOf M) := by
  haveI : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    have hinf : (S10.Msigma M).subgroupOf M ⊓ E.subgroupOf M
        = (S10.Msigma M ⊓ E).subgroupOf M := rfl
    rw [hinf, h.E_compl_inf, Subgroup.bot_subgroupOf]
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup (S10.Msigma_le M) h.E_le,
      h.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]

omit [Finite G] in
/-- `|M_σ| · |E| = |M|`. -/
theorem card_Msigma_mul_card_E (h : SubgroupESetup M E E₁ E₂ E₃) :
    Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
  have hc := h.isComplement'_subgroupOf.card_mul
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at hc

/-- `E` is a `σ(M)'`-group: `|E|` equals the index of the Hall subgroup `M_σ` in `M`. -/
theorem isPiGroup_sigma_compl (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (S10.sigma M)ᶜ E := by
  intro p hp
  have hidx : ((S10.Msigma M).subgroupOf M).index = Nat.card ↥E := by
    rw [h.isComplement'_subgroupOf.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv]
  have hHall := S10.Msigma_subgroupOf_isHall_of_isHall
    (S10.isHall_Msigma_Malpha hG h.mem_maximal).1
  exact hHall.2 p (by rwa [hidx])

/-- No prime divisor of `|E|` lies in `σ(M)`. -/
theorem not_mem_sigma_of_mem_primeFactors (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ}
    (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∉ S10.sigma M :=
  h.isPiGroup_sigma_compl hG p hp

/-- Prime divisors of `|E|` have `r_p(M) ≤ 2` (they avoid `α(M) ⊆ σ(M)`). -/
theorem pRank_M_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : pRank ↥M p ≤ 2 := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_contra hcon
  have hpM : p ∈ (Nat.card ↥M).primeFactors := by
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hprime, hp.2.1.trans (Subgroup.card_dvd_of_le h.E_le), Nat.card_pos.ne'⟩
  exact h.not_mem_sigma_of_mem_primeFactors hG hp
    (S10.alpha_subset_sigma hG h.mem_maximal
      ((S10.mem_alpha_iff M p).mpr ⟨hpM, by omega⟩))

/-- `r_p(E) ≤ 2` for every prime `p`. -/
theorem pRank_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) : pRank ↥E p ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E).primeFactors
  · exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le))
      (h.pRank_M_le_two hG hpE)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- `r(E) ≤ 2` (BG: `π(E) ∩ α(M) = ∅`, mmd L3032). -/
theorem rank_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃) :
    rank ↥E ≤ 2 :=
  rank_le_iff.mpr fun _ hp => h.pRank_le_two hG hp

/-- **BG (12.1)** (mmd L3032): the prime divisors of `|E|` are partitioned by
`τ₁(M) ∪ τ₂(M) ∪ τ₃(M)`. -/
theorem mem_tau_union_of_mem_primeFactors (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ}
    (hp : p ∈ (Nat.card ↥E).primeFactors) :
    p ∈ tau1 M ∪ tau2 M ∪ tau3 M := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hprime⟩
  have hσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hp
  have h1M : 1 ≤ pRank ↥M p :=
    (one_le_pRank_of_mem_primeFactors hp).trans
      (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le))
  have h2M : pRank ↥M p ≤ 2 := h.pRank_M_le_two hG hp
  by_cases hr2 : pRank ↥M p = 2
  · exact Or.inl (Or.inr ⟨hσ, hr2⟩)
  · have hr1 : pRank ↥M p = 1 := by omega
    by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
    · exact Or.inr ⟨hσ, hM', hr1⟩
    · exact Or.inl (Or.inl ⟨hσ, hM', hr1⟩)

end Basic

end SubgroupESetup

/-! ## Lemma 12.1 — `E` の構造の易しい帰結 (mmd L3035) -/

/-- **BG Lemma 12.1(g)** (mmd L3060, = Lemma 10.4(c) at the `τ₂` interface): for a prime
`p ∈ τ₂(M)` and `A ∈ ℰ_p²(M)` with `A ≤ M`, the subgroup `A` is maximal elementary
abelian in `G` and `p` is not an ideal prime. Direct application of `alpha_criterion`. -/
theorem isMaximalElementaryAbelian_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} (hprime : p.Prime)
    (hp : p ∈ tau2 M) {A : Subgroup G} (hAM : A ≤ M) (hA : A ∈ elemAbelianOfRank G p 2) :
    IsMaximalElementaryAbelian p A ∧ ¬ S10.idealPrime p G := by
  obtain ⟨hideal, hmax⟩ := (S10.alpha_criterion hG hM).2 p hprime hp.1 hp.2
  exact ⟨hmax A hAM hA, hideal⟩

/-- **BG Lemma 12.1(a)** (mmd L3037): `E'` is nilpotent.

原文は Thm 10.2 の「`M'/M_σ` nilpotent」から導くが、repo は商型を経由せず
Thm 4.20(a) (`derived_le_fitting_of_rank_fitting_le_two`) を `E` に直接適用する:
`E` は `σ(M)'`-群ゆえ `r(E) ≤ 2` (`SubgroupESetup.rank_le_two`)、従って
`E' ≤ F(E)` は冪零部分群。 -/
theorem SubgroupESetup.derived_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Group.IsNilpotent ↥(derivedInG E) := by
  by_cases hE : E = ⊥
  · have hbot : derivedInG E = ⊥ := by
      rw [hE]
      exact le_bot_iff.mp (Subgroup.map_subtype_le _)
    rw [hbot]
    infer_instance
  · haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
    haveI : IsSolvable ↥E := solvable_of_solvable_injective (Subgroup.inclusion_injective h.E_le)
    haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot _).mpr hE
    have hodd : Odd (Nat.card ↥E) :=
      hG.odd.of_dvd_nat
        ((Subgroup.card_dvd_of_le h.E_le).trans (Subgroup.card_subgroup_dvd_card M))
    have hrankF : rank ↥(Ch01.fitting ↥E) ≤ 2 :=
      le_trans (rank_le_of_injective (Subgroup.subtype_injective (Ch01.fitting ↥E)))
        (h.rank_le_two hG)
    have hderived : commutator ↥E ≤ Ch01.fitting ↥E :=
      Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hodd hrankF
    haveI : Group.IsNilpotent ↥(commutator ↥E) :=
      nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hderived)
    exact nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥E) E.subtype (Subgroup.subtype_injective E))

/-- **BG Lemma 12.1** (mmd L3035): §12 setup のもと、
(a) `E'` nilpotent; (b) `E₃ ⊆ E'` かつ `E₃ ⊴ E`; (c) `E₂=1 → E₁≠1`; (d) `E₁`,`E₃` cyclic;
(e) `E=E₁E₂E₃`, `E₂E₃⊴E`, `E₂⊴E₁₂`; (f) `C_{E₃}(E)=1`;
(g) 素数 `p∈τ₂(M)`, `A∈ℰ_p²(M)` ⇒ `A∈ℰ_p*(G)` かつ `p` は ideal でない (⇒ `p∉β(G)`)。
((g) の `p.Prime` は原典の暗黙仮定 (τ₂ ⊆ π(M)); repo の `tau2` は素数性を含まないため明示。) -/
theorem subgroupE_basic [Finite G] (hG : IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    Group.IsNilpotent ↥(derivedInG E) ∧
    (E₃ ≤ derivedInG E ∧ E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G)) ∧
    (E₂ = ⊥ → E₁ ≠ ⊥) ∧
    (IsCyclic ↥E₁ ∧ IsCyclic ↥E₃) ∧
    (E = E₁ ⊔ E₂ ⊔ E₃ ∧
      E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      (E₁ ⊔ E₂ : Subgroup G) ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G)) ∧
    Subgroup.centralizer (E : Set G) ⊓ E₃ = ⊥ ∧
    (∀ p : ℕ, p.Prime → p ∈ tau2 M → ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
      IsMaximalElementaryAbelian p A ∧ ¬ S10.idealPrime p G) := by
  sorry

/-! ## §12 追加結果 (clean core; 多部分の一部は後続) -/

/-- **BG Lemma 12.2(a)** (mmd L3062): `X` を `M` の非自明 `p`-部分群、`M* ∈ ℳ(N_G(X))` とすると
`p ∈ σ(M*) ∪ τ₂(M*)`。(原典 (b) の τ₁∪τ₃ 非共役は後続。) -/
theorem prime_mem_sigma_or_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXp : IsPGroup p ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    p ∈ S10.sigma Mstar ∨ p ∈ tau2 Mstar := by
  sorry

/-- **BG Proposition 12.4(a)** (mmd L3095): `A ∈ ℰ_p²(M)` なら `C_G(A) ⊆ M`。
(原典 (b): `N_G(A₀)` の uniqueness ⇒ `p∈σ(M), M_α=1, M_σ` nilpotent は後続。) -/
theorem centralizer_le_of_elemAb_rank_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  sorry

/-- **BG Theorem 12.13** (mmd L3347): `G` のすべての非可換 `p`-部分群は `𝒰` に属す。 -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative P) :
    IsUniquelyMaximal P := by
  sorry

/-- **BG Corollary 12.14** (mmd L3369): `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`、`p ∈ β(M)` または
`X ⊆ M_σ'` なら `ℳ(C_G(X)) = {M}`。 -/
theorem maximalContaining_centralizer_eq_singleton [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ S10.sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXM : X ≤ M)
    (hcase : p ∈ S10.beta M ∨ X ≤ derivedInG (S10.Msigma M)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  sorry

/-- **BG Corollary 12.16(a)** (mmd L3423): `M` の `σ(M)`-部分群 `Y` は `M_σ` に共役で写せる
(`∃ g ∈ M, Y^g ⊆ M_σ`)。(原典 (b) の rank/derived 評価は後続。) -/
theorem sigma_subgroup_conj_into_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y) :
    ∃ g ∈ M, MulAut.conj g • Y ≤ S10.Msigma M := by
  sorry

/-- **BG Lemma 12.17** (mmd L3448): `C_{M_σ}(E) ⊆ M_σ'` かつ `[M_σ, E] = M_σ`。
(原典の `M_σ ∩ M^g` cyclic 評価は後続。) -/
theorem Msigma_E_relations [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Subgroup.centralizer (E : Set G) ⊓ S10.Msigma M ≤ derivedInG (S10.Msigma M) ∧
    ⁅S10.Msigma M, E⁆ = S10.Msigma M := by
  sorry

/-- **BG Lemma 12.3** (mmd L3071): `M, M* ∈ ℳ`, `A ∈ ℰ_p²(M ∩ M*)`, `A₀ ∈ ℰ_p¹` (`A₀ ⊆ A`),
`N_G(A₀) ⊆ M*` なら `A` は `M_σ ∩ M*` と `M_α ∩ M*` を中心化する。 -/
theorem elemAb_centralizes_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] {A A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M ⊓ Mstar) (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) ∧
    A ≤ Subgroup.centralizer ((S10.Malpha M ⊓ Mstar : Subgroup G) : Set G) := by
  sorry

/-- **BG Lemma 12.19** (mmd L3480): `E'` は `M_σ` の Hall `β(M)'`-部分群を中心化する。 -/
theorem derivedE_centralizes_betaComplement [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    ∃ W : Subgroup G, W ≤ S10.Msigma M ∧
      Ch03.IsHallSubgroup (S10.beta M)ᶜ (W.subgroupOf (S10.Msigma M)) ∧
      derivedInG E ≤ Subgroup.centralizer (W : Set G) := by
  sorry

/-! ## §12 τ₂(M) ≠ ∅ の場合 (mmd L3129-3344) — 最複雑 subsection -/

/-- **BG Theorem 12.5** (mmd L3129): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(M)` のとき
(a) `M_σ` nilpotent; (b) `M` は abelian Sylow `p` を持ち、`A` を含む Sylow `p`-部分群 `P` で
`N_G(P) ⊄ M`; (c) `M_σA ⊴ M`; (d) `C_{M_σ}(A)=1`; (e) `M^* ∈ ℳ(A)-{M}` で `M_σ ∩ M^* = 1`;
(f) `∃ A₁ ∈ ℰ¹(A)` で `C_{M_σ}(A₁)=1`。
(原典 (b) の `Ω₁(P)=A` は Omega の入れ子のため docstring で defer。) -/
theorem Msigma_nilpotent_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Group.IsNilpotent ↥(S10.Msigma M) ∧
    ((∀ P : Sylow p ↥M, IsMulCommutative (P : Subgroup ↥M)) ∧
      ∃ P : Subgroup G, P ≤ M ∧ IsPGroup p ↥P ∧ A ≤ P ∧
        (∀ T : Subgroup G, T ≤ M → IsPGroup p ↥T → P ≤ T → P = T) ∧
        ¬ (Subgroup.normalizer (P : Set G) ≤ M)) ∧
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) ∧
    S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
    (∀ Mstar ∈ maximalSubgroupsContaining A, Mstar ≠ M → S10.Msigma M ⊓ Mstar = ⊥) ∧
    (∃ A₁ ∈ elemAbelianOfRank G p 1, A₁ ≤ A ∧
      S10.Msigma M ⊓ Subgroup.centralizer (A₁ : Set G) = ⊥) := by
  sorry

/-- **BG Corollary 12.6** (mmd L3150): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` のとき
(a) `A ⊴ E` かつ `ℰ_p¹(E)=ℰ¹(A)`; (b) `C_G(A) ⊆ N_M(A)=E`, `N_G(A) ⊄ M`;
(c) `X ∈ ℰ¹(A)` で `C_{M_σ}(X)≠1` なら `ℳ(C_G(X))={M}`; (d) `x ∈ E₃#` で `C_{M_σ}(x)=1`;
(e) `x ∈ C_{E₁}(A)#` で `C_{M_σ}(x)=1`; (f) `M^*` が `M` と非共役なら `M_σ ∩ M^*_σ = 1` かつ
`σ(M) ∩ σ(M^*) = ∅`。 -/
theorem elemAb_normal_in_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    (E ≤ Subgroup.normalizer (A : Set G) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E ↔ X ≤ A)) ∧
    (Subgroup.centralizer (A : Set G) ≤ E ∧
      M ⊓ Subgroup.normalizer (A : Set G) = E ∧ ¬ (Subgroup.normalizer (A : Set G) ≤ M)) ∧
    (∀ X ∈ elemAbelianOfRank G p 1, X ≤ A →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
    (∀ x ∈ E₃, x ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ x ∈ E₁, x ∈ Subgroup.centralizer (A : Set G) → x ≠ 1 →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ Mstar ∈ maximalSubgroups G, (¬ ∃ g : G, MulAut.conj g • M = Mstar) →
      S10.Msigma M ⊓ S10.Msigma Mstar = ⊥ ∧ Disjoint (S10.sigma M) (S10.sigma Mstar)) := by
  sorry

/-- **BG Theorem 12.7** (mmd L3171): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `G` が非可換 Sylow `p` を持つとき
(a) `τ₂(M)={p}`; (b) `A₀=C_A(M_σ)` は位数 `p` で `F(M)=M_σ × A₀`; (c) `X ∈ ℰ_p¹(E)-{A₀}` で
`C_{M_σ}(X)=1` かつ `C_G(X) ⊄ M`; (d) `A₀` は `E` 内に補群 `E₀`; (e) `x ∈ M_σ#` で
`π(C_{E₀}(x)) ⊆ τ₁(M)`。(内部直積 `F(M)=M_σ×A₀` は join + 自明交叉で表現。) -/
theorem tau2_singleton_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G)) :
    tau2 M = {p} ∧
    (∃ A₀ : Subgroup G, A₀ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      Nat.card ↥A₀ = p ∧
      (Ch2.S08.fittingInG M = S10.Msigma M ⊔ A₀ ∧ S10.Msigma M ⊓ A₀ = ⊥) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
        S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        ¬ (Subgroup.centralizer (X : Set G) ≤ M)) ∧
      (∃ E₀ : Subgroup G, E₀ ≤ E ∧ A₀ ⊓ E₀ = ⊥ ∧ A₀ ⊔ E₀ = E ∧
        ∀ x ∈ S10.Msigma M, x ≠ 1 →
          ∀ r ∈ (Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G))).primeFactors,
            r ∈ tau1 M)) := by
  sorry

/-- **BG Lemma 12.8** (mmd L3223): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `S` を `A` を含む `G` の Sylow
`p`-部分群とし `S` abelian とする。(a) `E₂` abelian normal in `E`; (b) `E₂` は `G` の Hall
`τ₂(M)`-部分群; (c) `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E`; (d) 正規化子の鎖の等式;
(e) `X ∈ ℰ¹(E₁)` で `C_{M_σ}(X)=1` なら `X ⊆ Z(E)`; (f) `X ≤ N_G(S)` で `C_S(X), [S,X] ⊴ N_G(S)`。 -/
theorem E2_abelian_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (S : Sylow p G) (hAS : A ≤ (S : Subgroup G)) (hSab : IsMulCommutative (S : Subgroup G)) :
    (IsMulCommutative ↥E₂ ∧ E ≤ Subgroup.normalizer (E₂ : Set G)) ∧
    Ch03.IsHallSubgroup (tau2 M) E₂ ∧
    ((S : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤ Ch2.S08.fittingInG E ∧
      Ch2.S08.fittingInG E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E) ∧
    (Subgroup.normalizer (A : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) = Subgroup.normalizer (E₂ : Set G) ∧
      Subgroup.normalizer (E₂ : Set G) = Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) =
        Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G)) ∧
    (∀ X : Subgroup G, (∃ q : ℕ, q.Prime ∧ X ∈ elemAbelianOfRank G q 1) → X ≤ E₁ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      X ≤ E ∧ E ≤ Subgroup.centralizer (X : Set G)) ∧
    (∀ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer (((S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G)) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G)) := by
  sorry

/-- **BG Corollary 12.9** (mmd L3260): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `q ∈ τ₁(M)`, `Q ∈ ℰ_q¹(E)`,
`C_{M_σ}(Q)=1`, `[A,Q]≠1` のとき `A₀=[A,Q]`, `A₁=C_A(Q)` で
(a) `A₀ ∈ ℰ¹(A)` かつ `A₀=C_A(M_σ) ⊴ M`; (b) `A₀` は `A₁` と `G` 内で非共役; (c) `A₁ ∈ ℰ¹(A)` かつ
`C_G(A₁) ⊄ M`。 -/
theorem commutator_decomp_of_tau1_action [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau2 M) (hq : q ∈ tau1 M)
    {A Q : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hCQ : S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥) (hAQ : ⁅A, Q⁆ ≠ ⊥) :
    (⁅A, Q⁆ ∈ elemAbelianOfRank G p 1 ∧ ⁅A, Q⁆ ≤ A ∧
      ⁅A, Q⁆ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer ((⁅A, Q⁆ : Subgroup G) : Set G)) ∧
    (¬ ∃ g : G, MulAut.conj g • (⁅A, Q⁆ : Subgroup G) = A ⊓ Subgroup.centralizer (Q : Set G)) ∧
    ((A ⊓ Subgroup.centralizer (Q : Set G)) ∈ elemAbelianOfRank G p 1 ∧
      (A ⊓ Subgroup.centralizer (Q : Set G)) ≤ A ∧
      ¬ (Subgroup.centralizer ((A ⊓ Subgroup.centralizer (Q : Set G)) : Set G) ≤ M)) := by
  sorry

/-- **BG Corollary 12.10** (mmd L3270): (a) `M` の nilpotent `σ(M)'`-部分群は abelian;
(b) `E₂` と `E'` は abelian; (c) `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` で `E₂E₃ ⊆ C_E(A) ⊴ E` かつ
`π(E/C_E(A)) ⊆ τ₁(M)`; (d) `p ∈ σ(M)`, `P` noncyclic `p`-部分群 ⇒ `N_G(P) ⊆ M`;
(e) `x ∈ M#`, `π(⟨x⟩) ⊆ τ₂(M)`, `C_{M_σ}(x)≠1` ⇒ `ℳ(C_G(x))={M}`。 -/
theorem nilpotent_sigmaComplement_abelian [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ N : Subgroup G, N ≤ M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) N →
      Group.IsNilpotent ↥N → IsMulCommutative ↥N) ∧
    (IsMulCommutative ↥E₂ ∧ IsMulCommutative ↥(derivedInG E)) ∧
    (∀ p : ℕ, p ∈ tau2 M → ∀ A ∈ elemAbelianOfRank G p 2, A ≤ E →
      E₂ ⊔ E₃ ≤ E ⊓ Subgroup.centralizer (A : Set G) ∧
      E ≤ Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ∧
      ∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
        r ∈ tau1 M) ∧
    (∀ p : ℕ, p ∈ S10.sigma M → ∀ P : Subgroup G, P ≤ M → IsPGroup p ↥P →
      ¬ IsCyclic ↥P → Subgroup.normalizer (P : Set G) ≤ M) ∧
    (∀ x ∈ M, x ≠ 1 → (∀ r ∈ (orderOf x).primeFactors, r ∈ tau2 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {M}) := by
  sorry

/-- **BG Lemma 12.11** (mmd L3284): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M^* ∈ ℳ(N_G(A))` のとき
(a) `τ₂(M) ⊆ σ(M^*) - β(M^*)`; (b) `π(E/C_E(A)) ⊆ τ₁(M^*) ∪ τ₂(M^*)`;
(c) `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` なら `q ∈ τ₂(M^*)`, `G` の Sylow `p` が `M^*` で正規,
`M^*` は `G` の abelian Sylow `q` を含む。 -/
theorem tau2_transfer_to_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    tau2 M ⊆ S10.sigma Mstar \ S10.beta Mstar ∧
    (∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
      r ∈ tau1 Mstar ∪ tau2 Mstar) ∧
    (∀ q : ℕ, q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors →
      q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors →
      q ∈ tau2 Mstar ∧
      (∃ P : Sylow p G, Mstar ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      (∃ Q : Sylow q G, (Q : Subgroup G) ≤ Mstar ∧ IsMulCommutative (Q : Subgroup G))) := by
  sorry

/-- **BG Theorem 12.12** (mmd L3306): すべての `(τ₁(M)∪τ₃(M))`-元 `e ∈ E#` で `C_{M_σ}(e)=1`
なら (a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の `E₀` を含み `E₀M_σ` は kernel `M_σ` の Frobenius 群。 -/
theorem frobenius_factorization_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    (∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
      E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
      ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀) ∧
    (∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent ↥E₀ = Monoid.exponent ↥E ∧
      Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
        ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
        (E₀.subgroupOf (S10.Msigma M ⊔ E₀))) := by
  sorry

/-! ## §12 σ(M) の埋め込みと一意性 (mmd L3385-3479) -/

/-- **BG Proposition 12.15** (mmd L3387): `q ∈ σ(M)`, `X` を `M` の非自明 `q`-部分群、
`M* ∈ ℳ(N_G(X)) - {M}`、`S` を `X` を含む `M ∩ M*` の Sylow `q`-部分群とすると
(a) `M*` は `M` と非共役; (b) `N_G(S) ⊆ M`; (c) `S` は `M*` の Sylow `q`;
(d) `q ∈ σ(M*)` なら `M*=(M∩M*)M*_β`, `τ₁(M*)⊆τ₁(M)∪α(M)`, `M_β=M_α≠1`;
(e) `q ∉ σ(M*)` なら `q ∈ τ₂(M*)`, `π(M)∩σ(M*)⊆β(M*)`, `M∩M*` は `M*_σ` の補群。 -/
theorem sigma_subgroup_maximal_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstarne : Mstar ≠ M) {S : Subgroup G} (hSle : S ≤ M ⊓ Mstar) (hXS : X ≤ S)
    (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T) :
    (¬ ∃ g : G, MulAut.conj g • M = Mstar) ∧
    Subgroup.normalizer (S : Set G) ≤ M ∧
    (∀ T : Subgroup G, T ≤ Mstar → IsPGroup q ↥T → S ≤ T → S = T) ∧
    (q ∈ S10.sigma Mstar →
      Mstar = (M ⊓ Mstar) ⊔ S10.Mbeta Mstar ∧
      tau1 Mstar ⊆ tau1 M ∪ S10.alpha M ∧
      S10.Mbeta M = S10.Malpha M ∧ S10.Malpha M ≠ ⊥) ∧
    (q ∉ S10.sigma Mstar →
      q ∈ tau2 Mstar ∧
      (∀ r ∈ (Nat.card ↥M).primeFactors, r ∈ S10.sigma Mstar → r ∈ S10.beta Mstar) ∧
      S10.Msigma Mstar ⊓ (M ⊓ Mstar) = ⊥ ∧ S10.Msigma Mstar ⊔ (M ⊓ Mstar) = Mstar) := by
  sorry

/-- **BG Lemma 12.18** (mmd L3454): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, `q ∈ p'`, `Q` を `M` の非自明
`P`-不変 `q`-部分群で `C_Q(P)=1`, `ℳ(N_G(Q))≠{M}` とすると
(a) `M_α≠1` かつ `q∉α(M)` なら `C_{M_α}(P)≠1` かつ `C_{M_α}(PQ)=1`;
(b) `Q` が `M` の Sylow `q` なら `α(M)=β(M)` で (a) の状況が成立。 -/
theorem tau1_Malpha_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQP : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M}) :
    (S10.Malpha M ≠ ⊥ → q ∉ S10.alpha M →
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) ∧
    ((∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T) →
      S10.alpha M = S10.beta M ∧ S10.Malpha M ≠ ⊥ ∧ q ∉ S10.alpha M ∧
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) := by
  sorry

end OddOrder.BG.Ch3.S12
