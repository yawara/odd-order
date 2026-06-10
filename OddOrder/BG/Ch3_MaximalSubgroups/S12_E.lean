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

/-- `⁅H, H⁆ ≤ H`: self-commutators stay inside the subgroup. -/
private theorem commutator_self_le {Γ : Type*} [Group Γ] (H : Subgroup Γ) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg₁ hg₂) (H.inv_mem hg₁)) (H.inv_mem hg₂)

/-! ### Conjugation-action bridges

`Prop 1.6(d)` (`fixedPoints_isComplement_actionCommutator_of_abelian`) is stated for an
abstract action `φ : A →* MulAut G`. The two bridges below identify, for the conjugation
action of `K ≤ N_Γ(P)` on `P`, the action commutator with the ambient subgroup commutator
`⁅P, K⁆` and the fixed points with `C_Γ(K) ⊓ P`. Used in Lemma 12.1(f). -/

section ConjugationBridges

variable {Γ : Type*} [Group Γ]

/-- Push-forward of the conjugation-action commutator: for `K ≤ N_Γ(P)`, the
`actionCommutator` of the conjugation action of `K` on `P` realizes the ambient
subgroup commutator `⁅P, K⁆`. -/
theorem actionCommutator_conj_map_subtype {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Ch04.actionCommutator
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype
      = ⁅P, K⁆ := by
  rw [Ch04.actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(g : Γ), g.2, (a : Γ), a.2, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          (g * ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) a g⁻¹) : Γ)
        = (g : Γ) * ((a : Γ) * (g : Γ)⁻¹ * (a : Γ)⁻¹) := rfl
    rw [hcoe]
    group
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨(⟨g, hg⟩ : ↥P) *
      ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩ ⟨g, hg⟩⁻¹,
      ⟨⟨g, hg⟩, ⟨a, ha⟩, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          ((⟨g, hg⟩ : ↥P) *
            ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩
              (⟨g, hg⟩ : ↥P)⁻¹) : Γ)
        = g * (a * g⁻¹ * a⁻¹) := rfl
    rw [hcoe]
    group

/-- Push-forward of the conjugation-action fixed points: `C_Γ(K) ⊓ P`. -/
theorem fixedPointsOfMulAut_conj_map_subtype {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype
      = Subgroup.centralizer (K : Set Γ) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun k hk => ?_, x.2⟩
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨k, hk⟩
    have hcoe : k * (x : Γ) * k⁻¹ = (x : Γ) := congrArg Subtype.val hfix
    calc k * (x : Γ) = (k * x * k⁻¹) * k := by group
    _ = (x : Γ) * k := by rw [hcoe]
  · rintro ⟨hy, hyP⟩
    refine ⟨⟨y, hyP⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun a => Subtype.ext ?_, rfl⟩
    show (a : Γ) * y * (a : Γ)⁻¹ = y
    rw [hy (a : Γ) a.2]
    group

end ConjugationBridges

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

omit [Finite G] in
/-- **BG (12.1) 直前の `E ∩ M' = E'`、`≤` 方向** (mmd L3032): the complement meets the
derived subgroup of `M` exactly in its own derived subgroup. Proof: pass to
`M/M_σ`; the complement maps isomorphically onto the quotient, whose commutator
subgroup is the image of both `commutator M` and `⁅E, E⁆`. -/
theorem inf_derivedInG_le_derivedInG (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ⊓ derivedInG M ≤ derivedInG E := by
  classical
  intro x hx
  have hxM : x ∈ M := h.E_le hx.1
  set Nσ : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNσ
  haveI : Nσ.Normal := by rw [hNσ, S10.Msigma_subgroupOf]; infer_instance
  set π : ↥M →* ↥M ⧸ Nσ := QuotientGroup.mk' Nσ with hπ
  -- the complement surjects onto the quotient
  have hEtop : (E.subgroupOf M).map π = ⊤ := by
    have h1 : Nσ ⊔ E.subgroupOf M = ⊤ := h.isComplement'_subgroupOf.sup_eq_top
    have h2 := congrArg (Subgroup.map π) h1
    have hNbot : Nσ.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨n, hn, rfl⟩
      rw [Subgroup.mem_bot, hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    rw [Subgroup.map_sup, hNbot, bot_sup_eq] at h2
    rw [h2, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Nσ)
  -- `commutator ↥M` and `⁅E', E'⁆` have the same image in the quotient
  have hcq : Subgroup.map π (commutator ↥M)
      = Subgroup.map π ⁅E.subgroupOf M, E.subgroupOf M⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_commutator, hEtop,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Nσ)]
  -- lift `x` to `commutator ↥M`
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ commutator ↥M := by
    obtain ⟨c, hc, hcx⟩ := hx.2
    have hxc : (⟨x, hxM⟩ : ↥M) = c := Subtype.ext hcx.symm
    rwa [hxc]
  have hmem : π ⟨x, hxM⟩ ∈ Subgroup.map π ⁅E.subgroupOf M, E.subgroupOf M⁆ := by
    rw [← hcq]
    exact ⟨_, hx', rfl⟩
  obtain ⟨c, hc, hcx⟩ := hmem
  -- the difference lies in `N_σ ⊓ E = ⊥`
  have heq : (⟨x, hxM⟩ : ↥M) = c := by
    have hker : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ Nσ := by
      have : π ((⟨x, hxM⟩ : ↥M) * c⁻¹) = 1 := by
        rw [map_mul, map_inv, hcx, mul_inv_cancel]
      rwa [← QuotientGroup.ker_mk' Nσ, MonoidHom.mem_ker]
    have hcE : c ∈ E.subgroupOf M := commutator_self_le (E.subgroupOf M) hc
    have hEmem : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ E.subgroupOf M :=
      mul_mem (Subgroup.mem_subgroupOf.mpr hx.1) (inv_mem hcE)
    have hbot : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ Nσ ⊓ E.subgroupOf M := ⟨hker, hEmem⟩
    rw [disjoint_iff.mp h.isComplement'_subgroupOf.disjoint, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot
  -- push back to the ambient group
  have hfinal : x ∈ (⁅E.subgroupOf M, E.subgroupOf M⁆).map M.subtype :=
    ⟨c, hc, by rw [← heq]; rfl⟩
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.E_le] at hfinal
  have hd : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
  rwa [hd]

/-- For `p ∈ τ₃(M)`, the prime `p` divides `|E'|` (mmd L3032: `p ∈ π(E')`):
`M' ≤ M_σ (E ⊓ M')` and `p ∤ |M_σ|`, so `p` survives into `E ⊓ M' ≤ E'`. -/
theorem dvd_card_derived_of_mem_tau3 (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} (hprime : p.Prime) (hp : p ∈ tau3 M) :
    p ∣ Nat.card ↥(derivedInG E) := by
  classical
  -- the derived subgroup factorizes through `M_σ` and `E ⊓ M'`
  have hfact : commutator ↥M ≤
      (S10.Msigma M).subgroupOf M ⊔ ((E ⊓ derivedInG M).subgroupOf M) := by
    intro x hxcomm
    obtain ⟨⟨s, e⟩, hse, -⟩ := h.isComplement'_subgroupOf.existsUnique x
    have hxse : (s : ↥M) * (e : ↥M) = x := hse
    have hsM' : (s : ↥M) ∈ commutator ↥M := by
      have hσle : (S10.Msigma M).subgroupOf M ≤ (derivedInG M).subgroupOf M :=
        Subgroup.subgroupOf_mono M (S10.Msigma_le_derived hG h.mem_maximal)
      have hD : (derivedInG M).subgroupOf M = commutator ↥M := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)]
      exact hD ▸ hσle s.2
    have heE : (e : ↥M) ∈ (E ⊓ derivedInG M).subgroupOf M := by
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp e.2
      · -- `e = s⁻¹ x ∈ commutator`, then push along the subtype
        have hecomm : (e : ↥M) ∈ commutator ↥M := by
          have he : (e : ↥M) = (s : ↥M)⁻¹ * x := by
            rw [← hxse]; group
          rw [he]
          exact mul_mem (inv_mem hsM') hxcomm
        exact (⟨_, hecomm, rfl⟩ : ((e : ↥M) : G) ∈ (commutator ↥M).map M.subtype)
    rw [← hxse]
    exact mul_mem (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right heE)
  -- count: `p ∣ |M'|`, `p ∤ |M_σ|`, hence `p ∣ |E ⊓ M'|`
  have hpM' : p ∣ Nat.card ↥(commutator ↥M) := by
    have hcardeq : Nat.card ↥(derivedInG M) = Nat.card ↥(commutator ↥M) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype
        (Subgroup.subtype_injective M)).toEquiv).symm
    have := Nat.dvd_of_mem_primeFactors hp.2.1
    rwa [hcardeq] at this
  haveI : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hsupcard : Nat.card ↥((S10.Msigma M).subgroupOf M ⊔ (E ⊓ derivedInG M).subgroupOf M)
      ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) *
        Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) := by
    have hmul := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
      ((S10.Msigma M).subgroupOf M) ((E ⊓ derivedInG M).subgroupOf M)
    rw [← Subgroup.normal_mul] at hmul
    exact ⟨_, hmul.symm⟩
  have hdvd1 : p ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) *
      Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) :=
    dvd_trans (hpM'.trans (Subgroup.card_dvd_of_le hfact)) hsupcard
  have hpσ : ¬ p ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) := by
    intro hcon
    have hcard : Nat.card ↥((S10.Msigma M).subgroupOf M) = Nat.card ↥(S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv
    rw [hcard] at hcon
    exact hp.1 (S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hprime, hcon, Nat.card_pos.ne'⟩))
  have hdvd2 : p ∣ Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) :=
    (hprime.dvd_mul.mp hdvd1).resolve_left hpσ
  have hcard2 : Nat.card ↥((E ⊓ derivedInG M).subgroupOf M)
      = Nat.card ↥(E ⊓ derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h.E_le)).toEquiv
  rw [hcard2] at hdvd2
  exact hdvd2.trans (Subgroup.card_dvd_of_le (h.inf_derivedInG_le_derivedInG))

omit [Finite G] in
/-- `E₁` is a `τ₁(M)`-group. -/
theorem isPiGroup_tau1 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau1 M) E₁ := fun p hp =>
  h.E₁_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv])

omit [Finite G] in
/-- `E₂` is a `τ₂(M)`-group. -/
theorem isPiGroup_tau2 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau2 M) E₂ := fun p hp =>
  h.E₂_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv])

omit [Finite G] in
/-- `E₃` is a `τ₃(M)`-group. -/
theorem isPiGroup_tau3 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau3 M) E₃ := fun p hp =>
  h.E₃_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv])

end Basic

end SubgroupESetup

/-- An odd finite nilpotent group with `pRank ≤ 1` at every prime is cyclic: each Sylow
subgroup is cyclic (converse of BG Lemma 4.5 at odd primes, trivial Sylow at `2`), so the
group is a nilpotent Z-group. Packages the `E₁`/`E₃` cyclicity argument of Lemma 12.1(d). -/
theorem isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] (hodd : Odd (Nat.card H))
    (hrank : ∀ p : ℕ, p.Prime → pRank H p ≤ 1) : IsCyclic H := by
  haveI : IsZGroup H := by
    rw [isZGroup_iff]
    intro r hr R
    haveI : Fact r.Prime := ⟨hr⟩
    rcases eq_or_ne r 2 with rfl | hrne
    · -- `|H|` is odd, so the Sylow `2`-subgroup is trivial.
      have h2 : ¬ 2 ∣ Nat.card H := by
        rw [Nat.odd_iff] at hodd
        omega
      have hR1 : Nat.card ↥(R : Subgroup H) = 1 := by
        obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simpa using hk
        · exact absurd ((dvd_pow_self 2 hkpos.ne').trans
            (hk ▸ (R : Subgroup H).card_subgroup_dvd_card)) h2
      haveI : Subsingleton ↥(R : Subgroup H) := (Nat.card_eq_one_iff_unique.mp hR1).1
      infer_instance
    · exact S10.isCyclic_of_pRank_le_one R.isPGroup' (hr.odd_of_ne_two hrne)
        (le_trans (pRank_le_of_injective (Subgroup.subtype_injective _)) (hrank r hr))
  infer_instance

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

/-- **Per-prime core of Lemma 12.1(b)/(f)** (mmd L3041-3055): for `p ∈ τ₃(M)` and a Sylow
`p`-subgroup `P` of `E`, the ambient image of `P` lies in `E'` and meets `C_G(E)` trivially.

BG's Frattini argument is reorganized around Burnside: let `W = N_E(P)` and let `K` be a
complement of `P` in `W` (Schur–Zassenhaus). By the cyclic-`P` dichotomy
(`Sylow.commutator_eq_bot_or_commutator_eq_self`), either `⁅K, P⁆ = ⊥` — then `W = PK`
centralizes `P`, Burnside yields a normal `p`-complement `N ⊇ E'`, contradicting
`p ∣ |E'|` (`dvd_card_derived_of_mem_tau3`) — or `⁅K, P⁆ = P`, which forces `P ≤ E'`,
and Prop 1.6(d) (via the conjugation bridges) gives `C_P(K) = 1`, hence `C_G(E) ⊓ P = ⊥`. -/
private theorem sylow_le_derived_of_mem_tau3 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau3 M) (P : Sylow p ↥E) :
    (P : Subgroup ↥E).map E.subtype ≤ derivedInG E ∧
    Subgroup.centralizer (E : Set G) ⊓ (P : Subgroup ↥E).map E.subtype = ⊥ := by
  classical
  have hprime : p.Prime := Fact.out
  have hpodd : Odd p := by
    refine hprime.odd_of_ne_two ?_
    rintro rfl
    have h2 : (2 : ℕ) ∣ Nat.card G :=
      (Nat.dvd_of_mem_primeFactors hp.2.1).trans
        (Subgroup.card_subgroup_dvd_card (derivedInG M))
    have hodd := hG.odd
    rw [Nat.odd_iff] at hodd
    omega
  -- `P` is cyclic (`r_p(M) = 1` on `τ₃`)
  haveI hPcyc : IsCyclic ↥(P : Subgroup ↥E) := by
    refine S10.isCyclic_of_pRank_le_one P.isPGroup' hpodd ?_
    refine le_trans (pRank_le_of_injective (Subgroup.subtype_injective _)) ?_
    refine le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le)) ?_
    exact le_of_eq hp.2.2
  -- Sylow `p`-subgroup `Q` of the normalizer `W`, with its complement `K`
  haveI hQnorm : (P.subtype P.le_normalizer).Normal := P.normal_in_normalizer
  haveI hQcyc : IsCyclic ↥(P.subtype P.le_normalizer : Subgroup
      ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
    rw [P.coe_subtype]
    exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  obtain ⟨K, hK⟩ :=
    Subgroup.exists_left_complement'_of_coprime (P.subtype P.le_normalizer).card_coprime_index
  rcases Sylow.commutator_eq_bot_or_commutator_eq_self (P.subtype P.le_normalizer) hK
    with hbot | hself
  · -- `⁅K, Q⁆ = ⊥`: Burnside contradiction with `p ∣ |E'|`
    exfalso
    have hKcent : K ≤ Subgroup.centralizer
        ((P.subtype P.le_normalizer :
          Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :
          Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hQcent : (P.subtype P.le_normalizer :
        Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
        ≤ Subgroup.centralizer
          ((P.subtype P.le_normalizer :
            Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :
            Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :=
      Subgroup.le_centralizer _
    have htop : Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)
        ≤ Subgroup.centralizer ((P : Subgroup ↥E) : Set ↥E) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyW : y ∈ Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E) := P.le_normalizer hy
      have hyQ : (⟨y, hyW⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ∈ (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
        rw [P.coe_subtype]
        exact Subgroup.mem_subgroupOf.mpr hy
      have hxcent : (⟨x, hx⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ∈ Subgroup.centralizer ((P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) : Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
        have hmem : (⟨x, hx⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
            ∈ K ⊔ (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
          rw [hK.sup_eq_top]
          exact Subgroup.mem_top _
        exact sup_le hKcent hQcent hmem
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxcent ⟨y, hyW⟩ hyQ)
    obtain ⟨N, hNnorm, hNcompl⟩ :=
      OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P htop
    haveI := hNnorm
    have hcompl := hNcompl P
    -- `E' ≤ N` (the quotient is the abelian Sylow `P`)
    have hE'N : commutator ↥E ≤ N := by
      have hPab : ⁅(P : Subgroup ↥E), (P : Subgroup ↥E)⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer _)
      have hmap : Subgroup.map (QuotientGroup.mk' N) (commutator ↥E) = ⊥ := by
        rw [commutator_def, Subgroup.map_commutator]
        have hNbot : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
          rw [eq_bot_iff]
          rintro y ⟨n, hn, rfl⟩
          rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact hn
        have htop2 : Subgroup.map (QuotientGroup.mk' N) (⊤ : Subgroup ↥E)
            = Subgroup.map (QuotientGroup.mk' N) (P : Subgroup ↥E) := by
          conv_lhs => rw [← hcompl.sup_eq_top]
          rw [Subgroup.map_sup, hNbot, bot_sup_eq]
        rw [htop2, ← Subgroup.map_commutator, hPab, Subgroup.map_bot]
      intro z hz
      have hz1 : QuotientGroup.mk' N z ∈ (⊥ : Subgroup (↥E ⧸ N)) := hmap ▸ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_bot] at hz1
      rwa [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    -- `p` divides both of the coprime orders `|P|`, `|N|`: contradiction
    have hpE' : p ∣ Nat.card ↥(derivedInG E) := h.dvd_card_derived_of_mem_tau3 hG hprime hp
    have hcardeq : Nat.card ↥(derivedInG E) = Nat.card ↥(commutator ↥E) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥E) E.subtype
        (Subgroup.subtype_injective E)).toEquiv).symm
    have hpN : p ∣ Nat.card ↥N :=
      (hcardeq ▸ hpE').trans (Subgroup.card_dvd_of_le hE'N)
    have hcop : Nat.Coprime (Nat.card ↥(P : Subgroup ↥E)) (Nat.card ↥N) := by
      have hidx := P.card_coprime_index
      rwa [hcompl.index_eq_card] at hidx
    have hpP : p ∣ Nat.card ↥(P : Subgroup ↥E) := by
      have hpdvdE : p ∣ Nat.card ↥E :=
        hpE'.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
      rw [P.card_eq_multiplicity]
      exact dvd_pow_self p (hprime.factorization_pos_of_dvd Nat.card_pos.ne' hpdvdE).ne'
    have hdvd1 : p ∣ Nat.gcd (Nat.card ↥(P : Subgroup ↥E)) (Nat.card ↥N) :=
      Nat.dvd_gcd hpP hpN
    rw [hcop] at hdvd1
    exact hprime.one_lt.ne' (Nat.dvd_one.mp hdvd1)
  · -- `⁅K, Q⁆ = Q`: `P ≤ E'` and `C_P(K) = ⊥`
    -- push the commutator identity to `↥E`
    have hmapQ : (P.subtype P.le_normalizer :
        Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))).map
          (Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)).subtype
        = (P : Subgroup ↥E) := by
      rw [P.coe_subtype]
      exact Subgroup.map_subgroupOf_eq_of_le P.le_normalizer
    have hmapped : ⁅K.map (Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)).subtype,
        (P : Subgroup ↥E)⁆ = (P : Subgroup ↥E) := by
      have hc := congrArg
        (Subgroup.map (Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)).subtype) hself
      rwa [Subgroup.map_commutator, hmapQ] at hc
    constructor
    · -- `P ≤ E'`
      have hd : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      calc (P : Subgroup ↥E).map E.subtype
          = (⁅K.map (Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)).subtype,
              (P : Subgroup ↥E)⁆).map E.subtype := by rw [hmapped]
        _ = ⁅(K.map (Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)).subtype).map E.subtype,
              ((P : Subgroup ↥E)).map E.subtype⁆ :=
            Subgroup.map_commutator _ _ _
        _ ≤ ⁅E, E⁆ :=
            Subgroup.commutator_mono (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
        _ = derivedInG E := hd.symm
    · -- `C_G(E) ⊓ P = ⊥` via Prop 1.6(d)
      have hKnormQ : K ≤ Subgroup.normalizer
          ((P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :
            Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
        have heq : Subgroup.normalizer
            ((P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :
              Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) = ⊤ :=
          Subgroup.normalizer_eq_top_iff.mpr hQnorm
        rw [heq]
        exact le_top
      -- `actionCommutator φ = ⊤`
      have hac : Ch04.actionCommutator
          ((Subgroup.normalizerMonoidHom (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))).comp
            (Subgroup.inclusion hKnormQ)) = ⊤ := by
        apply Subgroup.map_injective
          (Subgroup.subtype_injective (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))))
        rw [actionCommutator_conj_map_subtype hKnormQ]
        rw [show Subgroup.map (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))).subtype ⊤
            = (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) from by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]]
        rw [Subgroup.commutator_comm]
        exact hself
      -- Prop 1.6(d): fixed points form a complement of `⊤`, hence are trivial
      letI : CommGroup ↥(P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :=
        { (inferInstance : Group ↥(P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))) with
          mul_comm := fun a b => by
            have hcentral : (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
                ≤ Subgroup.centralizer ((P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :
                  Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) :=
              Subgroup.le_centralizer _
            exact Subtype.ext
              (Subgroup.mem_centralizer_iff.mp (hcentral a.2) _ b.2).symm }
      have hcop : Nat.Coprime (Nat.card ↥K)
          (Nat.card ↥(P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))) := by
        have hidx := (P.subtype P.le_normalizer).card_coprime_index
        rw [hK.index_eq_card] at hidx
        exact hidx.symm
      have h16d := OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
        (φ := (Subgroup.normalizerMonoidHom (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))).comp
          (Subgroup.inclusion hKnormQ)) hcop
      rw [hac] at h16d
      have hfpbot : Subgroup.fixedPointsOfMulAut
          ((Subgroup.normalizerMonoidHom (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))).comp
            (Subgroup.inclusion hKnormQ)) = ⊥ :=
        Subgroup.isComplement'_top_right.mp h16d
      have hcentbot : Subgroup.centralizer (K :
          Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ⊓ (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) = ⊥ := by
        rw [← fixedPointsOfMulAut_conj_map_subtype hKnormQ, hfpbot, Subgroup.map_bot]
      -- transfer to the ambient group
      rw [eq_bot_iff]
      rintro x ⟨hxc, hxP⟩
      obtain ⟨xE, hxE, rfl⟩ := hxP
      have hxW : xE ∈ Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E) := P.le_normalizer hxE
      have hxQ : (⟨xE, hxW⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ∈ (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
        rw [P.coe_subtype]
        exact Subgroup.mem_subgroupOf.mpr hxE
      have hxcent : (⟨xE, hxW⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ∈ Subgroup.centralizer (K :
            Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hgcomm : ((k : ↥E) : G) * (xE : G) = (xE : G) * ((k : ↥E) : G) :=
          Subgroup.mem_centralizer_iff.mp hxc _ (k : ↥E).2
        exact Subtype.ext (Subtype.ext hgcomm)
      have hbotmem : (⟨xE, hxW⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
          ∈ Subgroup.centralizer (K :
            Set ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)))
            ⊓ (P.subtype P.le_normalizer : Subgroup ↥(Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E))) := ⟨hxcent, hxQ⟩
      rw [hcentbot, Subgroup.mem_bot] at hbotmem
      have hxE1 : xE = 1 := congrArg Subtype.val hbotmem
      rw [Subgroup.mem_bot, hxE1]
      rfl

/-- **BG Lemma 12.1(b), first half** (mmd L3041-3052): `E₃ ≤ E'`. Each Sylow subgroup of
`E` at a `τ₃`-prime lies in `E'` (`sylow_le_derived_of_mem_tau3`), so `[E : E']` is coprime
to `|E₃|` and the `τ₃`-Hall subgroup is absorbed. -/
theorem SubgroupESetup.E3_le_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E₃ ≤ derivedInG E := by
  classical
  have hcop : Nat.Coprime (Nat.card ↥(E₃.subgroupOf E)) (commutator ↥E).index := by
    rw [Nat.coprime_comm]
    by_contra hncop
    obtain ⟨p, hprime, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
    haveI : Fact p.Prime := ⟨hprime⟩
    have hcardE₃ : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    have hpτ₃ : p ∈ tau3 M := h.isPiGroup_tau3 p (Nat.mem_primeFactors.mpr
      ⟨hprime, hcardE₃ ▸ hp2, Nat.card_pos.ne'⟩)
    -- a Sylow `p`-subgroup of `E` lies in `E'`, so `p` cannot divide the index
    obtain ⟨P⟩ : Nonempty (Sylow p ↥E) := inferInstance
    have hPle := (sylow_le_derived_of_mem_tau3 hG h hpτ₃ P).1
    have hPcomm : (P : Subgroup ↥E) ≤ commutator ↥E := by
      have hD : (derivedInG E).subgroupOf E = commutator ↥E := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective E)]
      rw [← hD]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hPle ⟨x, hx, rfl⟩)
    -- factorization bookkeeping: the full `p`-part sits inside `commutator ↥E`
    have hPdvd : p ^ (Nat.card ↥E).factorization p ∣ Nat.card ↥(commutator ↥E) := by
      have hPP := Subgroup.card_dvd_of_le hPcomm
      rwa [P.card_eq_multiplicity] at hPP
    have hfull : p ^ ((Nat.card ↥E).factorization p + 1) ∣ Nat.card ↥E := by
      calc p ^ ((Nat.card ↥E).factorization p + 1)
          = p ^ (Nat.card ↥E).factorization p * p := by ring
      _ ∣ Nat.card ↥(commutator ↥E) * (commutator ↥E).index :=
          mul_dvd_mul hPdvd hp1
      _ = Nat.card ↥E := Subgroup.card_mul_index (commutator ↥E)
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hprime hfull
  have hle := S10.le_of_coprime_card_index (K := commutator ↥E) (Q := E₃.subgroupOf E) hcop
  intro x hx
  exact ⟨_, hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, h.E₃_le hx⟩ : ↥E) ∈ _), rfl⟩

/-- **BG Lemma 12.1(b), second half** (mmd L3052): `E₃ ⊴ E`. Since `E'` is nilpotent,
`E₃ = O_{τ₃}(E')`, which `E` normalizes because it normalizes `E'`. -/
theorem SubgroupESetup.E3_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) := by
  classical
  haveI hnilp : Group.IsNilpotent ↥(derivedInG E) := h.derived_isNilpotent hG
  have hE₃D : E₃ ≤ derivedInG E := h.E3_le_derived hG
  have hcoreHall : Ch03.IsHallSubgroup (tau3 M) (Ch03.oPiCore (tau3 M) ↥(derivedInG E)) :=
    S10.oPiCore_isHall_of_isNilpotent (tau3 M)
  have hE₃core : E₃ ≤ opiCoreInG (tau3 M) (derivedInG E) := by
    have hsub : E₃.subgroupOf (derivedInG E) ≤ Ch03.oPiCore (tau3 M) ↥(derivedInG E) :=
      S10.isPiGroup_le_of_normal_isHallSubgroup hcoreHall
        (Ch03.Subgroup.IsPiGroup.subgroupOf hE₃D h.isPiGroup_tau3)
    intro x hx
    exact ⟨⟨x, hE₃D hx⟩, hsub (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcorele : Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E)) ≤ Nat.card ↥E₃ := by
    have hcorepi : Ch03.Subgroup.IsPiGroup (tau3 M)
        ((opiCoreInG (tau3 M) (derivedInG E)).subgroupOf E) := by
      refine Ch03.Subgroup.IsPiGroup.subgroupOf
        ((opiCoreInG_le _ _).trans (Subgroup.map_subtype_le _)) ?_
      intro r hr
      have hcard : Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E))
          = Nat.card ↥(Ch03.oPiCore (tau3 M) ↥(derivedInG E)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (Subgroup.subtype_injective (derivedInG E))).toEquiv).symm
      exact Ch03.oPiCore.isPiGroup (tau3 M) r (hcard ▸ hr)
    have hdvd := h.E₃_hall.card_dvd_of_isPiGroup hcorepi
    have hcard1 : Nat.card ↥((opiCoreInG (tau3 M) (derivedInG E)).subgroupOf E)
        = Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((opiCoreInG_le _ _).trans (Subgroup.map_subtype_le _))).toEquiv
    have hcard2 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    rw [hcard1, hcard2] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have heq : E₃ = opiCoreInG (tau3 M) (derivedInG E) :=
    Subgroup.eq_of_le_of_card_ge hE₃core hcorele
  rw [heq]
  exact le_normalizer_opiCoreInG_of_le_normalizer (tau3 M) (S10.le_normalizer_derivedInG E)

/-- **BG Lemma 12.1(d), `E₃` half** (mmd L3052): `E₃` is cyclic (it sits inside the
nilpotent `E'` with all `p`-ranks `≤ 1`). -/
theorem SubgroupESetup.E3_isCyclic [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    IsCyclic ↥E₃ := by
  haveI hnilp : Group.IsNilpotent ↥(derivedInG E) := h.derived_isNilpotent hG
  haveI : Group.IsNilpotent ↥E₃ :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (h.E3_le_derived hG))
  have hodd : Odd (Nat.card ↥E₃) :=
    hG.odd.of_dvd_nat
      ((Subgroup.card_dvd_of_le h.E3_le_M).trans (Subgroup.card_subgroup_dvd_card M))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E₃).primeFactors
  · have hp3 : p ∈ tau3 M := h.isPiGroup_tau3 p hpE
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E3_le_M))
      (le_of_eq hp3.2.2)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- **BG Lemma 12.1(f)** (mmd L3055): `C_{E₃}(E) = 1`. Any nontrivial element of
`C_G(E) ⊓ E₃` would yield a nontrivial `p`-subgroup (`p ∈ τ₃`) inside some Sylow
`p`-subgroup of `E`, contradicting `C_G(E) ⊓ P = ⊥` from the per-prime core. -/
theorem SubgroupESetup.centralizer_inf_E3_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Subgroup.centralizer (E : Set G) ⊓ E₃ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hprime⟩
  have hpE₃ : p ∈ (Nat.card ↥E₃).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩
  have hpτ₃ : p ∈ tau3 M := h.isPiGroup_tau3 p hpE₃
  -- a nontrivial Sylow `p`-subgroup `Y` of `Z := C_G(E) ⊓ E₃`
  obtain ⟨Y⟩ : Nonempty (Sylow p ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) := inferInstance
  have hYne : Nat.card
      ↥(Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) ≠ 1 := by
    rw [Y.card_eq_multiplicity]
    intro hone
    have hpos := hprime.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    rcases Nat.pow_eq_one.mp hone with h1 | h0
    · exact hprime.one_lt.ne' h1
    · omega
  -- realize `Y` inside a Sylow `p`-subgroup of `E`
  have hYG_le_Z : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype ≤ Subgroup.centralizer (E : Set G) ⊓ E₃ :=
    Subgroup.map_subtype_le _
  have hYG_le_E : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype ≤ E :=
    hYG_le_Z.trans (inf_le_right.trans h.E₃_le)
  have hYG_pgroup : IsPGroup p ↥((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype) :=
    Y.isPGroup'.map _
  have hYE_pgroup : IsPGroup p ↥(((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype).subgroupOf E) :=
    hYG_pgroup.of_injective (Subgroup.subgroupOfEquivOfLe hYG_le_E).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hYG_le_E).injective
  obtain ⟨P, hYP⟩ := hYE_pgroup.exists_le_sylow
  have hPbot := (sylow_le_derived_of_mem_tau3 hG h hpτ₃ P).2
  -- `Y ≤ C_G(E) ⊓ P = ⊥`
  have hYbot : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype = ⊥ := by
    rw [eq_bot_iff, ← hPbot]
    intro x hx
    refine ⟨(hYG_le_Z hx).1, ?_⟩
    exact ⟨⟨x, hYG_le_E hx⟩, hYP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hmap : Nat.card ↥((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype)
      = Nat.card ↥(Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) :=
    Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (Subgroup.centralizer (E : Set G) ⊓ E₃))
  rw [hYbot, Subgroup.card_bot] at hmap
  exact hYne hmap.symm

/-- **BG Lemma 12.1(d), `E₁` half** (mmd L3040-3041): `E₁` is cyclic.

`E₁' ≤ E₁ ⊓ M' = 1` (`τ₁(M)` avoids `π(M')`), so `E₁` is abelian; each Sylow subgroup is
cyclic by the converse of Lemma 4.5 since `r_p(M) = 1` on `τ₁(M)`. -/
theorem SubgroupESetup.E1_isCyclic [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    IsCyclic ↥E₁ := by
  -- `E₁ ⊓ M' = ⊥`: a common prime divisor would lie in `τ₁(M) ∩ π(M') = ∅`.
  have hinf : E₁ ⊓ derivedInG M = ⊥ := by
    rw [← Subgroup.card_eq_one]
    by_contra hne
    obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp1 : p ∈ tau1 M := h.isPiGroup_tau1 p (Nat.mem_primeFactors.mpr
      ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    exact hp1.2.1 (Nat.mem_primeFactors.mpr
      ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  -- `⁅E₁, E₁⁆ = ⊥`, so `E₁` is abelian.
  have hcomm : ⁅E₁, E₁⁆ = ⊥ := by
    have hle1 : ⁅E₁, E₁⁆ ≤ E₁ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact E₁.mul_mem (E₁.mul_mem (E₁.mul_mem hg₁ hg₂) (E₁.inv_mem hg₁)) (E₁.inv_mem hg₂)
    have hle2 : ⁅E₁, E₁⁆ ≤ derivedInG M := by
      have hd : derivedInG M = ⁅(M : Subgroup G), M⁆ := Subgroup.map_subtype_commutator M
      rw [hd]
      exact Subgroup.commutator_mono h.E1_le_M h.E1_le_M
    rw [← le_bot_iff, ← hinf]
    exact le_inf hle1 hle2
  have hab : ∀ a b : ↥E₁, a * b = b * a := by
    intro a b
    have hcentral : E₁ ≤ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentral a.2) (b : G) b.2).symm
  letI : CommGroup ↥E₁ := { (inferInstance : Group ↥E₁) with mul_comm := hab }
  have hodd : Odd (Nat.card ↥E₁) :=
    hG.odd.of_dvd_nat
      ((Subgroup.card_dvd_of_le (h.E1_le_M)).trans (Subgroup.card_subgroup_dvd_card M))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E₁).primeFactors
  · have hp1 : p ∈ tau1 M := h.isPiGroup_tau1 p hpE
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E1_le_M))
      (le_of_eq hp1.2.2)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

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
