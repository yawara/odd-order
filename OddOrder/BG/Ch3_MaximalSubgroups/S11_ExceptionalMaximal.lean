/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.PRank

/-!
# BG §11: Exceptional Maximal Subgroups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §11 (pp. 76-79), mmd `references/bg/local-analysis.mmd`
L2913-3022, **7 結果** (Lem 11.1 + Thm 11.3/11.5/11.7 + Cor 11.2/11.4/11.6)。

§11 は **Hypothesis 11.1** (`M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M`) のもとで、
*exceptional* maximal subgroup `M` (= `r(H/H_σ)=1` が破れる) の構造を示す: `M_σ` nilpotent (11.3)、
`M` の Sylow `p` abelian (11.5)、`M_σ A ⊴ M` (11.7)。Thompson Transitivity (§7 Thm 7.6) に依存。

## 記法

- 固定 `M, p, A₀` + 導出 `A ∈ ℰ_p²(M)` (`A₀⊆A`, Lem 10.5), `A ⊆ P ∈ Syl_p(M)`, `N_G(P)⊄M`,
  `A∈ℰ_p*(G)` を `Hypothesis111 M p A₀ A P` に束ねる。`M_σ` = `S10.Msigma M`。
- 「`A`-不変 Sylow `q`-部分群」= `IsAInvSylowIn` (M_σ 内の `A`-不変・`q`-極大 部分群)。
- 固定 G `(hG : IsMinimalSimpleOdd G)` を明示 thread。proof は §7/§10 + Thm 3.7 等に依存 (全 sorry)。
-/

namespace OddOrder.BG.Ch3.S11

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Hypothesis 11.1** (mmd L2917) + 導出データ: `M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`,
`N_G(A₀) ⊆ M`; さらに Lem 10.5 から `A ∈ ℰ_p²(M)` (`A₀⊆A`), `A ⊆ P ∈ Syl_p(M)`, `N_G(P)⊄M`,
`A ∈ ℰ_p*(G)`。§11 全体の standing assumption。 -/
structure Hypothesis111 (M : Subgroup G) (p : ℕ) (A₀ A P : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  prime : p.Prime
  notMem_sigma : p ∉ S10.sigma M
  A₀_mem : A₀ ∈ elemAbelianOfRank G p 1
  A₀_le : A₀ ≤ M
  normalizer_A₀_le : Subgroup.normalizer (A₀ : Set G) ≤ M
  A_mem : A ∈ elemAbelianOfRank G p 2
  A_le : A ≤ M
  A₀_le_A : A₀ ≤ A
  P_pgroup : IsPGroup p ↥P
  A_le_P : A ≤ P
  P_le : P ≤ M
  normalizer_P_not_le : ¬ Subgroup.normalizer (P : Set G) ≤ M
  A_maximal : IsMaximalElementaryAbelian p A

/-- `Q` は `H` の `A`-不変 Sylow `q`-部分群 (= `Q ≤ H`, `q`-群, `A`-不変, `H` 内で `q`-極大)。 -/
def IsAInvSylowIn (q : ℕ) (A Q H : Subgroup G) : Prop :=
  Q ≤ H ∧ IsPGroup q ↥Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
    ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup q ↥R → R = Q

/-- `φ • H = H.map φ`: the pointwise `MulAut`-action on a subgroup is its image under the
corresponding monoid hom. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- A `π`-Hall subgroup stays `π`-Hall after conjugation (cardinality and index are
preserved by the inner automorphism `MulAut.conj g`). -/
private theorem isHallSubgroup_conj_smul {π : Set ℕ} {H : Subgroup G} (g : G)
    (hH : Ch03.IsHallSubgroup π H) : Ch03.IsHallSubgroup π (MulAut.conj g • H) := by
  rw [mulAut_smul_eq_map]
  refine ⟨?_, ?_⟩
  · -- card preserved
    have hcard : Nat.card ↥(H.map (MulAut.conj g : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ (MulAut.conj g).injective).toEquiv).symm
    rw [hcard]; exact hH.1
  · -- index preserved
    have hidx : (H.map (MulAut.conj g : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H (MulAut.conj g)
    rw [hidx]; exact hH.2

/-- **STEP2 bridge** (auxiliary): an `A`-invariant Sylow `q`-subgroup `Q` of a `σ(M)`-Hall
subgroup `H` of `G` (with `q ∈ σ(M)`) is a *maximal* `A`-invariant `q`-subgroup of `G`, i.e.
`Q ∈ ℋ_G*(A;q)`.

Reason: the 4th conjunct of `IsAInvSylowIn` makes `Q` a maximal `q`-subgroup of `↥H`
(= Sylow `q` of `↥H`), so `q ∤ [H : Q]`. As `q ∈ σ(M)` and `H` is `σ(M)`-Hall, `q ∤ [G : H]`,
hence `q ∤ [G : Q]` by the index tower law; thus `Q` is a Sylow `q`-subgroup of `G`, so no
larger `q`-subgroup (a fortiori no larger `A`-invariant one) exists. We return both the
Sylow witness (`Q` is Sylow `q` of `G`) and the `ℋ_G*(A;q)`-membership. -/
private theorem isSylow_and_mem_hInvariantStar_of_isAInvSylowIn [Finite G]
    {M A H Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hHall : Ch03.IsHallSubgroup (S10.sigma M) H) (hq : q ∈ S10.sigma M)
    (hQ : IsAInvSylowIn q A Q H) :
    (∃ QS : Sylow q G, (QS : Subgroup G) = Q) ∧ Q ∈ hInvariantStar ⊤ A {q} := by
  obtain ⟨hQH, hQp, hAQ, hQmax⟩ := hQ
  -- `q ∤ [G : Q]`: Sylow of `↥H` index times Hall index, both `q`-prime.
  have hQidx : ¬ q ∣ Q.index := by
    -- Land `Q.subgroupOf H` in a Sylow `S` of `↥H`; map back and use maximality `Q = S.map`.
    obtain ⟨S, hS⟩ := hQp.comap_subtype.exists_le_sylow (G := H)
    -- `S.map H.subtype` is an `q`-subgroup of `H` containing `Q`, so it equals `Q` by maximality.
    have hSmaple : (S : Subgroup ↥H).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hSmapp : IsPGroup q ↥((S : Subgroup ↥H).map H.subtype) := S.2.map H.subtype
    have hQle : Q ≤ (S : Subgroup ↥H).map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQH]
      exact Subgroup.map_mono hS
    have hSeqQ : (S : Subgroup ↥H).map H.subtype = Q := hQmax _ hQle hSmaple hSmapp
    -- Hence `Q.subgroupOf H = S` (as a subgroup of `↥H`).
    have hsubOf : Q.subgroupOf H = (S : Subgroup ↥H) := by
      rw [← hSeqQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    -- Index tower: `[G : Q] = [H : Q]·[G : H]`, both factors `q`-prime.
    have htower : (Q.subgroupOf H).index * H.index = Q.index :=
      Subgroup.relIndex_mul_index hQH
    rw [hsubOf] at htower
    -- `q ∤ [↥H : S]` (Sylow of finite `↥H`) and `q ∤ [G : H]` (Hall, `q ∈ σ(M)`).
    haveI : (S : Subgroup ↥H).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    have hSidx : ¬ q ∣ (S : Subgroup ↥H).index := by
      have := S.not_dvd_index; simpa using this
    have hHidx : ¬ q ∣ H.index := fun hdvd =>
      hHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq
    rw [← htower]
    exact (Fact.out (p := q.Prime)).not_dvd_mul hSidx hHidx
  -- Upgrade `Q` to a Sylow `q`-subgroup of `G`.
  haveI : Q.FiniteIndex := ⟨fun h => hQidx (h ▸ dvd_zero q)⟩
  let QS : Sylow q G := hQp.toSylow hQidx
  have hQS : (QS : Subgroup G) = Q := hQp.toSylow_coe hQidx
  refine ⟨⟨QS, hQS⟩, ⟨le_top, hAQ, ?_⟩, ?_⟩
  · -- `Q` is a `{q}`-subgroup.
    intro r hr
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := Q)).mp hQp
    rw [hn] at hr
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0] at hr
    · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out] at hr; simpa using hr
  · -- Maximality among `A`-invariant `q`-subgroups: any larger `q`-subgroup equals `Q`.
    intro Q' hQ' hQQ'
    obtain ⟨-, -, hQ'pi⟩ := hQ'
    have hQ'p : IsPGroup q Q' := OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hQ'pi
    -- `QS` is a Sylow `q`-subgroup, so it is `≤`-maximal among `q`-subgroups.
    have heq : Q' = (QS : Subgroup G) := QS.3 hQ'p (hQS ▸ hQQ')
    rw [heq, hQS]

/-- **BG Lemma 11.1** (mmd L2939): Hyp 11.1 のもと、`g ∈ G−M`, `A ⊆ M^g`, `q ∈ σ(M)`、`Q₁`/`Q₂`
を `M_σ`/`M_σ^g` の `A`-不変 Sylow `q`-部分群とする。すると (a) `Q₁ ⊓ Q₂ = 1`、(b) 各 `X ∈ ℰ¹(A)`
で `C_{Q₁}(X) = 1` または `C_{Q₂}(X) = 1`。 -/
theorem invariant_sylow_disjoint [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {Q₁ Q₂ : Subgroup G}
    (hQ₁ : IsAInvSylowIn q A Q₁ (S10.Msigma M))
    (hQ₂ : IsAInvSylowIn q A Q₂ (MulAut.conj g • S10.Msigma M)) :
    Q₁ ⊓ Q₂ = ⊥ ∧
    ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ A →
      Subgroup.centralizer (X : Set G) ⊓ Q₁ = ⊥ ∨
      Subgroup.centralizer (X : Set G) ⊓ Q₂ = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  -- Basic facts about `A`.
  have hAelem : A.IsElementaryAbelian p := h.A_mem.1
  have hAcomm : IsMulCommutative ↥A := ⟨⟨fun x y => hAelem.comm x y⟩⟩
  have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
  -- `p ∣ |G|` (Lagrange via `A ≤ G`, `|A| = p²`).
  have hpG : p ∣ Nat.card G := by
    have hdvd : Nat.card ↥A ∣ Nat.card G := Subgroup.card_subgroup_dvd_card A
    rw [hAcard] at hdvd
    exact dvd_trans (dvd_pow_self p (by norm_num)) hdvd
  -- STEP1: `A` satisfies Hypothesis 7.1 (Prop 7.5, case (1)).
  have hHyp71 : Ch2.S07.Hypothesis71 A := by
    refine Ch2.S07.hypothesis71_of_scn2_or_pLengthOne hG hpG A hAcomm hAelem.isPGroup
      (Or.inl ⟨?_, fun N hN => S10.proper_hasPLengthOne hG N hN⟩)
    -- `(A : Set G) = {x | x ∈ C_G(A) ∧ x ^ p = 1}` (= `A = Ω₁(C_G(A))`).
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · -- `x ∈ A ⟹ x ∈ C_G(A) ∧ x ^ p = 1`.
      intro hx
      haveI := hAcomm
      refine ⟨Subgroup.le_centralizer (H := A) hx, ?_⟩
      have hxp1 : (⟨x, hx⟩ : ↥A) ^ p = 1 := hAelem.2 _
      have := congrArg (Subgroup.subtype A) hxp1
      simpa using this
    · -- `x ∈ C_G(A) ∧ x ^ p = 1 ⟹ x ∈ A` (maximality of `A`).
      rintro ⟨hxc, hxp⟩
      -- `B := closure(A ∪ {x})` is `p`-elementary abelian and contains `A`, so `B = A`.
      -- Generating set `A ∪ {x}` consists of pairwise-commuting elements.
      have hgen_comm : ∀ a ∈ (A : Set G) ∪ {x}, ∀ b ∈ (A : Set G) ∪ {x}, a * b = b * a := by
        rintro a (ha | ha) b (hb | hb)
        · have := hAelem.comm ⟨a, ha⟩ ⟨b, hb⟩
          simpa using congrArg (Subgroup.subtype A) this
        · rw [Set.mem_singleton_iff] at hb; subst hb; exact hxc a ha
        · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hxc b hb).symm
        · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {x}) with hB_def
      haveI hBcomm : IsMulCommutative ↥B := Subgroup.isMulCommutative_closure hgen_comm
      -- Every generator is `p`-torsion; in the commutative `B`, so is every element.
      have hgen_pow : ∀ w ∈ (A : Set G) ∪ {x}, w ^ p = 1 := by
        rintro w (hw | hw)
        · have := hAelem.2 ⟨w, hw⟩; simpa using congrArg (Subgroup.subtype A) this
        · rw [Set.mem_singleton_iff] at hw; subst hw; exact hxp
      -- Commutativity inside the closure `B` (lifted from `IsMulCommutative ↥B`).
      have hBclos_comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
        have := hBcomm.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
        simpa using congrArg (Subgroup.subtype B) this
      -- Every element of the closure is `p`-torsion.
      have hclos_pow : ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {x}), y ^ p = 1 := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem z hz => exact hgen_pow z hz
        | one => simp
        | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
            have hc : Commute z₁ z₂ := hBclos_comm z₁ hz₁ z₂ hz₂
            rw [hc.mul_pow, h₁, h₂, mul_one]
        | inv z _ h => rw [inv_pow, h, inv_one]
      have hB_pow : ∀ u : ↥B, u ^ p = 1 := fun u =>
        Subtype.ext (by simpa using hclos_pow (u : G) u.2)
      -- `B` is `p`-elementary abelian; maximality collapses it to `A`.
      have hBelem : B.IsElementaryAbelian p := ⟨fun u v => hBcomm.is_comm.comm u v, hB_pow⟩
      have hAleB : A ≤ B := fun z hz => Subgroup.subset_closure (Or.inl hz)
      have hBeqA : B = A := h.A_maximal.2 B hBelem hAleB
      have hxB : x ∈ B := by
        rw [hB_def]; exact Subgroup.subset_closure (Or.inr rfl)
      rw [hBeqA] at hxB
      exact hxB
  -- STEP2: bridge `IsAInvSylowIn` to `ℋ_G*(A;q)` for `Q₁` (in `M_σ`) and `Q₂` (in `M_σ^g`).
  haveI : Fact q.Prime := ‹Fact q.Prime›
  have hHallMsigma : Ch03.IsHallSubgroup (S10.sigma M) (S10.Msigma M) :=
    (S10.isHall_Msigma_Malpha hG h.mem_maximal).1
  have hHallConj : Ch03.IsHallSubgroup (S10.sigma M) (MulAut.conj g • S10.Msigma M) :=
    isHallSubgroup_conj_smul g hHallMsigma
  obtain ⟨⟨Q₁S, hQ₁S⟩, hQ₁star⟩ :=
    isSylow_and_mem_hInvariantStar_of_isAInvSylowIn (M := M) hHallMsigma hq hQ₁
  obtain ⟨⟨Q₂S, hQ₂S⟩, hQ₂star⟩ :=
    isSylow_and_mem_hInvariantStar_of_isAInvSylowIn (M := M) hHallConj hq hQ₂
  -- `q ∈ π(A)' = {p}ᶜ` because `q ∈ σ(M)` but `p ∉ σ(M)`, so `q ≠ p`.
  have hqp : q ≠ p := by rintro rfl; exact h.notMem_sigma hq
  have hqπ' : q ∈ (Ch2.S07.primesOf A)ᶜ := by
    simp only [Ch2.S07.primesOf, Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hmem
    rw [hAcard, Nat.primeFactors_prime_pow (by norm_num) h.prime, Finset.mem_singleton] at hmem
    exact hqp hmem
  -- `C_G(A) ⊆ M` (via `C_G(A) ≤ C_G(A₀) ≤ N_G(A₀) ≤ M`).
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M := by
    have h1 : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.A₀_le_A)
    exact le_trans (le_trans h1 (Subgroup.centralizer_le_normalizer _)) h.normalizer_A₀_le
  -- `kSubgroup A ≤ C_G(A) ⊆ M`.
  have hKM : Ch2.S07.kSubgroup A ≤ M :=
    le_trans (Subgroup.map_subtype_le _) hCAM
  -- STEP3-5: prove both conjuncts by contradiction via the inductive lemma.
  -- A reusable contradiction: if some proper `H ⊇ A` meets both `Q₁` and `Q₂` nontrivially,
  -- the inductive lemma forces `Q₂ = Q₁^k` with `k ∈ K ⊆ M`, so `Q₂ ⊆ M`; then `g ∈ M`.
  have key : ∀ H : Subgroup G, H < ⊤ → A ≤ H → H ⊓ Q₁ ≠ ⊥ → H ⊓ Q₂ ≠ ⊥ → False := by
    intro H hHproper hAH hHQ₁ hHQ₂
    obtain ⟨k, hk, hkconj⟩ :=
      Ch2.S07.inductiveLemma hG hHyp71 hqπ' hQ₁star hQ₂star H hHproper hAH hHQ₁ hHQ₂
    -- `Q₂ = Q₁^k ≤ M^? ` — actually `Q₂ ≤ M`: `Q₂ = conj k • Q₁`, `Q₁ ≤ M_σ ≤ M`, `k ∈ M`.
    have hkM : k ∈ M := hKM hk
    have hQ₁M : Q₁ ≤ M := le_trans hQ₁.1 (Subgroup.map_subtype_le _)
    have hQ₂M : Q₂ ≤ M := by
      rw [← hkconj]
      intro y hy
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
      have hmem : k⁻¹ * y * k⁻¹⁻¹ ∈ M := by
        have hy' : (MulAut.conj k)⁻¹ y ∈ Q₁ := hy
        rw [← map_inv, MulAut.conj_apply] at hy'
        exact hQ₁M hy'
      have hres : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hkM hmem) (M.inv_mem hkM)
      simpa [inv_inv, mul_assoc] using hres
    -- `R := Q₂^{g⁻¹}` is a Sylow `q`-subgroup of `G` inside `M_σ ⊆ M`, and `R^g = Q₂ ⊆ M`.
    -- By Theorem 10.1(d) applied to the Sylow `q`-subgroup `R` of `M`, `g ∈ M` — contradiction.
    set R : Subgroup G := (MulAut.conj g)⁻¹ • Q₂ with hR_def
    -- `R ≤ M_σ` (because `Q₂ ≤ M_σ^g`).
    have hRMsigma : R ≤ S10.Msigma M := by
      have hQ₂g : Q₂ ≤ MulAut.conj g • S10.Msigma M := hQ₂.1
      rw [hR_def]
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := (MulAut.conj g)⁻¹)).mpr hQ₂g
      rwa [inv_smul_smul] at this
    have hRM : R ≤ M := le_trans hRMsigma (Subgroup.map_subtype_le _)
    -- `conj g • R = Q₂`.
    have hconjR : MulAut.conj g • R = Q₂ := by rw [hR_def, smul_inv_smul]
    -- `R = Q₂^{g⁻¹}` as the image of `Q₂` under the automorphism `(MulAut.conj g)⁻¹`.
    have hReqmap : R = Q₂.map (((MulAut.conj g)⁻¹ : MulAut G) : G →* G) := by
      rw [hR_def, mulAut_smul_eq_map]
    -- `R` is a `q`-group (conjugate of the `q`-group `Q₂`).
    have hRp : IsPGroup q ↥R := by
      rw [hReqmap]
      exact hQ₂.2.1.of_equiv (Subgroup.equivMapOfInjective Q₂ _ (MulAut.conj g)⁻¹.injective)
    -- `R` Sylow of `G`: `R.index = Q₂.index` (conjugation), and `Q₂ = Q₂S` is Sylow of `G`.
    have hRidxG : ¬ q ∣ R.index := by
      have hRidx_eq : R.index = Q₂.index := by
        rw [hReqmap, Subgroup.index_map_equiv Q₂ (MulAut.conj g)⁻¹]
      rw [hRidx_eq, ← hQ₂S]
      haveI : (Q₂S : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
      exact Q₂S.not_dvd_index
    -- Build the Sylow `q`-subgroup of `↥M` whose image is `R`.
    have hRsubM_idx : ¬ q ∣ (R.subgroupOf M).index := by
      have htower : (R.subgroupOf M).index * M.index = R.index := Subgroup.relIndex_mul_index hRM
      exact fun hdvd => hRidxG (htower ▸ Dvd.dvd.mul_right hdvd M.index)
    haveI : (R.subgroupOf M).FiniteIndex := ⟨fun h => hRsubM_idx (h ▸ dvd_zero q)⟩
    let RM : Sylow q ↥M := (hRp.comap_subtype (K := M)).toSylow hRsubM_idx
    have hRM_coe : (RM : Subgroup ↥M).map M.subtype = R := by
      show ((hRp.comap_subtype (K := M)).toSylow hRsubM_idx : Subgroup ↥M).map M.subtype = R
      rw [(hRp.comap_subtype (K := M)).toSylow_coe hRsubM_idx, Subgroup.comap_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRM]
    -- `R ≠ ⊥`: else `R.index = |G|`, which `q` divides (`q ∈ σ(M) ⊆ π(G)`), contradicting `hRidxG`.
    have hqG : q ∣ Nat.card G :=
      dvd_trans (Nat.dvd_of_mem_primeFactors hq.1) (Subgroup.card_subgroup_dvd_card M)
    have hRnebot : R ≠ ⊥ := fun hRbot => hRidxG (by rw [hRbot, Subgroup.index_bot]; exact hqG)
    -- Theorem 10.1(d): `R` Sylow `q` of `M`, `R^g ⊆ M` ⇒ `g ∈ M`.
    have hgM : g ∈ M := by
      have hfusion := (S10.fusion_control_of_mem_sigma hG h.mem_maximal hq
        (X := R) hRnebot hRp).2.2.2.1
      exact hfusion ⟨RM, hRM_coe.symm⟩ g (hconjR ▸ hQ₂M)
    exact hg hgM
  -- `Z(G) = 1` (simple nonabelian) — used for `C_G(X) < ⊤`.
  have hZbot : Subgroup.center G = ⊥ := by
    haveI : IsSimpleGroup G := hG.simple
    refine (Subgroup.Normal.eq_bot_or_eq_top Subgroup.instNormalCenter).resolve_right
      (fun htop => ?_)
    exact hG.notSolvable (isSolvable_of_comm (fun a b =>
      (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm))
  -- `M < ⊤`.
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr h.mem_maximal.1
  -- `M^g ⊓ M < ⊤` and `A ≤ M^g ⊓ M`.
  have hHmm_le : (MulAut.conj g • M) ⊓ M ≤ M := inf_le_right
  have hHmm_lt : (MulAut.conj g • M) ⊓ M < ⊤ := lt_of_le_of_lt hHmm_le hMlt
  have hAHmm : A ≤ (MulAut.conj g • M) ⊓ M := le_inf hAg h.A_le
  -- `Q₁ ≤ M` and `Q₂ ≤ M^g`.
  have hQ₁leM : Q₁ ≤ M := le_trans hQ₁.1 (Subgroup.map_subtype_le _)
  have hQ₂leMg : Q₂ ≤ MulAut.conj g • M := by
    refine le_trans hQ₂.1 ?_
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr
      (Subgroup.map_subtype_le _)
  refine ⟨?_, ?_⟩
  · -- (a) `Q₁ ⊓ Q₂ = ⊥`.
    by_contra hne
    -- `Q₁ ⊓ Q₂ ≤ (M^g ⊓ M) ⊓ Q₁` and `≤ (M^g ⊓ M) ⊓ Q₂`, both nonbot.
    refine key ((MulAut.conj g • M) ⊓ M) hHmm_lt hAHmm ?_ ?_
    · refine fun hbot => hne (le_bot_iff.mp ?_)
      calc Q₁ ⊓ Q₂ ≤ ((MulAut.conj g • M) ⊓ M) ⊓ Q₁ :=
            le_inf (le_inf (le_trans inf_le_right hQ₂leMg) (le_trans inf_le_left hQ₁leM))
              inf_le_left
        _ = ⊥ := hbot
    · refine fun hbot => hne (le_bot_iff.mp ?_)
      calc Q₁ ⊓ Q₂ ≤ ((MulAut.conj g • M) ⊓ M) ⊓ Q₂ :=
            le_inf (le_inf (le_trans inf_le_right hQ₂leMg) (le_trans inf_le_left hQ₁leM))
              inf_le_right
        _ = ⊥ := hbot
  · -- (b) for each `X ∈ ℰ¹(A)` with `X ≤ A`: `C_{Q₁}(X) = ⊥` or `C_{Q₂}(X) = ⊥`.
    intro X hX hXA
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    -- `X ≠ ⊥` (`|X| = p`).
    have hXne : X ≠ ⊥ := by
      rintro rfl
      have := hX.2; simp only [Subgroup.card_bot] at this
      exact h.prime.one_lt.ne' (by simpa using this.symm)
    -- `A ≤ C_G(X)` (`A` abelian, `X ≤ A`).
    have hAcX : A ≤ Subgroup.centralizer (X : Set G) := by
      haveI := hAcomm
      exact le_trans (Subgroup.le_centralizer (H := A))
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXA))
    -- `C_G(X) < ⊤` (else `X ≤ Z(G) = ⊥`, contradicting `X ≠ ⊥`).
    have hCXlt : Subgroup.centralizer (X : Set G) < ⊤ := by
      refine lt_of_le_of_ne le_top (fun htop => hXne (le_bot_iff.mp ?_))
      rw [← hZbot, ← SetLike.coe_subset_coe]
      exact (Subgroup.centralizer_eq_top_iff_subset.mp htop)
    exact key (Subgroup.centralizer (X : Set G)) hCXlt hAcX hc1 hc2

/-- **BG Corollary 11.2** (mmd L2946): `g ∈ G−M`, `A ⊆ M^g` ⇒ (a) `M_σ ⊓ M^g = 1`、
(b) `M_σ ⊓ C_G(A₀^g) = 1`。 -/
theorem Msigma_meet_conjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) :
    S10.Msigma M ⊓ MulAut.conj g • M = ⊥ ∧
    S10.Msigma M ⊓ Subgroup.centralizer ((MulAut.conj g • A₀ : Subgroup G) : Set G) = ⊥ := by
  sorry

/-- **BG Theorem 11.3** (mmd L2955): `M_σ` は nilpotent。 -/
theorem Msigma_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    Group.IsNilpotent ↥(S10.Msigma M) := by
  sorry

/-- **BG Corollary 11.4** (mmd L2959): `H ∈ ℳ(A)` で `M_σ ⊓ H_σ ≠ 1` なら `M = H`。 -/
theorem eq_of_Msigma_meet_Hsigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {H : Subgroup G} (hH : H ∈ maximalSubgroupsContaining A)
    (hne : S10.Msigma M ⊓ S10.Msigma H ≠ ⊥) :
    M = H := by
  sorry

/-- **BG Theorem 11.5** (mmd L2963): `M` の Sylow `p`-部分群は abelian。 -/
theorem sylow_p_isCommutative [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    (S : Sylow p ↥M) :
    IsMulCommutative (S : Subgroup ↥M) := by
  sorry

/-- **BG Corollary 11.6 (a)(b)** (mmd L2974 付近): (a) `A = Ω₁(P)`、(b) `C_{M_σ}(A) = 1`。
(原典 (c): `g₁,g₂∈N_G(P)−N_M(P)` で `C_{M_σ}(A₀^{gᵢ})=1` ∧ `A=A₁×A₂` — 後続。) -/
theorem omega1_eq_and_centralizer_trivial [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    A = (Omega ↥P p 1).map P.subtype ∧
    Subgroup.centralizer (A : Set G) ⊓ S10.Msigma M = ⊥ := by
  sorry

/-- **BG Theorem 11.7** (mmd L2997): `M_σ A ⊴ M`。§11 の主結果。 -/
theorem MsigmaA_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) := by
  sorry

end OddOrder.BG.Ch3.S11
