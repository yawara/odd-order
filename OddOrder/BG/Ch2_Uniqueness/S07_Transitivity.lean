/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.AppA_PStability
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank
import OddOrder.BG.Ch1_Preliminary.S06_Additional
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.GroupTheory.SCN
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# BG §7: The Transitivity Theorem

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter II §7 (pp. 55-60), mmd `references/bg/local-analysis.mmd`
L2131-2314, **6 結果** (Lem 7.1 + Thm 7.2/7.3/7.4/7.6 + Prop 7.5).

§7 で **最小反例 G を本書全体で fix** (`IsMinimalSimpleOdd G`, `Ch2_Uniqueness/Setup`)。中核は
**Hypothesis 7.1** と、その下で `K = O_{π'}(C_G(A))` が `ℋ_G*(A;q)` 上 conjugation で推移的に作用する
ための十分条件群。終結果 **Thm 7.6 (Thompson Transitivity)** は §8–§16 で最頻出。

## 記法 (BG → repo)

- `ℳ`/`ℳ(H)`/`𝒰` = `GroupTheory.MaximalSubgroup`。
- `ℋ_H(A;π)`/`ℋ*` = `GroupTheory.AInvariantPiSubgroups`。
- `ℋ_G*(A;q)` (H = G) = `hInvariantStar ⊤ A {q}`。
- `π(A)` = `primesOf A`; `π'` = `(primesOf A)ᶜ`。`O_π(H)` を `G` 内に戻したもの = `opiCoreInG π H`。
- `K = O_{π'}(C_G(A))` = `kSubgroup A`。`m(Z(A))` = `rank ↥(Subgroup.center ↥A)`。
- `K が S 上推移的に conjugation 作用` = `ConjTransitiveOn K S` (`∃ k∈K, conj k • Q₁ = Q₂`)。
- `SCN₃(p)` global = `scn3Global p` (`∃ Sylow P, A ≤ P ∧ A ∈ SCN₃(P)`; SCN は ↥P 相対)。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を各定理に明示的に通す (Peterfalvi Hypothesis 流儀)。

## proof 完了 (§7 fully sorry-free, 2026-06-04)

全 6 結果 (Lem 7.1 + Thm 7.2/7.3/7.4/7.6 + Prop 7.5) 完全証明済。Prop 1.16 (coprime action
generation, §1), Lem 6.5/6.6 + Thm 6.7 (§6), SCN/p-stability に依存。Prop 7.5 は case (2)
(SCN₂) + case (1) (`A = Ω₁(C_G(A))` ∧ 全真部分群 p-length one, Thm 6.7 経由) の両分岐。

## Lane C proof-gate notes

§7 itself does not consume the Blackburn classification (BG Thm 4.16) or the §5
narrow-p-group theorems. The only §4/§5-sensitive notation here is `SCN_n`: Prop 7.5
assumes `A ∈ SCN₂(P)` directly, and Thm 7.6 assumes `A ∈ SCN₃(p)`. Existence of such
subgroups is a downstream §8/§9 concern (BG Lem 5.1, mmd L1795-1806, L2324, L2629),
not a hypothesis to add to §7.
-/

namespace OddOrder.BG.Ch2.S07

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06 (actionFixedBy mem_actionFixedBy nontrivialActionFixedByClosure
  nontrivialActionFixedByClosure_le_iff)
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7 記法のための helper 定義 -/

/-- `π(A)`: `|A|` の素因子集合。 -/
def primesOf (A : Subgroup G) : Set ℕ := {q | q ∈ (Nat.card ↥A).primeFactors}

/-- `K = O_{π'}(C_G(A))` (Hypothesis 7.1 の `K`)。`opiCoreInG` と `derivedInG` の canonical は
`OddOrder.GroupTheory.SubgroupInAmbient` に移動 (issue 0052; `open OddOrder.GroupTheory` で参照)。 -/
def kSubgroup (A : Subgroup G) : Subgroup G :=
  opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))

/-- `K` が部分群の集合 `S` 上 conjugation で **推移的に作用**する: 任意の `Q₁,Q₂ ∈ S` に対し
ある `k ∈ K` で `Q₁^k = Q₂` (`MulAut.conj k • Q₁ = Q₂`)。 -/
def ConjTransitiveOn (K : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, ∃ k ∈ K, MulAut.conj k • Q₁ = Q₂

/-- If a trivial subgroup acts transitively on `ℋ_H*(A;π)`, that set has at most one
member. -/
theorem hInvariantStar_eq_of_conjTransitiveOn_bot
    {K H A : Subgroup G} {π : Set ℕ} (hKbot : K = ⊥)
    (htrans : ConjTransitiveOn K (hInvariantStar H A π))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar H A π)
    (hQ₂ : Q₂ ∈ hInvariantStar H A π) :
    Q₁ = Q₂ := by
  obtain ⟨k, hkK, hkQ⟩ := htrans Q₁ hQ₁ Q₂ hQ₂
  have hk_one : k = 1 := by
    rw [hKbot, Subgroup.mem_bot] at hkK
    exact hkK
  rw [hk_one, map_one, one_smul] at hkQ
  exact hkQ

/-- **`SCN₃(p)` global** (BG §7 L2137): あるシロー `p`-部分群 `P` で `A ∈ SCN₃(P)`
(↥P 内で `IsSCN₃`) となる `A ≤ G`。 -/
def scn3Global (p : ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G))}

@[simp]
theorem mem_scn3Global {p : ℕ} {A : Subgroup G} :
    A ∈ scn3Global p G ↔
      ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G)) :=
  Iff.rfl

/-- Unpack global `SCN₃(p)` membership into the Sylow subgroup that witnesses it. -/
theorem exists_sylow_of_mem_scn3Global {p : ℕ} {A : Subgroup G}
    (hA : A ∈ scn3Global p G) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G)) :=
  hA

/-- Global `SCN₃(p)` membership also gives the `SCN₂` input used in Proposition 7.5. -/
theorem exists_scn2_sylow_of_mem_scn3Global {p : ℕ} {A : Subgroup G}
    (hA : A ∈ scn3Global p G) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  exact ⟨P, hAP, IsSCN_n.mono (by norm_num) hAscn3⟩

/-- The rank bound carried by global `SCN₃(p)` membership. -/
theorem exists_three_le_pRank_of_mem_scn3Global {p : ℕ} {A : Subgroup G}
    (hA : A ∈ scn3Global p G) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ 3 ≤ pRank (A.subgroupOf (P : Subgroup G)) p := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  exact ⟨P, hAP, hAscn3.2⟩

/-! ## Hypothesis 7.1 -/

/-- **BG Hypothesis 7.1** (mmd L2141): `A` についての固定設定。`π = π(A)`,
`K = O_{π'}(C_G(A))` (`kSubgroup A`) を伴い:

1. `A` は `G` の非自明な真部分群、
2. `A` を含む任意の真部分群 `X` について `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`
   (`sSup (hInvariant X A π') = opiCoreInG π' X`)。 -/
structure Hypothesis71 (A : Subgroup G) : Prop where
  /-- `A ≠ 1`. -/
  ne_bot : A ≠ ⊥
  /-- `A` は `G` の真部分群。 -/
  proper : A < ⊤
  /-- (2): `A ⊆ X < G` なら `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`。 -/
  generated_eq : ∀ X : Subgroup G, A ≤ X → X < ⊤ →
    sSup (hInvariant X A (primesOf A)ᶜ) = opiCoreInG (primesOf A)ᶜ X

namespace Hypothesis71

/-- The generated-subgroup equality from BG Hypothesis 7.1(2), as a named accessor. -/
theorem generated_eq_of_le_of_lt_top {A X : Subgroup G} (hA : Hypothesis71 A)
    (hAX : A ≤ X) (hX : X < ⊤) :
    sSup (hInvariant X A (primesOf A)ᶜ) = opiCoreInG (primesOf A)ᶜ X :=
  hA.generated_eq X hAX hX

end Hypothesis71

/-! ## Conjugation-action bridge and `kSubgroup` API (Lemma 7.1 の部品) -/

/-- The conjugation action of a subgroup `A` on the ambient group `G`. -/
def conjAction (A : Subgroup G) : ↥A →* MulAut G :=
  MulAut.conj.comp A.subtype

/-- `Q` is invariant under the conjugation action of `A` iff `A` normalizes `Q`. -/
theorem isAInvariant_conjAction_iff {A Q : Subgroup G} :
    Ch03.IsAInvariant (conjAction A) Q ↔ A ≤ Subgroup.normalizer Q := by
  constructor
  · intro h a ha
    exact mem_normalizer_of_conj_smul_eq_self (h ⟨a, ha⟩)
  · intro h a
    exact conj_smul_eq_self_of_mem_normalizer (h a.2)

/-- `K = O_{π'}(C_G(A)) ≤ C_G(A)`. -/
theorem kSubgroup_le_centralizer (A : Subgroup G) :
    kSubgroup A ≤ Subgroup.centralizer (A : Set G) :=
  opiCoreInG_le _ _

/-- `K` is a `π'`-subgroup of `G`. -/
theorem isPiSubgroup_kSubgroup [Finite G] (A : Subgroup G) :
    Subgroup.IsPiSubgroup (primesOf A)ᶜ (kSubgroup A) :=
  isPiSubgroup_opiCoreInG _ _

/-- If the centralizer C_G(A) is a pi(A)-subgroup, then K = O_{pi(A)-prime}(C_G(A))
is trivial. This is the group-theoretic bridge used in BG (8.3) -> (8.6). -/
theorem kSubgroup_eq_bot_of_centralizer_isPiSubgroup [Finite G] {A : Subgroup G}
    (hCpi : Subgroup.IsPiSubgroup (primesOf A) (Subgroup.centralizer (A : Set G))) :
    kSubgroup A = ⊥ :=
  opiCoreInG_compl_eq_bot_of_isPiSubgroup hCpi

/-- **BG §7 の Note** (Hypothesis 7.1 直後, mmd L2145): Hypothesis 7.1 のもとで、
`C_G(A)` の任意の `π'`-元は `K = O_{π'}(C_G(A))` に入る。

証明: `X := A ⊔ C_G(A) ≤ N_G(A)` は真部分群 (`G` simple, `A` 非自明真部分群)。
`⟨c⟩ ∈ ℋ_X(A;π')` なので Hypothesis 7.1(2) から `c ∈ O_{π'}(X)`;
`O_{π'}(X) ⊓ C_G(A)` は `C_G(A)` の正規 `π'`-部分群なので `K` に入る。 -/
theorem mem_kSubgroup_of_piPrime_mem_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {c : G}
    (hc : c ∈ Subgroup.centralizer (A : Set G))
    (hc_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ (Subgroup.zpowers c)) :
    c ∈ kSubgroup A := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hC_def
  set X : Subgroup G := A ⊔ C with hX_def
  have hAX : A ≤ X := le_sup_left
  have hCX : C ≤ X := le_sup_right
  -- `X` is proper: it normalizes `A`, and `N_G(A) < ⊤` by simplicity
  have hX_proper : X < ⊤ := by
    have hX_le : X ≤ Subgroup.normalizer A := by
      refine sup_le Subgroup.le_normalizer ?_
      intro x hx
      apply mem_normalizer_of_conj_smul_eq_self
      ext y
      rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        show x * z * x⁻¹ ∈ A
        have hxz : x * z * x⁻¹ = z := by
          rw [← Subgroup.mem_centralizer_iff.mp hx z hz, mul_inv_cancel_right]
        rw [hxz]
        exact hz
      · intro hy
        refine ⟨y, hy, ?_⟩
        show x * y * x⁻¹ = y
        rw [← Subgroup.mem_centralizer_iff.mp hx y hy, mul_inv_cancel_right]
    rw [lt_top_iff_ne_top]
    intro hX_top
    have hnorm_top : Subgroup.normalizer (A : Set G) = ⊤ := by
      apply le_antisymm le_top
      rw [← hX_top]
      exact hX_le
    haveI hA_normal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    rcases hG.simple.eq_bot_or_eq_top_of_normal A hA_normal with h | h
    · exact hA.ne_bot h
    · exact hA.proper.ne h
  -- Hypothesis 7.1(2) puts `c` into `O_{π'}(X)`
  have hzc_mem : Subgroup.zpowers c ∈ hInvariant X A π' := by
    refine ⟨Subgroup.zpowers_le.mpr (hCX hc), ?_, hc_pi'⟩
    intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have hac : a * c * a⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc a ha, mul_inv_cancel_right]
    ext y
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      show c ^ n = MulAut.conj a (c ^ n)
      rw [map_zpow]
      simp only [MulAut.conj_apply]
      rw [hac]
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine ⟨c ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, ?_⟩
      show MulAut.conj a (c ^ n) = y
      rw [map_zpow]
      simp only [MulAut.conj_apply]
      rw [hac, hn]
  have hc_O : c ∈ opiCoreInG π' X := by
    rw [← hA.generated_eq X hAX hX_proper]
    exact le_sSup hzc_mem (Subgroup.mem_zpowers c)
  -- `O_{π'}(X) ⊓ C` is a normal `π'`-subgroup of `C`, hence lies in `K`
  set W : Subgroup G := opiCoreInG π' X ⊓ C with hW_def
  have hW_le_C : W ≤ C := inf_le_right
  have hW_pi' : Subgroup.IsPiSubgroup π' W := by
    intro r hr
    refine isPiSubgroup_opiCoreInG π' X r ?_
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
      dvd_trans (Nat.mem_primeFactors.mp hr).2.1
        (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩
  haveI hWC_normal : (W.subgroupOf C).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgO : (g : G) ∈ Subgroup.normalizer (opiCoreInG π' X) :=
      le_normalizer_opiCoreInG π' X (hCX g.2)
    constructor
    · exact (Subgroup.mem_normalizer_iff.mp hgO _).mp hn.1
    · exact C.mul_mem (C.mul_mem g.2 hn.2) (C.inv_mem g.2)
  have hW_le_K : W ≤ kSubgroup A :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hW_le_C hWC_normal hW_pi'
  exact hW_le_K ⟨hc_O, hc⟩

/-! ## Lemma 7.1 の証明部品 (action 制限・normalizer 増大・q-部分群の真性) -/

/-- `MulAut.conj` 作用は `map` で書ける (S01/S11 の private 版の局所コピー)。 -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- A-不変 `U` 上の制限作用に対し, A-不変な `H` の `subgroupOf U` も不変 (S01 private の局所複製)。 -/
private theorem isAInvariant_subgroupOf_restrict {A : Type*} [Group A]
    {φ : A →* MulAut G} {U H : Subgroup G} (hU : Ch03.IsAInvariant φ U)
    (hH : Ch03.IsAInvariant φ H) :
    Ch03.IsAInvariant hU.restrict (H.subgroupOf U) := by
  rw [Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [Ch03.IsAInvariant.restrict_apply_val]
  exact hH.smul_mem a hh

/-- 不変 `U` の不変部分群を `U.subtype` で `G` に戻すと不変 (S01 private の局所複製)。 -/
private theorem isAInvariant_map_subtype_of_restrict {A : Type*} [Group A]
    {φ : A →* MulAut G} {U : Subgroup G} (hU : Ch03.IsAInvariant φ U)
    {L : Subgroup ↥U} (hL : Ch03.IsAInvariant hU.restrict L) :
    Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl, Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- **q-群内 normalizer 増大** (Lem 7.1 Case B 用, `lt_normalizer_inf_sylow_of_lt` の一般化):
有限 `q`-群 `P` の真部分群 `Q < P` は `N_G(Q) ⊓ P` の真部分群。 -/
private theorem lt_normalizer_inf_of_pgroup_lt [Finite G] {q : ℕ} [Fact q.Prime]
    {P Q : Subgroup G} (hP : IsPGroup q ↥P) (hQP : Q < P) :
    Q < P ⊓ Subgroup.normalizer Q := by
  classical
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hNC : NormalizerCondition ↥P := normalizerCondition_of_isNilpotent (G := ↥P)
  have hQ_le : Q ≤ P := le_of_lt hQP
  have hsub_lt_top : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hQP) (le_antisymm hQ_le htop)
  have hlt := hNC (Q.subgroupOf P) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf hQ_le Subgroup.le_normalizer) ?_
  intro heq
  apply ht_not
  have hmem : (t : G) ∈ P ⊓ Subgroup.normalizer Q := ⟨t.2, ht_norm⟩
  rw [← heq] at hmem
  exact hmem

/-- `ℋ_G*(A;q)` の元は `G` の真部分群 (`G` は `q`-群でない: さもなくば可解)。 -/
private theorem lt_top_of_mem_hInvariantStar [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} {q : ℕ} [Fact q.Prime] {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ A {q}) : Q < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hQtop
  have hpi : Subgroup.IsPiSubgroup {q} (⊤ : Subgroup G) :=
    hQtop ▸ hInvariantStar_isPiSubgroup hQ
  have hpg : IsPGroup q ↥(⊤ : Subgroup G) :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hpi
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) := hpg.isNilpotent
  exact hG.notSolvable
    (solvable_of_surjective (MonoidHom.range_eq_top.mp (Subgroup.range_subtype ⊤)))

/-! ## Lemma 7.1 — 推移性の基底補題 -/

/-- **Lemma 7.1 の共通構成** (mmd L2151-2158): Hypothesis 7.1 のもと、真部分群 `H ⊇ A` で
`H ⊓ Q₁ ≠ 1 ≠ H ⊓ Q₂` のとき、`H ⊓ Qᵢ` を `O_{π'}(H)` の `A`-不変 Sylow `q`-部分群 `Rᵢ` に
含め (Prop 1.5(b))、`R₁^h = R₂` (`h ∈ C_G(A) ∩ O_{π'}(H) ⊆ K`, Prop 1.5(c)) とし、`R₂ ⊆ Q₃`
となる `Q₃ ∈ ℋ_G*(A;q)` を取る。すると (7.1) と `|Q₁^h ∩ H| = |Q₁ ∩ H|` が成り立つ。 -/
private theorem commonConstruction [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q})
    {H : Subgroup G} (hHproper : H < ⊤) (hAH : A ≤ H) :
    ∃ h ∈ kSubgroup A, ∃ Q₃ ∈ hInvariantStar ⊤ A {q},
      MulAut.conj h • Q₁ ∈ hInvariantStar ⊤ A {q} ∧
      (MulAut.conj h • Q₁) ⊓ H ≤ Q₃ ∧
      Q₂ ⊓ H ≤ Q₃ ∧
      Nat.card ↥((MulAut.conj h • Q₁) ⊓ H) = Nat.card ↥(Q₁ ⊓ H) := by
  classical
  set N : Subgroup G := opiCoreInG (primesOf A)ᶜ H with hN_def
  have hN_le_H : N ≤ H := opiCoreInG_le _ _
  have hN_lt : N < ⊤ := lt_of_le_of_lt hN_le_H hHproper
  haveI hN_solv : IsSolvable ↥N := hG.solvable_of_lt_top N hN_lt
  have hN_inv : Ch03.IsAInvariant (conjAction A) N := by
    rw [isAInvariant_conjAction_iff]
    exact le_trans hAH (le_normalizer_opiCoreInG (primesOf A)ᶜ H)
  have hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N) := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG (primesOf A)ᶜ H p hp
  -- `hle_N`: `H ⊓ Q ≤ O_{π'}(H)` for each `Q ∈ ℋ_G*(A;q)` (via Hypothesis 7.1(2)).
  have hle_N : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → H ⊓ Q ≤ N := by
    intro Q hQ
    have hpi_HQ : Subgroup.IsPiSubgroup ((primesOf A)ᶜ) (H ⊓ Q) := by
      refine Subgroup.IsPiSubgroup.mono (Set.singleton_subset_iff.mpr hq) ?_
      intro p hp
      exact (hInvariantStar_isPiSubgroup hQ) p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
          (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
    have hnorm_HQ : A ≤ Subgroup.normalizer (H ⊓ Q) := by
      intro a ha
      apply mem_normalizer_of_conj_smul_eq_self (Q := H ⊓ Q)
      rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hAH ha)),
          conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ ha)]
    have hmem : H ⊓ Q ∈ hInvariant H A ((primesOf A)ᶜ) := ⟨inf_le_left, hnorm_HQ, hpi_HQ⟩
    have h1 := le_sSup hmem
    rwa [hA.generated_eq H hAH hHproper] at h1
  -- `getR`: each `H ⊓ Q` sits in an `A`-invariant Hall `q`-subgroup of `↥N` (Prop 1.5(b)).
  have getR : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} →
      ∃ R : Subgroup ↥N, Ch03.IsHallSubgroup {q} R ∧ Ch03.IsAInvariant hN_inv.restrict R ∧
        (H ⊓ Q).subgroupOf N ≤ R := by
    intro Q hQ
    have hle := hle_N Q hQ
    have hpi_HQ : Subgroup.IsPiSubgroup {q} (H ⊓ Q) := by
      intro p hp
      exact (hInvariantStar_isPiSubgroup hQ) p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
          (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
    have hpi_sub : Ch03.Subgroup.IsPiGroup {q} ((H ⊓ Q).subgroupOf N) := by
      intro p hp
      apply hpi_HQ p
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hp
    have hinv_HQ : Ch03.IsAInvariant (conjAction A) (H ⊓ Q) := by
      rw [isAInvariant_conjAction_iff]
      intro a ha
      apply mem_normalizer_of_conj_smul_eq_self (Q := H ⊓ Q)
      rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hAH ha)),
          conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ ha)]
    have hinv_sub : Ch03.IsAInvariant hN_inv.restrict ((H ⊓ Q).subgroupOf N) :=
      isAInvariant_subgroupOf_restrict hN_inv hinv_HQ
    exact OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := hN_inv.restrict) hCop hpi_sub hinv_sub
  obtain ⟨R₁', hR₁'_hall, hR₁'_inv, hR₁'_ge⟩ := getR Q₁ hQ₁
  obtain ⟨R₂', hR₂'_hall, hR₂'_inv, hR₂'_ge⟩ := getR Q₂ hQ₂
  -- Prop 1.5(c): `R₁ ↦ R₂` by some `c` fixed by `A`, inside `↥N`.
  obtain ⟨c, hc_fix, hc_conj⟩ := OddOrder.BG.Ch1.S01.aInvariant_hall_conj
    (G := ↥N) (A := ↥A) (φ := hN_inv.restrict) hCop hR₁'_hall hR₂'_hall hR₁'_inv hR₂'_inv
  have hc_mem_H : (c : G) ∈ H := hN_le_H c.2
  have hc_norm_H : (c : G) ∈ Subgroup.normalizer H := Subgroup.le_normalizer hc_mem_H
  -- `(c : G) ∈ C_G(A)` (fixed by `A`).
  have hc_centralizer : (c : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hval := congrArg Subtype.val (hc_fix ⟨a, ha⟩)
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  -- `(c : G) ∈ K` (it is a `π'`-element of `C_G(A)`).
  have hzc_le_N : Subgroup.zpowers (c : G) ≤ N := Subgroup.zpowers_le.mpr c.2
  have hc_pi' : Subgroup.IsPiSubgroup ((primesOf A)ᶜ) (Subgroup.zpowers (c : G)) := by
    intro p hp
    exact isPiSubgroup_opiCoreInG (primesOf A)ᶜ H p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
        (Subgroup.card_dvd_of_le hzc_le_N), Nat.card_pos.ne'⟩)
  have hc_K : (c : G) ∈ kSubgroup A :=
    mem_kSubgroup_of_piPrime_mem_centralizer hG hA hc_centralizer hc_pi'
  -- `R₂ := R₂'.map N.subtype` and its `ℋ_G*`-extension `Q₃`.
  set R₂ : Subgroup G := R₂'.map N.subtype with hR₂_def
  have hR₂_pi : Subgroup.IsPiSubgroup {q} R₂ := by
    intro p hp
    rw [hR₂_def] at hp
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₂' N.subtype
      N.subtype_injective).toEquiv] at hp
    exact hR₂'_hall.1 p hp
  have hR₂_norm : A ≤ Subgroup.normalizer R₂ := by
    rw [hR₂_def]
    exact isAInvariant_conjAction_iff.mp (isAInvariant_map_subtype_of_restrict hN_inv hR₂'_inv)
  obtain ⟨Q₃, hQ₃_star, hR₂_le_Q₃⟩ :=
    exists_le_hInvariantStar (H := ⊤) (A := A) (π := {q}) ⟨le_top, hR₂_norm, hR₂_pi⟩
  -- containments of `H ⊓ Qᵢ` in `Rᵢ`.
  have hHQ₁_le_R₁ : H ⊓ Q₁ ≤ R₁'.map N.subtype := by
    have h1 : ((H ⊓ Q₁).subgroupOf N).map N.subtype ≤ R₁'.map N.subtype :=
      Subgroup.map_mono hR₁'_ge
    rwa [Subgroup.map_subgroupOf_eq_of_le (hle_N Q₁ hQ₁)] at h1
  have hHQ₂_le_R₂ : H ⊓ Q₂ ≤ R₂ := by
    have h1 : ((H ⊓ Q₂).subgroupOf N).map N.subtype ≤ R₂'.map N.subtype :=
      Subgroup.map_mono hR₂'_ge
    rw [Subgroup.map_subgroupOf_eq_of_le (hle_N Q₂ hQ₂)] at h1
    rw [hR₂_def]; exact h1
  -- the conjugation/inf identity `(c • Q₁) ⊓ H = c • (Q₁ ⊓ H)`.
  have heq : (MulAut.conj (c : G) • Q₁) ⊓ H = MulAut.conj (c : G) • (Q₁ ⊓ H) := by
    rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer hc_norm_H]
  -- `R₂`-transport `(c • R₁) = R₂`.
  have htransport : MulAut.conj (c : G) • (R₁'.map N.subtype) = R₂ := by
    rw [hR₂_def, ← hc_conj, mulAut_smul_eq_map, mulAut_smul_eq_map, Subgroup.map_map,
        Subgroup.map_map]
    congr 1
  -- assemble.
  refine ⟨(c : G), hc_K, Q₃, hQ₃_star,
    conj_smul_mem_hInvariantStar_top hQ₁ hc_centralizer, ?_, ?_, ?_⟩
  · -- `(c • Q₁) ⊓ H ≤ Q₃`
    rw [heq]
    calc MulAut.conj (c : G) • (Q₁ ⊓ H)
        = MulAut.conj (c : G) • (H ⊓ Q₁) := by rw [inf_comm]
      _ ≤ MulAut.conj (c : G) • (R₁'.map N.subtype) := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]; exact hHQ₁_le_R₁
      _ = R₂ := htransport
      _ ≤ Q₃ := hR₂_le_Q₃
  · -- `Q₂ ⊓ H ≤ Q₃`
    rw [inf_comm]; exact le_trans hHQ₂_le_R₂ hR₂_le_Q₃
  · -- card equality
    rw [heq]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (c : G)) (Q₁ ⊓ H)).toEquiv).symm

/-- **BG Lemma 7.1** (Inductive Lemma, mmd L2147): Hypothesis 7.1 のもと、`q ∈ π'`,
`Q₁, Q₂ ∈ ℋ_G*(A;q)`、`A ⊆ H < G` で `H ∩ Q₁ ≠ 1`, `H ∩ Q₂ ≠ 1` となる真部分群 `H` が
あれば、`Q₂ = Q₁^k` (`k ∈ K`)。`|G|_q / |Q₁∩Q₂|` の帰納が核。 -/
theorem inductiveLemma [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q})
    (H : Subgroup G) (hHproper : H < ⊤) (hAH : A ≤ H)
    (hHQ₁ : H ⊓ Q₁ ≠ ⊥) (hHQ₂ : H ⊓ Q₂ ≠ ⊥) :
    ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁ = Q₂ := by
  classical
  -- 強帰納法 on `|G| - |Q₁ ∩ Q₂|` (BG の `|G|_q/|Q₁∩Q₂|` と同値な減少測度)。
  suffices key : ∀ n : ℕ, ∀ Q₁ Q₂ : Subgroup G, Q₁ ∈ hInvariantStar ⊤ A {q} →
      Q₂ ∈ hInvariantStar ⊤ A {q} → Nat.card G - Nat.card ↥(Q₁ ⊓ Q₂) = n →
      ∀ H : Subgroup G, H < ⊤ → A ≤ H → H ⊓ Q₁ ≠ ⊥ → H ⊓ Q₂ ≠ ⊥ →
      ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁ = Q₂ by
    exact key _ Q₁ Q₂ hQ₁ hQ₂ rfl H hHproper hAH hHQ₁ hHQ₂
  -- 汎用 card ヘルパー。
  have card_mono : ∀ {S T : Subgroup G}, S ≤ T → Nat.card ↥S ≤ Nat.card ↥T :=
    fun h => Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)
  have card_lt : ∀ {S T : Subgroup G}, S < T → Nat.card ↥S < Nat.card ↥T := by
    intro S T hST
    have h2 := Set.ncard_lt_ncard (SetLike.coe_ssubset_coe.mpr hST) (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h2
  have card_inf_le : ∀ S T : Subgroup G, Nat.card ↥(S ⊓ T) ≤ Nat.card G :=
    fun S T => Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q₁ Q₂ hQ₁ hQ₂ hmeasure H hHproper hAH hHQ₁ hHQ₂
    -- IH ラッパー: 交わりが増大 (= 測度減少) すれば再帰できる。
    have applyIH : ∀ Q₁' Q₂' : Subgroup G, Q₁' ∈ hInvariantStar ⊤ A {q} →
        Q₂' ∈ hInvariantStar ⊤ A {q} →
        Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₁' ⊓ Q₂') →
        ∀ H' : Subgroup G, H' < ⊤ → A ≤ H' → H' ⊓ Q₁' ≠ ⊥ → H' ⊓ Q₂' ≠ ⊥ →
        ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁' = Q₂' := by
      intro Q₁' Q₂' hQ₁' hQ₂' hgt H' hH'p hAH' hne1 hne2
      have hlt : Nat.card G - Nat.card ↥(Q₁' ⊓ Q₂') < n := by
        have hle := card_inf_le Q₁' Q₂'; omega
      exact ih _ hlt Q₁' Q₂' hQ₁' hQ₂' rfl H' hH'p hAH' hne1 hne2
    -- 共通構成 (witness = 与えられた `H`)。
    obtain ⟨h, hh_K, Q₃, hQ₃, hconjQ₁, hstep1, hstep2, hcard⟩ :=
      commonConstruction hG hA hq hQ₁ hQ₂ hHproper hAH
    -- `(h • Q₁) ⊓ H` の非自明性。
    have hne_conj : (MulAut.conj h • Q₁) ⊓ H ≠ ⊥ := by
      intro hbot
      have h1 : Q₁ ⊓ H = ⊥ := by
        apply Subgroup.card_eq_one.mp
        rw [← hcard, hbot]; exact Subgroup.card_eq_one.mpr rfl
      exact hHQ₁ (by rw [inf_comm]; exact h1)
    by_cases hQinf : Q₁ ⊓ Q₂ = ⊥
    · -- Case A: `Q₁ ⊓ Q₂ = 1`. 共通構成を H で 1 回、合成 `k = g·f·h`。
      have hbig1 : (MulAut.conj h • Q₁) ⊓ Q₃ ≠ ⊥ := by
        intro hb
        have hle : (MulAut.conj h • Q₁) ⊓ H ≤ (MulAut.conj h • Q₁) ⊓ Q₃ :=
          le_inf inf_le_left hstep1
        rw [hb, le_bot_iff] at hle; exact hne_conj hle
      have hHQ₃ : H ⊓ Q₃ ≠ ⊥ := by
        intro hb
        apply hHQ₂
        have h2 : Q₂ ⊓ H ≤ H ⊓ Q₃ := le_inf inf_le_right hstep2
        rw [hb, le_bot_iff] at h2; rw [inf_comm]; exact h2
      have hbig2 : Q₂ ⊓ Q₃ ≠ ⊥ := by
        intro hb
        apply hHQ₂
        have h2 : Q₂ ⊓ H ≤ Q₂ ⊓ Q₃ := le_inf inf_le_left hstep2
        rw [hb, le_bot_iff] at h2; rw [inf_comm]; exact h2
      have hmes1 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) := by
        rw [hQinf, Subgroup.card_eq_one.mpr rfl]
        exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hbig1
      have hmes2 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₃ ⊓ Q₂) := by
        rw [hQinf, Subgroup.card_eq_one.mpr rfl]
        refine (Subgroup.one_lt_card_iff_ne_bot _).mpr ?_
        rw [inf_comm]; exact hbig2
      obtain ⟨f, hf_K, hf_eq⟩ := applyIH (MulAut.conj h • Q₁) Q₃ hconjQ₁ hQ₃ hmes1
        H hHproper hAH (by rw [inf_comm]; exact hne_conj) hHQ₃
      obtain ⟨g, hg_K, hg_eq⟩ := applyIH Q₃ Q₂ hQ₃ hQ₂ hmes2 H hHproper hAH hHQ₃ hHQ₂
      refine ⟨g * f * h, (kSubgroup A).mul_mem ((kSubgroup A).mul_mem hg_K hf_K) hh_K, ?_⟩
      calc MulAut.conj (g * f * h) • Q₁
          = MulAut.conj g • (MulAut.conj f • (MulAut.conj h • Q₁)) := by
            rw [map_mul, map_mul, mul_smul, mul_smul]
        _ = MulAut.conj g • Q₃ := by rw [hf_eq]
        _ = Q₂ := hg_eq
    · -- Case B: `Q₁ ⊓ Q₂ ≠ 1`. `H' = N_G(Q)` で共通構成し、normalizer 増大で結論。
      have hQ₁_lt : Q₁ < ⊤ := lt_top_of_mem_hInvariantStar hG hQ₁
      have hQ_proper : Q₁ ⊓ Q₂ < ⊤ := lt_of_le_of_lt inf_le_left hQ₁_lt
      have hA_normQ : A ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) := by
        intro a ha
        apply mem_normalizer_of_conj_smul_eq_self (Q := Q₁ ⊓ Q₂)
        rw [Subgroup.smul_inf,
            conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₁ ha),
            conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₂ ha)]
      have hNQ_lt : Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        haveI hnorm : (Q₁ ⊓ Q₂).Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases hG.simple.eq_bot_or_eq_top_of_normal (Q₁ ⊓ Q₂) hnorm with hh | hh
        · exact hQinf hh
        · exact (ne_of_lt hQ_proper) hh
      obtain ⟨h, hh_K, Q₃, hQ₃, hconjQ₁, hstep1, hstep2, hcard⟩ :=
        commonConstruction hG hA hq hQ₁ hQ₂ hNQ_lt hA_normQ
      set NQ : Subgroup G := Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) with hNQ_def
      have hQ_le_NQ : Q₁ ⊓ Q₂ ≤ NQ := Subgroup.le_normalizer
      have hQ_le_M₁ : Q₁ ⊓ Q₂ ≤ Q₁ ⊓ NQ := le_inf inf_le_left hQ_le_NQ
      have hQ_le_M₂ : Q₁ ⊓ Q₂ ≤ Q₂ ⊓ NQ := le_inf inf_le_right hQ_le_NQ
      have hcard1 : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) := by
        rw [← hcard]; exact card_mono (le_inf inf_le_left hstep1)
      have hcard2 : Nat.card ↥(Q₂ ⊓ NQ) ≤ Nat.card ↥(Q₂ ⊓ Q₃) :=
        card_mono (le_inf inf_le_left hstep2)
      have hPQ₁ : IsPGroup q ↥Q₁ :=
        OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (hInvariantStar_isPiSubgroup hQ₁)
      have hPQ₂ : IsPGroup q ↥Q₂ :=
        OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (hInvariantStar_isPiSubgroup hQ₂)
      by_cases hb1 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) ∧
          Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₂ ⊓ Q₃)
      · -- B1: 両交わりが増大 → Case A と同じ合成 (witness = N_G(Q))。
        obtain ⟨hb1a, hb1b⟩ := hb1
        have hM₁_ne : Q₁ ⊓ NQ ≠ ⊥ := fun hb => hQinf (le_bot_iff.mp (hb ▸ hQ_le_M₁))
        have hM₂_ne : Q₂ ⊓ NQ ≠ ⊥ := fun hb => hQinf (le_bot_iff.mp (hb ▸ hQ_le_M₂))
        have hne_conjNQ : NQ ⊓ (MulAut.conj h • Q₁) ≠ ⊥ := by
          rw [inf_comm]
          intro hb
          apply hM₁_ne
          apply Subgroup.card_eq_one.mp
          rw [← hcard, hb]; exact Subgroup.card_eq_one.mpr rfl
        have hNQ_Q₃ : NQ ⊓ Q₃ ≠ ⊥ := by
          intro hb
          apply hM₂_ne
          have h2 : Q₂ ⊓ NQ ≤ NQ ⊓ Q₃ := le_inf inf_le_right hstep2
          rw [hb, le_bot_iff] at h2; exact h2
        have hNQ_Q₂ : NQ ⊓ Q₂ ≠ ⊥ := fun hb => hM₂_ne (by rw [inf_comm]; exact hb)
        obtain ⟨f, hf_K, hf_eq⟩ := applyIH (MulAut.conj h • Q₁) Q₃ hconjQ₁ hQ₃ hb1a
          NQ hNQ_lt hA_normQ hne_conjNQ hNQ_Q₃
        obtain ⟨g, hg_K, hg_eq⟩ := applyIH Q₃ Q₂ hQ₃ hQ₂
          (by rw [inf_comm Q₃ Q₂]; exact hb1b) NQ hNQ_lt hA_normQ hNQ_Q₃ hNQ_Q₂
        refine ⟨g * f * h, (kSubgroup A).mul_mem ((kSubgroup A).mul_mem hg_K hf_K) hh_K, ?_⟩
        calc MulAut.conj (g * f * h) • Q₁
            = MulAut.conj g • (MulAut.conj f • (MulAut.conj h • Q₁)) := by
              rw [map_mul, map_mul, mul_smul, mul_smul]
          _ = MulAut.conj g • Q₃ := by rw [hf_eq]
          _ = Q₂ := hg_eq
      · -- B2: 片方の交わりが増大しない → normalizer 増大より `Q = Qᵢ`、ゆえ `Q₁ = Q₂` (k = 1)。
        rw [not_and_or, not_lt, not_lt] at hb1
        have hle12 : Q₁ ≤ Q₂ ∨ Q₂ ≤ Q₁ := by
          rcases hb1 with hb | hb
          · left
            rw [← inf_eq_left]
            by_contra hne
            have hlt : Q₁ ⊓ Q₂ < Q₁ := lt_of_le_of_ne inf_le_left hne
            have hlt2 : Q₁ ⊓ Q₂ < Q₁ ⊓ NQ := lt_normalizer_inf_of_pgroup_lt hPQ₁ hlt
            have hgt := card_lt hlt2
            have hle' : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥(Q₁ ⊓ Q₂) := le_trans hcard1 hb
            omega
          · right
            rw [← inf_eq_right]
            by_contra hne
            have hlt : Q₁ ⊓ Q₂ < Q₂ := lt_of_le_of_ne inf_le_right hne
            have hlt2 : Q₁ ⊓ Q₂ < Q₂ ⊓ NQ := lt_normalizer_inf_of_pgroup_lt hPQ₂ hlt
            have hgt := card_lt hlt2
            have hle' : Nat.card ↥(Q₂ ⊓ NQ) ≤ Nat.card ↥(Q₁ ⊓ Q₂) := le_trans hcard2 hb
            omega
        have hQ₁Q₂ : Q₁ = Q₂ := by
          rcases hle12 with hle | hle
          · exact (hInvariantStar_eq_of_le hQ₁ (hInvariantStar_mem_hInvariant hQ₂) hle).symm
          · exact hInvariantStar_eq_of_le hQ₂ (hInvariantStar_mem_hInvariant hQ₁) hle
        exact ⟨1, one_mem _, by rw [hQ₁Q₂, map_one, one_smul]⟩

/-! ## Theorem 7.2 / 7.3 — 推移性の rank 条件 -/

/-- `actionFixedBy` of the conjugation action of `B` on `Q` (= `C_Q(x) = Q ⊓ C_G(x)` in
`subgroupOf` form). -/
private theorem actionFixedBy_conjAction_restrict {B Q : Subgroup G}
    (hQ_inv : Ch03.IsAInvariant (conjAction B) Q) (x : ↥B) :
    actionFixedBy hQ_inv.restrict x
      = (Q ⊓ Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf Q := by
  ext g
  rw [mem_actionFixedBy, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)⟩
    rw [Set.mem_singleton_iff] at hy; subst hy
    have hval : ((hQ_inv.restrict x) g : G) = (g : G) := congrArg Subtype.val h
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · rintro ⟨-, hgC⟩
    apply Subtype.ext
    rw [Ch03.IsAInvariant.restrict_apply_val]
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_iff.mp hgC (x : G) (Set.mem_singleton _)]; group

/-- **BG Prop 1.16(1), conjugation form**: a noncyclic abelian subgroup `B ≤ G` normalizing a
coprime subgroup `Q ≠ 1` has a nonidentity element `x` with `Q ⊓ C_G(x) ≠ 1`. (If every
`C_Q(x)` were trivial the centralizers would generate only `1`, contradicting Isaacs 6.21.) -/
theorem exists_mem_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    {B Q : Subgroup G} [IsMulCommutative ↥B] (hBQ : B ≤ Subgroup.normalizer Q)
    (hB_nc : ¬ IsCyclic ↥B) (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q)) (hQ : Q ≠ ⊥) :
    ∃ x ∈ B, x ≠ (1 : G) ∧ Q ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  classical
  have hQ_inv : Ch03.IsAInvariant (conjAction B) Q := isAInvariant_conjAction_iff.mpr hBQ
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hQ_inv.restrict hCop hB_nc
  by_contra hcon
  have hle : nontrivialActionFixedByClosure hQ_inv.restrict ≤ ⊥ := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro x hx_ne
    rw [actionFixedBy_conjAction_restrict]
    have hxbot : Q ⊓ Subgroup.centralizer ({(x : G)} : Set G) = ⊥ := by
      by_contra hne
      exact hcon ⟨(x : G), x.2, fun h => hx_ne (Subtype.ext (by rw [h]; rfl)), hne⟩
    rw [hxbot, Subgroup.bot_subgroupOf]
  rw [htop, top_le_iff] at hle
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  exact bot_ne_top hle

/-- **BG Prop 1.16(2), conjugation form**: a noncyclic abelian `B ≤ G` normalizing a coprime
`Q ≠ 1` has a subgroup `Y ≤ B` with `B/Y` cyclic (`Y ⊔ ⟨b⟩ = B`) and `Q ⊓ C_G(Y) ≠ 1`. -/
theorem exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    {B Q : Subgroup G} [IsMulCommutative ↥B] (hBQ : B ≤ Subgroup.normalizer Q)
    (hB_nc : ¬ IsCyclic ↥B) (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q)) (hQ : Q ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ B ∧ (∃ b ∈ B, Y ⊔ Subgroup.zpowers b = B) ∧
      Q ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := by
  classical
  have hQ_inv : Ch03.IsAInvariant (conjAction B) Q := isAInvariant_conjAction_iff.mpr hBQ
  have htop := OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
    hQ_inv.restrict hCop hB_nc
  by_contra hcon
  push_neg at hcon
  have hle : OddOrder.BG.Ch1.S01.cocyclicFixedByClosure hQ_inv.restrict ≤ ⊥ := by
    rw [OddOrder.BG.Ch1.S01.cocyclicFixedByClosure, Subgroup.closure_le]
    rintro g ⟨Yb, ⟨b, hb⟩, hYfix⟩
    set Y : Subgroup G := Yb.map B.subtype with hYdef
    have hYcocyc : ∃ b' ∈ B, Y ⊔ Subgroup.zpowers b' = B := by
      refine ⟨(b : G), b.2, ?_⟩
      have hzp : Subgroup.zpowers (b : G) = (Subgroup.zpowers b).map B.subtype :=
        (MonoidHom.map_zpowers B.subtype b).symm
      rw [hYdef, hzp, ← Subgroup.map_sup, hb, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmemG : (g : G) ∈ Q ⊓ Subgroup.centralizer (Y : Set G) := by
      refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro y hy
      rw [hYdef, Subgroup.coe_map, Set.mem_image] at hy
      obtain ⟨yb, hyb, rfl⟩ := hy
      have hval : ((hQ_inv.restrict yb) g : G) = (g : G) := congrArg Subtype.val (hYfix yb hyb)
      rw [Ch03.IsAInvariant.restrict_apply_val] at hval
      simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
      exact mul_inv_eq_iff_eq_mul.mp hval
    rw [hcon Y (Subgroup.map_subtype_le _) hYcocyc] at hmemG
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmemG))
  rw [htop, top_le_iff] at hle
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  exact bot_ne_top hle

/-- `n ≤ rank G` で `n > 0` なら、ある素数 `p` で `n ≤ pRank G p` (`rank_le_iff` の逆向き)。 -/
private theorem exists_le_pRank_of_le_rank {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hn : 0 < n) (h : n ≤ rank H) : ∃ p : ℕ, n ≤ pRank H p := by
  by_contra hcon
  push_neg at hcon
  have : rank H ≤ n - 1 := by
    rw [rank_le_iff]; intro p; have := hcon p; omega
  omega

/-- **`m(Z(A)) ≥ n` (n ≥ 2) から `Z(A)` 内の noncyclic elementary abelian 部分群を抽出**:
ある `p ≥ 2` と `B ≤ A`, `B ≤ C_G(A)` (= `B ≤ Z(A)`) で `B` は elementary abelian `p`, noncyclic,
`n ≤ log_p |B|`。Thm 7.2/7.3 の `B ∈ ℰ_p^n(Z(A))` 部分。`B ≤ A` から coprimality (`q ∈ π'` で
`q ∤ |B|`) が従うので `p` の素数性は不要。 -/
private theorem exists_elementaryAbelian_le_center_of_le_rank [Finite G]
    {A : Subgroup G} {n : ℕ} (hn2 : 2 ≤ n) (hm : n ≤ rank ↥(Subgroup.center ↥A)) :
    ∃ (p : ℕ) (B : Subgroup G), B.IsElementaryAbelian p ∧ ¬ IsCyclic ↥B ∧
      n ≤ Nat.log p (Nat.card ↥B) ∧ B ≤ A ∧ B ≤ Subgroup.centralizer (A : Set G) := by
  classical
  set ZA : Subgroup G := (Subgroup.center ↥A).map A.subtype with hZA
  have hrankZA : n ≤ rank ↥ZA :=
    le_trans hm (rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective (Subgroup.center ↥A) A.subtype
        A.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (Subgroup.center ↥A) A.subtype A.subtype_injective).injective)
  obtain ⟨p, hp_rank⟩ := exists_le_pRank_of_le_rank (by omega) hrankZA
  obtain ⟨B₀, hB₀_ea, hB₀_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (by omega : 0 < n) hp_rank
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with hlt | hge
    · exfalso
      have h0 : pRank ↥ZA p ≤ 0 := by
        rw [pRank_le_iff]; intro A' _; rw [Nat.log_of_left_le_one (by omega)]
      omega
    · exact hge
  set B : Subgroup G := B₀.map ZA.subtype with hB
  have hB_ea : B.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.map ZA.subtype_injective hB₀_ea
  have hlogB : n ≤ Nat.log p (Nat.card ↥B) := by
    rw [hB, Subgroup.card_map_of_injective ZA.subtype_injective]; exact hB₀_log
  refine ⟨p, B, hB_ea, ?_, hlogB, le_trans (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _),
    ?_⟩
  · -- ¬ IsCyclic: exponent ∣ p but |B| ≥ p² > p.
    intro hcyc
    have hexp : Monoid.exponent ↥B = Nat.card ↥B := hcyc.exponent_eq_card
    have hdvd : Monoid.exponent ↥B ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact hB_ea.pow_eq_one
    rw [hexp] at hdvd
    have hcard_le : Nat.card ↥B ≤ p := Nat.le_of_dvd (by omega) hdvd
    have hp_sq : p ^ 2 ≤ Nat.card ↥B :=
      (Nat.le_log_iff_pow_le (by omega) Nat.card_pos.ne').mp (le_trans hn2 hlogB)
    rw [pow_two] at hp_sq; nlinarith
  · refine le_trans (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨a, ha⟩)

/-- A cocyclic subgroup `Y` (`Y ⊔ ⟨b⟩ = B`) of an elementary abelian `p`-group `B` of rank
`≥ 3` is noncyclic: `|B| ≤ |Y|·|⟨b⟩| ≤ |Y|·p`, so `|Y| ≥ p²`. -/
private theorem not_isCyclic_of_cocyclic [Finite G] {p : ℕ} (hp2 : 2 ≤ p) {B Y : Subgroup G}
    (hB_ea : B.IsElementaryAbelian p) (hlog : 3 ≤ Nat.log p (Nat.card ↥B))
    (hYB : Y ≤ B) {b : G} (hb : b ∈ B) (hsup : Y ⊔ Subgroup.zpowers b = B) :
    ¬ IsCyclic ↥Y := by
  classical
  haveI : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  set Y' : Subgroup ↥B := Y.subgroupOf B with hY'
  set K : Subgroup ↥B := (Subgroup.zpowers b).subgroupOf B with hK
  haveI : Y'.Normal := Subgroup.normal_of_isMulCommutative _
  have hzple : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hsup' : Y' ⊔ K = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, hY', hK, Subgroup.map_subgroupOf_eq_of_le hYB,
      Subgroup.map_subgroupOf_eq_of_le hzple, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKle : Nat.card ↥K ≤ p := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers]
    refine Nat.le_of_dvd (by omega : 0 < p) (orderOf_dvd_of_pow_eq_one ?_)
    have hbp := congrArg Subtype.val (hB_ea.2 (⟨b, hb⟩ : ↥B)); simpa using hbp
  have hKmap : K.map (QuotientGroup.mk' Y') = ⊤ := by
    have h1 : (Y' ⊔ K).map (QuotientGroup.mk' Y') = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y')]
    rwa [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff Y').mpr (le_of_eq (QuotientGroup.ker_mk' Y').symm),
      bot_sup_eq] at h1
  have hquot_le : Nat.card (↥B ⧸ Y') ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective ((QuotientGroup.mk' Y').comp K.subtype) (by
      intro x
      obtain ⟨k, hk, hkx⟩ := hKmap ▸ Subgroup.mem_top x
      exact ⟨⟨k, hk⟩, hkx⟩)
  have hcardB : Nat.card ↥B ≤ Nat.card ↥K * Nat.card ↥Y := by
    have hY'card : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y', hY'card]
    exact Nat.mul_le_mul_right _ hquot_le
  intro hcyc
  -- `Y` is elementary abelian and cyclic, so `|Y| ≤ p`.
  have hY_ea : Y.IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · show (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (Subtype.val : ↥B → G) (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩)
    · show (x : G) ^ p = 1
      exact congrArg (Subtype.val : ↥B → G) (hB_ea.2 (⟨(x : G), hYB x.2⟩ : ↥B))
  have hYle : Nat.card ↥Y ≤ p := by
    have hdvd : Monoid.exponent ↥Y ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact hY_ea.2
    rw [← hcyc.exponent_eq_card]; exact Nat.le_of_dvd (by omega : 0 < p) hdvd
  have hp3 : p ^ 3 ≤ Nat.card ↥B :=
    (Nat.le_log_iff_pow_le (by omega : 1 < p) Nat.card_pos.ne').mp hlog
  have h1 : Nat.card ↥B ≤ p ^ 2 := by
    rw [pow_two]; exact le_trans hcardB (Nat.mul_le_mul hKle hYle)
  have h2 : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

/-- `C_G(x) < ⊤` for `x ≠ 1` in a minimal simple group (`Z(G) = 1`). -/
private theorem centralizer_singleton_lt_top [Finite G] (hG : IsMinimalSimpleOdd G) {x : G}
    (hx : x ≠ (1 : G)) : Subgroup.centralizer ({x} : Set G) < ⊤ := by
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  rw [lt_top_iff_ne_top]
  intro htop
  refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm

/-- **BG Theorem 7.2** (mmd L2177): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 3` ⇒ `K` は
`ℋ_G*(A;q)` 上推移的。Prop 1.16(2) で `B ∈ ℰ_p³(Z(A))` から cocyclic `Y` (noncyclic) を取り、
`C_{Q₁}(Y) ⊆ C_G(z)` (z∈Y) で Lem 7.1 を適用。 -/
theorem transitive_of_three_le_rank_center [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  classical
  have hCop : ∀ {S Q : Subgroup G}, S ≤ A → Q ∈ hInvariantStar ⊤ A {q} →
      Nat.Coprime (Nat.card ↥S) (Nat.card ↥Q) := by
    intro S Q hSA hQ
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun r hr => ?_) (fun r hr => ?_)
    · exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le hSA), Nat.card_pos.ne'⟩
    · rw [Set.mem_singleton_iff.mp (hInvariantStar_isPiSubgroup hQ r hr)]; exact hq
  have hA_Cz : ∀ z : G, z ∈ Subgroup.centralizer (A : Set G) →
      A ≤ Subgroup.centralizer ({z} : Set G) := by
    intro z hz a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact (Subgroup.mem_centralizer_iff.mp hz a ha).symm
  obtain ⟨p, B, hB_ea, hB_nc, hB_log, hBA, hB_cent⟩ :=
    exists_elementaryAbelian_le_center_of_le_rank (n := 3) (by norm_num) hm
  have hp2 : 2 ≤ p := by
    by_contra h; push_neg at h
    rw [Nat.log_of_left_le_one (by omega)] at hB_log; omega
  intro Q₁ hQ₁ Q₂ hQ₂
  by_cases hQ₁bot : Q₁ = ⊥
  · refine ⟨1, one_mem _, ?_⟩
    rw [map_one, one_smul]
    exact (hQ₁.2 Q₂ (hInvariantStar_mem_hInvariant hQ₂) (by rw [hQ₁bot]; exact bot_le)).symm
  · have hQ₂bot : Q₂ ≠ ⊥ := fun h =>
      hQ₁bot ((hQ₂.2 Q₁ (hInvariantStar_mem_hInvariant hQ₁) (by rw [h]; exact bot_le)).trans h)
    haveI : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
    obtain ⟨Y, hYB, ⟨b, hbB, hsup⟩, hYQ₁⟩ :=
      exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic
        (le_trans hBA (hInvariantStar_le_normalizer hQ₁)) hB_nc (hCop hBA hQ₁) hQ₁bot
    have hY_nc : ¬ IsCyclic ↥Y := not_isCyclic_of_cocyclic hp2 hB_ea hB_log hYB hbB hsup
    haveI : IsMulCommutative ↥Y :=
      IsMulCommutative.of_comm fun x y => Subtype.ext (by
        show (x : G) * (y : G) = (y : G) * (x : G)
        exact congrArg (Subtype.val : ↥B → G) (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩))
    have hYA : Y ≤ A := le_trans hYB hBA
    obtain ⟨z, hzY, hz_ne, hzQ₂⟩ :=
      exists_mem_inf_centralizer_ne_bot_of_not_isCyclic
        (le_trans hYA (hInvariantStar_le_normalizer hQ₂)) hY_nc (hCop hYA hQ₂) hQ₂bot
    have hHQ₁ : Subgroup.centralizer ({z} : Set G) ⊓ Q₁ ≠ ⊥ := by
      rw [inf_comm]
      refine fun h => hYQ₁ (le_bot_iff.mp ?_)
      rw [← h]
      exact le_inf inf_le_left (le_trans inf_le_right
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzY)))
    obtain ⟨k, hk_K, hk_eq⟩ := inductiveLemma hG hA hq hQ₁ hQ₂
      (Subgroup.centralizer ({z} : Set G)) (centralizer_singleton_lt_top hG hz_ne)
      (hA_Cz z (le_trans hYB hB_cent hzY)) hHQ₁ (by rw [inf_comm]; exact hzQ₂)
    exact ⟨k, hk_K, hk_eq⟩

/-- If `K = O_{π'}(C_G(A))` is trivial, Theorem 7.2 makes `ℋ_G*(A;q)`
a singleton. This is the reusable form of the first conclusion in BG (8.6). -/
theorem hInvariantStar_eq_of_three_le_rank_center_of_kSubgroup_eq_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {A : Subgroup G} (hA : Hypothesis71 A)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) (hKbot : kSubgroup A = ⊥)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_conjTransitiveOn_bot hKbot
    (transitive_of_three_le_rank_center hG hA hq hm) hQ₁ hQ₂

/-- If C_G(A) is a pi(A)-subgroup, Theorem 7.2 makes H_G*(A;q) a singleton.
This packages the kSubgroup-triviality bridge needed in BG (8.6). -/
theorem hInvariantStar_eq_of_three_le_rank_center_of_centralizer_isPiSubgroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {A : Subgroup G} (hA : Hypothesis71 A)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A))
    (hCpi : Subgroup.IsPiSubgroup (primesOf A) (Subgroup.centralizer (A : Set G)))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_three_le_rank_center_of_kSubgroup_eq_bot hG hA hq hm
    (kSubgroup_eq_bot_of_centralizer_isPiSubgroup hCpi) hQ₁ hQ₂

/-- **BG Theorem 7.3** (mmd L2187): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 2` かつ
`q ∈ π(C_G(A))` ⇒ `K` は `ℋ_G*(A;q)` 上推移的。`R ⊇ Sylow_q(C_G(A))` 経由で Lem 7.1 を連鎖。 -/
theorem transitive_of_two_le_rank_center_of_dvd [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 2 ≤ rank ↥(Subgroup.center ↥A))
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  classical
  -- `Z(G) = 1` (nonabelian simple), so `C_G(x) < ⊤` for `x ≠ 1`.
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hCGx_proper : ∀ x : G, x ≠ 1 → Subgroup.centralizer ({x} : Set G) < ⊤ := by
    intro x hx
    rw [lt_top_iff_ne_top]
    intro htop
    refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm
  -- `B ≤ Z(A)` noncyclic elementary abelian.
  obtain ⟨p, B, hB_ea, hB_nc, _hB_log, hBA, hB_cent⟩ :=
    exists_elementaryAbelian_le_center_of_le_rank (n := 2) le_rfl hm
  haveI : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  -- coprimality `(|B|, |Q|) = 1` for any `Q ∈ ℋ_G*(A;q)`.
  have hCop_BQ : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} →
      Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q) := by
    intro Q hQ
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun r hr => ?_) (fun r hr => ?_)
    · exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le hBA), Nat.card_pos.ne'⟩
    · rw [Set.mem_singleton_iff.mp (hInvariantStar_isPiSubgroup hQ r hr)]; exact hq
  -- `B` normalizes every `Q ∈ ℋ_G*(A;q)` (via `B ≤ A`).
  have hBnorm : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → B ≤ Subgroup.normalizer Q :=
    fun Q hQ => le_trans hBA (hInvariantStar_le_normalizer hQ)
  -- Cauchy: a nonidentity `A`-invariant `q`-subgroup `cc ≤ C_G(A)`.
  obtain ⟨c, hc_ord⟩ :=
    exists_prime_orderOf_dvd_card' q (G := ↥(Subgroup.centralizer (A : Set G)))
      (Nat.mem_primeFactors.mp hqc).2.1
  set cc : Subgroup G := Subgroup.zpowers (c : G) with hcc
  have hc_mem : (c : G) ∈ Subgroup.centralizer (A : Set G) := c.2
  have hcc_le_cent : cc ≤ Subgroup.centralizer (A : Set G) := Subgroup.zpowers_le.mpr hc_mem
  have hcc_card : Nat.card ↥cc = q := by
    rw [hcc, Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.centralizer (A : Set G)).subtype
      (Subgroup.subtype_injective _) c).trans hc_ord
  have hcc_ne : cc ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hcc_card
    exact (Nat.Prime.one_lt (Fact.out : q.Prime)).ne hcc_card
  have hcc_mem : cc ∈ hInvariant ⊤ A {q} := by
    refine ⟨le_top, ?_, ?_⟩
    · intro a ha
      apply mem_normalizer_of_conj_smul_eq_self
      have hac : a * (c : G) * a⁻¹ = (c : G) := by
        rw [Subgroup.mem_centralizer_iff.mp hc_mem a ha, mul_inv_cancel_right]
      ext y
      rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        show (c : G) ^ n = MulAut.conj a ((c : G) ^ n)
        rw [map_zpow]; simp only [MulAut.conj_apply]; rw [hac]
      · intro hy
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ⟨(c : G) ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, by
          show MulAut.conj a ((c : G) ^ n) = y
          rw [map_zpow]; simp only [MulAut.conj_apply]; rw [hac, hn]⟩
    · intro r hr
      rw [hcc_card] at hr
      rw [Set.mem_singleton_iff,
        ← Finset.mem_singleton, ← Nat.Prime.primeFactors (Fact.out : q.Prime)]
      exact hr
  -- every `Q ∈ ℋ_G*(A;q)` is nontrivial.
  have hQne : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → Q ≠ ⊥ := by
    intro Q hQ hQbot
    have heq : cc = Q := hQ.2 cc hcc_mem (by rw [hQbot]; exact bot_le)
    rw [hQbot] at heq; exact hcc_ne heq
  -- `A ≤ C_G(x)` and `C_R(x) ≠ 1` for `x ∈ B`.
  have hA_CGx : ∀ x ∈ B, A ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hB_cent hx) a ha).symm
  -- main transitivity.
  intro Q₁ hQ₁ Q₂ hQ₂
  obtain ⟨R, hR_mem, hcc_le_R⟩ := exists_le_hInvariantStar hcc_mem
  have hCRx : ∀ x ∈ B, R ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro x hx h
    refine hcc_ne (le_bot_iff.mp ?_)
    rw [← h]
    exact le_inf hcc_le_R
      (le_trans hcc_le_cent (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hBA hx))))
  obtain ⟨x, hxB, hx_ne, hQ₁x⟩ :=
    exists_mem_inf_centralizer_ne_bot_of_not_isCyclic (hBnorm Q₁ hQ₁) hB_nc (hCop_BQ Q₁ hQ₁)
      (hQne Q₁ hQ₁)
  obtain ⟨f, hf_K, hf_eq⟩ := inductiveLemma hG hA hq hQ₁ hR_mem
    (Subgroup.centralizer ({x} : Set G)) (hCGx_proper x hx_ne) (hA_CGx x hxB)
    (by rw [inf_comm]; exact hQ₁x) (by rw [inf_comm]; exact hCRx x hxB)
  obtain ⟨x', hx'B, hx'_ne, hQ₂x'⟩ :=
    exists_mem_inf_centralizer_ne_bot_of_not_isCyclic (hBnorm Q₂ hQ₂) hB_nc (hCop_BQ Q₂ hQ₂)
      (hQne Q₂ hQ₂)
  obtain ⟨g, hg_K, hg_eq⟩ := inductiveLemma hG hA hq hR_mem hQ₂
    (Subgroup.centralizer ({x'} : Set G)) (hCGx_proper x' hx'_ne) (hA_CGx x' hx'B)
    (by rw [inf_comm]; exact hCRx x' hx'B) (by rw [inf_comm]; exact hQ₂x')
  exact ⟨g * f, (kSubgroup A).mul_mem hg_K hf_K, by rw [map_mul, mul_smul, hf_eq]; exact hg_eq⟩

/-! ## Theorem 7.4 — 推移性の伝播 -/

-- **Hall C in a subgroup** engine (`↥V` 可解 + `π`-Hall 共役) は §6 へ移動済:
-- `OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf` (Thm 7.4(d) と Lem 6.5(c) の共有)。

/-- **subnormal proper ⟹ 真の正規 overgroup** (Thm 7.4 還元 R1 step1): `A'` が `Q` で subnormal
かつ `A' < ⊤` なら `∃ B ⊴ Q`, `A' ≤ B < ⊤`。subnormal 系列の頂点直下を `IsSubnormal` 帰納で。 -/
private theorem exists_normal_lt_top_of_isSubnormal {Q : Type*} [Group Q] {A' : Subgroup Q}
    (hA' : A'.IsSubnormal) (hlt : A' < ⊤) :
    ∃ B : Subgroup Q, A' ≤ B ∧ B < ⊤ ∧ B.Normal := by
  revert hlt
  induction hA' with
  | top => intro hlt; exact absurd rfl hlt.ne
  | step H K hle hSubn hN ih =>
    intro hlt
    rcases eq_or_lt_of_le (le_top : K ≤ ⊤) with hKtop | hKlt
    · refine ⟨H, le_refl _, hlt, ?_⟩
      subst hKtop
      exact Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN))
    · obtain ⟨B, hKB, hBlt, hBnorm⟩ := ih hKlt
      exact ⟨B, hle.trans hKB, hBlt, hBnorm⟩

/-- **nontrivial 有限可解群は素数指数の正規部分群を持つ** (Thm 7.4 還元 R1a, mmd L2206
composition factor)。card 最大の proper 正規部分群 `N` を取ると `Q⧸N` は simple かつ solvable
ゆえ abelian、`Group.is_simple_iff_prime_card` で素数位数 `= N.index`。 -/
private theorem exists_normal_index_prime_of_solvable {Q : Type*} [Group Q] [Finite Q]
    [IsSolvable Q] (hQ : Nontrivial Q) : ∃ N : Subgroup Q, N.Normal ∧ N.index.Prime := by
  obtain ⟨N, hNmem, hNmax⟩ :=
    Set.exists_max_image {N : Subgroup Q | N.Normal ∧ N < ⊤} (fun N : Subgroup Q => Nat.card ↥N)
      (Set.toFinite _) ⟨⊥, inferInstance, bot_lt_top⟩
  obtain ⟨hNnorm, hNlt⟩ := hNmem
  haveI := hNnorm
  refine ⟨N, hNnorm, ?_⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI hntq : Nontrivial (Q ⧸ N) := by
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hNlt
    exact ⟨QuotientGroup.mk x, 1, by rw [Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  haveI hsimple : IsSimpleGroup (Q ⧸ N) := by
    refine ⟨fun Nbar hNbar => ?_⟩
    set N' : Subgroup Q := Nbar.comap (QuotientGroup.mk' N) with hN'
    haveI : N'.Normal := hNbar.comap _
    have hNN' : N ≤ N' := by
      intro x hx
      rw [hN', Subgroup.mem_comap,
        show (QuotientGroup.mk' N) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hmapeq : N'.map (QuotientGroup.mk' N) = Nbar := by
      rw [hN', Subgroup.map_comap_eq_self_of_surjective hsurj]
    rcases lt_or_eq_of_le (le_top : N' ≤ ⊤) with hN'lt | hN'top
    · left
      have hcard : Nat.card ↥N' ≤ Nat.card ↥N := hNmax N' ⟨inferInstance, hN'lt⟩
      have hN'eqN : N = N' := Subgroup.eq_of_le_of_card_ge hNN' hcard
      rw [← hmapeq, ← hN'eqN]
      simp [QuotientGroup.map_mk'_self]
    · right
      rw [← hmapeq, hN'top, Subgroup.map_top_of_surjective _ hsurj]
  haveI : IsMulCommutative (Q ⧸ N) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  rw [Subgroup.index_eq_card]
  exact Group.is_simple_iff_prime_card.mp hsimple

/-- **Theorem 7.4 composition-series 還元** (R1, mmd L2206-2216): `A < P` subnormal, `P` 可解
(`hG`+`P<⊤`) ⟹ `∃ B`, `A ≤ B < P`, `B ⊴ P`, `|P:B|` 素数。subnormal 系列頂点直下
(`exists_normal_lt_top_of_isSubnormal`) を素数指数化 (`exists_normal_index_prime_of_solvable`
@`↥P⧸B̄`) し pull back + `↥P`→`G` translate。「`A` subnormal in `B`」は R3 で別途。 -/
private theorem tp_reduction [Finite G] (hG : IsMinimalSimpleOdd G) {A P : Subgroup G}
    (hAP : A ≤ P) (hAlt : A < P) (hPlt : P < ⊤) (hAsub : (A.subgroupOf P).IsSubnormal) :
    ∃ B : Subgroup G, A ≤ B ∧ B < P ∧ (B.subgroupOf P).Normal ∧ (B.subgroupOf P).index.Prime := by
  haveI : IsSolvable ↥P := hG.solvable_of_lt_top P hPlt
  have hA'lt : A.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hAlt.not_ge h
  obtain ⟨Bbar, hABbar, hBbarlt, hBbarnorm⟩ := exists_normal_lt_top_of_isSubnormal hAsub hA'lt
  haveI := hBbarnorm
  haveI hnt : Nontrivial (↥P ⧸ Bbar) := by
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hBbarlt
    exact ⟨QuotientGroup.mk x, 1, by rw [Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  obtain ⟨Nbar, hNbarnorm, hNbarprime⟩ := exists_normal_index_prime_of_solvable hnt
  set C : Subgroup ↥P := Nbar.comap (QuotientGroup.mk' Bbar) with hC
  haveI : C.Normal := hNbarnorm.comap _
  have hBbarC : Bbar ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_comap,
      show (QuotientGroup.mk' Bbar) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hCindex : C.index = Nbar.index :=
    Nbar.index_comap_of_surjective (QuotientGroup.mk'_surjective Bbar)
  have hCeq : (C.map P.subtype).subgroupOf P = C :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective C
  refine ⟨C.map P.subtype, ?_, ?_, ?_, ?_⟩
  · have hAC : A.subgroupOf P ≤ C := hABbar.trans hBbarC
    have hA_eq : (A.subgroupOf P).map P.subtype = A := by
      rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hAP
    rw [← hA_eq]; exact Subgroup.map_mono hAC
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
    intro hBP
    have : C = ⊤ := by rw [← hCeq, hBP, Subgroup.subgroupOf_self]
    rw [this, Subgroup.index_top] at hCindex
    exact hNbarprime.ne_one hCindex.symm
  · rw [hCeq]; infer_instance
  · rw [hCeq, hCindex]; exact hNbarprime

/-- **Theorem 7.4(a)** (mmd L2204): `C_G(P) ⊓ K = O_{π'}(C_G(P))`。`A ≤ P` ⟹ `C_G(P) ⊆ C_G(A)`,
`K = O_{π'}(C_G(A)) ⊴ C_G(A)` ゆえ `C_G(P)⊓K` は `C_G(P)` の正規 `π'`-部分群 (⊆ O_{π'});
逆は O_{π'}(C_G(P)) の各元が `C_G(A)` の `π'`-元 ⟹ §7 Note で `K` 入り。 -/
private theorem tp_centralizer_eq [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {P : Subgroup G} (hAP : A ≤ P) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) := by
  set π' : Set ℕ := (primesOf A)ᶜ
  set CP : Subgroup G := Subgroup.centralizer (P : Set G) with hCP
  have hCPCA : CP ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    exact fun y hy => hx y (hAP hy)
  have hCPnK : CP ≤ Subgroup.normalizer (kSubgroup A) :=
    hCPCA.trans (le_normalizer_opiCoreInG _ _)
  apply le_antisymm
  · refine le_opiCoreInG_of_normal_of_isPiSubgroup inf_le_left ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) h
      have h2 := Subgroup.mem_normalizer_iff.mp (hCPnK hx) h
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨h1.mp ha, h2.mp hb⟩
      · rintro ⟨ha, hb⟩; exact ⟨h1.mpr ha, h2.mpr hb⟩
    · intro r hr
      have hdvd : Nat.card ↥(CP ⊓ kSubgroup A) ∣ Nat.card ↥(kSubgroup A) :=
        Subgroup.card_dvd_of_le inf_le_right
      refine isPiSubgroup_kSubgroup A r ?_
      rw [Nat.mem_primeFactors] at hr ⊢
      exact ⟨hr.1, hr.2.1.trans hdvd, Nat.card_pos.ne'⟩
  · refine le_inf (opiCoreInG_le _ _) ?_
    intro c hc
    refine mem_kSubgroup_of_piPrime_mem_centralizer hG hA (hCPCA (opiCoreInG_le _ _ hc)) ?_
    have hzle : Subgroup.zpowers c ≤ opiCoreInG π' CP := Subgroup.zpowers_le.mpr hc
    intro r hr
    refine isPiSubgroup_opiCoreInG π' CP r ?_
    have hdvd : Nat.card ↥(Subgroup.zpowers c) ∣ Nat.card ↥(opiCoreInG π' CP) :=
      Subgroup.card_dvd_of_le hzle
    rw [Nat.mem_primeFactors] at hr ⊢
    exact ⟨hr.1, hr.2.1.trans hdvd, Nat.card_pos.ne'⟩

/-- `A ≤ B ≤ P` で `P` が `π(A)`-群なら `π(B) = π(A)` (`A≤B` で `⊆`、`B≤P` で `⊇`)。
Thm 7.4 帰納で `B` を `A` の役に据えるとき `π` 不変を保証。 -/
private theorem primesOf_eq_of_le_of_isPiSubgroup [Finite G] {A B P : Subgroup G}
    (hAB : A ≤ B) (hBP : B ≤ P) (hP : Subgroup.IsPiSubgroup (primesOf A) P) :
    primesOf B = primesOf A := by
  have hAB_card : Nat.card ↥A ∣ Nat.card ↥B := Subgroup.card_dvd_of_le hAB
  have hBP_card : Nat.card ↥B ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hBP
  ext r
  constructor
  · intro hr
    have hrB : r ∈ (Nat.card ↥B).primeFactors := hr
    rw [Nat.mem_primeFactors] at hrB
    exact hP r (Nat.mem_primeFactors.mpr ⟨hrB.1, hrB.2.1.trans hBP_card, Nat.card_pos.ne'⟩)
  · intro hr
    have hrA : r ∈ (Nat.card ↥A).primeFactors := hr
    rw [Nat.mem_primeFactors] at hrA
    exact Nat.mem_primeFactors.mpr ⟨hrA.1, hrA.2.1.trans hAB_card, Nat.card_pos.ne'⟩

/-- **Hypothesis 7.1 の単調性** (mmd L2212 "Hypothesis 7.1 is satisfied with `B`"): `A ≤ B`,
`π(B) = π(A)`, `B ≠ 1`, `B < ⊤` なら `Hypothesis71 B`。`generated_eq` は
`ℋ_X(B;π') ⊆ ℋ_X(A;π')` と `O_{π'}(X) ∈ ℋ_X(B;π')` から。 -/
private theorem tp_hyp71_of_le [Finite G] {A B : Subgroup G} (hA : Hypothesis71 A)
    (hAB : A ≤ B) (hprimes : primesOf B = primesOf A) (hBne : B ≠ ⊥) (hBlt : B < ⊤) :
    Hypothesis71 B := by
  refine ⟨hBne, hBlt, ?_⟩
  intro X hBX hXlt
  rw [hprimes]
  have hAX : A ≤ X := hAB.trans hBX
  have hA_eq := hA.generated_eq X hAX hXlt
  refine le_antisymm ?_ ?_
  · rw [← hA_eq]
    refine sSup_le_sSup ?_
    intro Y hY
    exact ⟨hY.1, hAB.trans hY.2.1, hY.2.2⟩
  · exact le_sSup ⟨opiCoreInG_le _ _, hBX.trans (le_normalizer_opiCoreInG _ _),
      isPiSubgroup_opiCoreInG _ _⟩

/-- **(c) の `q`-群正規化条件 finish** (mmd L2230-2232): `Q ≤ Q₁` (`Q₁` `q`-群) かつ
`Q₁ ⊓ N_G(Q) ≤ Q` なら `Q = Q₁` (`q`-群で自己正規化部分群は全体)。 -/
private theorem eq_of_inf_normalizer_le [Finite G] {q : ℕ} [Fact q.Prime] {Q Q₁ : Subgroup G}
    (hQ₁ : IsPGroup q ↥Q₁) (hQQ₁ : Q ≤ Q₁) (hself : Q₁ ⊓ Subgroup.normalizer Q ≤ Q) :
    Q = Q₁ := by
  rcases eq_or_lt_of_le hQQ₁ with h | h
  · exact h
  · have hlt := lt_normalizer_inf_of_pgroup_lt hQ₁ h
    have heq : Q₁ ⊓ Subgroup.normalizer Q = Q :=
      le_antisymm hself (le_inf hQQ₁ Subgroup.le_normalizer)
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl Q)

/-- **(c) の `Q ≤ O_{π'}(N_G(Q))`**: `π`-部分群 `Q` は自身の正規化群の `O_π` に入る
(`Q ⊴ N_G(Q)` + `Q` は `π`-群; `le_opiCoreInG_of_normal_of_isPiSubgroup`)。 -/
private theorem le_opiCoreInG_normalizer_self [Finite G] {π : Set ℕ} {Q : Subgroup G}
    (hQpi : Subgroup.IsPiSubgroup π Q) :
    Q ≤ opiCoreInG π (Subgroup.normalizer Q) :=
  le_opiCoreInG_of_normal_of_isPiSubgroup Subgroup.le_normalizer
    Subgroup.normal_in_normalizer hQpi

/-- **`opiCoreInG` is `MulAut`-equivariant**: `φ • O_π(H) = O_π(φ • H)`. The `π`-core
`oPiCore π ↥H` is characteristic, so the iso `↥H ≃* ↥(φ•H)` induced by `φ` carries it onto
`oPiCore π ↥(φ•H)` (`oPiCore.map_eq_of_mulEquiv`); mapping back along the subtypes agrees with
applying `φ`. -/
private theorem conj_smul_opiCoreInG [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  -- `φ` restricts to an isomorphism `↥H ≃* ↥(φ • H)`.
  have hHmap : H.map (φ : G →* G) = φ • H := (mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]
    _ = opiCoreInG π (φ • H) := rfl

/-- **Conjugation by a normalizing element fixes the centralizer**: if `conj x • A = A`
then `conj x • C_G(A) = C_G(A)`. -/
private theorem conj_smul_centralizer_eq {A : Subgroup G} {x : G}
    (hAeq : MulAut.conj x • A = A) :
    MulAut.conj x • Subgroup.centralizer (A : Set G) = Subgroup.centralizer (A : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  have hAeq' : MulAut.conj x⁻¹ • A = A := by
    conv_lhs => rw [← hAeq]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hconj : ((MulAut.conj x)⁻¹ • y) = x⁻¹ * y * x := by
    rw [← map_inv]
    simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
  constructor
  · intro hy a ha
    have haxA : x⁻¹ * a * x ∈ A := by
      have hmem : MulAut.conj x⁻¹ a ∈ MulAut.conj x⁻¹ • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hAeq'] at hmem
      simpa only [MulAut.conj_apply, inv_inv] using hmem
    have hc := hy (x⁻¹ * a * x) haxA
    rw [hconj] at hc
    have hkey : x⁻¹ * (a * y) * x = x⁻¹ * (y * a) * x := by
      calc x⁻¹ * (a * y) * x = (x⁻¹ * a * x) * (x⁻¹ * y * x) := by group
        _ = (x⁻¹ * y * x) * (x⁻¹ * a * x) := hc
        _ = x⁻¹ * (y * a) * x := by group
    exact mul_left_cancel (mul_right_cancel hkey)
  · intro hy a ha
    rw [hconj]
    have haxA : x * a * x⁻¹ ∈ A := by
      have hmem : MulAut.conj x a ∈ MulAut.conj x • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hAeq] at hmem
      simpa only [MulAut.conj_apply] using hmem
    have hc := hy (x * a * x⁻¹) haxA
    calc a * (x⁻¹ * y * x) = x⁻¹ * ((x * a * x⁻¹) * y) * x := by group
      _ = x⁻¹ * (y * (x * a * x⁻¹)) * x := by rw [hc]
      _ = x⁻¹ * y * x * a := by group

/-- **`N_G(A)` normalizes `K = O_{π'}(C_G(A))`**: for `x ∈ N_G(A)`, conjugation fixes `C_G(A)`
(centralizer of the normalized `A`) and hence (by equivariance) its `π'`-core `K`. -/
private theorem conj_smul_kSubgroup_eq [Finite G] {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer A) :
    MulAut.conj x • kSubgroup A = kSubgroup A := by
  rw [kSubgroup, conj_smul_opiCoreInG,
    conj_smul_centralizer_eq (conj_smul_eq_self_of_mem_normalizer hx)]

/-- **`N_G(P)` normalizes `O_{π'}(C_G(P))`**: same equivariance, for any subgroup `P`. -/
private theorem conj_smul_opiCore_centralizer_eq [Finite G] {π : Set ℕ} {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj x • opiCoreInG π (Subgroup.centralizer (P : Set G))
      = opiCoreInG π (Subgroup.centralizer (P : Set G)) := by
  rw [conj_smul_opiCoreInG,
    conj_smul_centralizer_eq (conj_smul_eq_self_of_mem_normalizer hx)]

/-- **Conjugation transports normalization**: `S ≤ N(Q) ⟹ conj g • S ≤ N(conj g • Q)`. -/
private theorem conj_smul_le_normalizer_of_le_normalizer {S Q : Subgroup G} {g : G}
    (hS : S ≤ Subgroup.normalizer Q) :
    MulAut.conj g • S ≤ Subgroup.normalizer (MulAut.conj g • Q) := by
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
  have hyN : (MulAut.conj g)⁻¹ • y ∈ Subgroup.normalizer Q := hS hy
  -- `y = conj g • ((conj g)⁻¹ • y)` normalizes `conj g • Q`.
  apply mem_normalizer_of_conj_smul_eq_self
  have hcval : ((MulAut.conj g)⁻¹ • y) = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
  have hyeq : MulAut.conj y • (MulAut.conj g • Q)
      = MulAut.conj g • (MulAut.conj ((MulAut.conj g)⁻¹ • y) • Q) := by
    rw [hcval, smul_smul, smul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hyeq, conj_smul_eq_self_of_mem_normalizer hyN]

/-- **Conjugation commutes with the normalizer** (equality form): `conj g • N(Q) = N(conj g • Q)`. -/
private theorem conj_smul_normalizer_eq (g : G) (Q : Subgroup G) :
    MulAut.conj g • Subgroup.normalizer (Q : Set G)
      = Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G) := by
  refine le_antisymm (conj_smul_le_normalizer_of_le_normalizer (le_refl _)) ?_
  have hback := conj_smul_le_normalizer_of_le_normalizer
    (S := Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G))
    (Q := MulAut.conj g • Q) (g := g⁻¹) (le_refl _)
  have hQ' : MulAut.conj g⁻¹ • (MulAut.conj g • Q) = Q := by
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hQ'] at hback
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  have hmem : MulAut.conj g⁻¹ • y
      ∈ MulAut.conj g⁻¹ • Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G) :=
    Subgroup.smul_mem_pointwise_smul_iff.mpr hy
  exact hback hmem

/-- **A `K`-element normalizing `P` centralizes `P`** (`N_K(P) = C_K(P)`, mmd L2242): if
`A ⊴ P` (so `P ≤ N_G(A)`, whence `P` normalizes `K = O_{π'}(C_G(A))`) and `P ⊓ K = 1`
(coprime orders), then `c ∈ K` normalizing `P` lies in `C_G(P)`. For `x ∈ P`,
`⁅x, c⁆ ∈ P` (as `c ∈ N(P)`) and `⁅x, c⁆ ∈ K` (as `P ≤ N(K)`, `c ∈ K`), so `⁅x,c⁆ ∈ P⊓K = 1`. -/
private theorem mem_centralizer_of_mem_kSubgroup_normalizer [Finite G] {A P : Subgroup G}
    (hPnA : P ≤ Subgroup.normalizer A) (hPK : P ⊓ kSubgroup A = ⊥)
    {c : G} (hcK : c ∈ kSubgroup A) (hcN : c ∈ Subgroup.normalizer P) :
    c ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  -- `⁅x, c⁆ = x c x⁻¹ c⁻¹ ∈ P ⊓ K = 1`.
  have hxcx : x * c * x⁻¹ ∈ kSubgroup A := by
    have h := conj_smul_kSubgroup_eq (hPnA hx)
    have hmem : MulAut.conj x c ∈ MulAut.conj x • kSubgroup A :=
      Subgroup.smul_mem_pointwise_smul_iff.mpr hcK
    rw [h] at hmem
    simpa only [MulAut.conj_apply] using hmem
  have hcomm_K : x * c * x⁻¹ * c⁻¹ ∈ kSubgroup A :=
    (kSubgroup A).mul_mem hxcx ((kSubgroup A).inv_mem hcK)
  have hcomm_P : x * c * x⁻¹ * c⁻¹ ∈ P := by
    have hcxc : c * x⁻¹ * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (P.inv_mem hx)
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]; exact P.mul_mem hx hcxc
  have hcomm_one : x * c * x⁻¹ * c⁻¹ = 1 := by
    have : x * c * x⁻¹ * c⁻¹ ∈ P ⊓ kSubgroup A := Subgroup.mem_inf.mpr ⟨hcomm_P, hcomm_K⟩
    rw [hPK, Subgroup.mem_bot] at this
    exact this
  -- `x c x⁻¹ c⁻¹ = 1 ⟹ x * c = c * x`.
  have : x * c = c * x := by
    have h2 : x * c * x⁻¹ = c := mul_inv_eq_one.mp hcomm_one
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h2]
  exact this

/-- **`ℋ_⊤(A;π)` は `N_G(A)`-共役で安定** (C_G(A) 版 `conj_smul_mem_hInvariant_top` の N_G(A) 拡張)。
`g` が `A` を (conj 作用で) 不変にすれば `conj g • Q` も `A`-不変。 -/
private theorem conj_smul_mem_hInvariant_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariant ⊤ A π) {g : G} (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariant ⊤ A π := by
  obtain ⟨-, hQnorm, hQpi⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨le_top, ?_, ?_⟩
  · intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have ha' : g⁻¹ * a * g ∈ A := by
      have hmem : MulAut.conj g⁻¹ a ∈ MulAut.conj g⁻¹ • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hgA'] at hmem
      simpa only [MulAut.conj_apply, inv_inv] using hmem
    calc MulAut.conj a • MulAut.conj g • Q
        = MulAut.conj (a * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj (g * (g⁻¹ * a * g)) • Q := by group
      _ = MulAut.conj g • MulAut.conj (g⁻¹ * a * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj g • Q := by
          rw [conj_smul_eq_self_of_mem_normalizer (hQnorm ha')]
  · have hcard : Nat.card ↥(MulAut.conj g • Q) = Nat.card ↥Q :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Q).toEquiv).symm
    intro r hr
    rw [hcard] at hr
    exact hQpi r hr

/-- **`ℋ_⊤*(A;π)` は `N_G(A)`-共役で安定**: 極大性は順序同型 `Q ↦ Q^g` で移送。 -/
private theorem conj_smul_mem_hInvariantStar_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A π) {g : G} (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariantStar ⊤ A π := by
  obtain ⟨hQmem, hQmax⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨conj_smul_mem_hInvariant_of_normalizer hQmem hgA, ?_⟩
  intro Q' hQ' hle
  have h1 : MulAut.conj g⁻¹ • Q' ∈ hInvariant ⊤ A π :=
    conj_smul_mem_hInvariant_of_normalizer hQ' hgA'
  have h2 : Q ≤ MulAut.conj g⁻¹ • Q' := by
    calc Q = MulAut.conj g⁻¹ • MulAut.conj g • Q := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj g⁻¹ • Q' := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]; exact hle
  have h3 : MulAut.conj g⁻¹ • Q' = Q := hQmax _ h1 h2
  calc Q' = MulAut.conj g • MulAut.conj g⁻¹ • Q' := by
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    _ = MulAut.conj g • Q := by rw [h3]

/-- **Theorem 7.4(c) 主要 case** (mmd L2224-2232): `Q ∈ ℋ*(P;q)` 非自明 ⟹ `Q ∈ ℋ*(A;q)`。
`Q ⊆ Q₁ ∈ ℋ*(A;q)`; `M := O_{π'}(N_G(Q))`; Prop 1.5(b) で `Q ⊆` P-不変 Sylow-q `R₂` of `M`,
`Q ∈ ℋ*(P;q)` 極大で `Q = R₂`; Hyp 7.1 で `Q₁⊓N(Q) ⊆ M`; 位数 `|Q|=|R₂|=|M|_q ≥ |Q₁⊓N(Q)| ≥ |Q|`
⟹ `Q = Q₁⊓N(Q)`, `eq_of_inf_normalizer_le` で `Q = Q₁`。`commonConstruction` の relativize を踏襲。 -/
private theorem tp_c_main [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ P {q}) (hQne : Q ≠ ⊥) :
    Q ∈ hInvariantStar ⊤ A {q} := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ with hπ'
  have hPnQ : P ≤ Subgroup.normalizer Q := hInvariantStar_le_normalizer hQ
  have hQpi : Subgroup.IsPiSubgroup {q} Q := hInvariantStar_isPiSubgroup hQ
  have hQpi' : Subgroup.IsPiSubgroup π' Q := hQpi.mono (Set.singleton_subset_iff.mpr hq)
  have hAnQ : A ≤ Subgroup.normalizer Q := hAP.trans hPnQ
  obtain ⟨Q₁, hQ₁star, hQQ₁⟩ :=
    exists_le_hInvariantStar (H := ⊤) (A := A) (π := {q}) ⟨le_top, hAnQ, hQpi⟩
  suffices hQeqQ₁ : Q = Q₁ by rw [hQeqQ₁]; exact hQ₁star
  have hQlt : Q < ⊤ := lt_top_of_mem_hInvariantStar hG hQ
  have hNQ_lt : Subgroup.normalizer (Q : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    haveI : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with h | h
    · exact hQne h
    · exact (ne_of_lt hQlt) h
  set NQ : Subgroup G := Subgroup.normalizer Q with hNQ
  set M : Subgroup G := opiCoreInG π' NQ with hMdef
  have hM_le : M ≤ NQ := opiCoreInG_le _ _
  have hM_lt : M < ⊤ := lt_of_le_of_lt hM_le hNQ_lt
  haveI hM_solv : IsSolvable ↥M := hG.solvable_of_lt_top M hM_lt
  have hPnM : P ≤ Subgroup.normalizer M := hPnQ.trans (le_normalizer_opiCoreInG π' NQ)
  have hM_inv : Ch03.IsAInvariant (conjAction P) M := isAInvariant_conjAction_iff.mpr hPnM
  have hCop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥M) := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hP_pi p hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG π' NQ p hp
  have hQM : Q ≤ M := le_opiCoreInG_normalizer_self hQpi'
  have hQ_inv : Ch03.IsAInvariant (conjAction P) Q := isAInvariant_conjAction_iff.mpr hPnQ
  have hQM_pi : Ch03.Subgroup.IsPiGroup {q} (Q.subgroupOf M) := by
    intro p hp
    exact hQpi p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv] at hp)
  have hQM_inv : Ch03.IsAInvariant hM_inv.restrict (Q.subgroupOf M) :=
    isAInvariant_subgroupOf_restrict hM_inv hQ_inv
  obtain ⟨R, hR_hall, hR_inv, hR_ge⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥M) (A := ↥P) (φ := hM_inv.restrict) hCop hQM_pi hQM_inv
  set R₂ : Subgroup G := R.map M.subtype with hR₂def
  have hR₂_pi : Subgroup.IsPiSubgroup {q} R₂ := by
    intro p hp
    rw [hR₂def, ← Nat.card_congr (Subgroup.equivMapOfInjective R M.subtype
      M.subtype_injective).toEquiv] at hp
    exact hR_hall.1 p hp
  have hR₂_inv : P ≤ Subgroup.normalizer R₂ :=
    isAInvariant_conjAction_iff.mp (isAInvariant_map_subtype_of_restrict hM_inv hR_inv)
  have hQR₂ : Q ≤ R₂ := by
    rw [hR₂def]
    calc Q = (Q.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hQM).symm
      _ ≤ R.map M.subtype := Subgroup.map_mono hR_ge
  have hQeqR₂ : R₂ = Q := hInvariantStar_eq_of_le hQ ⟨le_top, hR₂_inv, hR₂_pi⟩ hQR₂
  -- `Q₁ ⊓ NQ ≤ M` via Hypothesis 7.1.
  have hnorm : A ≤ Subgroup.normalizer (Q₁ ⊓ NQ) := by
    intro a ha
    apply mem_normalizer_of_conj_smul_eq_self (Q := Q₁ ⊓ NQ)
    rw [Subgroup.smul_inf,
      conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₁star ha),
      conj_smul_eq_self_of_mem_normalizer ((hAnQ.trans Subgroup.le_normalizer) ha)]
  have hQ₁NQ_pi' : Subgroup.IsPiSubgroup π' (Q₁ ⊓ NQ) := by
    intro p hp
    have hpq : p = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ₁star) p
      (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩))
    rw [hpq]; exact hq
  have hNQ₁_le_M : Q₁ ⊓ NQ ≤ M := by
    have h1 := le_sSup (s := hInvariant NQ A π') (a := Q₁ ⊓ NQ)
      ⟨inf_le_right, hnorm, hQ₁NQ_pi'⟩
    rwa [hA.generated_eq NQ hAnQ hNQ_lt] at h1
  -- Order: `|Q₁ ⊓ NQ| ∣ |R| = |R₂| = |Q|`.
  have h1 : Ch03.Subgroup.IsPiGroup {q} ((Q₁ ⊓ NQ).subgroupOf M) := by
    intro p hp
    have hp' : p ∈ (Nat.card ↥(Q₁ ⊓ NQ)).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ₁_le_M).toEquiv] at hp
    exact (hInvariantStar_isPiSubgroup hQ₁star) p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp').1, (Nat.mem_primeFactors.mp hp').2.1.trans
        (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
  have hcard_dvd : Nat.card ↥(Q₁ ⊓ NQ) ∣ Nat.card ↥R := by
    have hd := hR_hall.card_dvd_of_isPiGroup h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ₁_le_M).toEquiv] at hd
  have hcardR_eq : Nat.card ↥R = Nat.card ↥Q := by
    rw [← hQeqR₂, hR₂def,
      Nat.card_congr (Subgroup.equivMapOfInjective R M.subtype M.subtype_injective).toEquiv]
  have hle1 : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥Q := by
    rw [← hcardR_eq]; exact Nat.le_of_dvd Nat.card_pos hcard_dvd
  have hQ_le_NQ₁ : Q ≤ Q₁ ⊓ NQ := le_inf hQQ₁ Subgroup.le_normalizer
  have heq : Q = Q₁ ⊓ NQ := Subgroup.eq_of_le_of_card_ge hQ_le_NQ₁ hle1
  exact eq_of_inf_normalizer_le
    (isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ₁star)) hQQ₁
    (le_of_eq heq.symm)

/-- **BG Theorem 7.4 (7.3)** (mmd L2218-2220): `P` が `A` を (conj 作用で) 不変にし `g ∈ P`,
`g^p ∈ A`, `A ⊔ ⟨g⟩ = P` かつ `p ∤ |ℋ*(A;q)|` なら `P` は `ℋ*(A;q)` のある元を正規化する。
`P/A` は位数 `1` か `p` の `p`-群として `Ω = ℋ*(A;q)` に作用 (`A` は各元を固定) ⟹ 不動点
(`card_modEq_card_fixedPoints` + `p ∤ |Ω|`)。証明では生成元 `g` の誘導 perm `σ` の `zpowers σ`
を使う (`σ^p = 1` since `g^p ∈ A`)。 -/
private theorem tp_exists_normalized [Finite G] {A P : Subgroup G} {q : ℕ} [Fact q.Prime]
    {p : ℕ} [Fact p.Prime] (hPnA : ∀ x ∈ P, MulAut.conj x • A = A) {g : G} (hgP : g ∈ P)
    (hgpA : g ^ p ∈ A) (hsup : A ⊔ Subgroup.zpowers g = P)
    (hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q})) :
    ∃ Q ∈ hInvariantStar ⊤ A {q}, P ≤ Subgroup.normalizer Q := by
  classical
  set S : Set (Subgroup G) := hInvariantStar ⊤ A {q} with hS_def
  -- `↥P` acts on `↥S` by conjugation; `conj_smul_mem_hInvariantStar_of_normalizer` keeps us in `S`.
  let smulFn : ↥P → ↥S → ↥S := fun x Q => ⟨MulAut.conj (x : G) • (Q : Subgroup G),
      conj_smul_mem_hInvariantStar_of_normalizer Q.2 (hPnA (x : G) x.2)⟩
  letI act : MulAction ↥P ↥S :=
    { smul := smulFn
      one_smul := fun Q => by
        apply Subtype.ext
        show MulAut.conj ((1 : ↥P) : G) • (Q : Subgroup G) = (Q : Subgroup G)
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun x y Q => by
        apply Subtype.ext
        show MulAut.conj (((x * y : ↥P)) : G) • (Q : Subgroup G)
          = MulAut.conj ((x : G)) • MulAut.conj ((y : G)) • (Q : Subgroup G)
        rw [Subgroup.coe_mul, map_mul, mul_smul] }
  have hsmul_coe : ∀ (x : ↥P) (Q : ↥S),
      ((x • Q : ↥S) : Subgroup G) = MulAut.conj (x : G) • (Q : Subgroup G) := fun _ _ => rfl
  -- The induced permutation of the generator `g`.
  set σ : Equiv.Perm ↥S := MulAction.toPermHom ↥P ↥S ⟨g, hgP⟩ with hσ_def
  -- `σ ^ p = 1` because `g ^ p ∈ A` acts trivially (every `Q ∈ S` is `A`-invariant).
  have hσp : σ ^ p = 1 := by
    rw [hσ_def, ← map_pow]
    apply Equiv.ext
    intro Q
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    apply Subtype.ext
    rw [hsmul_coe, Subgroup.coe_pow]
    show MulAut.conj (g ^ p) • (Q : Subgroup G) = (Q : Subgroup G)
    exact conj_smul_eq_self_of_mem_normalizer
      ((hInvariantStar_le_normalizer Q.2) hgpA)
  -- `zpowers σ` is a `p`-group: its order `= orderOf σ ∣ p`.
  haveI hPgroup : IsPGroup p ↥(Subgroup.zpowers σ) := by
    rcases (Nat.dvd_prime (Fact.out (p := p.Prime))).mp
      (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  -- `p ∤ |S|` ⟹ fixed points are nonempty (`card_modEq_card_fixedPoints`).
  have hmod := hPgroup.card_modEq_card_fixedPoints (α := ↥S)
  have hcard_ne : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥S) ≠ 0 := by
    intro hzero
    apply hpdvd
    have hSeq : Nat.card ↥S = Nat.card ↥(hInvariantStar ⊤ A {q}) := by rw [hS_def]
    rw [hzero] at hmod
    rw [← hSeq]
    exact (Nat.modEq_zero_iff_dvd).mp hmod
  haveI hne : Nonempty (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥S) :=
    (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hcard_ne)).1
  obtain ⟨Q, hQfix⟩ := hne.some
  -- Unfold the fixed-point property: `σ` fixes `Q`, i.e. `conj g • Q.1 = Q.1`.
  have hσQ : (⟨σ, Subgroup.mem_zpowers σ⟩ : ↥(Subgroup.zpowers σ)) • Q = Q :=
    hQfix ⟨σ, Subgroup.mem_zpowers σ⟩
  -- The subgroup action of `⟨σ,_⟩` is `σ Q`, and `σ Q = ⟨g,hgP⟩ • Q` (`toPermHom`).
  have hσval : σ Q = Q := by
    rw [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] at hσQ
    exact hσQ
  have h1 : (⟨g, hgP⟩ : ↥P) • Q = Q := by
    have hstep : (⟨g, hgP⟩ : ↥P) • Q = σ Q := by
      rw [hσ_def, MulAction.toPermHom_apply, MulAction.toPerm_apply]
    rw [hstep, hσval]
  have hgN : MulAut.conj g • (Q : Subgroup G) = (Q : Subgroup G) := by
    have h2 := congrArg (Subtype.val : ↥S → Subgroup G) h1
    rwa [hsmul_coe] at h2
  refine ⟨(Q : Subgroup G), Q.2, ?_⟩
  -- `P = A ⊔ ⟨g⟩ ≤ N(Q)`: `A` normalizes `Q` (membership of `S`), `g ∈ N(Q)` by `hgN`.
  rw [← hsup, sup_le_iff]
  refine ⟨hInvariantStar_le_normalizer Q.2, ?_⟩
  rw [Subgroup.zpowers_le]
  exact mem_normalizer_of_conj_smul_eq_self hgN

/-- **(7.3) for prime index** (mmd L2218-2220): if `A ⊴ P` with `|P:A| = p` prime and
`p ∤ |ℋ*(A;q)|`, then `P` normalizes some element of `ℋ*(A;q)`. Extract a generator `g` of
the cyclic prime-order quotient `↥P ⧸ A` and apply `tp_exists_normalized`. -/
private theorem tp_exists_normalized_of_prime_index [Finite G] {A P : Subgroup G} {q : ℕ}
    [Fact q.Prime] [hAnormal : (A.subgroupOf P).Normal] (hAP : A ≤ P) {p : ℕ} (hp : p.Prime)
    (hindex : (A.subgroupOf P).index = p)
    (hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q})) :
    ∃ Q ∈ hInvariantStar ⊤ A {q}, P ≤ Subgroup.normalizer Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Bbar : Subgroup ↥P := A.subgroupOf P with hBbar
  have hcardQ : Nat.card (↥P ⧸ Bbar) = p := by rw [← Subgroup.index_eq_card]; exact hindex
  haveI hcyc : IsCyclic (↥P ⧸ Bbar) := isCyclic_of_prime_card hcardQ
  obtain ⟨gbar, hgbar⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective Bbar gbar
  set g : G := (g' : G) with hg_def
  have hgP : g ∈ P := g'.2
  -- `g ^ p ∈ A`.
  have hgpA : g ^ p ∈ A := by
    have hpow : (QuotientGroup.mk' Bbar g') ^ p = 1 := by
      rw [← hcardQ]; exact pow_card_eq_one'
    rw [← map_pow] at hpow
    have hmem : (g' ^ p) ∈ Bbar := (QuotientGroup.eq_one_iff _).mp hpow
    rw [hBbar, Subgroup.mem_subgroupOf] at hmem
    have hcoe : ((g' ^ p : ↥P) : G) = g ^ p := by rw [Subgroup.coe_pow]
    rwa [hcoe] at hmem
  -- `A ⊔ zpowers g = P`.
  have hsup : A ⊔ Subgroup.zpowers g = P := by
    have htop : Bbar ⊔ Subgroup.zpowers g' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' Bbar x ∈ Subgroup.zpowers (QuotientGroup.mk' Bbar g') := by
        rw [hgbar]; exact Subgroup.mem_top _
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, hn⟩ := hx
      rw [← map_zpow] at hn
      have hmemB : x * (g' ^ n)⁻¹ ∈ Bbar := by
        rw [← QuotientGroup.eq_one_iff]
        rw [show ((x * (g' ^ n)⁻¹ : ↥P) : ↥P ⧸ Bbar) = QuotientGroup.mk' Bbar (x * (g' ^ n)⁻¹) from
          rfl, map_mul, map_inv, hn, mul_inv_cancel]
      have hx_eq : x = (x * (g' ^ n)⁻¹) * g' ^ n := by group
      rw [hx_eq]
      exact (Bbar ⊔ Subgroup.zpowers g').mul_mem (Subgroup.mem_sup_left hmemB)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩))
    -- Map `Bbar ⊔ ⟨g'⟩ = ⊤` from `↥P` to `G`.
    apply le_antisymm
    · exact sup_le hAP ((Subgroup.zpowers_le).mpr hgP)
    · intro x hxP
      have hximg : (⟨x, hxP⟩ : ↥P) ∈ Bbar ⊔ Subgroup.zpowers g' := htop ▸ Subgroup.mem_top _
      rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hximg
      obtain ⟨a, ha, z, hz, haz⟩ := hximg
      rw [SetLike.mem_coe, hBbar, Subgroup.mem_subgroupOf] at ha
      have hzG : (z : G) ∈ Subgroup.zpowers g := by
        rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hz
        obtain ⟨n, hn⟩ := hz
        have hzval : (z : G) = g ^ n := by rw [← hn, hg_def, Subgroup.coe_zpow]
        rw [hzval]
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
      have hxval : x = (a : G) * (z : G) := by
        have hc := congrArg (Subtype.val : ↥P → G) haz
        rw [Subgroup.coe_mul] at hc
        exact hc.symm
      rw [hxval]
      exact (A ⊔ Subgroup.zpowers g).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hzG)
  have hPnA : ∀ x ∈ P, MulAut.conj x • A = A := fun x hx =>
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer_of_normal_subgroupOf hAP hx)
  exact tp_exists_normalized hPnA hgP hgpA hsup hpdvd

/-- **Theorem 7.4(b)** (mmd L2234-2244): `O_{π'}(C_G(P))` is transitive on `ℋ_G*(P;q)`.
For `Q₁,Q₂ ∈ ℋ*(P;q)`: by (c) (`hc_sub`) both lie in `ℋ*(A;q)`, so `htrans` gives `k ∈ K`
with `Q₂ = Q₁^k`. Inside `V := (K⊔P)⊓N(Q₂) = (K∩N(Q₂))·P`, the Hall-`π` subgroups `P` and
`P^k` are conjugate by some `κ ∈ K∩N(Q₂)` (`exists_conj_eq_of_isHall_subgroupOf`); then
`c := κk ∈ K∩N(P)`, which centralizes `P` (`mem_centralizer_of_mem_kSubgroup_normalizer`),
so `c ∈ C_G(P)⊓K = O_{π'}(C_G(P))` by (a), and `Q₁^c = Q₂`. -/
private theorem tp_b [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) (hPlt : P < ⊤)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}))
    (hc_sub : hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q}) :
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) := by
  classical
  set K : Subgroup G := kSubgroup A with hK_def
  -- Standing facts.
  have hPnA : P ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hAP
  have hKnA : K ≤ Subgroup.normalizer (A : Set G) :=
    (kSubgroup_le_centralizer A).trans (Subgroup.centralizer_le_normalizer _)
  have hK_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ K := isPiSubgroup_kSubgroup A
  have hAne : A ≠ ⊥ := hA.ne_bot
  have hNA_lt : Subgroup.normalizer (A : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    haveI : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal A inferInstance with h | h
    · exact hAne h
    · exact (ne_of_lt hA.proper) h
  have hKsupP_lt : K ⊔ P < ⊤ := lt_of_le_of_lt (sup_le hKnA hPnA) hNA_lt
  haveI hKsupP_solv : IsSolvable ↥(K ⊔ P) := hG.solvable_of_lt_top _ hKsupP_lt
  -- `P` normalizes `K` (since `P ≤ N(A)` normalizes `K = O_{π'}(C_G(A))`).
  have hPnK : P ≤ Subgroup.normalizer (K : Set G) :=
    fun x hx => mem_normalizer_of_conj_smul_eq_self (conj_smul_kSubgroup_eq (hPnA hx))
  have hKsupP_le_NK : K ⊔ P ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hPnK
  haveI hKnorm : (K.subgroupOf (K ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hKsupP_le_NK
  -- `P ⊓ K = ⊥` (coprime orders: `P` is `π`, `K` is `π'`).
  have hCopPK : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p hp => hP_pi p hp) (fun p hp => hK_pi' p hp)
  have hPK_bot : P ⊓ K = ⊥ := by
    have h1 : Nat.card ↥(P ⊓ K) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(P ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
    have : Nat.card ↥(P ⊓ K) = 1 :=
      Nat.dvd_one.mp (hCopPK.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
    exact Subgroup.card_eq_one.mp this
  -- Part (a): `O_{π'}(C_G(P)) = C_G(P) ⊓ K`.
  have hpartA : opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G))
      = Subgroup.centralizer (P : Set G) ⊓ K := (tp_centralizer_eq hG hA hAP).symm
  rw [hpartA]
  -- Main transitivity argument.
  intro Q₁ hQ₁ Q₂ hQ₂
  -- (c): both lie in `ℋ*(A;q)`; `htrans` gives `k ∈ K` with `Q₂ = Q₁^k`.
  obtain ⟨k, hkK, hkeq⟩ := htrans Q₁ (hc_sub hQ₁) Q₂ (hc_sub hQ₂)
  -- `P` normalizes both `Q₁, Q₂` and `P^k = conj k • P` normalizes `Q₂`.
  have hPnQ₁ : P ≤ Subgroup.normalizer Q₁ := hInvariantStar_le_normalizer hQ₁
  have hPnQ₂ : P ≤ Subgroup.normalizer Q₂ := hInvariantStar_le_normalizer hQ₂
  have hP'nQ₂ : MulAut.conj k • P ≤ Subgroup.normalizer Q₂ := by
    rw [← hkeq]; exact conj_smul_le_normalizer_of_le_normalizer hPnQ₁
  set P' : Subgroup G := MulAut.conj k • P with hP'_def
  set NQ₂ : Subgroup G := Subgroup.normalizer Q₂ with hNQ₂_def
  set V : Subgroup G := (K ⊔ P) ⊓ NQ₂ with hV_def
  set K' : Subgroup G := K ⊓ NQ₂ with hK'_def
  -- `P' = conj k • P ≤ K ⊔ P` (`k ∈ K ≤ K⊔P`, `P ≤ K⊔P`).
  have hP'_le_KsupP : P' ≤ K ⊔ P := by
    rw [hP'_def]
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hkmem : k ∈ K ⊔ P := Subgroup.mem_sup_left hkK
    have h := (K ⊔ P).mul_mem ((K ⊔ P).mul_mem hkmem (Subgroup.mem_sup_right hy)) (inv_mem hkmem)
    have heq : k * ((MulAut.conj k)⁻¹ • y) * k⁻¹ = y := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rwa [heq] at h
  -- Memberships in `V`.
  have hP_le_V : P ≤ V := le_inf le_sup_right hPnQ₂
  have hP'_le_V : P' ≤ V := le_inf hP'_le_KsupP hP'nQ₂
  have hK'_le_V : K' ≤ V := le_inf (le_trans inf_le_left le_sup_left) inf_le_right
  have hV_lt : V < ⊤ := lt_of_le_of_lt (le_trans inf_le_left (le_refl _)) hKsupP_lt
  haveI hV_solv : IsSolvable ↥V := hG.solvable_of_lt_top V hV_lt
  -- `V = K' ⊔ P` (BG `N_{KP}(Q₂) = (K∩N(Q₂))·P`).
  have hKP_mul : (↑(K ⊔ P) : Set G) = (K : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K P hPnK
  have hV_eq : K' ⊔ P = V := by
    refine le_antisymm (sup_le hK'_le_V hP_le_V) ?_
    intro v hv
    rw [hV_def, Subgroup.mem_inf] at hv
    obtain ⟨hvKP, hvNQ₂⟩ := hv
    rw [← SetLike.mem_coe, hKP_mul, Set.mem_mul] at hvKP
    obtain ⟨κ, hκK, s, hsP, hvκs⟩ := hvKP
    have hsNQ₂ : s ∈ NQ₂ := hPnQ₂ hsP
    have hκNQ₂ : κ ∈ NQ₂ := by
      have : κ = v * s⁻¹ := by rw [← hvκs]; group
      rw [this]; exact NQ₂.mul_mem hvNQ₂ (NQ₂.inv_mem hsNQ₂)
    have hκK' : κ ∈ K' := Subgroup.mem_inf.mpr ⟨hκK, hκNQ₂⟩
    rw [← hvκs]
    exact (K' ⊔ P).mul_mem (Subgroup.mem_sup_left hκK') (Subgroup.mem_sup_right hsP)
  -- `K' ⊓ P = ⊥` (`K'≤K`, `K⊓P=⊥`).
  have hK'P_bot : K' ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf_right P (inf_le_left : K' ≤ K)) ?_
    rw [inf_comm]; exact le_of_eq hPK_bot
  -- `V` normalizes `K'` (each `v ∈ V` normalizes `K` and `N(Q₂)`).
  have hVnK' : V ≤ Subgroup.normalizer (K' : Set G) := by
    intro v hv
    apply mem_normalizer_of_conj_smul_eq_self
    have hvNK : MulAut.conj v • K = K := by
      have : v ∈ K ⊔ P := (le_trans inf_le_left (le_refl (K ⊔ P))) hv
      exact conj_smul_eq_self_of_mem_normalizer (hKsupP_le_NK this)
    have hvNQ₂ : v ∈ NQ₂ := (le_trans inf_le_right (le_refl NQ₂)) hv
    have hvNNQ₂ : MulAut.conj v • NQ₂ = NQ₂ := by
      have hvQ₂ : MulAut.conj v • Q₂ = Q₂ := conj_smul_eq_self_of_mem_normalizer hvNQ₂
      rw [hNQ₂_def, conj_smul_normalizer_eq, hvQ₂]
    rw [hK'_def, Subgroup.smul_inf, hvNK, hvNNQ₂]
  -- `K'` is normal in `↥V`.
  haveI hK'_normal : (K'.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK'_le_V).mpr hVnK'
  -- `IsComplement'` of `K'` and `P` inside `↥V`, giving `|V| = |K'| * |P|`.
  have hdisj : Disjoint (K'.subgroupOf V) (P.subgroupOf V) := by
    rw [disjoint_iff]
    rw [show K'.subgroupOf V ⊓ P.subgroupOf V = (K' ⊓ P).subgroupOf V from
      (Subgroup.comap_inf K' P V.subtype).symm, hK'P_bot, Subgroup.bot_subgroupOf]
  have hsup_top : K'.subgroupOf V ⊔ P.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK'_le_V hP_le_V, hV_eq, Subgroup.subgroupOf_self]
  have hcompl : Subgroup.IsComplement' (K'.subgroupOf V) (P.subgroupOf V) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    have hmul := Subgroup.normal_mul (K'.subgroupOf V) (P.subgroupOf V)
    rw [hsup_top] at hmul
    rw [← hmul]; rfl
  have hVcard : Nat.card ↥K' * Nat.card ↥P = Nat.card ↥V := by
    have h := hcompl.card_mul
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'_le_V).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_V).toEquiv] at h
  -- `K'` is a `π'`-group (subgroup of `K`).
  have hK'_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ K' := fun p hp =>
    hK_pi' p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le inf_le_left),
      Nat.card_pos.ne'⟩)
  -- Both `P` and `P'` are `π`-Hall subgroups of `V`.
  have mkHall : ∀ R : Subgroup G, R ≤ V → Nat.card ↥R = Nat.card ↥P →
      Ch03.IsHallSubgroup (primesOf A) (R.subgroupOf V) := by
    intro R hRV hRcard
    constructor
    · intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv, hRcard] at hp
      exact hP_pi p hp
    · intro p hp
      -- `index = card K'`, a `π'`-number.
      have hidx : (R.subgroupOf V).index = Nat.card ↥K' := by
        have hlag := Subgroup.card_mul_index (R.subgroupOf V)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv, hRcard, ← hVcard,
          mul_comm (Nat.card ↥K')] at hlag
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
      rw [hidx] at hp
      exact hK'_pi' p hp
  have hP_hall : Ch03.IsHallSubgroup (primesOf A) (P.subgroupOf V) := mkHall P hP_le_V rfl
  have hP'_hall : Ch03.IsHallSubgroup (primesOf A) (P'.subgroupOf V) :=
    mkHall P' hP'_le_V (by
      rw [hP'_def, Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) P).toEquiv])
  -- Conjugate `P'` to `P` inside `V` (Hall conjugacy).
  obtain ⟨w, hwV, hwconj⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hV_solv hP'_le_V hP_le_V hP'_hall hP_hall
  -- Decompose `w = s · κ` with `s ∈ P`, `κ ∈ K'` (`V = P · K'`, `K' ⊴ V`).
  have hPnK' : P ≤ Subgroup.normalizer (K' : Set G) := hP_le_V.trans hVnK'
  have hw_mem : w ∈ (P : Set G) * (K' : Set G) := by
    have hVcoe : (V : Set G) = (P : Set G) * (K' : Set G) := by
      rw [← hV_eq, sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right P K' hPnK'
    rw [← SetLike.mem_coe, hVcoe] at hwV
    exact hwV
  obtain ⟨s, hsP, κ, hκK', hwsκ⟩ := hw_mem
  simp only at hwsκ
  -- `conj κ • P' = P` (cancel the `P`-factor `s`).
  have hs : MulAut.conj s • P = P :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hsP)
  have hs' : MulAut.conj s⁻¹ • P = P := by
    conv_lhs => rw [← hs]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hκconj : MulAut.conj κ • P' = P := by
    have h1 : MulAut.conj s • (MulAut.conj κ • P') = P := by
      rw [smul_smul, ← map_mul, hwsκ]; exact hwconj
    have h2 : MulAut.conj s⁻¹ • (MulAut.conj s • (MulAut.conj κ • P'))
        = MulAut.conj s⁻¹ • P := congrArg _ h1
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hs'] at h2
    exact h2
  -- The conjugator `c := κ · k ∈ K ∩ N(P)`, which centralizes `P` (part a route).
  set c : G := κ * k with hc_def
  have hκK : κ ∈ K := (Subgroup.mem_inf.mp hκK').1
  have hκNQ₂ : κ ∈ NQ₂ := (Subgroup.mem_inf.mp hκK').2
  have hcK : c ∈ K := K.mul_mem hκK hkK
  have hcQ : MulAut.conj c • Q₁ = Q₂ := by
    rw [hc_def, map_mul, mul_smul, hkeq, conj_smul_eq_self_of_mem_normalizer hκNQ₂]
  have hcNP : c ∈ Subgroup.normalizer (P : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    rw [hc_def, map_mul, mul_smul, ← hP'_def, hκconj]
  have hcCP : c ∈ Subgroup.centralizer (P : Set G) :=
    mem_centralizer_of_mem_kSubgroup_normalizer hPnA hPK_bot hcK hcNP
  exact ⟨c, Subgroup.mem_inf.mpr ⟨hcCP, hcK⟩, hcQ⟩

/-- **Theorem 7.4(d)** (mmd L2246-2248): for `Q ∈ ℋ*(P;q)`, `N_G(P) = O_{π'}(C_G(P))·(N(P)∩N(Q))`
and `P ∩ N(P)′ ⊆ N(Q)′`. The factorization comes from (b) (transitivity): for `n ∈ N(P)`,
`conj n • Q ∈ ℋ*(P;q)`, so some `c ∈ O_{π'}(C_G(P))` has `conj c • Q = conj n • Q`, whence
`m := c⁻¹n ∈ N(P)∩N(Q)`. The commutator inclusion is **Lemma 6.5(a)**
(`inf_commutator_eq_of_coprime`) in `↥N(P)` with `K := O_{π'}(C_G(P))`, `U := N(P)∩N(Q)`,
`H := P`, using `derivedInG H = ⁅H,H⁆`. -/
private theorem tp_d [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P)
    (hPlt : P < ⊤) (hPne : P ≠ ⊥)
    (hb : ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}))
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ P {q}) :
    P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
    ∀ n : G, n ∈ Subgroup.normalizer P →
      ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
        ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ with hπ'
  set OC : Subgroup G := opiCoreInG π' (Subgroup.centralizer (P : Set G)) with hOC_def
  set NP : Subgroup G := Subgroup.normalizer (P : Set G) with hNP_def
  set NQ : Subgroup G := Subgroup.normalizer (Q : Set G) with hNQ_def
  have hPnQ : P ≤ NQ := hInvariantStar_le_normalizer hQ
  have hOC_le_CP : OC ≤ Subgroup.centralizer (P : Set G) := opiCoreInG_le _ _
  have hOC_le_NP : OC ≤ NP := hOC_le_CP.trans (Subgroup.centralizer_le_normalizer _)
  have hP_le_NP : P ≤ NP := Subgroup.le_normalizer
  -- Factorization (the existential clause).
  have hfact : ∀ n : G, n ∈ NP →
      ∃ c ∈ OC, ∃ m ∈ NP ⊓ NQ, n = c * m := by
    intro n hn
    have hnP : MulAut.conj n • P = P := conj_smul_eq_self_of_mem_normalizer hn
    have hnQmem : MulAut.conj n • Q ∈ hInvariantStar ⊤ P {q} :=
      conj_smul_mem_hInvariantStar_of_normalizer hQ hnP
    obtain ⟨c, hcOC, hcQeq⟩ := hb Q hQ (MulAut.conj n • Q) hnQmem
    refine ⟨c, hcOC, c⁻¹ * n, ?_, by group⟩
    have hcNP : c ∈ NP := hOC_le_NP hcOC
    have hmNP : c⁻¹ * n ∈ NP := NP.mul_mem (NP.inv_mem hcNP) hn
    have hmNQ : c⁻¹ * n ∈ NQ := by
      apply mem_normalizer_of_conj_smul_eq_self
      rw [map_mul, mul_smul, map_inv, ← hcQeq, inv_smul_smul]
    exact Subgroup.mem_inf.mpr ⟨hmNP, hmNQ⟩
  refine ⟨?_, hfact⟩
  -- Commutator inclusion via Lemma 6.5(a) in `↥NP`.
  -- `NP < ⊤` (`P` not normal: `P ≠ ⊥, ⊤`, `G` simple), hence `↥NP` solvable.
  have hNP_lt : NP < ⊤ := by
    rw [hNP_def, lt_top_iff_ne_top]
    intro htop
    haveI : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal P inferInstance with h | h
    · exact hPne h
    · exact (ne_of_lt hPlt) h
  haveI hNP_solv : IsSolvable ↥NP := hG.solvable_of_lt_top NP hNP_lt
  -- `OC = O_{π'}(C_G(P)) ⊴ NP`.
  have hOCnNP : NP ≤ Subgroup.normalizer (OC : Set G) := by
    intro x hx
    exact mem_normalizer_of_conj_smul_eq_self (conj_smul_opiCore_centralizer_eq hx)
  haveI hOC_normal : (OC.subgroupOf NP).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOC_le_NP).mpr hOCnNP
  -- `OC ⊔ (NP ⊓ NQ) = NP` from the factorization, so `K ⊔ U = ⊤` in `↥NP`.
  have hLU : OC ⊔ (NP ⊓ NQ) = NP := by
    refine le_antisymm (sup_le hOC_le_NP inf_le_left) ?_
    intro n hn
    obtain ⟨c, hcOC, m, hmNPNQ, hncm⟩ := hfact n hn
    rw [hncm]
    exact (OC ⊔ (NP ⊓ NQ)).mul_mem (Subgroup.mem_sup_left hcOC) (Subgroup.mem_sup_right hmNPNQ)
  have hKU : OC.subgroupOf NP ⊔ (NP ⊓ NQ).subgroupOf NP = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOC_le_NP inf_le_left, hLU, Subgroup.subgroupOf_self]
  -- Coprimality `|P|`, `|OC|`.
  have hcop : Nat.Coprime (Nat.card ↥(P.subgroupOf NP)) (Nat.card ↥(OC.subgroupOf NP)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_NP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC_le_NP).toEquiv]
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hP_pi p hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG π' (Subgroup.centralizer (P : Set G)) p hp
  have hHU : P.subgroupOf NP ≤ (NP ⊓ NQ).subgroupOf NP :=
    Subgroup.comap_mono (le_inf hP_le_NP hPnQ)
  -- Apply Lemma 6.5(a) inside `↥NP`.
  have h65 := OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime
    (G := ↥NP) (K := OC.subgroupOf NP) (U := (NP ⊓ NQ).subgroupOf NP)
    (H := P.subgroupOf NP) hKU hHU hcop
  -- Map the equation back to `G` and deduce the inclusion.
  have hmap := congrArg (Subgroup.map NP.subtype) h65
  simp only [Subgroup.map_inf _ _ _ NP.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_subtype_commutator, Subgroup.map_commutator,
    inf_of_le_left hP_le_NP] at hmap
  -- `hmap : P ⊓ ⁅NP, NP⁆ = P ⊓ ⁅NP ⊓ NQ, NP ⊓ NQ⁆`.
  rw [show derivedInG NP = ⁅(NP : Subgroup G), NP⁆ from Subgroup.map_subtype_commutator NP, hmap]
  refine le_trans inf_le_right ?_
  rw [show derivedInG NQ = ⁅(NQ : Subgroup G), NQ⁆ from Subgroup.map_subtype_commutator NQ]
  exact Subgroup.commutator_mono (le_trans inf_le_left inf_le_right)
    (le_trans inf_le_left inf_le_right)

/-- **`|ℋ*(A;q)| ∣ |K|`** (mmd L2218): `K` acts transitively on the finite set `ℋ*(A;q)` by
conjugation (each `k ∈ K ≤ C_G(A) ≤ N(A)`), so by orbit-stabilizer its cardinality divides `|K|`. -/
private theorem tp_card_hStar_dvd_kSubgroup [Finite G] {A : Subgroup G} {q : ℕ}
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Nat.card ↥(hInvariantStar ⊤ A {q}) ∣ Nat.card ↥(kSubgroup A) := by
  classical
  set S : Set (Subgroup G) := hInvariantStar ⊤ A {q} with hS_def
  set K : Subgroup G := kSubgroup A with hK_def
  -- `↥K` acts on `↥S` by conjugation.
  have hkA : ∀ k : ↥K, MulAut.conj (k : G) • A = A := fun k =>
    conj_smul_eq_self_of_mem_normalizer
      ((Subgroup.centralizer_le_normalizer _) (kSubgroup_le_centralizer A k.2))
  let smulFn : ↥K → ↥S → ↥S := fun k Q => ⟨MulAut.conj (k : G) • (Q : Subgroup G),
    conj_smul_mem_hInvariantStar_of_normalizer Q.2 (hkA k)⟩
  letI act : MulAction ↥K ↥S :=
    { smul := smulFn
      one_smul := fun Q => by
        apply Subtype.ext
        show MulAut.conj ((1 : ↥K) : G) • (Q : Subgroup G) = (Q : Subgroup G)
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun x y Q => by
        apply Subtype.ext
        show MulAut.conj (((x * y : ↥K)) : G) • (Q : Subgroup G)
          = MulAut.conj ((x : G)) • MulAut.conj ((y : G)) • (Q : Subgroup G)
        rw [Subgroup.coe_mul, map_mul, mul_smul] }
  have hsmul_coe : ∀ (k : ↥K) (Q : ↥S),
      ((k • Q : ↥S) : Subgroup G) = MulAut.conj (k : G) • (Q : Subgroup G) := fun _ _ => rfl
  haveI hpre : MulAction.IsPretransitive ↥K ↥S := by
    refine ⟨fun Q₁ Q₂ => ?_⟩
    obtain ⟨k, hkK, hkeq⟩ := htrans Q₁ Q₁.2 Q₂ Q₂.2
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    rw [hsmul_coe]; exact hkeq
  -- Orbit-stabilizer: `|orbit Q₀| = (stab).index ∣ |K|`, and `orbit Q₀ = ↥S`.
  obtain ⟨Q₀⟩ : Nonempty ↥S := by
    have hbot_norm : (A : Subgroup G) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      intro a _
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro h
        have : z = a⁻¹ * 1 * a := by rw [← (h : a * z * a⁻¹ = 1)]; group
        simpa using this
    have hbot_mem : (⊥ : Subgroup G) ∈ hInvariant ⊤ A {q} :=
      ⟨le_top, hbot_norm, Subgroup.IsPiSubgroup.bot⟩
    obtain ⟨Qs, hQs, _⟩ := exists_le_hInvariantStar hbot_mem
    exact ⟨⟨Qs, hQs⟩⟩
  have horb_univ : MulAction.orbit ↥K Q₀ = Set.univ :=
    MulAction.orbit_eq_univ (M := ↥K) (α := ↥S) Q₀
  have hcard_orbit : Nat.card ↥(MulAction.orbit ↥K Q₀) = Nat.card ↥S := by
    rw [horb_univ]; exact Nat.card_congr (Equiv.Set.univ ↥S)
  have hdvd : Nat.card ↥(MulAction.orbit ↥K Q₀) ∣ Nat.card ↥K := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥K Q₀),
      ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  rw [hcard_orbit] at hdvd
  exact hdvd

/-- **Theorem 7.4(c) base case** (mmd L2222-2232): `A ⊴ P` with `|P:A| = p` prime ⟹
`ℋ*(P;q) ⊆ ℋ*(A;q)`. For `Q ≠ ⊥` it is `tp_c_main`; for `Q = ⊥` (so `ℋ*(P;q) = {⊥}`), (7.3)
gives a `P`-normalized `Q₀ ∈ ℋ*(A;q)`, and `⊥`'s maximality in `ℋ(P;q)` forces `Q₀ = ⊥`. -/
private theorem tp_c_full [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) {p : ℕ} (hp : p.Prime)
    (hindex : (A.subgroupOf P).index = p)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} := by
  -- `p ∈ π = primesOf A`, so `p ∤ |K|`, hence `p ∤ |ℋ*(A;q)|`.
  have hp_pi : p ∈ primesOf A := by
    refine hP_pi p (Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩)
    have hdvd : (A.subgroupOf P).index ∣ Nat.card ↥P := by
      rw [← Subgroup.index_mul_card (A.subgroupOf P)]; exact Dvd.intro _ rfl
    rw [hindex] at hdvd; exact hdvd
  have hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q}) := by
    intro hpd
    have hdvdK : p ∣ Nat.card ↥(kSubgroup A) :=
      hpd.trans (tp_card_hStar_dvd_kSubgroup htrans)
    exact (isPiSubgroup_kSubgroup A p (Nat.mem_primeFactors.mpr ⟨hp, hdvdK, Nat.card_pos.ne'⟩)) hp_pi
  intro Q hQ
  by_cases hQbot : Q = ⊥
  · -- `Q = ⊥`: use (7.3) and maximality.
    subst hQbot
    obtain ⟨Q₀, hQ₀star, hPnQ₀⟩ :=
      tp_exists_normalized_of_prime_index hAP hp hindex hpdvd
    have hQ₀_hInvP : Q₀ ∈ hInvariant ⊤ P {q} :=
      ⟨le_top, hPnQ₀, hInvariantStar_isPiSubgroup hQ₀star⟩
    have hbot_eq : Q₀ = ⊥ := hInvariantStar_eq_of_le hQ hQ₀_hInvP bot_le
    rw [← hbot_eq]; exact hQ₀star
  · exact tp_c_main hG hA hq hAP hP_pi hQ hQbot

/-- **BG Theorem 7.4 base case** (`A ⊴ P` with `|P:A|` prime): conjuncts (a)/(b)/(c)/(d). -/
private theorem tp_base [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) (hPlt : P < ⊤) (hPne : P ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hindex : (A.subgroupOf P).index = p)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m) := by
  have hcsub : hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} :=
    tp_c_full hG hA hq hAP hP_pi hp hindex htrans
  have hbpart : ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
      (hInvariantStar ⊤ P {q}) :=
    tp_b hG hA hq hAP hP_pi hPlt htrans hcsub
  refine ⟨tp_centralizer_eq hG hA hAP, hbpart, hcsub, ?_⟩
  intro Q hQ
  exact tp_d hG hq hAP hP_pi hPlt hPne hbpart hQ

/-- **BG Theorem 7.4** (Propagation, mmd L2197): Hypothesis 7.1, `q ∈ π'`, `P` は `A` を
subnormal に含む真 `π`-部分群、`K` は `ℋ_G*(A;q)` 上推移的とする。すると:

* (a) `C_K(P) = O_{π'}(C_G(P))`,
* (b) `O_{π'}(C_G(P))` は `ℋ_G*(P;q)` 上推移的,
* (c) `ℋ_G*(P;q) ⊆ ℋ_G*(A;q)`,
* (d) 各 `Q ∈ ℋ_G*(P;q)` で `P ∩ N_G(P)′ ⊆ N_G(Q)′` かつ
  `N_G(P) = O_{π'}(C_G(P))·(N_G(P) ∩ N_G(Q))`。

`|P:A|` の帰納 + composition series 還元。 -/
theorem transitivity_propagates [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (P : Subgroup G) (hPproper : P < ⊤) (hPpi : Subgroup.IsPiSubgroup (primesOf A) P)
    (hAP : A ≤ P) (hAsub : Subgroup.IsSubnormal (A.subgroupOf P))
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m) := by
  classical
  -- The four-conjunct conclusion for a pair `(A, P)`.
  let Goal : Subgroup G → Subgroup G → Prop := fun A P =>
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m)
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Hypothesis71 A → q ∈ (primesOf A)ᶜ →
      ∀ P : Subgroup G, P < ⊤ → Subgroup.IsPiSubgroup (primesOf A) P → A ≤ P →
      Subgroup.IsSubnormal (A.subgroupOf P) →
      ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) →
      (A.subgroupOf P).index = n → Goal A P by
    exact key _ A hA hq P hPproper hPpi hAP hAsub htrans rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hq P hPproper hPpi hAP hAsub htrans hn
    have hAne : A ≠ ⊥ := hA.ne_bot
    have hPne : P ≠ ⊥ := fun h => hAne (le_bot_iff.mp (h ▸ hAP))
    by_cases hAeqP : A = P
    · -- Base `A = P`: everything is reflexive / `tp_centralizer_eq`.
      subst hAeqP
      refine ⟨tp_centralizer_eq hG hA (le_refl A), ?_, ?_, ?_⟩
      · -- (b): `O_{π'}(C_G(A)) = kSubgroup A`, transitive `= htrans`.
        rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G)) = kSubgroup A from rfl]
        exact htrans
      · exact le_refl _
      · intro Q hQ
        refine ⟨?_, ?_⟩
        · exact tp_d hG hq (le_refl A) hPpi hPproper hPne
            (by rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))
              = kSubgroup A from rfl]; exact htrans) hQ |>.1
        · exact tp_d hG hq (le_refl A) hPpi hPproper hPne
            (by rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))
              = kSubgroup A from rfl]; exact htrans) hQ |>.2
    · -- `A < P`: reduce to a normal subgroup `B` of prime index.
      have hAltP : A < P := lt_of_le_of_ne hAP hAeqP
      obtain ⟨B, hAB, hBlt, hBnorm, hBindex⟩ := tp_reduction hG hAP hAltP hPproper hAsub
      haveI := hBnorm
      have hBP : B ≤ P := le_of_lt hBlt
      -- `B` is a `π(A)`-subgroup; `primesOf B = primesOf A`.
      have hBpi : Subgroup.IsPiSubgroup (primesOf A) B := fun r hr =>
        hPpi r (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
          (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_dvd_of_le hBP), Nat.card_pos.ne'⟩)
      have hprimesBA : primesOf B = primesOf A :=
        primesOf_eq_of_le_of_isPiSubgroup hAB hBP hPpi
      by_cases hAeqB : A = B
      · -- `A = B`: prime-index base case.
        subst hAeqB
        haveI : (A.subgroupOf P).Normal := hBnorm
        exact tp_base hG hA hq hAP hPpi hPproper hPne
          (p := (A.subgroupOf P).index) hBindex rfl htrans
      · -- `A < B`: double recursion on `(A, B)` and `(B, P)`.
        have hABlt : A < B := lt_of_le_of_ne hAB hAeqB
        have hBlt_top : B < ⊤ := lt_trans hBlt hPproper
        have hBne : B ≠ ⊥ := fun h => hAne (le_bot_iff.mp (h ▸ hAB))
        -- Measure: `|B:A| · |P:B| = |P:A| = n`, both factors `> 1`.
        have hmul : (A.subgroupOf B).index * (B.subgroupOf P).index = (A.subgroupOf P).index := by
          have h := Subgroup.relIndex_mul_relIndex A B P hAB hBP
          simpa only [Subgroup.relIndex] using h
        have hBA_ne0 : (A.subgroupOf B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hPB_ne0 : (B.subgroupOf P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hBA_gt : 1 < (A.subgroupOf B).index := by
          rcases Nat.lt_or_ge 1 (A.subgroupOf B).index with h | h
          · exact h
          · exfalso
            have : (A.subgroupOf B).index = 1 := by omega
            rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at this
            exact (ne_of_lt hABlt) (le_antisymm hAB this)
        have hPB_gt : 1 < (B.subgroupOf P).index := by
          rcases Nat.lt_or_ge 1 (B.subgroupOf P).index with h | h
          · exact h
          · exfalso
            have : (B.subgroupOf P).index = 1 := by omega
            rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at this
            exact (ne_of_lt hBlt) (le_antisymm hBP this)
        have hBA_lt_n : (A.subgroupOf B).index < n := by
          rw [← hn, ← hmul]
          exact lt_mul_of_one_lt_right (by omega) hPB_gt
        have hPB_lt_n : (B.subgroupOf P).index < n := by
          rw [← hn, ← hmul]
          exact lt_mul_of_one_lt_left (by omega) hBA_gt
        -- `A` subnormal in `B`, `B` subnormal in `P`.
        have hAsubB : (A.subgroupOf B).IsSubnormal := by
          have h := Subgroup.IsSubnormal.comap (Subgroup.inclusion hBP) hAsub
          rwa [Subgroup.comap_inclusion_subgroupOf hBP] at h
        have hBsubP : (B.subgroupOf P).IsSubnormal := (hBnorm).isSubnormal
        -- IH on `(A, B)`.
        obtain ⟨_, hbAB, hcAB, _⟩ :=
          ih _ hBA_lt_n A hA hq B hBlt_top hBpi hAB hAsubB htrans rfl
        -- `Hypothesis71 B`, `htrans` on `B`.
        have hBhyp : Hypothesis71 B := tp_hyp71_of_le hA hAB hprimesBA hBne hBlt_top
        have hqB : q ∈ (primesOf B)ᶜ := by rw [hprimesBA]; exact hq
        have hPpiB : Subgroup.IsPiSubgroup (primesOf B) P := by rw [hprimesBA]; exact hPpi
        have htransB : ConjTransitiveOn (kSubgroup B) (hInvariantStar ⊤ B {q}) := by
          have heqK : kSubgroup B = opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (B : Set G)) := by
            rw [kSubgroup, hprimesBA]
          rw [heqK]; exact hbAB
        -- IH on `(B, P)`.
        obtain ⟨_, hbBP, hcBP, hdBP⟩ :=
          ih _ hPB_lt_n B hBhyp hqB P hPproper hPpiB hBP hBsubP htransB rfl
        -- Compose. `primesOf B = primesOf A` lets us re-tag the `O_{π'}` parts.
        have hOCeq : opiCoreInG (primesOf B)ᶜ (Subgroup.centralizer (P : Set G))
            = opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) := by rw [hprimesBA]
        refine ⟨tp_centralizer_eq hG hA hAP, ?_, ?_, ?_⟩
        · rw [← hOCeq]; exact hbBP
        · exact fun Q hQ => hcAB (hcBP hQ)
        · intro Q hQ
          obtain ⟨hd1, hd2⟩ := hdBP Q hQ
          refine ⟨hd1, ?_⟩
          intro nn hnn
          obtain ⟨c, hc, m, hm, hcm⟩ := hd2 nn hnn
          exact ⟨c, hOCeq ▸ hc, m, hm, hcm⟩

/-! ## Proposition 7.5 — Hypothesis 7.1 の十分条件 -/

/-! ## Proposition 7.5 — Hypothesis 7.1 の十分条件 -/

/-- **Reduction for Hypothesis 7.1(2)** (mmd L2273 "it suffices to show that `Y ⊆ O_{π'}(X)`"):
for a fixed proper `X ⊇ A`, the equality `⟨ℋ_X(A;π)⟩ = O_π(X)` is equivalent to showing every
member of `ℋ_X(A;π)` is contained in `O_π(X)`. The reverse inclusion is automatic because
`O_π(X) = opiCoreInG π X` is itself an `A`-invariant `π`-subgroup of `X`
(`opiCoreInG_le` + `le_normalizer_opiCoreInG` with `A ≤ X` + `isPiSubgroup_opiCoreInG`).
Used by both branches of Proposition 7.5. -/
theorem generated_eq_of_forall_le_opiCoreInG [Finite G]
    {A X : Subgroup G} {π : Set ℕ} (hAX : A ≤ X)
    (hY : ∀ Y ∈ hInvariant X A π, Y ≤ opiCoreInG π X) :
    sSup (hInvariant X A π) = opiCoreInG π X := by
  refine le_antisymm (sSup_le hY) (le_sSup ?_)
  exact ⟨opiCoreInG_le π X, hAX.trans (le_normalizer_opiCoreInG π X),
    isPiSubgroup_opiCoreInG π X⟩

/-- **`oPiCore` is natural under a group isomorphism**: `(O_π G₁).map φ = O_π G₂` for
`φ : G₁ ≃* G₂` (apply `oPiCore.map_le_of_surjective` to `φ` and to `φ.symm`). General lemma;
could be promoted to `Ch03`. Used by `opiCoreInG_eq_map_subgroupOf`. -/
private theorem oPiCore_map_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (π : Set ℕ) (φ : G₁ ≃* G₂) :
    (Ch03.oPiCore π G₁).map φ.toMonoidHom = Ch03.oPiCore π G₂ := by
  refine le_antisymm (Ch03.oPiCore.map_le_of_surjective π φ.toMonoidHom φ.surjective) ?_
  intro h hh
  exact ⟨φ.symm h,
    Ch03.oPiCore.map_le_of_surjective π φ.symm.toMonoidHom φ.symm.surjective ⟨h, hh, rfl⟩, by simp⟩

/-- **`opiCoreInG` transport to an intermediate subgroup**: for `K ≤ X`,
`O_π(K) = O_π(K.subgroupOf X)` mapped from `↥X` back to `G`. Lets one apply a result proved
inside `↥X` (e.g. Proposition 1.15(b) with ambient group `↥X`) to the ambient realization
`opiCoreInG π K`. General lemma; could be promoted to `SubgroupInAmbient`. -/
private theorem opiCoreInG_eq_map_subgroupOf [Finite G] {π : Set ℕ} {X K : Subgroup G}
    (hKX : K ≤ X) :
    opiCoreInG π K = (opiCoreInG π (K.subgroupOf X)).map X.subtype := by
  have hcomp : X.subtype.comp (K.subgroupOf X).subtype
      = K.subtype.comp (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  calc opiCoreInG π K
      = ((Ch03.oPiCore π ↥(K.subgroupOf X)).map
            (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom).map K.subtype := by
        rw [oPiCore_map_mulEquiv]; rfl
    _ = (Ch03.oPiCore π ↥(K.subgroupOf X)).map
            (K.subtype.comp (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(K.subgroupOf X)).map (X.subtype.comp (K.subgroupOf X).subtype) := by
        rw [hcomp]
    _ = (opiCoreInG π (K.subgroupOf X)).map X.subtype := by
        rw [← Subgroup.map_map]; rfl

/-- **Relativized BG Proposition 1.15(b)**: for a finite solvable subgroup `X ≤ G` and a
`p`-subgroup `R ≤ X`, `O_{p'}(C_X(R)) ≤ O_{p'}(X)` (both realized in the ambient `G`). Obtained
from the absolute Prop 1.15(b) (`oPiPrimeCore_centralizer_le_oPiPrimeCore`) inside the group `↥X`,
transported back to `G` via `opiCoreInG_eq_map_subgroupOf`. Here `C_X(R) = C_G(R) ⊓ X`. This is
the cross-group bridge for Proposition 7.5's general case (and is reusable in §8–§16). -/
theorem opiCoreInG_centralizer_inf_le_opiCoreInG [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hXsolv : IsSolvable ↥X) {R : Subgroup G} (hRX : R ≤ X) (hRp : IsPGroup p R) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G) ⊓ X)
      ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  haveI := hXsolv
  have hR'p : IsPGroup p (R.subgroupOf X) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv]; exact hn)
  have hbridge : (Subgroup.centralizer (R : Set G) ⊓ X).subgroupOf X
      = Subgroup.centralizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hc, -⟩ m hm
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
      exact Subtype.ext (hc (m : G) hm)
    · intro hc
      refine ⟨?_, x.2⟩
      intro r hr
      exact congrArg Subtype.val
        (hc ⟨r, hRX hr⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hr))
  have habs := OddOrder.BG.Ch1.S01.oPiPrimeCore_centralizer_le_oPiPrimeCore (G := ↥X) hR'p
  calc opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G) ⊓ X)
      = (opiCoreInG ({p} : Set ℕ)ᶜ
          ((Subgroup.centralizer (R : Set G) ⊓ X).subgroupOf X)).map X.subtype :=
        opiCoreInG_eq_map_subgroupOf inf_le_right
    _ = (opiCoreInG ({p} : Set ℕ)ᶜ
          (Subgroup.centralizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X))).map X.subtype := by
        rw [hbridge]
    _ ≤ (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥X).map X.subtype := Subgroup.map_mono habs
    _ = opiCoreInG ({p} : Set ℕ)ᶜ X := rfl

/-- **Bar-quotient bridge** for Proposition 7.5's special case: the image of `O_{π',π}(G')` under
the quotient `mk' : G' → G'/O_{π'}(G')` is exactly `O_π(G'/O_{π'}(G'))` — i.e. `O_p(X̄) = mk(O_{p',p}(X))`.
Immediate from `oPiPrimePiCore` being defined as `comap (mk' O_{π'}) (O_π of the quotient)` plus
`map_comap_eq_self_of_surjective`. With Theorem 6.1 (`thmA4b`: `A ≤ O_{p',p}(X)`) this gives
`Ā ≤ O_p(X̄)`. -/
private theorem oPiPrimePiCore_map_mk'_eq {G' : Type*} [Group G'] (π : Set ℕ) :
    (Ch03.oPiPrimePiCore π G').map (QuotientGroup.mk' (Ch03.oPiCore {p | p ∉ π} G'))
      = Ch03.oPiCore π (G' ⧸ Ch03.oPiCore {p | p ∉ π} G') := by
  rw [Ch03.oPiPrimePiCore]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- **Step 6 of Prop 7.5's special case** (`C_{O_p(X̄)}(Ā) ⊆ Ā`): with `N = O_{p'}(G')` and
`mk : G' → G'/N`, if `c ∈ O_p(G'/N)` commutes with `mk a` for every `a ∈ A`, then `c ∈ mk(A)`.
Clean route avoiding an explicit Sylow iso: `O_p(X̄) ⊆ mk(P)` (image of the Sylow `P` is Sylow,
and `O_p ≤` every Sylow), so `c = mk s` with `s ∈ P`; then for `a ∈ A`, `[a,s] ∈ N ⊓ P = ⊥`
(it lies in `N` since `mk` kills it, and in `P` since `a, s ∈ P`), so `s ∈ C_P(A) ⊆ A`. -/
private theorem mem_map_mk'_of_mem_oPiCore_quotient_of_commute
    {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    (P : Sylow p G') {A : Subgroup G'} (hAP : A ≤ (P : Subgroup G'))
    (hCPA : Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') ≤ A)
    {c : G' ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ G'}
    (hc : c ∈ Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ G'))
    (hcomm : ∀ a ∈ A, QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a * c
        = c * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a) :
    c ∈ A.map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) :=
    QuotientGroup.mk'_surjective _
  -- `N := O_{p'}(G')` is a `p'`-group, so `P ⊓ N = ⊥`.
  have hN_cop : Nat.Coprime (Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hPN : (P : Subgroup G') ⊓ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' = ⊥ :=
    OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime P.2 hN_cop
  -- `O_p(X̄) ⊆ mk(P)`: the image of the Sylow `P` is Sylow, and `O_p ≤` every Sylow.
  have hc_inP :
      c ∈ (P : Subgroup G').map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) := by
    have hle := OddOrder.Isaacs.Ch01.opCore_le (P.mapSurjective hsurj)
    rw [Sylow.coe_mapSurjective, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore] at hle
    exact hle hc
  obtain ⟨s, hsP, hsc⟩ := Subgroup.mem_map.mp hc_inP
  -- `s ∈ C_P(A)`: for `a ∈ A`, `[a,s] ∈ N ⊓ P = ⊥`.
  have hs_cent : s ∈ Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') := by
    refine Subgroup.mem_inf.mpr ⟨?_, hsP⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmkcomm : QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a
          * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') s
        = QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') s
          * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a := by
      rw [hsc]; exact hcomm a ha
    have hin_N : a * s * a⁻¹ * s⁻¹ ∈ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' := by
      rw [← QuotientGroup.ker_mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G'), MonoidHom.mem_ker,
        map_mul, map_mul, map_mul, map_inv, map_inv, hmkcomm]
      group
    have hin_P : a * s * a⁻¹ * s⁻¹ ∈ (P : Subgroup G') :=
      (P : Subgroup G').mul_mem ((P : Subgroup G').mul_mem
        ((P : Subgroup G').mul_mem (hAP ha) hsP) ((P : Subgroup G').inv_mem (hAP ha)))
        ((P : Subgroup G').inv_mem hsP)
    have h1 : a * s * a⁻¹ * s⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hPN ▸ Subgroup.mem_inf.mpr ⟨hin_P, hin_N⟩)
    have h2 : a * s * a⁻¹ = s := mul_inv_eq_one.mp h1
    calc a * s = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h2]
  rw [← hsc]
  exact Subgroup.mem_map_of_mem _ (hCPA hs_cent)

/-- **Abstract special case of BG Proposition 7.5** (mmd L2275-2285), `b`-independent and reusable:
if `G'` is finite solvable of odd order, `P` is a Sylow `p`-subgroup, `A ≤ P` is abelian and normal
in `P` with `C_P(A) ⊆ A`, and `Y` is an `A`-invariant `p'`-subgroup, then `Y ≤ O_{p'}(G')`.

Proof (in the bar-quotient `X̄ = G'/O_{p'}(G')`): Theorem 6.1 puts `Ā ≤ O_p(X̄)`; the commutator
`[Ā,Ȳ] ≤ O_p(X̄) ⊓ Ȳ = 1` so `Ā` centralizes `Ȳ`; step 6
(`mem_map_mk'_of_mem_oPiCore_quotient_of_commute`) gives `C_{O_p(X̄)}(Ā) ⊆ Ā`; Proposition 1.10 then
makes `Ȳ` centralize `O_p(X̄)`, and Proposition 1.15(a) forces `Ȳ ≤ O_p(X̄)`, whence `Ȳ = 1`. -/
private theorem specialCase
    {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G'] [IsSolvable G']
    (hp2 : p ≠ 2) (hodd : Odd (Nat.card G')) (P : Sylow p G')
    {A : Subgroup G'} (hAP : A ≤ (P : Subgroup G')) [IsMulCommutative A]
    (hAnormP : (P : Subgroup G') ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') ≤ A)
    {Y : Subgroup G'} (hYnorm : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y) :
    Y ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' := by
  classical
  set N : Subgroup G' := Ch03.oPiCore ({p} : Set ℕ)ᶜ G' with hN
  set mk := QuotientGroup.mk' N with hmkdef
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective N
  have hker : mk.ker = N := QuotientGroup.ker_mk' N
  set Q : Subgroup (G' ⧸ N) := Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ N) with hQ
  haveI hQnorm : Q.Normal := by rw [hQ]; infer_instance
  set Ybar : Subgroup (G' ⧸ N) := Y.map mk with hYbar
  set Abar : Subgroup (G' ⧸ N) := A.map mk with hAbar
  -- `Q = O_p(X̄)` is a `p`-group; `Ȳ` is a `p'`-group; hence `Q ⊓ Ȳ = ⊥`.
  have hQ_pg : IsPGroup p ↥Q := by
    rw [hQ, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p _
  have hYbar_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Ybar := by
    intro q hq
    have hdvd : Nat.card ↥Ybar ∣ Nat.card ↥Y := by rw [hYbar]; exact Subgroup.card_map_dvd _ _
    exact hYpi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
  have hYbar_cop : Nat.Coprime (Nat.card ↥Ybar) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      exact hYbar_pi q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hQYbot : Q ⊓ Ybar = ⊥ := OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQ_pg hYbar_cop
  -- Theorem 6.1 (`thmA4b`) ⟹ `A ≤ O_{p',p}(G')` ⟹ `Ā ≤ Q`.
  have hThm61 : A ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G' :=
    OddOrder.BG.AppA.thmA4b hp2 ‹IsSolvable G'› hodd P hAP hAnormP
  have hAbar_le_Q : Abar ≤ Q := by rw [hAbar]; exact Subgroup.map_le_iff_le_comap.mpr hThm61
  -- `[Ā,Ȳ] = 1`: each commutator lies in `Q ⊓ Ȳ = ⊥`.
  have hcommute : ∀ a' ∈ Abar, ∀ y' ∈ Ybar, a' * y' * a'⁻¹ * y'⁻¹ = 1 := by
    intro a' ha' y' hy'
    have hin_Q : a' * y' * a'⁻¹ * y'⁻¹ ∈ Q := by
      have ha'Q : a' ∈ Q := hAbar_le_Q ha'
      have hconj : y' * a'⁻¹ * y'⁻¹ ∈ Q := hQnorm.conj_mem a'⁻¹ (Q.inv_mem ha'Q) y'
      have heq : a' * y' * a'⁻¹ * y'⁻¹ = a' * (y' * a'⁻¹ * y'⁻¹) := by group
      rw [heq]; exact Q.mul_mem ha'Q hconj
    have hin_Y : a' * y' * a'⁻¹ * y'⁻¹ ∈ Ybar := by
      rw [hAbar, Subgroup.mem_map] at ha'
      rw [hYbar, Subgroup.mem_map] at hy'
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨y, hy, rfl⟩ := hy'
      have hY : a * y * a⁻¹ * y⁻¹ ∈ Y :=
        Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYnorm ha) y).mp hy) (Y.inv_mem hy)
      have heq : mk a * mk y * (mk a)⁻¹ * (mk y)⁻¹ = mk (a * y * a⁻¹ * y⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [hYbar, heq]
      exact Subgroup.mem_map_of_mem mk hY
    exact Subgroup.mem_bot.mp (hQYbot ▸ Subgroup.mem_inf.mpr ⟨hin_Q, hin_Y⟩)
  -- conjugation action of `Ȳ` on `Q`.
  have hYbar_norm : Ybar ≤ Subgroup.normalizer Q := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hQnorm.conj_mem z hz y
    · intro hz
      have h := hQnorm.conj_mem _ hz y⁻¹
      have heq : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
      rwa [heq] at h
  set φ : ↥Ybar →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hYbar_norm) with hφ
  have hφcoe : ∀ (a : ↥Ybar) (g : ↥Q),
      ((φ a) g : G' ⧸ N) = (a : G' ⧸ N) * (g : G' ⧸ N) * (a : G' ⧸ N)⁻¹ := by
    intro a g; rw [hφ]; rfl
  -- `Ā ≤ C_Q(Ȳ)`: `Ā` (inside `Q`) is fixed by `Ȳ`.
  have hAbar_le_fix : Abar.subgroupOf Q ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    have hc := hcommute (g : G' ⧸ N) hg (a : G' ⧸ N) a.2
    have h3 : (g : G' ⧸ N) * (a : G' ⧸ N) * (g : G' ⧸ N)⁻¹ = (a : G' ⧸ N) := mul_inv_eq_one.mp hc
    have h4 : (g : G' ⧸ N) * (a : G' ⧸ N) = (a : G' ⧸ N) * (g : G' ⧸ N) := by
      calc (g : G' ⧸ N) * (a : G' ⧸ N)
          = ((g : G' ⧸ N) * (a : G' ⧸ N) * (g : G' ⧸ N)⁻¹) * (g : G' ⧸ N) := by group
        _ = (a : G' ⧸ N) * (g : G' ⧸ N) := by rw [h3]
    calc (a : G' ⧸ N) * (g : G' ⧸ N) * (a : G' ⧸ N)⁻¹
        = (g : G' ⧸ N) * (a : G' ⧸ N) * (a : G' ⧸ N)⁻¹ := by rw [← h4]
      _ = (g : G' ⧸ N) := by group
  -- `C_Q(C_Q(Ȳ)) ⊆ C_Q(Ȳ)` for Proposition 1.10, using step 6.
  have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
      ≤ Subgroup.fixedPointsOfMulAut φ := by
    refine le_trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAbar_le_fix)) ?_
    refine le_trans ?_ hAbar_le_fix
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    refine mem_map_mk'_of_mem_oPiCore_quotient_of_commute P hAP hCPA (c := (c : G' ⧸ N)) c.2 ?_
    intro a ha
    have hmkaAbar : mk a ∈ Abar := by rw [hAbar]; exact Subgroup.mem_map_of_mem mk ha
    have hmkaQ : mk a ∈ Q := hAbar_le_Q hmkaAbar
    have hmem : (⟨mk a, hmkaQ⟩ : ↥Q) ∈ Abar.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]; exact hmkaAbar
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨mk a, hmkaQ⟩ hmem)
  haveI : Group.IsNilpotent ↥Q := hQ_pg.isNilpotent
  have hcop : Nat.Coprime (Nat.card ↥Ybar) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQ_pg.exists_card_eq
    rw [hn]; exact hYbar_cop.pow_right n
  have htrivφ := OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥Ybar) (G := ↥Q) (φ := φ) hcop hCC
  -- `Ȳ` centralizes `Q`, so `Ȳ ≤ C_X̄(Q) ≤ Q` (Prop 1.15(a)), hence `Ȳ ≤ Q ⊓ Ȳ = ⊥`.
  have hYbar_cent : Ybar ≤ Subgroup.centralizer (Q : Set (G' ⧸ N)) := by
    intro yb hyb
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := htrivφ ⟨yb, hyb⟩ ⟨q, hq⟩
    have hco := congrArg Subtype.val h
    rw [hφcoe] at hco
    have : yb * q * yb⁻¹ = q := hco
    calc q * yb = (yb * q * yb⁻¹) * yb := by rw [this]
      _ = yb * q := by group
  have h115a : Subgroup.centralizer (Q : Set (G' ⧸ N)) ≤ Q := by
    have hbot : Ch03.oPiCore ({q | q ∉ ({p} : Set ℕ)}) (G' ⧸ N) = ⊥ := by
      have := Ch03.oPiCore_quotient_self_eq_bot (G := G') ({p} : Set ℕ)ᶜ
      exact this
    have := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G' ⧸ N) hbot
    rw [← hQ] at this
    exact this
  have hYbar_le_Q : Ybar ≤ Q := le_trans hYbar_cent h115a
  have hYbar_bot : Ybar = ⊥ := le_bot_iff.mp (hQYbot ▸ le_inf hYbar_le_Q le_rfl)
  -- `Y.map mk = ⊥` ⟹ `Y ≤ ker mk = N`.
  have hYmap_bot : Y.map mk = ⊥ := by rw [← hYbar]; exact hYbar_bot
  rw [Subgroup.map_eq_bot_iff, hker] at hYmap_bot
  exact hYmap_bot

/-- **Per-`b` bridge for Prop 7.5's general case**: if `W ≤ X` lies in `O_{p'}(C_G(b))` for a
`p`-element `b ∈ X`, then `W ≤ O_{p'}(X)`. Combines `le_opiCoreInG_of_normal_of_isPiSubgroup`
(`O_{p'}(C_G(b)) ⊓ C_X(b) ≤ O_{p'}(C_X(b))`) with the relativized Proposition 1.15(b)
(`O_{p'}(C_X(b)) ≤ O_{p'}(X)`). -/
private theorem le_opiCoreInG_of_le_opiCoreInG_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hXsolv : IsSolvable ↥X) {b : G} (hbp : IsPGroup p (Subgroup.zpowers b))
    (hbX : b ∈ X) {W : Subgroup G} (hWX : W ≤ X)
    (hW_le : W ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G))) :
    W ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set H := C ⊓ X with hH
  have hW_cent : W ≤ C := hW_le.trans (opiCoreInG_le _ _)
  have hWH : W ≤ H := le_inf hW_cent hWX
  -- `O_{p'}(C) ⊓ H ≤ O_{p'}(H)` via the normal-`p'`-subgroup bridge.
  have hstep : opiCoreInG ({p} : Set ℕ)ᶜ C ⊓ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
    refine le_opiCoreInG_of_normal_of_isPiSubgroup inf_le_right ?_ ?_
    · constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgC : (g : G) ∈ Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ C) :=
        le_normalizer_opiCoreInG _ _ (Subgroup.mem_inf.mp g.2).1
      refine ⟨(Subgroup.mem_normalizer_iff.mp hgC _).mp hn.1, ?_⟩
      exact H.mul_mem (H.mul_mem g.2 hn.2) (H.inv_mem g.2)
    · intro r hr
      refine isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ C r ?_
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩
  -- `O_{p'}(H) = O_{p'}(C_X(b)) ≤ O_{p'}(X)` via the relativized Proposition 1.15(b).
  have hrel : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
    have heqcent : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = C := by
      rw [hC]
      refine le_antisymm (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr (Subgroup.mem_zpowers b)))) ?_
      · intro g hg
        rw [Subgroup.mem_centralizer_iff] at hg ⊢
        intro z hz
        rw [SetLike.mem_coe] at hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hcom : Commute b g := hg b (Set.mem_singleton b)
        exact hcom.zpow_left k
    have hrel := opiCoreInG_centralizer_inf_le_opiCoreInG hXsolv (Subgroup.zpowers_le.mpr hbX) hbp
    rwa [heqcent, ← hH] at hrel
  exact (le_inf hW_le hWH).trans (hstep.trans hrel)

/-- **General case of BG Proposition 7.5** (mmd L2299-2307): given a noncyclic abelian `B ≤ A`
of `p`-elements that normalizes the `A`-invariant `p'`-subgroup `Y ≤ X` coprimely, if each
`C_Y(b) ⊆ O_{p'}(C_G(b))` (`b ∈ B^#`, the special-case input `hspec`), then `Y ≤ O_{p'}(X)`.
Proof: Proposition 1.16 gives `Y = ⟨C_Y(b) | b ∈ B^#⟩` (`nontrivialActionFixedByClosure = ⊤`),
and `le_opiCoreInG_of_le_opiCoreInG_centralizer` sends each `C_Y(b)` into `O_{p'}(X)`. -/
private theorem coreClaimGeneral
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hXsolv : IsSolvable ↥X) {A : Subgroup G} (hAX : A ≤ X)
    {B : Subgroup G} (hBA : B ≤ A) [IsMulCommutative ↥B] (hB_nc : ¬ IsCyclic ↥B)
    (hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b))
    {Y : Subgroup G} (hYX : Y ≤ X) (hAY : A ≤ Subgroup.normalizer Y)
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y))
    (hspec : ∀ b ∈ B, b ≠ (1 : G) →
      Y ⊓ Subgroup.centralizer ({b} : Set G)
        ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G))) :
    Y ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  classical
  have hBY : B ≤ Subgroup.normalizer Y := hBA.trans hAY
  have hY_inv : Ch03.IsAInvariant (conjAction B) Y := isAInvariant_conjAction_iff.mpr hBY
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hY_inv.restrict hcop hB_nc
  have hle : nontrivialActionFixedByClosure hY_inv.restrict
      ≤ (opiCoreInG ({p} : Set ℕ)ᶜ X ⊓ Y).subgroupOf Y := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb_ne
    rw [actionFixedBy_conjAction_restrict]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hb_ne' : (b : G) ≠ 1 := fun h => hb_ne (Subtype.ext h)
    have hbX : (b : G) ∈ X := hAX (hBA b.2)
    have hW_le_X : Y ⊓ Subgroup.centralizer ({(b : G)} : Set G) ≤ opiCoreInG ({p} : Set ℕ)ᶜ X :=
      le_opiCoreInG_of_le_opiCoreInG_centralizer hXsolv (hBp (b : G) b.2) hbX
        (le_trans inf_le_left hYX) (hspec (b : G) b.2 hb_ne')
    exact Subgroup.mem_inf.mpr ⟨hW_le_X hz, (Subgroup.mem_inf.mp hz).1⟩
  rw [htop, top_le_iff, Subgroup.subgroupOf_eq_top] at hle
  exact le_trans hle inf_le_left

/-- **Sylow-of-subgroup**: a Sylow `p`-subgroup `P` of `G` contained in `K ≤ G` restricts to a
Sylow `p`-subgroup of `↥K` (with carrier `P.subgroupOf K`): `P.subgroupOf K` is a `p`-group, and
`p ∤ (P.subgroupOf K).index` since it divides `P.index` (`relIndex_dvd_index_of_le`). Used for
`b ∈ Z(P)`: `P` is a Sylow of `C_G(b)`. -/
private theorem sylow_subgroupOf_of_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow p G) {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ∃ Q : Sylow p ↥K, (Q : Subgroup ↥K) = (P : Subgroup G).subgroupOf K := by
  have hpg : IsPGroup p ↥((P : Subgroup G).subgroupOf K) := by
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]; exact hn)
  have hidx : ¬ p ∣ ((P : Subgroup G).subgroupOf K).index := fun h =>
    P.not_dvd_index (dvd_trans h (Subgroup.relIndex_dvd_index_of_le hPK))
  exact ⟨hpg.toSylow hidx, hpg.toSylow_coe hidx⟩

/-- **`hspec` for `b ∈ Z(P)`** (special case 1, mmd L2275-2285 packaged for the general case): if
`b ∈ Z(P)` (so `P ≤ C_G(b)`), then any `A`-invariant `p'`-subgroup `W` of `C_G(b)` lies in
`O_{p'}(C_G(b))`. Proof: `P` is a Sylow `p`-subgroup of `K := C_G(b)` (`sylow_subgroupOf_of_le`),
`A.subgroupOf K` is `SCN` in it (transported from `A ⊴ P`, `C_P(A) ⊆ A`), so `specialCase` at `↥K`
gives `W.subgroupOf K ≤ O_{p'}(↥K)`, which maps back to `W ≤ O_{p'}(C_G(b))`. -/
private theorem le_opiCoreInG_centralizer_of_mem_centralizer_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (hp2 : p ≠ 2) (P : Sylow p G) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G))
    [hAcomm : IsMulCommutative A] (hAnormP : (P : Subgroup G) ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A)
    {b : G} (hb_ne : b ≠ 1) (hbP : (P : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G))
    {W : Subgroup G} (hWcent : W ≤ Subgroup.centralizer ({b} : Set G))
    (hAW : A ≤ Subgroup.normalizer W) (hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W) :
    W ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G)) := by
  classical
  set K : Subgroup G := Subgroup.centralizer ({b} : Set G) with hK
  haveI hKsolv : IsSolvable ↥K :=
    hG.solvable_of_lt_top K (by rw [hK]; exact centralizer_singleton_lt_top hG hb_ne)
  have hodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hAK : A ≤ K := le_trans hAP (by rw [hK]; exact hbP)
  have hWK : W ≤ K := by rw [hK]; exact hWcent
  obtain ⟨Q, hQeq⟩ := sylow_subgroupOf_of_le P hbP
  -- `A.subgroupOf K` is abelian, contained in `Q`, normalized by `Q`, with `C_Q(A) ⊆ A`.
  haveI : IsMulCommutative ↥(A.subgroupOf K) := by
    refine ⟨⟨fun a c => Subtype.ext (Subtype.ext ?_)⟩⟩
    have := (isMulCommutative_iff_of_setLike.mp hAcomm)
    exact this _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp c.2)
  have hAQ : A.subgroupOf K ≤ (Q : Subgroup ↥K) := by
    rw [hQeq]; intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢; exact hAP hx
  have hQnorm : (Q : Subgroup ↥K) ≤ Subgroup.normalizer (A.subgroupOf K) := by
    rw [hQeq]; intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    have hqP : (q : G) ∈ Subgroup.normalizer A := hAnormP hq
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hqP (z : G)
  have hCQA : Subgroup.centralizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊓ (Q : Subgroup ↥K)
      ≤ A.subgroupOf K := by
    rw [hQeq]
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    have hqP : (q : G) ∈ (P : Subgroup G) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hq).2
    have hqC : (q : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haK : a ∈ K := hAK ha
      have hmem : (⟨a, haK⟩ : ↥K) ∈ A.subgroupOf K := by rw [Subgroup.mem_subgroupOf]; exact ha
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).1 ⟨a, haK⟩ hmem
      exact congrArg Subtype.val this
    exact hCPA (Subgroup.mem_inf.mpr ⟨hqC, hqP⟩)
  -- `W.subgroupOf K` is `A`-invariant and a `p'`-subgroup.
  have hWnorm : A.subgroupOf K ≤ Subgroup.normalizer (W.subgroupOf K) := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    have haW : (a : G) ∈ Subgroup.normalizer W := hAW ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp haW (z : G)
  have hWpi' : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (W.subgroupOf K) := by
    intro r hr
    refine hWpi r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at hr
  -- specialCase at `↥K`, then transport back.
  have hW' := specialCase hp2 hodd Q hAQ hQnorm hCQA hWnorm hWpi'
  rw [hK]
  calc W = (W.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hWK).symm
    _ ≤ (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥K).map K.subtype := Subgroup.map_mono hW'
    _ = opiCoreInG ({p} : Set ℕ)ᶜ K := rfl

/-- **SCN unpacked into ambient form**: if `A.subgroupOf P` is `SCN` in `↥P` (with `A ≤ P`), then
`A` is abelian, `P ≤ N_G(A)`, and `C_G(A) ⊓ P ≤ A` — exactly the hypotheses `specialCase` /
`le_opiCoreInG_centralizer_of_mem_centralizer_sylow` require. Transports normality/self-centralizing
from `↥P` to `G`. -/
private theorem scn_ambient {p : ℕ} {G : Type*} [Group G] {P : Sylow p G} {A : Subgroup G}
    (hAP : A ≤ (P : Subgroup G)) (h : IsSCN (A.subgroupOf (P : Subgroup G))) :
    IsMulCommutative A ∧ (P : Subgroup G) ≤ Subgroup.normalizer A ∧
      Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A := by
  haveI hAcomm : IsMulCommutative A :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp h.isMulCommutative
        (⟨a, hAP ha⟩ : ↥(P : Subgroup G)) (Subgroup.mem_subgroupOf.mpr ha)
        ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  refine ⟨hAcomm, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have := h.isNormal.conj_mem ⟨a, hAP ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨g, hg⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    · intro ha
      have hga : g * a * g⁻¹ ∈ A := ha
      have := h.isNormal.conj_mem ⟨g * a * g⁻¹, hAP hga⟩ (Subgroup.mem_subgroupOf.mpr hga)
        ⟨g, hg⟩⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      have heq : ((⟨g, hg⟩⁻¹ * ⟨g * a * g⁻¹, hAP hga⟩ * (⟨g, hg⟩⁻¹)⁻¹ : ↥(P : Subgroup G)) : G)
          = a := by simp [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rwa [heq] at this
  · intro x hx
    have hmem : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : ↥(P : Subgroup G))
        ∈ Subgroup.centralizer ((A.subgroupOf (P : Subgroup G) : Subgroup ↥(P : Subgroup G))
          : Set ↥(P : Subgroup G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 (a : G) ha)
    rw [h.selfCentralizing] at hmem
    rwa [Subgroup.mem_subgroupOf] at hmem

/-- **Coprime decomposition reduction** (for special case 2): if `z` normalizes `W` coprimely and
both `C_W(z) = W ⊓ C_G(z)` and `⁅⟨z⟩, W⁆` lie in `L`, then `W ≤ L`. From the coprime decomposition
`W = C_W(z)·⁅W,z⁆` (`fixedPoints_sup_actionCommutator_eq_top`): the `fixedPoints` summand is
`C_W(z)` and the `actionCommutator` summand is `⁅⟨z⟩, W⁆`, both `≤ L`. -/
private theorem le_of_centralizer_inf_le_of_commutator_le {G : Type*} [Group G] [Finite G]
    {z : G} {W : Subgroup G} (hzW : z ∈ Subgroup.normalizer W)
    (hcop : Nat.Coprime (orderOf z) (Nat.card ↥W)) {L : Subgroup G}
    (hcent : W ⊓ Subgroup.centralizer ({z} : Set G) ≤ L)
    (hcomm : ⁅Subgroup.zpowers z, W⁆ ≤ L) :
    W ≤ L := by
  classical
  have hzpW : Subgroup.zpowers z ≤ Subgroup.normalizer W := Subgroup.zpowers_le.mpr hzW
  have hW_inv : Ch03.IsAInvariant (conjAction (Subgroup.zpowers z)) W :=
    isAInvariant_conjAction_iff.mpr hzpW
  have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers z)) (Nat.card ↥W) := by
    rw [Nat.card_zpowers]; exact hcop
  have htop := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
    (φ := hW_inv.restrict) hCop' (Or.inl inferInstance)
  rw [← Subgroup.subgroupOf_eq_top, eq_top_iff, ← htop, sup_le_iff]
  refine ⟨?_, ?_⟩
  · -- `fixedPoints ≤ L.subgroupOf W`: a fixed point centralizes `z`.
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hcent (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hval := congrArg Subtype.val
      (Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨z, Subgroup.mem_zpowers z⟩)
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `actionCommutator ≤ L.subgroupOf W`: each generator is a `⁅z, w⁆`.
    rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a g
    rw [Subgroup.mem_subgroupOf]
    have hgen : (((hW_inv.restrict a) g * g⁻¹ : ↥W) : G)
        = (a : G) * (g : G) * (a : G)⁻¹ * (g : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Ch03.IsAInvariant.restrict_apply_val]
      simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [hgen]
    exact hcomm (Subgroup.commutator_mem_commutator a.2 g.2)

/-- **Commutator part of special case 2**: if `z ∈ O_{p',p}(H)` normalizes a `p'`-subgroup `W`,
then `⁅⟨z⟩, W⁆ ≤ O_{p'}(H)`. Proof: `⁅⟨z⟩,W⁆ ≤ W` (z normalizes W) and `≤ O_{p',p}(H)`
(z ∈ O_{p',p} ⊴ H), so `⁅⟨z⟩,W⁆ ≤ W ⊓ O_{p',p}(H)`, a `p'`-subgroup whose image in
`H/O_{p'}(H) = O_p(quotient)` (via `oPiPrimePiCore_map_mk'_eq`) is a `p'`-subgroup of a `p`-group,
hence trivial — so it lies in `ker = O_{p'}(H)`. -/
private theorem commutator_zpowers_le_oPiCore {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] {z : H} (hz : z ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H)
    {W : Subgroup H} (hzW : z ∈ Subgroup.normalizer W)
    (hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W) :
    ⁅Subgroup.zpowers z, W⁆ ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ H := by
  haveI hOnorm : (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).Normal := inferInstance
  have hsubW : ⁅Subgroup.zpowers z, W⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : a * b * a⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hzW) ha) b).mp hb
    simpa [commutatorElement_def, mul_assoc] using W.mul_mem hab (W.inv_mem hb)
  have hsubO : ⁅Subgroup.zpowers z, W⁆ ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) H := by
    rw [Subgroup.commutator_le]
    intro a ha b _
    have haO : a ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).zpow_mem hz k
    have hconj : b * a⁻¹ * b⁻¹ ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H :=
      hOnorm.conj_mem a⁻¹ ((Ch03.oPiPrimePiCore ({p} : Set ℕ) H).inv_mem haO) b
    simpa [commutatorElement_def, mul_assoc] using
      (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).mul_mem haO hconj
  -- `⁅⟨z⟩,W⁆ ≤ W ⊓ O_{p',p}(H)`; its mk'-image is a `p'`-subgroup of the `p`-group `O_p(H/O_{p'})`.
  refine (le_inf hsubW hsubO).trans ?_
  have hbridge : (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
        (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))
      = Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H) :=
    oPiPrimePiCore_map_mk'_eq ({p} : Set ℕ)
  have hle : (W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
        (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))
      ≤ Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H) :=
    hbridge ▸ Subgroup.map_mono inf_le_right
  have hT_pg : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H)) := by
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p _
  have hM_cop : Nat.Coprime (Nat.card ↥((W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
      (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H)))) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      have hdvd : Nat.card ↥((W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
            (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))) ∣ Nat.card ↥W :=
        (Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_le inf_le_left)
      exact hWpi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hbot : (W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
      (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H)) = ⊥ := by
    have hinf := OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hT_pg hM_cop
    rwa [inf_eq_right.mpr hle] at hinf
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

/-- **Orbit-stabilizer crux for Proposition 7.5, special case 2**: if `b ≠ 1` lies in a subgroup
`B ≤ P` of order `p²` invariant under `P`-conjugation (`B ⊴ P`), then `|P : C_P(b)| ≤ p`, i.e.
`|P| ≤ p · |C_P(b)|`. The `P`-conjugacy orbit of `b` lies in `B ∖ {1}` (so `< p²` elements) and its
size divides `|P|`, hence is a power of `p` below `p²`, so `≤ p`; orbit-stabilizer
(`|P| = |orbit| · |stabilizer|`, `stabilizer = C_P(b)`) converts this into the index bound. -/
private theorem card_le_prime_mul_card_centralizer_inf {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] {P : Sylow p G} {B : Subgroup G} (hBP : B ≤ (P : Subgroup G))
    (hBcard : Nat.card ↥B = p ^ 2) (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {b : G} (hb_ne : b ≠ 1) (hbP : b ∈ (P : Subgroup G)) (hbB : b ∈ B) :
    Nat.card ↥(P : Subgroup G)
      ≤ p * Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) := by
  classical
  set R : Type _ := ↥(P : Subgroup G) with hRdef
  set bhat : R := ⟨b, hbP⟩ with hbhat
  set Bsub : Subgroup R := B.subgroupOf (P : Subgroup G) with hBsub
  haveI : Finite (ConjAct R) := inferInstanceAs (Finite R)
  have hBsub_card : Nat.card ↥Bsub = p ^ 2 := by
    rw [hBsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hBcard]
  have horb_sub : MulAction.orbit (ConjAct R) bhat ⊆ (Bsub : Set R) := by
    rintro _ ⟨c, rfl⟩
    show (c • bhat) ∈ (Bsub : Set R)
    rw [SetLike.mem_coe, hBsub, Subgroup.mem_subgroupOf, ConjAct.smul_def]
    show (ConjAct.ofConjAct c : R).val * b * ((ConjAct.ofConjAct c : R).val)⁻¹ ∈ B
    exact hBnorm _ (ConjAct.ofConjAct c).2 b hbB
  have hone_not : (1 : R) ∉ MulAction.orbit (ConjAct R) bhat := by
    rintro ⟨c, hc⟩
    rw [show (fun m : ConjAct R => m • bhat) c = c • bhat from rfl, ConjAct.smul_def] at hc
    have hb1 : bhat = 1 := by
      have h2 : ConjAct.ofConjAct c * bhat = ConjAct.ofConjAct c * 1 := by
        rw [mul_one]; exact mul_inv_eq_one.mp hc
      exact mul_left_cancel h2
    exact hb_ne (congrArg (Subtype.val : R → G) hb1)
  have hBsub_ncard : (Bsub : Set R).ncard = p ^ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hBsub_card
  have hlt : Nat.card (MulAction.orbit (ConjAct R) bhat) < p ^ 2 := by
    calc Nat.card (MulAction.orbit (ConjAct R) bhat)
        = (MulAction.orbit (ConjAct R) bhat).ncard := Nat.card_coe_set_eq _
      _ < (Bsub : Set R).ncard :=
          Set.ncard_lt_ncard ⟨horb_sub, fun h => hone_not (h Bsub.one_mem)⟩ (Set.toFinite _)
      _ = p ^ 2 := hBsub_ncard
  have hdvd : Nat.card (MulAction.orbit (ConjAct R) bhat) ∣ Nat.card R := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct R) bhat),
      Nat.card_congr (ConjAct.toConjAct (G := R)).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  rw [← hRdef] at hk
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hk ▸ hdvd)
  have horb_le : Nat.card (MulAction.orbit (ConjAct R) bhat) ≤ p := by
    rw [hj] at hlt ⊢
    have hj1 : j ≤ 1 := by
      by_contra h
      push_neg at h
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le h))
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hj1
      _ = p := pow_one p
  -- Orbit-stabilizer: `|P| = |orbit| · |stab|`, with `stab = C_R(bhat)` injecting into `C_G(b) ⊓ P`.
  set stab : Subgroup (ConjAct R) := MulAction.stabilizer (ConjAct R) bhat with hstabdef
  have hPeq : Nat.card R = Nat.card (MulAction.orbit (ConjAct R) bhat) * Nat.card ↥stab := by
    have hidx : stab.index = Nat.card (MulAction.orbit (ConjAct R) bhat) := by
      rw [hstabdef, MulAction.index_stabilizer, Nat.card_coe_set_eq]
    have hmul : stab.index * Nat.card ↥stab = Nat.card (ConjAct R) := Subgroup.index_mul_card stab
    rw [hidx] at hmul
    rw [Nat.card_congr (ConjAct.toConjAct (G := R)).toEquiv]
    exact hmul.symm
  -- `|stab| ≤ |C_G(b) ⊓ P|` via `c ↦ (ofConjAct c).val`.
  have hmem : ∀ c : ↥stab, ((ConjAct.ofConjAct (c : ConjAct R) : R) : G)
      ∈ Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G) := by
    rintro ⟨c, hc⟩
    rw [hstabdef, MulAction.mem_stabilizer_iff, ConjAct.smul_def] at hc
    refine Subgroup.mem_inf.mpr ⟨?_, (ConjAct.ofConjAct c : R).2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
    have hcomm : (ConjAct.ofConjAct c : R) * bhat = bhat * (ConjAct.ofConjAct c : R) := by
      rw [mul_inv_eq_iff_eq_mul] at hc; exact hc
    have hval : ((ConjAct.ofConjAct c : R) : G) * b = b * ((ConjAct.ofConjAct c : R) : G) := by
      have h := congrArg (Subtype.val : R → G) hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hbhat] at h
      exact h
    exact hval.symm
  have hstab_le : Nat.card ↥stab
      ≤ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) ?_
    intro c₁ c₂ h
    have hv : ((ConjAct.ofConjAct (c₁ : ConjAct R) : R) : G)
        = ((ConjAct.ofConjAct (c₂ : ConjAct R) : R) : G) := by
      have := Subtype.ext_iff.mp h
      simpa using this
    exact Subtype.ext (ConjAct.ofConjAct.injective (Subtype.ext hv))
  calc Nat.card ↥(P : Subgroup G) = Nat.card R := rfl
    _ = Nat.card (MulAction.orbit (ConjAct R) bhat) * Nat.card ↥stab := hPeq
    _ ≤ p * Nat.card ↥stab := Nat.mul_le_mul_right _ horb_le
    _ ≤ p * Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) :=
        Nat.mul_le_mul_left _ hstab_le

/-- For a nontrivial `p`-group `A`, `π(A) = {p}` (so `(π(A))ᶜ = {p}ᶜ`). Used to align
`hInvariant`/`opiCoreInG (primesOf A)ᶜ` with the single-prime lemmas of §1. -/
private theorem primesOf_eq_singleton [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAp : IsPGroup p A) (hAne : A ≠ ⊥) : primesOf A = ({p} : Set ℕ) := by
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hAne (Subgroup.card_eq_one.mp hn)
  ext q
  simp only [primesOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- **`z ∈ O_{p',p}(C_G(b))` for special case 2** (mmd L2289-2293): given `B ⊴ P` of order `p²`
containing `b ≠ 1`, and `z` central in `P` with `z ∈ C_G(b)`, the element `z` lies in
`O_{p',p}(C_G(b))`. Proof: `P₁ = C_P(b)` extends to a Sylow `P₂` of `C_G(b)`; the orbit bound
`card_le_prime_mul_card_centralizer_inf` plus `|P₂| ≤ |P|` give `|P₂ : P₁| ≤ p`, so `P₁ ⊴ P₂`. Then
`Z(P₁) = C(P₁) ⊓ P₁` is abelian, normal in `P₂`, contains `z`, so Theorem 6.1 (`thmA4b`) places it
in `O_{p',p}(C_G(b))`. -/
private theorem mem_oPiPrimePiCore_centralizer_of_central {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (hp2 : p ≠ 2) (P : Sylow p G)
    {B : Subgroup G} (hBP : B ≤ (P : Subgroup G)) (hBcard : Nat.card ↥B = p ^ 2)
    (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {z : G} (hzP : z ∈ (P : Subgroup G))
    (hz_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {b : G} (hbB : b ∈ B) (hb_ne : b ≠ 1) (hzCb : z ∈ Subgroup.centralizer ({b} : Set G)) :
    (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G)))
      ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥(Subgroup.centralizer ({b} : Set G)) := by
  classical
  set K : Subgroup G := Subgroup.centralizer ({b} : Set G) with hK
  haveI hKsolv : IsSolvable ↥K :=
    hG.solvable_of_lt_top K (by rw [hK]; exact centralizer_singleton_lt_top hG hb_ne)
  have hodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hbP : b ∈ (P : Subgroup G) := hBP hbB
  -- `P₁ = C_P(b)` inside `K`, extended to a Sylow `P₂` of `K`.
  set P₁ : Subgroup ↥K := (P : Subgroup G).subgroupOf K with hP₁def
  have hP₁pg : IsPGroup p ↥P₁ := P.isPGroup'.comap_subtype
  obtain ⟨P₂, hP₁₂⟩ := hP₁pg.exists_le_sylow
  -- `|P₂| ≤ |P|`.
  have hcardP₂_le : Nat.card ↥(P₂ : Subgroup ↥K) ≤ Nat.card ↥(P : Subgroup G) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp P₂.isPGroup'
    have hdvdG : Nat.card ↥(P₂ : Subgroup ↥K) ∣ Nat.card G := by
      have h1 : Nat.card ↥((P₂ : Subgroup ↥K).map K.subtype) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card ↥((P₂ : Subgroup ↥K).map K.subtype) = Nat.card ↥(P₂ : Subgroup ↥K) :=
        Subgroup.card_map_of_injective Subtype.coe_injective
      rwa [h2] at h1
    have hdvdP : Nat.card ↥(P₂ : Subgroup ↥K) ∣ Nat.card ↥(P : Subgroup G) := by
      rw [ha] at hdvdG ⊢
      exact P.pow_dvd_card_of_pow_dvd_card hdvdG
    exact Nat.le_of_dvd Nat.card_pos hdvdP
  -- `|P| ≤ p · |P₁|` (orbit bound), via `|P₁| = |C_G(b) ⊓ P|`.
  have hcardP₁ : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G))
      = Nat.card ↥P₁ := by
    rw [hP₁def, hK, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv, inf_comm]
  have hbound : Nat.card ↥(P : Subgroup G) ≤ p * Nat.card ↥P₁ := by
    rw [← hcardP₁]
    exact card_le_prime_mul_card_centralizer_inf hBP hBcard hBnorm hb_ne hbP hbB
  -- `|P₂ : P₁| ≤ p`.
  have hidx_le : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ≤ p := by
    have hmul : Nat.card ↥(P₁.subgroupOf (P₂ : Subgroup ↥K))
        * (P₁.subgroupOf (P₂ : Subgroup ↥K)).index = Nat.card ↥(P₂ : Subgroup ↥K) :=
      Subgroup.card_mul_index _
    have hsub : Nat.card ↥(P₁.subgroupOf (P₂ : Subgroup ↥K)) = Nat.card ↥P₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁₂).toEquiv
    rw [hsub] at hmul
    have hpos : 0 < Nat.card ↥P₁ := Nat.card_pos
    have hle : Nat.card ↥P₁ * (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ≤ Nat.card ↥P₁ * p := by
      rw [hmul, mul_comm (Nat.card ↥P₁) p]
      exact le_trans hcardP₂_le hbound
    exact Nat.le_of_mul_le_mul_left hle hpos
  -- `P₁ ⊴ P₂`.
  have hP₁₂normal : (P₁.subgroupOf (P₂ : Subgroup ↥K)).Normal := by
    obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp P₂.isPGroup'
    have hidx_dvd : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ∣ p ^ c :=
      hc ▸ Subgroup.index_dvd_card _
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hidx_dvd
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, pow_zero] at hj
      exact Subgroup.normal_of_index_eq_one hj
    · have hj1 : j = 1 := by
        by_contra h
        have hj2 : 2 ≤ j := by omega
        have hple : p ^ 2 ≤ p :=
          le_trans (Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hj2) (hj ▸ hidx_le)
        nlinarith [(Fact.out : p.Prime).two_le, hple]
      have hc_ne : c ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hc
        have hdvd1 : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ∣ 1 := hc ▸ Subgroup.index_dvd_card _
        rw [hj, hj1, pow_one, Nat.dvd_one] at hdvd1
        exact (Fact.out : p.Prime).one_lt.ne' hdvd1
      have hmin : (Nat.card ↥(P₂ : Subgroup ↥K)).minFac = p := by
        rw [hc, (Fact.out : p.Prime).pow_minFac hc_ne]
      refine Subgroup.normal_of_index_eq_minFac_card ?_
      rw [hj, hj1, pow_one, hmin]
  have hP₂_norm_P₁ : (P₂ : Subgroup ↥K) ≤ Subgroup.normalizer P₁ :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP₁₂).mp hP₁₂normal
  -- `A' = Z(P₁) = C(P₁) ⊓ P₁`: abelian, ≤ P₂, normal in P₂, contains `z`.
  set A' : Subgroup ↥K := Subgroup.centralizer (P₁ : Set ↥K) ⊓ P₁ with hA'def
  haveI hA'comm : IsMulCommutative ↥A' :=
    IsMulCommutative.of_setLike_mul_comm fun a ha c hc =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).1 c
        (SetLike.mem_coe.mpr (Subgroup.mem_inf.mp hc).2)).symm
  have hA'_le_P₂ : A' ≤ (P₂ : Subgroup ↥K) := le_trans inf_le_right hP₁₂
  have hconj_pres : ∀ g ∈ (P₂ : Subgroup ↥K), ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro g hg x hx
    obtain ⟨hxc, hxP₁⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwP₁ : w ∈ P₁ := hw
      have hg'norm : g⁻¹ ∈ Subgroup.normalizer P₁ := inv_mem (hP₂_norm_P₁ hg)
      have hv : g⁻¹ * w * g ∈ P₁ := by
        have := (Subgroup.mem_normalizer_iff.mp hg'norm w).mp hwP₁
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc (g⁻¹ * w * g) (SetLike.mem_coe.mpr hv)
      calc w * (g * x * g⁻¹)
          = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * w := by group
    · exact (Subgroup.mem_normalizer_iff.mp (hP₂_norm_P₁ hg) x).mp hxP₁
  have hA'_norm : (P₂ : Subgroup ↥K) ≤ Subgroup.normalizer A' := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hconj_pres g hg x hx
    · intro hx
      have h2 := hconj_pres g⁻¹ ((P₂ : Subgroup ↥K).inv_mem hg) _ hx
      have heq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [heq] at h2
  have hzK : z ∈ K := by rw [hK]; exact hzCb
  have hzA' : (⟨z, hzK⟩ : ↥K) ∈ A' := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwP₁ : w ∈ P₁ := hw
      rw [hP₁def, Subgroup.mem_subgroupOf] at hwP₁
      have hcomm : ((w : ↥K) : G) * z = z * ((w : ↥K) : G) :=
        (Subgroup.mem_centralizer_iff.mp (hz_cent hwP₁) z rfl).symm
      exact Subtype.ext hcomm
    · rw [hP₁def, Subgroup.mem_subgroupOf]; exact hzP
  -- Theorem 6.1: `Z(P₁) ⊆ O_{p',p}(C_G(b))`.
  have hThm61 : A' ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥K :=
    OddOrder.BG.AppA.thmA4b hp2 hKsolv hodd P₂ hA'_le_P₂ hA'_norm
  exact hThm61 hzA'

/-- **`hspec` for special case 2** (mmd L2287-2297): for `b ∈ B^#`, with a `p`-central element `z`
of order `p`, the `A`-invariant `p'`-subgroup `W = Y ⊓ C_G(b)` lies in `O_{p'}(C_G(b))`. The coprime
decomposition `W = C_W(z)·⁅⟨z⟩,W⁆` (`le_of_centralizer_inf_le_of_commutator_le`) splits the goal:
`C_W(z)` lands in `O_{p'}(C_G(b))` by special case 1 at `z` plus the per-`b` bridge, and `⁅⟨z⟩,W⁆`
by `commutator_zpowers_le_oPiCore` (its `z ∈ O_{p',p}(C_G(b))` input is the crux above). -/
private theorem centralizer_inf_le_opiCoreInG_of_central
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (hp2 : p ≠ 2) (P : Sylow p G) {A : Subgroup G} (hAcomm : IsMulCommutative A)
    (hAP : A ≤ (P : Subgroup G)) (hAnormP : (P : Subgroup G) ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A)
    {B : Subgroup G} (hBA : B ≤ A) (hBP : B ≤ (P : Subgroup G)) (hBcard : Nat.card ↥B = p ^ 2)
    (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {z : G} (hzA : z ∈ A) (hzP : z ∈ (P : Subgroup G))
    (hz_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) (hz_ord : orderOf z = p)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y)
    {b : G} (hbB : b ∈ B) (hb_ne : b ≠ 1) :
    Y ⊓ Subgroup.centralizer ({b} : Set G)
      ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G)) := by
  classical
  haveI := hAcomm
  set W : Subgroup G := Y ⊓ Subgroup.centralizer ({b} : Set G) with hWdef
  have hWY : W ≤ Y := inf_le_left
  have hWCb : W ≤ Subgroup.centralizer ({b} : Set G) := inf_le_right
  have hbA : b ∈ A := hBA hbB
  have hz_ne : z ≠ 1 := by
    rintro rfl; rw [orderOf_one] at hz_ord; exact (Fact.out : p.Prime).one_lt.ne hz_ord
  have hz_pg : IsPGroup p (Subgroup.zpowers z) := (P.isPGroup').to_le (Subgroup.zpowers_le.mpr hzP)
  -- `z` commutes with `b` (both in abelian `A`).
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨b, hbA⟩ ⟨z, hzA⟩)
  -- `z ∈ N_G(W)`: it normalizes both `Y` (`z ∈ A`) and `C_G(b)` (`z ∈ C_G(b)`).
  have hzNW : z ∈ Subgroup.normalizer W := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hWdef, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (hAY hzA) x,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hzCb) x]
  have hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W := fun q hq =>
    hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hWY) Nat.card_pos.ne' hq)
  refine le_of_centralizer_inf_le_of_commutator_le hzNW ?_ ?_ ?_
  · -- coprimality.
    rw [hz_ord]
    refine (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hdvd => ?_)
    exact hYpi p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hdvd.trans (Subgroup.card_dvd_of_le hWY), Nat.card_pos.ne'⟩) rfl
  · -- `C_W(z) ≤ O_{p'}(C_G(b))`: special case 1 at `z`, then the per-`b` bridge.
    have hCYz : Y ⊓ Subgroup.centralizer ({z} : Set G)
        ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({z} : Set G)) := by
      refine le_opiCoreInG_centralizer_of_mem_centralizer_sylow hG hp2 P hAP hAnormP hCPA hz_ne
        hz_cent inf_le_right ?_ ?_
      · intro a ha
        have haCz : a ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
          exact congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨z, hzA⟩ ⟨a, ha⟩)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hAY ha) x,
          Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haCz) x]
      · intro q hq
        exact hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left)
          Nat.card_pos.ne' hq)
    have hWz_le : W ⊓ Subgroup.centralizer ({z} : Set G)
        ≤ Y ⊓ Subgroup.centralizer ({z} : Set G) := by
      rw [hWdef]; exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    exact le_opiCoreInG_of_le_opiCoreInG_centralizer
      (hG.solvable_of_lt_top _ (centralizer_singleton_lt_top hG hb_ne)) hz_pg hzCb
      (le_trans inf_le_left hWCb) (le_trans hWz_le hCYz)
  · -- `⁅⟨z⟩,W⁆ ≤ O_{p'}(C_G(b))`: `commutator_zpowers_le_oPiCore` in `↥(C_G(b))`, transported back.
    have hzO := mem_oPiPrimePiCore_centralizer_of_central hG hp2 P hBP hBcard hBnorm hzP hz_cent
      hbB hb_ne hzCb
    have hzW_H : (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G)))
        ∈ Subgroup.normalizer (W.subgroupOf (Subgroup.centralizer ({b} : Set G))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hzNW (x : G)
    have hWpi_H : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ
        (W.subgroupOf (Subgroup.centralizer ({b} : Set G))) := by
      intro q hq
      refine hWpi q ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWCb).toEquiv] at hq
    have hcomm_H := commutator_zpowers_le_oPiCore hzO hzW_H hWpi_H
    have hmapeq : (⁅Subgroup.zpowers (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G))),
          W.subgroupOf (Subgroup.centralizer ({b} : Set G))⁆).map
          (Subgroup.centralizer ({b} : Set G)).subtype = ⁅Subgroup.zpowers z, W⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hWCb]
      rfl
    rw [← hmapeq]
    exact Subgroup.map_mono hcomm_H

/-- **Core claim of BG Proposition 7.5, case (2)** (mmd L2273-2307): for `A ∈ SCN₂(P)`, every
`A`-invariant `p'`-subgroup `Y ≤ X` (of a proper subgroup `X ⊇ A`) lies in `O_{p'}(X)`. Proof:
build `B ∈ E_p²(A)` with `B ⊴ P` (cyclic/noncyclic `Z(P)` split via G 2.6.4), then feed the
special-case inputs (`b ∈ Z(P)` via `le_opiCoreInG_centralizer_of_mem_centralizer_sylow`; general
`b ∈ B^#` via the coprime decomposition) to `coreClaimGeneral`. -/
private theorem coreClaim_scn2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    {P : Sylow p G} (hAP : A ≤ (P : Subgroup G))
    (hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))
    {X : Subgroup G} (hAX : A ≤ X) (hXlt : X < ⊤)
    {Y : Subgroup G} (hYX : Y ≤ X) (hAY : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup (primesOf A)ᶜ Y) :
    Y ≤ opiCoreInG (primesOf A)ᶜ X := by
  classical
  -- `A ≠ ⊥` from `pRank (A.subgroupOf P) ≥ 2`, then `π(A) = {p}`.
  have hAne : A ≠ ⊥ := by
    intro hAbot
    obtain ⟨B, _, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (p := p) (by norm_num) hAscn2.le_pRank
    have hp2 : p ^ 2 ≤ Nat.card ↥B := Nat.pow_le_of_le_log Nat.card_pos.ne' hBlog
    have hBdvd : Nat.card ↥B ∣ Nat.card ↥(A.subgroupOf (P : Subgroup G)) :=
      Subgroup.card_subgroup_dvd_card B
    have hcard1 : Nat.card ↥(A.subgroupOf (P : Subgroup G)) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAbot, Subgroup.card_bot]
    rw [hcard1, Nat.dvd_one] at hBdvd
    rw [hBdvd] at hp2
    nlinarith [hp2, (Fact.out : p.Prime).two_le]
  have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hAne
  rw [hπ] at hYpi ⊢
  -- SCN ambient facts and solvability of `X` (a proper subgroup of a minimal simple group).
  obtain ⟨_, hAnormP, hCPA⟩ := scn_ambient hAP hAscn2.isSCN
  haveI hXsolv : IsSolvable ↥X := hG.solvable_of_lt_top X hXlt
  -- `p` is odd (it divides `|G|`, which is odd).
  have hpA : p ∣ Nat.card ↥A := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [pow_zero] at hn; exact absurd (Subgroup.card_eq_one.mp hn) hAne
    · rw [hn]; exact dvd_pow_self p hn0.ne'
  have hp_odd : Odd p := hG.odd.of_dvd_nat (hpA.trans (Subgroup.card_subgroup_dvd_card A))
  have hp2 : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hp_odd; omega
  -- `Z(P)` inside `G`: elements of `P` that centralize `P`. `Z(P) ≤ A` (SCN), each is central in `P`.
  set ZP : Subgroup G :=
    Subgroup.centralizer ((P : Subgroup G) : Set G) ⊓ (P : Subgroup G) with hZPdef
  have hZP_le_A : ZP ≤ A := by
    intro x hx
    rw [hZPdef, Subgroup.mem_inf] at hx
    exact hCPA (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP) hx.1, hx.2⟩)
  have hZP_cent : ∀ b ∈ ZP, (P : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro b hb y hy
    rw [hZPdef, Subgroup.mem_inf] at hb
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
    exact (Subgroup.mem_centralizer_iff.mp hb.1 y hy).symm
  have hZP_le_P : ZP ≤ (P : Subgroup G) := by rw [hZPdef]; exact inf_le_right
  have hZP_pg : IsPGroup p ↥ZP := (P.isPGroup').to_le hZP_le_P
  by_cases hZPcyc : IsCyclic ↥ZP
  · -- **cyclic `Z(P)`**: `B = ⟨z⟩ × Ω₁(Z(P))` via Isaacs Lemma 1.23; `b ∈ B^#` uses special case 2.
    -- A `p`-central element `z` of order `p` (Cauchy on the nontrivial `p`-group `Z(P) = ZP`).
    haveI hPnt : Nontrivial ↥(P : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => hAne (le_bot_iff.mp (hAP.trans_eq hbot))
    haveI hZc : Nontrivial (Subgroup.center ↥(P : Subgroup G)) :=
      IsPGroup.center_nontrivial P.isPGroup'
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup G))
    have hz₀_mem : ((w : ↥(P : Subgroup G)) : G) ∈ ZP := by
      rw [hZPdef, Subgroup.mem_inf]
      refine ⟨?_, (w : ↥(P : Subgroup G)).2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg (Subtype.val : ↥(P : Subgroup G) → G)
        (Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩)
    have hZP_nt : Nontrivial ↥ZP :=
      (Subgroup.nontrivial_iff_exists_ne_one ZP).mpr
        ⟨_, hz₀_mem, fun hval => hw1 (Subtype.ext (Subtype.ext hval))⟩
    have hp_dvd_ZP : p ∣ Nat.card ↥ZP := by
      obtain ⟨n, hn0, hn⟩ := hZP_pg.nontrivial_iff_card.mp hZP_nt
      rw [hn]; exact dvd_pow_self p hn0.ne'
    obtain ⟨zsub, hz_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_ZP
    set z : G := (zsub : G) with hzdef
    have hzZP : z ∈ ZP := SetLike.coe_mem zsub
    have hzA : z ∈ A := hZP_le_A hzZP
    have hzP : z ∈ (P : Subgroup G) := hZP_le_P hzZP
    have hz_centP : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := hZP_cent z hzZP
    have hz_ord' : orderOf z = p := by
      rw [hzdef, ← hz_ord]; exact orderOf_injective ZP.subtype ZP.subtype_injective zsub
    -- `A` is abelian (set form), `Ω₁(A)` and its normality in `P`.
    have hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨x, hx⟩ ⟨y, hy⟩)
    set Om : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set with hOmdef
    have hOm_le_A : Om ≤ A := OddOrder.GroupTheory.omega1OfAbelian_le
    have hOm_le_P : Om ≤ (P : Subgroup G) := hOm_le_A.trans hAP
    have hz_mem_Om : z ∈ Om := by
      rw [hOmdef, OddOrder.GroupTheory.mem_omega1OfAbelian]
      exact ⟨hzA, by rw [← hz_ord']; exact pow_orderOf_eq_one z⟩
    -- `|Ω₁(A)| ≥ p²` from `pRank A ≥ 2`.
    have hpRankA : 2 ≤ pRank A p := le_trans hAscn2.le_pRank
      (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hAP).injective)
    have hp2_dvd_Om : p ^ 2 ∣ Nat.card ↥Om := by
      rw [hOmdef]
      exact OddOrder.GroupTheory.pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankA
    -- `⟨z⟩ ⊴ P` and `Ω₁(A) ⊴ P` (both restricted to `↥P`).
    have hZ₁_le_P : Subgroup.zpowers z ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hzP
    have hP_norm_Z : (P : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers z) := by
      intro g hg
      have hc : Commute g z := (Subgroup.mem_centralizer_iff.mp (hz_centP hg) z rfl).symm
      have hfix : ∀ y ∈ Subgroup.zpowers z, g * y * g⁻¹ = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [(hc.zpow_right k).eq]; group
      have hfix' : ∀ y ∈ Subgroup.zpowers z, g⁻¹ * y * g = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [(hc.inv_left.zpow_right k).eq]; group
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; rw [hfix x hx]; exact hx
      · intro hx
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := hfix' _ hx
        have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [h2] at h1; rw [h1]; exact hx
    have hP_norm_Om : (P : Subgroup G) ≤ Subgroup.normalizer Om := by
      intro g hg
      have hgN : g ∈ Subgroup.normalizer A := hAnormP hg
      have hconjp : ∀ y : G, (g * y * g⁻¹) ^ p = g * y ^ p * g⁻¹ := fun y => by
        have := map_pow (MulAut.conj g) y p
        simpa [MulAut.conj_apply] using this.symm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hOmdef, OddOrder.GroupTheory.mem_omega1OfAbelian]
      constructor
      · rintro ⟨hxA, hxp⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp hxA, by rw [hconjp x, hxp]; group⟩
      · rintro ⟨hxA, hxp⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mpr hxA, ?_⟩
        have hgx : g * x ^ p * g⁻¹ = 1 := by rw [← hconjp x]; exact hxp
        calc x ^ p = g⁻¹ * (g * x ^ p * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hgx]
          _ = 1 := by group
    -- Isaacs Lemma 1.23 inside `↥P`: a normal `L` with `⟨z⟩ < L ≤ Ω₁(A)`, `|⟨z⟩ : L| = p`.
    set Npp : Subgroup ↥(P : Subgroup G) := (Subgroup.zpowers z).subgroupOf (P : Subgroup G)
      with hNppdef
    set Mpp : Subgroup ↥(P : Subgroup G) := Om.subgroupOf (P : Subgroup G) with hMppdef
    haveI hNpp_normal : Npp.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZ₁_le_P).mpr hP_norm_Z
    haveI hMpp_normal : Mpp.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOm_le_P).mpr hP_norm_Om
    have hNcard : Nat.card ↥Npp = p := by
      rw [hNppdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₁_le_P).toEquiv,
        Nat.card_zpowers, hz_ord']
    have hNleM : Npp ≤ Mpp :=
      Subgroup.comap_mono (Subgroup.zpowers_le.mpr hz_mem_Om)
    have hMcard_ge : p ^ 2 ≤ Nat.card ↥Mpp := by
      rw [hMppdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOm_le_P).toEquiv]
      exact Nat.le_of_dvd Nat.card_pos hp2_dvd_Om
    have hNM : Npp < Mpp := by
      refine lt_of_le_of_ne hNleM (fun heq => ?_)
      rw [heq] at hNcard; rw [hNcard] at hMcard_ge
      nlinarith [(Fact.out : p.Prime).two_le, hMcard_ge]
    obtain ⟨Lpp, hLpp_normal, hN_lt_L, hL_le_M, hrelidx⟩ :=
      OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime P.isPGroup' hNM
    set B : Subgroup G := Lpp.map (P : Subgroup G).subtype with hBdef
    have hB_le_Om : B ≤ Om := by
      rw [hBdef]
      calc Lpp.map (P : Subgroup G).subtype ≤ Mpp.map (P : Subgroup G).subtype :=
            Subgroup.map_mono hL_le_M
        _ = Om := by rw [hMppdef, Subgroup.map_subgroupOf_eq_of_le hOm_le_P]
    have hBA : B ≤ A := hB_le_Om.trans hOm_le_A
    have hBP : B ≤ (P : Subgroup G) := hB_le_Om.trans hOm_le_P
    have hBcard : Nat.card ↥B = p ^ 2 := by
      rw [hBdef, Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective]
      have hmul : Nat.card ↥(Npp.subgroupOf Lpp) * (Npp.subgroupOf Lpp).index = Nat.card ↥Lpp :=
        Subgroup.card_mul_index _
      have hNsub : Nat.card ↥(Npp.subgroupOf Lpp) = Nat.card ↥Npp :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_lt_L.le).toEquiv
      have hidx_p : (Npp.subgroupOf Lpp).index = p := hrelidx
      rw [hNsub, hNcard, hidx_p] at hmul
      rw [← hmul]; ring
    have hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B := by
      intro g hg x hx
      rw [hBdef, Subgroup.mem_map] at hx
      obtain ⟨xhat, hxhatL, rfl⟩ := hx
      rw [hBdef, Subgroup.mem_map]
      exact ⟨⟨g, hg⟩ * xhat * ⟨g, hg⟩⁻¹, hLpp_normal.conj_mem xhat hxhatL ⟨g, hg⟩, by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]⟩
    -- `B` is elementary abelian of order `p²`, hence noncyclic.
    have hB_elem : B.IsElementaryAbelian p := by
      refine ⟨fun x y => Subtype.ext (hAcomm_set _ (hBA x.2) _ (hBA y.2)), fun x => Subtype.ext ?_⟩
      exact OddOrder.GroupTheory.pow_eq_one_of_mem_omega1OfAbelian (hB_le_Om x.2)
    haveI hBcomm : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_elem.1
    have hB_nc : ¬ IsCyclic ↥B := hB_elem.not_isCyclic_of_card_prime_sq Fact.out hBcard
    have hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b) := fun b hb =>
      (P.isPGroup').to_le (Subgroup.zpowers_le.mpr (hBP hb))
    have hpY : ¬ p ∣ Nat.card ↥Y := fun hdvd =>
      hYpi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩) rfl
    have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y) := by
      rw [hBcard]; exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpY).pow_left 2
    -- General case: feed special case 2 for each `b ∈ B^#`.
    refine coreClaimGeneral hXsolv hAX hBA hB_nc hBp hYX hAY hcop ?_
    intro b hb hb_ne
    exact centralizer_inf_le_opiCoreInG_of_central hG hp2 P hAab hAP hAnormP hCPA hBA hBP hBcard
      hBnorm hzA hzP hz_centP hz_ord' hAY hYpi hb hb_ne
  · -- **noncyclic `Z(P)`**: an `E_{p²} ⊆ Z(P) ⊆ A` of central elements; every `b ∈ B^#` lies in
    -- `Z(P)`, so special case 1 (`le_opiCoreInG_centralizer_of_mem_centralizer_sylow`) applies.
    obtain ⟨E, hE_elem, hE_card⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        hZP_pg hp_odd hZPcyc
    set B : Subgroup G := E.map ZP.subtype with hBdef
    have hB_le_ZP : B ≤ ZP := by rw [hBdef]; exact Subgroup.map_subtype_le E
    have hBA : B ≤ A := hB_le_ZP.trans hZP_le_A
    have hB_elem : B.IsElementaryAbelian p := by
      rw [hBdef]; exact hE_elem.map ZP.subtype_injective
    have hBcard : Nat.card ↥B = p ^ 2 := by
      rw [hBdef, (Nat.card_congr
        (Subgroup.equivMapOfInjective E ZP.subtype ZP.subtype_injective).toEquiv).symm]
      exact hE_card
    haveI hBcomm : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_elem.1
    have hB_nc : ¬ IsCyclic ↥B := hB_elem.not_isCyclic_of_card_prime_sq Fact.out hBcard
    have hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b) := fun b hb =>
      (P.isPGroup').to_le (Subgroup.zpowers_le.mpr (hZP_le_P (hB_le_ZP hb)))
    have hpY : ¬ p ∣ Nat.card ↥Y := fun hdvd =>
      hYpi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩) rfl
    have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y) := by
      rw [hBcard]; exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpY).pow_left 2
    refine coreClaimGeneral hXsolv hAX hBA hB_nc hBp hYX hAY hcop ?_
    intro b hb hb_ne
    have hbA : b ∈ A := hBA hb
    have hA_le_Cb : A ≤ Subgroup.centralizer ({b} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      rintro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨b, hbA⟩ ⟨a, ha⟩)
    refine le_opiCoreInG_centralizer_of_mem_centralizer_sylow hG hp2 P hAP hAnormP hCPA hb_ne
      (hZP_cent b (hB_le_ZP hb)) inf_le_right ?_ ?_
    · -- `A ≤ N_G(Y ⊓ C_G(b))`: `A` normalizes both `Y` and `C_G(b)` (since `A ≤ C_G(b)`).
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hAY ha) x,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hA_le_Cb ha)) x]
    · -- `Y ⊓ C_G(b)` is a `p'`-subgroup (its order divides `|Y|`).
      intro q hq
      exact hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hq)

/-- **BG Proposition 7.5, case (2)** (SCN₂ branch, mmd L2263-2309): if `A ∈ SCN₂(P)` for a Sylow
`p`-subgroup `P`, then `A` satisfies Hypothesis 7.1. Separated from the `p`-length-one branch
(`hypothesis71_of_scn2_or_pLengthOne` case 1, which awaits Theorem 6.7) so that the Thompson
Transitivity Theorem (7.6) depends only on this `sorry`-free statement. -/
theorem hypothesis71_of_scn2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G))) :
    Hypothesis71 A := by
  -- `A ≠ ⊥`: `pRank (A.subgroupOf P) ≥ 2` forces an elementary abelian subgroup of order `≥ p²`.
  have hAne : A ≠ ⊥ := by
    intro hAbot
    obtain ⟨B, _, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (p := p) (by norm_num) hAscn2.le_pRank
    have hp2 : p ^ 2 ≤ Nat.card ↥B := Nat.pow_le_of_le_log Nat.card_pos.ne' hBlog
    have hBdvd : Nat.card ↥B ∣ Nat.card ↥(A.subgroupOf (P : Subgroup G)) :=
      Subgroup.card_subgroup_dvd_card B
    have hcard1 : Nat.card ↥(A.subgroupOf (P : Subgroup G)) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAbot, Subgroup.card_bot]
    rw [hcard1, Nat.dvd_one] at hBdvd
    rw [hBdvd] at hp2
    nlinarith [hp2, (Fact.out : p.Prime).two_le]
  -- `A < ⊤`: `A ≤ P` and a Sylow `p`-subgroup of a (non-solvable) minimal simple group is proper.
  have hAproper : A < ⊤ := by
    have hP_lt : (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hPtop
      have hGp : IsPGroup p G :=
        (hPtop ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      haveI : Group.IsNilpotent G := hGp.isNilpotent
      exact hG.notSolvable inferInstance
    exact lt_of_le_of_lt hAP hP_lt
  refine ⟨hAne, hAproper, ?_⟩
  intro X hAX hXlt
  refine generated_eq_of_forall_le_opiCoreInG hAX ?_
  intro Y hY
  rw [mem_hInvariant] at hY
  exact coreClaim_scn2 hG hAab hAp hAP hAscn2 hAX hXlt hY.1 hY.2.1 hY.2.2

/-- **BG Proposition 7.5** (mmd L2252): `p ∈ π(G)`, `A` abelian `p`-部分群で、
(1) `A = {x ∈ C_G(A) : x^p = 1}` かつ `G` の全真部分群が `p`-length one、または
(2) ある Sylow `p`-部分群 `P` で `A ∈ SCN₂(P)`、
のいずれかなら `A` は Hypothesis 7.1 を満たす。case (1) は `A = Ω₁(C_G(A))` から `A` が `↥X` 内で
包含極大 elementary abelian になることを使い Theorem 6.7 を適用; case (2) は `hypothesis71_of_scn2`
へ委譲。 -/
theorem hypothesis71_of_scn2_or_pLengthOne [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (A : Subgroup G) (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        (∀ M : Subgroup G, M < ⊤ → Ch1.hasPLengthOne p M)) ∨
      (∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
        IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))) :
    Hypothesis71 A := by
  rcases hcase with hcase1 | hcase2
  · -- **case (1)**: `A = Ω₁(C_G(A))` and every proper subgroup is `p`-length one. Each
    -- `Y ∈ ℋ_X(A;p')` lands in `O_{p'}(X)` by **Theorem 6.7** (applied inside `↥X`), using that
    -- `A = {x ∈ C_G(A) : x^p = 1}` makes `A` maximal-by-inclusion elementary abelian in `↥X`.
    classical
    obtain ⟨hAeq, hplM⟩ := hcase1
    -- `x ∈ A ↔ x ∈ C_G(A) ∧ x^p = 1` (membership unfolding of `hAeq`).
    have hAmem : ∀ x : G, x ∈ A ↔
        (x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1) := fun x => by
      simpa using Set.ext_iff.mp hAeq x
    -- `p` is odd (it divides `|G|`, which is odd).
    have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_mem
    have hp_odd : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hp_odd_prop; omega
    -- `A` is elementary abelian: abelian (`hAab`) of exponent `p` (`hAmem`).
    have hAelem : A.IsElementaryAbelian p := by
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · exact isMulCommutative_iff.mp hAab x y
      · exact Subtype.ext (by
          rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
          exact ((hAmem (x : G)).mp x.2).2)
    -- `A` is maximal-by-inclusion elementary abelian in `G`: any elementary abelian `F ⊇ A`
    -- collapses to `A`, since every `f ∈ F` is `p`-torsion and (being in the abelian `F ⊇ A`)
    -- centralizes `A`, hence lies in `A` by `hAmem`.
    have hAmax : OddOrder.GroupTheory.IsMaximalElementaryAbelian p A := by
      refine ⟨hAelem, fun F hF hAF => le_antisymm ?_ hAF⟩
      intro f hf
      refine (hAmem f).mpr ⟨?_, ?_⟩
      · -- `f ∈ C_G(A)`: `f` and any `a ∈ A` both lie in the abelian `F`.
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have := hF.1 ⟨a, hAF ha⟩ ⟨f, hf⟩
        exact congrArg Subtype.val this
      · -- `f ^ p = 1`: `F` has exponent `p`.
        have := hF.2 ⟨f, hf⟩
        have := congrArg Subtype.val this
        rwa [SubmonoidClass.coe_pow, Subgroup.coe_one] at this
    -- `A ≠ ⊥`: otherwise `C_G(A) = ⊤`, so a Cauchy element of order `p` would satisfy `hAmem`
    -- and land in `A = ⊥`, forcing it to be trivial.
    have hAne : A ≠ ⊥ := by
      intro hAbot
      have hCtop : Subgroup.centralizer (A : Set G) = ⊤ := by
        rw [Subgroup.centralizer_eq_top_iff_subset, hAbot]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
        rw [hx]
        exact Subgroup.one_mem _
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hp_mem
      rw [orderOf_eq_prime_iff] at hg
      have hgA : g ∈ A := (hAmem g).mpr ⟨hCtop ▸ Subgroup.mem_top g, hg.1⟩
      rw [hAbot, Subgroup.mem_bot] at hgA
      exact hg.2 hgA
    -- `A < ⊤`: otherwise `G` is a `p`-group, hence nilpotent and solvable, contradicting `hG`.
    have hAproper : A < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hAtop
      have hGp : IsPGroup p G :=
        (hAtop ▸ hAp : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      haveI : Group.IsNilpotent G := hGp.isNilpotent
      exact hG.notSolvable inferInstance
    refine ⟨hAne, hAproper, ?_⟩
    intro X hAX hXlt
    have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hAne
    refine generated_eq_of_forall_le_opiCoreInG hAX ?_
    intro Y hY
    obtain ⟨hYX, hAnormY, hYpi⟩ := mem_hInvariant.mp hY
    haveI hXsolv : IsSolvable ↥X := hG.solvable_of_lt_top X hXlt
    -- **Translate to `↥X`** and apply Theorem 6.7 with `E := A.subgroupOf X`,
    -- `L := Y.subgroupOf X`. `A.subgroupOf X` is maximal-by-inclusion elementary abelian
    -- in `↥X` (lift of `hAmax`).
    have hEXmax :
        OddOrder.GroupTheory.IsMaximalElementaryAbelian p (A.subgroupOf X) := by
      refine ⟨?_, fun Fbar hFbar hsub => ?_⟩
      · -- elementary abelian, transported along `A.subgroupOf X ≃* A`.
        exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hAX).symm hAelem
      · -- maximality: push `Fbar` down to `F := Fbar.map X.subtype ≤ G`, which is elementary
        -- abelian and contains `A`; by `hAmax`, `F = A`, so `Fbar = A.subgroupOf X`.
        set F : Subgroup G := Fbar.map X.subtype with hFdef
        have hF_elem : F.IsElementaryAbelian p := hFbar.map X.subtype_injective
        have hAF : A ≤ F := by
          have hmap : (A.subgroupOf X).map X.subtype ≤ Fbar.map X.subtype :=
            Subgroup.map_mono hsub
          rwa [Subgroup.map_subgroupOf_eq_of_le hAX] at hmap
        have hFA : F = A := hAmax.2 F hF_elem hAF
        -- `Fbar = (Fbar.map X.subtype).comap X.subtype = A.comap X.subtype = A.subgroupOf X`.
        calc Fbar = (Fbar.map X.subtype).comap X.subtype :=
              (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Fbar).symm
          _ = A.comap X.subtype := by rw [← hFdef, hFA]
          _ = A.subgroupOf X := rfl
    -- `Y.subgroupOf X` is a `p'`-group (its order equals `|Y|`, a `p'`-number).
    have hLp' : ¬ p ∣ Nat.card (Y.subgroupOf X) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv]
      intro hdvd
      have hpmem : p ∈ (Nat.card ↥Y).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
      have : p ∈ (primesOf A)ᶜ := hYpi p hpmem
      rw [hπ] at this
      exact this rfl
    -- `A.subgroupOf X` normalizes `Y.subgroupOf X` (lift of `hAnormY`).
    have hELY : A.subgroupOf X ≤ Subgroup.normalizer (Y.subgroupOf X) := by
      intro a ha
      rw [Subgroup.mem_subgroupOf] at ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hcoe : ((a * y * a⁻¹ : ↥X) : G) = (a : G) * (y : G) * (a : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      exact Subgroup.mem_normalizer_iff.mp (hAnormY ha) (y : G)
    have hpl1X : OddOrder.BG.Ch1.hasPLengthOne p ↥X := hplM X hXlt
    have key := OddOrder.BG.Ch1.S06.le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian
      (G := ↥X) hp_odd hEXmax hLp' hELY hpl1X
    -- `key : Y.subgroupOf X ≤ O_{p'}(↥X)`. Map back to `G` and rewrite `(primesOf A)ᶜ = {q ∉ {p}}`.
    have hYeq : Y = (Y.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hYX).symm
    have hcompl : (primesOf A)ᶜ = {q | q ∉ ({p} : Set ℕ)} := by rw [hπ]; rfl
    rw [hcompl, opiCoreInG, hYeq]
    exact Subgroup.map_mono key
  · -- **case (2)**: delegate to the `sorry`-free SCN₂ branch.
    obtain ⟨P, hAP, hAscn2⟩ := hcase2
    exact hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2

/-! ## Theorem 7.6 — Thompson Transitivity Theorem -/

/-- **BG Theorem 7.6** (Thompson Transitivity Theorem, mmd L2311): `p ∈ π(G)`,
`A ∈ SCN₃(p)`, `q ∈ p'` ⇒ `O_{p'}(C_G(A))` は `ℋ_G*(A;q)` 上推移的に作用する。
§8–§16 で最頻出。証明は Prop 7.5(2) + Thm 7.2。 -/
theorem thompsonTransitivity [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    {A : Subgroup G} (hA : A ∈ scn3Global p G) {q : ℕ} [Fact q.Prime] (hq : q ≠ p) :
    ConjTransitiveOn (opiCoreInG {p}ᶜ (Subgroup.centralizer (A : Set G)))
      (hInvariantStar ⊤ A {q}) := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  have hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) := IsSCN_n.mono (by norm_num) hAscn3
  haveI hAab : IsMulCommutative A := (scn_ambient hAP hAscn2.isSCN).1
  have hAp : IsPGroup p ↥A := (P.isPGroup').to_le hAP
  -- `A` satisfies Hypothesis 7.1 (Proposition 7.5, SCN₂ branch).
  have hHyp : Hypothesis71 A := hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2
  -- `π(A) = {p}`, so `q ∈ (π A)ᶜ` and `kSubgroup A = O_{p'}(C_G(A))`.
  have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hHyp.ne_bot
  have hq' : q ∈ (primesOf A)ᶜ := by rw [hπ]; simpa using hq
  -- `3 ≤ rank ↥(Z(A))`: `A` is abelian, so `Z(A) = ⊤`, and `pRank (A.subgroupOf P) ≥ 3`.
  have hrank : 3 ≤ rank ↥(Subgroup.center ↥A) := by
    have h3 : (3 : ℕ) ≤ pRank ↥A p :=
      le_trans hAscn3.le_pRank
        (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hAP).injective)
    have hcenter : Subgroup.center (↥A) = ⊤ := by
      rw [Subgroup.center_eq_top_iff]; exact hAab
    rw [hcenter]
    exact le_trans (le_trans h3 (pRank_le_rank p))
      (rank_le_of_injective (f := (Subgroup.topEquiv (G := ↥A)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥A)).symm.injective)
  -- Theorem 7.2, then rewrite `kSubgroup A = O_{p'}(C_G(A))`.
  have htrans := transitive_of_three_le_rank_center hG hHyp hq' hrank
  rw [← hπ]
  exact htrans

end OddOrder.BG.Ch2.S07
