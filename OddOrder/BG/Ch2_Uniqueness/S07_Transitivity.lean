/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
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

## proof は後続

全 6 結果は faithful statement + `sorry`。proof は Prop 1.16 (coprime action generation, §1),
Lem 6.5/6.6 (§6), Thm 6.7, SCN/p-stability に依存 (foundation-first scaffold)。

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

/-- `opiCoreInG π H` is a `π`-subgroup (ambient form of `oPiCore.isPiGroup`). -/
theorem isPiSubgroup_opiCoreInG [Finite G] (π : Set ℕ) (H : Subgroup G) :
    Subgroup.IsPiSubgroup π (opiCoreInG π H) := by
  intro r hr
  rw [card_opiCoreInG] at hr
  exact Ch03.oPiCore.isPiGroup π r hr

/-- `K = O_{π'}(C_G(A)) ≤ C_G(A)`. -/
theorem kSubgroup_le_centralizer (A : Subgroup G) :
    kSubgroup A ≤ Subgroup.centralizer (A : Set G) :=
  opiCoreInG_le _ _

/-- `K` is a `π'`-subgroup of `G`. -/
theorem isPiSubgroup_kSubgroup [Finite G] (A : Subgroup G) :
    Subgroup.IsPiSubgroup (primesOf A)ᶜ (kSubgroup A) :=
  isPiSubgroup_opiCoreInG _ _

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
  have hWC_pi : Ch03.Subgroup.IsPiGroup π' (W.subgroupOf C) := by
    intro r hr
    refine hW_pi' r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_C).toEquiv] at hr
  have hW_le_K : W ≤ kSubgroup A := by
    have h1 : W.subgroupOf C ≤ Ch03.oPiCore π' ↥C :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore hWC_pi
    calc W = (W.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hW_le_C).symm
      _ ≤ (Ch03.oPiCore π' ↥C).map C.subtype := Subgroup.map_mono h1
      _ = kSubgroup A := rfl
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

/-- **BG Theorem 7.2** (mmd L2177): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 3` ⇒ `K` は
`ℋ_G*(A;q)` 上推移的。Prop 1.16 で `Q₁ = ⟨C_{Q₁}(C)⟩` に分解し Lem 7.1 を適用。 -/
theorem transitive_of_three_le_rank_center [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  sorry

/-- **BG Theorem 7.3** (mmd L2187): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 2` かつ
`q ∈ π(C_G(A))` ⇒ `K` は `ℋ_G*(A;q)` 上推移的。`R ⊇ Sylow_q(C_G(A))` 経由で Lem 7.1 を連鎖。 -/
theorem transitive_of_two_le_rank_center_of_dvd [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 2 ≤ rank ↥(Subgroup.center ↥A))
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  sorry

/-! ## Theorem 7.4 — 推移性の伝播 -/

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
  sorry

/-! ## Proposition 7.5 — Hypothesis 7.1 の十分条件 -/

/-- **BG Proposition 7.5** (mmd L2252): `p ∈ π(G)`, `A` abelian `p`-部分群で、
(1) `A = {x ∈ C_G(A) : x^p = 1}` かつ `G` の全真部分群が `p`-length one、または
(2) ある Sylow `p`-部分群 `P` で `A ∈ SCN₂(P)`、
のいずれかなら `A` は Hypothesis 7.1 を満たす。 -/
theorem hypothesis71_of_scn2_or_pLengthOne [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (A : Subgroup G) (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        (∀ M : Subgroup G, M < ⊤ → Ch1.hasPLengthOne p M)) ∨
      (∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
        IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))) :
    Hypothesis71 A := by
  sorry

/-! ## Theorem 7.6 — Thompson Transitivity Theorem -/

/-- **BG Theorem 7.6** (Thompson Transitivity Theorem, mmd L2311): `p ∈ π(G)`,
`A ∈ SCN₃(p)`, `q ∈ p'` ⇒ `O_{p'}(C_G(A))` は `ℋ_G*(A;q)` 上推移的に作用する。
§8–§16 で最頻出。証明は Prop 7.5(2) + Thm 7.2。 -/
theorem thompsonTransitivity [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    {A : Subgroup G} (hA : A ∈ scn3Global p G) {q : ℕ} [Fact q.Prime] (hq : q ≠ p) :
    ConjTransitiveOn (opiCoreInG {p}ᶜ (Subgroup.centralizer (A : Set G)))
      (hInvariantStar ⊤ A {q}) := by
  sorry

end OddOrder.BG.Ch2.S07
