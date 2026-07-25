/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch01_Sylow.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Isaacs Chapter 1 — Problems §1D (Frobenius complements, Frattini, nilpotency)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1 "Sylow Theory" の章末演習 §1D
(pp. 19-28)。Frobenius complement (自明交叉条件)・Frattini 部分群 (非生成元)・冪零性判定を扱う。

§1A–§1C (`Problems.lean`) から分割 (2026-07-23、1682 行→分割、hub 1500 flag)。§1A–§1C の helper
(`exists_sylow_inf_card_eq`, `card_mul_card_inf` 等) は `Problems.lean` の import 経由で利用。
方針は `Problems.lean` 冒頭と同じ (ラッパー方針)。
-/

namespace OddOrder.Isaacs.Ch01

section /- Problems 1D: Frobenius complements, Frattini, nilpotency (pp. 19-28) -/

/-- **Isaacs Problem 1D.1**. `P` を `H ⊴ G` の Sylow `p`-部分群とし、`N_G(P) ⊆ H` とする。
このとき `p ∤ |G : H|`。

Frattini 論法 (`Sylow.normalizer_sup_eq_top`) で `N_G(P) ⊔ H = ⊤`。仮定 `N_G(P) ≤ H` から
`N_G(P) ⊔ H = H`、ゆえ `H = ⊤`、`|G : H| = 1` で `p ∤ 1`。 -/
theorem not_dvd_index_of_sylow_normalizer_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (P : Sylow p ↥H)
    (hle : Subgroup.normalizer (P.map H.subtype) ≤ H) : ¬ p ∣ H.index := by
  have hfrat : Subgroup.normalizer (P.map H.subtype) ⊔ H = ⊤ := Sylow.normalizer_sup_eq_top P
  have hHtop : H = ⊤ := top_le_iff.mp (hfrat ▸ sup_le hle le_rfl)
  rw [hHtop, Subgroup.index_top]
  exact fun h => absurd (Nat.dvd_one.mp h) (Fact.out : p.Prime).ne_one

/-- **Isaacs Problem 1D.6**. 冪零群 `G` の部分群 `H` が極大 (coatom) であることと、指数 `|G : H|`
が素数であることは同値。

`⟹`: 冪零群は正規化条件をみたす (`normalizerCondition_of_isNilpotent`) ので極大部分群は正規
(`NormalizerCondition.normal_of_coatom`)。対応定理で `G ⧸ H` は単純群、単純かつ冪零ゆえ可換
(mathlib instance)、可換単純群は素数位数 (`IsSimpleGroup.prime_card`)、`|G:H| = |G ⧸ H|`。
`⟸`: 素数指数なら `H ≠ ⊤`、また `H < K` のとき `K.index ∣ H.index` (`index_dvd_of_le`) が素数ゆえ
`K.index = 1` (`K = ⊤`) しかない。 -/
theorem isCoatom_iff_index_prime {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : IsCoatom H ↔ (H.index).Prime := by
  refine ⟨fun hco => ?_, fun hp => ?_⟩
  · -- 極大 ⟹ 素数指数
    haveI hN : H.Normal :=
      Subgroup.normalizer_eq_top_iff.mp
        (hco.2 _ (Group.normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hco.1)))
    haveI hnt : Nontrivial (G ⧸ H) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [← Subgroup.index_eq_card]
      have h1 : H.index ≠ 1 := fun h => hco.1 (Subgroup.index_eq_one.mp h)
      have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    haveI hsimple : IsSimpleGroup (G ⧸ H) := by
      refine ⟨fun N _ => ?_⟩
      have hle : H ≤ N.comap (QuotientGroup.mk' H) := by
        have h := Subgroup.ker_le_comap (QuotientGroup.mk' H) N
        rwa [QuotientGroup.ker_mk'] at h
      have hinj : Function.Injective (Subgroup.comap (QuotientGroup.mk' H)) :=
        Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
      rcases hle.lt_or_eq with hlt | heq
      · right
        apply hinj
        rw [Subgroup.comap_top]
        exact hco.2 _ hlt
      · left
        apply hinj
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
        exact heq.symm
    rw [Subgroup.index_eq_card]
    exact IsSimpleGroup.prime_card
  · -- 素数指数 ⟹ 極大
    refine ⟨fun htop => ?_, fun K hHK => ?_⟩
    · rw [htop, Subgroup.index_top] at hp; exact hp.ne_one rfl
    · by_contra hKtop
      have h1 : K.index ∣ H.index := Subgroup.index_dvd_of_le hHK.le
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp K.index h1) with h | h
      · exact hKtop (Subgroup.index_eq_one.mp h)
      · -- K.index = H.index, H ≤ K, 有限 ⟹ H = K, `H < K` に矛盾
        have key : Nat.card K * H.index = Nat.card H * H.index := by
          conv_lhs => rw [← h, Subgroup.card_mul_index K]
          rw [Subgroup.card_mul_index H]
        have hcard : Nat.card K = Nat.card H := Nat.eq_of_mul_eq_mul_right hp.pos key
        exact hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le hcard.le)

/-- **Isaacs Problem 1D.13**. `Z ≤ Z(G)` かつ `G ⧸ Z` が冪零ならば `G` は冪零。

mathlib の `Group.isNilpotent_of_ker_le_center` (核が中心に含まれる準同型で冪零性が降りる) を
商写像 `mk' Z` (核 `= Z ≤ Z(G)`) に適用した特殊化。 -/
theorem isNilpotent_of_center_le {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hq : Group.IsNilpotent (G ⧸ Z)) : Group.IsNilpotent G :=
  haveI := hq
  Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z)
    (by rw [QuotientGroup.ker_mk']; exact hZ)

/-
**Problem 1D.14** (Frattini 部分群 `Φ(G)` は冪零): mathlib の `frattini_nilpotent`
(`[Finite G]` で `Group.IsNilpotent (frattini G)`) がまさにこれ。`frattini G` は
`Order.radical (Subgroup G)` = 全極大部分群の交わり = Isaacs の `Φ(G)`。純粋対応ゆえ
ラッパーは書かない (ラッパー方針)。

**Problem 1D.7** (`Φ(G)` = 非生成元全体): mathlib の `frattini_nongenerating` が subgroup 形
(`K ⊔ frattini G = ⊤ → K = ⊤`)。Isaacs の元/部分集合形は下記 `mem_frattini_iff_forall_closure`。
-/

/-- **Isaacs Problem 1D.7**. `g ∈ Φ(G)` であることと、`g` が「非生成元」であること
(任意の `X ⊆ G` について `⟨X ∪ {g}⟩ = G` ならば `⟨X⟩ = G`) は同値。

`⟹`: `g ∈ Φ(G)` なら `⟨{g}⟩ ≤ Φ(G)`、`⊤ = ⟨X∪{g}⟩ = ⟨{g}⟩ ⊔ ⟨X⟩ ≤ Φ(G) ⊔ ⟨X⟩` から
`⟨X⟩ ⊔ Φ(G) = ⊤`、`frattini_nongenerating` で `⟨X⟩ = ⊤`。
`⟸`: 対偶。`g ∉ Φ(G) = ⨅ 極大部分群` なら `g ∉ M` なる極大 `M` があり、`X = M` で
`⟨M ∪ {g}⟩ = ⟨{g}⟩ ⊔ M = ⊤` (M 極大, `g∉M`) だが `⟨M⟩ = M ≠ ⊤`、非生成元性に反する。 -/
theorem mem_frattini_iff_forall_closure {G : Type*} [Group G] [Finite G] {g : G} :
    g ∈ frattini G ↔
    ∀ X : Set G, Subgroup.closure (insert g X) = ⊤ → Subgroup.closure X = ⊤ := by
  constructor
  · intro hg X hX
    apply frattini_nongenerating
    have h2 : Subgroup.closure {g} ≤ frattini G := by
      intro x hx
      rw [Subgroup.mem_closure_singleton] at hx
      obtain ⟨n, rfl⟩ := hx
      exact (frattini G).zpow_mem hg n
    rw [← top_le_iff]
    calc (⊤ : Subgroup G) = Subgroup.closure (insert g X) := hX.symm
      _ = Subgroup.closure {g} ⊔ Subgroup.closure X := by
          rw [Set.insert_eq, Subgroup.closure_union]
      _ ≤ frattini G ⊔ Subgroup.closure X := sup_le_sup_right h2 _
      _ = Subgroup.closure X ⊔ frattini G := sup_comm _ _
  · intro h
    by_contra hg
    have hex : ∃ M : Subgroup G, IsCoatom M ∧ g ∉ M := by
      by_contra hall
      apply hg
      rw [frattini, Order.radical]
      simp only [Subgroup.mem_iInf, Set.mem_setOf_eq]
      intro M hM
      by_contra hgM
      exact hall ⟨M, hM, hgM⟩
    obtain ⟨M, hMco, hgM⟩ := hex
    have hlt : M < Subgroup.closure {g} ⊔ M := by
      refine lt_of_le_of_ne le_sup_right (fun heq => hgM ?_)
      have hgc : g ∈ Subgroup.closure {g} ⊔ M :=
        Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_singleton g))
      rwa [← heq] at hgc
    have hclosure : Subgroup.closure (insert g (↑M : Set G)) = ⊤ := by
      rw [Set.insert_eq, Subgroup.closure_union, Subgroup.closure_eq]
      exact hMco.2 _ hlt
    exact hMco.1 (Subgroup.closure_eq M ▸ h (↑M) hclosure)

open MulAction in
/-- **Isaacs Problem 1D.2**. 素数 `p` を固定し、部分群 `H ≤ G` が「位数 `p` の任意の元 `x ∈ H` に
ついて `C_G(x) ⊆ H`」をみたすとする。このとき `p` は `|H|` と `|G : H|` を同時には割らない。

背理法。`p ∣ |H|` かつ `p ∣ |G:H|` とすると、`Q ∈ Syl_p(G)` に対し `P := Q ∩ H` は `H` の Sylow で
`|P| = pPart(H) < pPart(G) = |Q|` ゆえ `P < Q`。`Q` は p-群 (冪零) で正規化条件をみたすので
`P.subgroupOf Q < N(P.subgroupOf Q) = (N_G(P)).subgroupOf Q` (`subgroupOf_normalizer_eq`)、よって
`g ∈ N_G(P) ∩ Q`, `g ∉ P` が取れる。`⟨g⟩` を `P` に共役作用させると固定点 (= `C_P(g)`) は非自明
(p-群作用、`exists_fixed_point_of_prime_dvd_card_of_fixed_point`)、その非単位固定点の適当な冪 `x` は
位数 `p` で `g` と可換、`x ∈ P ⊆ H` ゆえ `g ∈ C_G(x) ⊆ H`、`g ∈ Q ∩ H = P` で `g ∉ P` に矛盾。 -/
theorem not_dvd_card_and_index_of_centralizer_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G}
    (hC : ∀ x : G, x ∈ H → orderOf x = p → Subgroup.centralizer {x} ≤ H) :
    ¬ (p ∣ Nat.card H ∧ p ∣ H.index) := by
  rintro ⟨hpH, hpI⟩
  obtain ⟨Q, hPcard⟩ := exists_sylow_inf_card_eq (p := p) H
  set P : Subgroup G := (Q : Subgroup G) ⊓ H with hPdef
  have hPQ : P ≤ (Q : Subgroup G) := inf_le_left
  have hPH : P ≤ H := inf_le_right
  -- p ∣ |P|、P 非自明
  have hpP : p ∣ Nat.card ↥P := by
    rw [hPcard]
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos).ne' hpH).ne'
  haveI : Nontrivial ↥P :=
    Finite.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hpP))
  -- |P| < |Q|
  have hlt : Nat.card ↥P < Nat.card ↥(Q : Subgroup G) := by
    rw [hPcard, Q.card_eq_multiplicity]
    have hfac : (Nat.card H).factorization p + (H.index).factorization p
        = (Nat.card G).factorization p := by
      rw [← Finsupp.add_apply, ← Nat.factorization_mul (Nat.card_pos).ne'
        Subgroup.index_ne_zero_of_finite, Subgroup.card_mul_index]
    have hpos : 0 < (H.index).factorization p :=
      Nat.Prime.factorization_pos_of_dvd Fact.out Subgroup.index_ne_zero_of_finite hpI
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have hPltQ : P < (Q : Subgroup G) :=
    lt_of_le_of_ne hPQ (fun h => hlt.ne (by rw [h]))
  -- g ∈ N_G(P) ∩ Q, g ∉ P
  haveI : Group.IsNilpotent ↥(Q : Subgroup G) := Q.isPGroup'.isNilpotent
  have hlt2 : P.subgroupOf (Q : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hPltQ.ne (le_antisymm hPQ h)
  have hnorm := Group.normalizerCondition_of_isNilpotent _ hlt2
  rw [← Subgroup.subgroupOf_normalizer_eq hPQ] at hnorm
  obtain ⟨g0, hg0mem, hg0notin⟩ := SetLike.exists_of_lt hnorm
  set g : G := (g0 : G) with hgdef
  have hgN : g ∈ Subgroup.normalizer P := Subgroup.mem_subgroupOf.mp hg0mem
  have hgQ : g ∈ (Q : Subgroup G) := g0.2
  have hgnotP : g ∉ P := fun h => hg0notin (Subgroup.mem_subgroupOf.mpr h)
  -- ⟨g⟩ の P への共役作用
  have hzpN : Subgroup.zpowers g ≤ Subgroup.normalizer P := Subgroup.zpowers_le.mpr hgN
  have hzpg : IsPGroup p ↥(Subgroup.zpowers g) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp
      (hn ▸ Subgroup.orderOf_dvd_natCard (Q : Subgroup G) hgQ)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  letI : MulAction ↥(Subgroup.zpowers g) ↥P :=
    { smul := fun k y => ⟨(k : G) * (y : G) * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hzpN k.2) (y : G)).mp y.2⟩
      one_smul := fun y => by
        apply Subtype.ext
        change ((1 : ↥(Subgroup.zpowers g)) : G) * (y : G) * ((1 : ↥(Subgroup.zpowers g)) : G)⁻¹
          = (y : G)
        simp
      mul_smul := fun k₁ k₂ y => by
        apply Subtype.ext
        change ((k₁ * k₂ : ↥(Subgroup.zpowers g)) : G) * (y : G)
            * ((k₁ * k₂ : ↥(Subgroup.zpowers g)) : G)⁻¹
          = (k₁ : G) * ((k₂ : G) * (y : G) * (k₂ : G)⁻¹) * (k₁ : G)⁻¹
        simp only [Subgroup.coe_mul]; group }
  have h1fix : (1 : ↥P) ∈ fixedPoints ↥(Subgroup.zpowers g) ↥P := by
    rw [mem_fixedPoints]
    intro k
    apply Subtype.ext
    change (k : G) * ((1 : ↥P) : G) * (k : G)⁻¹ = ((1 : ↥P) : G)
    simp
  obtain ⟨b, hbfix, hbne⟩ :=
    hzpg.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥P hpP h1fix
  -- b ≠ 1, g と可換
  have hbcomm : g * (b : G) = (b : G) * g := by
    have := congrArg Subtype.val (hbfix ⟨g, Subgroup.mem_zpowers g⟩)
    -- (⟨g,_⟩ • b).1 = b.1 : g * b * g⁻¹ = b
    have hgbg : g * (b : G) * g⁻¹ = (b : G) := this
    rw [mul_inv_eq_iff_eq_mul] at hgbg
    exact hgbg
  have hbP : (b : G) ∈ (Q : Subgroup G) := hPQ b.2
  obtain ⟨k, hk⟩ : ∃ k, orderOf (b : G) = p ^ k := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp
      (hn ▸ Subgroup.orderOf_dvd_natCard (Q : Subgroup G) hbP)
    exact ⟨k, hk⟩
  have hbne1 : (b : G) ≠ 1 := fun h => hbne (Subtype.ext h.symm)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, h, pow_zero])) hbne1
    · exact h
  -- x := b^(p^(k-1)) は位数 p
  set x : G := (b : G) ^ (p ^ (k - 1)) with hxdef
  have hxord : orderOf x = p := by
    rw [hxdef, orderOf_pow, hk, Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le k 1)),
      Nat.pow_div (Nat.sub_le k 1) (Fact.out : p.Prime).pos,
      show k - (k - 1) = 1 from by omega, pow_one]
  have hxP : x ∈ P := by rw [hxdef]; exact Subgroup.pow_mem P b.2 _
  -- g ∈ C_G(x) ⊆ H、しかし g ∈ Q ∩ H = P で g ∉ P に矛盾
  have hgx : g ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (((show Commute g (b : G) from hbcomm).pow_right (p ^ (k - 1))).symm).eq
  have hgH : g ∈ H := hC x (hPH hxP) hxord hgx
  exact hgnotP (Subgroup.mem_inf.mpr ⟨hgQ, hgH⟩)

open Pointwise in
/-- **Isaacs Problem 1D.3(a)**. `H ≤ G` が `H ⊓ H^g = 1` (すべての `g ∉ H`) をみたす (Frobenius
complement) とき、`1 < K ≤ H` なる任意の部分群 `K` について `N_G(K) ⊆ H`。

`n ∈ N_G(K)`, `n ∉ H` とすると `K = n·K·n⁻¹ ≤ n·H·n⁻¹ = H^{n}` かつ `K ≤ H` ゆえ
`K ≤ H ⊓ H^n = 1`、`K > 1` に矛盾。 -/
theorem normalizer_le_of_disjoint_conj {G : Type*} [Group G] {H : Subgroup G}
    (hH : ∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥)
    {K : Subgroup G} (hK1 : K ≠ ⊥) (hKH : K ≤ H) : Subgroup.normalizer K ≤ H := by
  intro n hn
  by_contra hnH
  refine hK1 (le_bot_iff.mp ?_)
  rw [← hH n hnH]
  refine le_inf hKH ?_
  have hnorm : MulAut.conj n • K = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  calc K = MulAut.conj n • K := hnorm.symm
    _ ≤ MulAut.conj n • H := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKH

open Pointwise in
/-- **Isaacs Problem 1D.3(b)**. `H ≤ G` が `H ⊓ H^g = 1` (すべての `g ∉ H`) をみたす (Frobenius
complement) とき、`H` は Hall 部分群 (`|H|` と `|G : H|` は互いに素)。

素数 `p ∣ gcd(|H|, |G:H|)` があると仮定。`Q ∈ Syl_p(G)`, `P := Q ∩ H` は `|P| = pPart(H) > 1`
(∴ `P ≠ ⊥`)、(a) より `N_G(P) ⊆ H`。もし `P < Q` なら正規化条件で `g ∈ N_G(P) ∩ Q`, `g ∉ P` が
取れるが `g ∈ N_G(P) ⊆ H` かつ `g ∈ Q` ゆえ `g ∈ Q ∩ H = P` で矛盾。ゆえ `P = Q`、
`pPart(H) = |P| = |Q| = pPart(G)`。しかし `p ∣ |G:H|` からは `pPart(H) < pPart(G)`、矛盾。 -/
theorem coprime_card_index_of_disjoint_conj {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : ∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥) :
    Nat.Coprime (Nat.card H) H.index := by
  by_contra hnc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnc
  have hpH : p ∣ Nat.card H := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpI : p ∣ H.index := hpg.trans (Nat.gcd_dvd_right _ _)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hPcard⟩ := exists_sylow_inf_card_eq (p := p) H
  set P : Subgroup G := (Q : Subgroup G) ⊓ H with hPdef
  have hpP : p ∣ Nat.card ↥P := by
    rw [hPcard]
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp (Nat.card_pos).ne' hpH).ne'
  have hP1 : P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hpP; exact hp.one_lt.ne' (Nat.dvd_one.mp hpP)
  have hNle : Subgroup.normalizer P ≤ H := normalizer_le_of_disjoint_conj hH hP1 inf_le_right
  -- P = ↑Q
  have hPQeq : P = (Q : Subgroup G) := by
    by_contra hne
    have hPltQ : P < (Q : Subgroup G) := lt_of_le_of_ne inf_le_left hne
    haveI : Group.IsNilpotent ↥(Q : Subgroup G) := Q.isPGroup'.isNilpotent
    have hlt2 : P.subgroupOf (Q : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hPltQ.ne (le_antisymm inf_le_left h)
    have hnorm := Group.normalizerCondition_of_isNilpotent _ hlt2
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_left] at hnorm
    obtain ⟨g0, hg0m, hg0n⟩ := SetLike.exists_of_lt hnorm
    exact hg0n (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨g0.2, hNle (Subgroup.mem_subgroupOf.mp hg0m)⟩))
  -- pPart(H) = |P| = |Q| = pPart(G), しかし p ∣ index で pPart(H) < pPart(G)
  have heq : p ^ (Nat.card H).factorization p = p ^ (Nat.card G).factorization p := by
    rw [← hPcard, hPQeq, Q.card_eq_multiplicity]
  have hfac : (Nat.card H).factorization p + (H.index).factorization p
      = (Nat.card G).factorization p := by
    rw [← Finsupp.add_apply, ← Nat.factorization_mul (Nat.card_pos).ne'
      Subgroup.index_ne_zero_of_finite, Subgroup.card_mul_index]
  have hpos : 0 < (H.index).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp Subgroup.index_ne_zero_of_finite hpI
  have := Nat.pow_right_injective hp.two_le heq
  omega

open Pointwise in
/-- **Isaacs Problem 1D.4**. `G = NH` で `1 < N ⊴ G`, `N ∩ H = 1` とする。`H` が Frobenius
complement (`H ⊓ H^g = 1` すべての `g ∉ H`) であることと、すべての非単位 `h ∈ H` について
`C_N(h) = 1` であることは同値。

`⟹`: `n ∈ C_N(h)`, `n ≠ 1` があれば `n ∉ H` (`N∩H=1`) かつ `h = n·h·n⁻¹ ∈ H^n` (可換)、
`h ∈ H ⊓ H^n`, `h ≠ 1` で Frobenius に反する。
`⟸`: `g ∉ H` を `g = n·h'` 分解、`H^g = H^n` (`conj_smul_eq_self_of_mem`) で `n ∈ N`, `n ≠ 1` に帰着。
`x ∈ H ⊓ H^n`, `x ≠ 1` とすると `n⁻¹·x·n ∈ H` かつ `x ∈ H` ゆえ `x⁻¹·n⁻¹·x·n ∈ H`、また N 正規で
`∈ N`、`N∩H=1` から `= 1`、つまり `x` と `n` は可換で `n ∈ C_N(x) = 1`、`n ≠ 1` に矛盾。 -/
theorem frobenius_complement_iff_centralizer_eq_bot {G : Type*} [Group G] {N H : Subgroup G}
    [hN : N.Normal] (hNH : (N : Set G) * (H : Set G) = Set.univ) (hinf : N ⊓ H = ⊥) :
    (∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥) ↔
    (∀ h : G, h ∈ H → h ≠ 1 → Subgroup.centralizer {h} ⊓ N = ⊥) := by
  constructor
  · -- Frobenius ⟹ C_N(h) = 1
    intro hfrob h hhH hh1
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨hnc, hnN⟩ := Subgroup.mem_inf.mp hn
    rw [Subgroup.mem_bot]
    by_contra hn1
    have hnH : n ∉ H := fun hnH =>
      hn1 (Subgroup.mem_bot.mp (hinf ▸ Subgroup.mem_inf.mpr ⟨hnN, hnH⟩))
    have hcomm : n * h = h * n := (Subgroup.mem_centralizer_iff.mp hnc h rfl).symm
    have hhconj : h ∈ MulAut.conj n • H := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
        MulAut.conj_apply, inv_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hhH
    exact hh1 (Subgroup.mem_bot.mp (hfrob n hnH ▸ Subgroup.mem_inf.mpr ⟨hhH, hhconj⟩))
  · -- C_N(h) = 1 ⟹ Frobenius
    intro hcent g hg
    obtain ⟨n, hnN, h', hh'H, hgeq⟩ := Set.mem_mul.mp (hNH ▸ Set.mem_univ g)
    have hconjeq : MulAut.conj g • H = MulAut.conj n • H := by
      rw [← hgeq, map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem hh'H]
    rw [hconjeq]
    have hn1 : n ≠ 1 := by rintro rfl; rw [one_mul] at hgeq; exact hg (hgeq ▸ hh'H)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hinvH : n⁻¹ * x * n ∈ H := by
      have h0 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hxc
      rwa [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at h0
    have hcomm0 : x⁻¹ * n⁻¹ * x * n = 1 := by
      have hHm : x⁻¹ * n⁻¹ * x * n ∈ H := by
        have h5 : x⁻¹ * (n⁻¹ * x * n) ∈ H := H.mul_mem (H.inv_mem hxH) hinvH
        rwa [← mul_assoc, ← mul_assoc] at h5
      have hNm : x⁻¹ * n⁻¹ * x * n ∈ N :=
        N.mul_mem (by simpa using hN.conj_mem n⁻¹ (N.inv_mem hnN) x⁻¹) hnN
      have hmem : x⁻¹ * n⁻¹ * x * n ∈ N ⊓ H := Subgroup.mem_inf.mpr ⟨hNm, hHm⟩
      rw [hinf] at hmem; exact Subgroup.mem_bot.mp hmem
    have h2 : n⁻¹ * x * n = x := by
      have h3 : x * (x⁻¹ * n⁻¹ * x * n) = x * 1 := congrArg (x * ·) hcomm0
      rw [mul_one, show x * (x⁻¹ * n⁻¹ * x * n) = n⁻¹ * x * n by group] at h3
      exact h3
    have hxn : x * n = n * x := by
      have h4 : n * (n⁻¹ * x * n) = n * x := congrArg (n * ·) h2
      rwa [show n * (n⁻¹ * x * n) = x * n by group] at h4
    have hcn : n ∈ Subgroup.centralizer {x} := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact hxn
    exact hn1 (Subgroup.mem_bot.mp (hcent x hxH hx1 ▸ Subgroup.mem_inf.mpr ⟨hcn, hnN⟩))

/-- 特性部分群を正規部分群 `N` に沿って `G` へ押し出したものは `G` で正規。共役 `MulAut.conj g` を
`N` に制限した `MulAut.conjNormal g` の下で特性部分群は不変。 -/
theorem characteristic_map_subtype_normal {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (H : Subgroup ↥N) [H.Characteristic] : (H.map N.subtype).Normal := by
  constructor
  intro n hn g
  obtain ⟨h, hhH, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g h, ?_, MulAut.conjNormal_apply g h⟩
  rw [← Subgroup.characteristic_iff_map_eq.mp ‹H.Characteristic› (MulAut.conjNormal g)]
  exact Subgroup.mem_map_of_mem _ hhH

open Pointwise in
/-- **Isaacs Problem 1D.16**. `N ◁ G` ならば `Φ(N) ⊆ Φ(G)` (Frattini 部分群の単調性、`N` の
Frattini を `G` へ押し出したもの)。

各極大部分群 `M` について `Φ(N) ⊆ M` を示す。`Φ(N)` は `N` の特性部分群 (`frattini` characteristic)
かつ `N ◁ G` ゆえ `Φ(N) ◁ G`。`Φ(N) ⊄ M` なら `M` 極大で `M ⊔ Φ(N) = ⊤`、`Φ(N)` 正規ゆえ
`M ⊔ Φ(N) = M · Φ(N)` (`mul_normal`)。任意の `x ∈ N` は `x = m·φ` (`m∈M`, `φ∈Φ(N)`) と書け
`m = x·φ⁻¹ ∈ N` から `m ∈ N ⊓ M`、`x ∈ (N⊓M) ⊔ Φ(N)`。ゆえ `N ≤ (N⊓M) ⊔ Φ(N)`、`N` の部分群として
`(N⊓M) ⊔ Φ(N) = ⊤`、`frattini_nongenerating` で `N ⊓ M = N`、`N ⊆ M`、`Φ(N) ⊆ N ⊆ M` で矛盾。 -/
theorem frattini_map_subtype_le_frattini {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] : (frattini ↥N).map N.subtype ≤ frattini G := by
  set ΦN := (frattini ↥N).map N.subtype with hΦN
  haveI hΦnorm : ΦN.Normal := characteristic_map_subtype_normal (frattini ↥N)
  have hΦNle : ΦN ≤ N := Subgroup.map_subtype_le _
  have hround : ΦN.subgroupOf N = frattini ↥N :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N) _
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ?_
  simp only [Set.mem_setOf_eq] at hM
  by_contra hnle
  have htop : M ⊔ ΦN = ⊤ :=
    hM.2 _ (lt_of_le_of_ne le_sup_left (fun h => hnle (le_sup_right.trans_eq h.symm)))
  have hle : N ≤ (N ⊓ M) ⊔ ΦN := by
    intro x hxN
    have hxmul : x ∈ (M : Set G) * (ΦN : Set G) := by
      rw [← Subgroup.mul_normal M ΦN, htop]; exact Subgroup.mem_top x
    obtain ⟨m, hmM, φ, hφΦ, rfl⟩ := Set.mem_mul.mp hxmul
    have hmN : m ∈ N := by
      have he : m = m * φ * φ⁻¹ := by group
      rw [he]; exact N.mul_mem hxN (N.inv_mem (hΦNle hφΦ))
    exact ((N ⊓ M) ⊔ ΦN).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hmN, hmM⟩)) (Subgroup.mem_sup_right hφΦ)
  have hsup : (N ⊓ M).subgroupOf N ⊔ frattini ↥N = ⊤ := by
    rw [← hround, ← Subgroup.subgroupOf_sup inf_le_left hΦNle, Subgroup.subgroupOf_eq_top]
    exact hle
  have hNM : N ≤ N ⊓ M := Subgroup.subgroupOf_eq_top.mp (frattini_nongenerating hsup)
  exact hnle (hΦNle.trans (le_inf_iff.mp hNM).2)

/-- **Isaacs Problem 1D.8** (可換部分). 冪零有限群 `G` では `[G, G] ⊆ Φ(G)`、すなわち `G / Φ(G)` は
可換。各極大部分群 `M` は素数指数 (1D.6) ゆえ正規で `G ⧸ M` は素数位数、したがって巡回=可換なので
`[G, G] ⊆ M`、これが全極大部分群にわたるので `[G, G] ⊆ Φ(G)`。 -/
theorem commutator_le_frattini {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] :
    commutator G ≤ frattini G := by
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ?_
  simp only [Set.mem_setOf_eq] at hM
  haveI hMnorm : M.Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (hM.2 _ (Group.normalizerCondition_of_isNilpotent M (lt_top_iff_ne_top.mpr hM.1)))
  haveI : Fact (M.index).Prime := ⟨(isCoatom_iff_index_prime M).mp hM⟩
  haveI hcyc : IsCyclic (G ⧸ M) := isCyclic_of_prime_card (p := M.index)
    (Subgroup.index_eq_card (H := M) ▸ rfl)
  have hcomm : IsMulCommutative (G ⧸ M) :=
    (MonoidHom.id (G ⧸ M)).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.ker_mk' M, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hcomm.is_comm.comm (QuotientGroup.mk' M g₁) (QuotientGroup.mk' M g₂)

/-- **Isaacs Problem 1D.15** (`N = G` の場合). 有限群 `G` で商 `G / Φ(G)` が冪零ならば `G` 自身が
冪零。各 Sylow `p`-部分群 `P` について、その像 `θ(P)` (`θ = G ↠ G/Φ(G)`) は `G/Φ(G)` の Sylow
(1B.5(b) の像構成) ゆえ冪零性から正規、逆像 `P ⊔ Φ(G) = θ⁻¹(θ(P))` (`comap_map_eq` + `ker θ = Φ(G)`)
が `G` で正規。Frattini 論法 `N_G(P) ⊔ (P ⊔ Φ(G)) = ⊤` から `P` を吸収して `N_G(P) ⊔ Φ(G) = ⊤`、
Frattini 部分群の非生成性 (`frattini_nongenerating`) で `N_G(P) = ⊤`、すなわち `P ◁ G`。全 Sylow が
正規なので `G` は冪零 (`isNilpotent_of_finite_tfae`)。1D.14 (`Φ(G) ⊆ Z(G) ⟹ 冪零`) を一般化する。 -/
theorem isNilpotent_of_quotient_frattini_isNilpotent {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent (G ⧸ frattini G)] : Group.IsNilpotent G := by
  refine (Group.isNilpotent_of_finite_tfae.out 3 0 rfl rfl).mp ?_
  intro p hp P
  haveI := hp
  -- `θ(P)` は `G/Φ(G)` の Sylow `p`-部分群 `Q`
  obtain ⟨Q, hQ⟩ := exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (IsHallSubgroup.map_of_surjective (QuotientGroup.mk'_surjective (frattini G))
      (sylow_isHallSubgroup_singleton P))
  -- `G/Φ(G)` 冪零ゆえ `θ(P) = ↑Q` は正規、逆像 `P ⊔ Φ(G)` も正規
  have hmapnorm : ((P : Subgroup G).map (QuotientGroup.mk' (frattini G))).Normal :=
    hQ ▸ (inferInstance : (Q : Subgroup (G ⧸ frattini G)).Normal)
  haveI hPΦnorm : ((P : Subgroup G) ⊔ frattini G).Normal := by
    have h := hmapnorm.comap (QuotientGroup.mk' (frattini G))
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  -- Frattini 論法 + 非生成性で `N_G(P) = ⊤`、すなわち `P ◁ G`
  have hfr := Sylow.normalizer_sup_eq_top' (N := (P : Subgroup G) ⊔ frattini G) P le_sup_left
  rw [← sup_assoc] at hfr
  have h1 := frattini_nongenerating hfr
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
  rw [← h1]
  exact sup_le le_rfl Subgroup.le_normalizer

/-- **Isaacs Problem 1D.17**. `N ◁ G` が冪零で商 `G / N'` (`N' = ⁅N, N⁆` は `N` の導来部分群) も
冪零ならば `G` は冪零。導来部分群 `N' = ⁅N, N⁆` は 1D.8 (`commutator_le_frattini`, `N` 冪零) で `Φ(N)`
に含まれ、1D.16 (`frattini_map_subtype_le_frattini`) で `Φ(N)` の像 `⊆ Φ(G)`、あわせて `N' ⊆ Φ(G)`
(`Subgroup.map_subtype_commutator` で `(commutator ↥N).map N.subtype = ⁅N, N⁆`)。ゆえに全射
`G / N' ↠ G / Φ(G)` (`QuotientGroup.map`) があり、`G / N'` 冪零から `G / Φ(G)` 冪零
(`nilpotent_of_surjective`)、1D.15 (`isNilpotent_of_quotient_frattini_isNilpotent`) で `G` 冪零。

弱めて「`G/N` 冪零」を仮定しても `G` 冪零は従わない (Isaacs の Note)。 -/
theorem isNilpotent_of_quotient_commutator_isNilpotent {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent (N : Subgroup G)]
    [Group.IsNilpotent (G ⧸ ⁅N, N⁆)] : Group.IsNilpotent G := by
  -- `N' = ⁅N, N⁆ ⊆ Φ(G)`
  have hN'le : ⁅N, N⁆ ≤ frattini G := by
    rw [← Subgroup.map_subtype_commutator]
    exact (Subgroup.map_mono commutator_le_frattini).trans frattini_map_subtype_le_frattini
  have hcomap : ⁅N, N⁆ ≤ (frattini G).comap (MonoidHom.id G) := by rwa [Subgroup.comap_id]
  -- 全射 `G / N' ↠ G / Φ(G)` で `G / Φ(G)` が冪零
  haveI : Group.IsNilpotent (G ⧸ frattini G) :=
    Group.nilpotent_of_surjective _
      (QuotientGroup.map_surjective_of_surjective ⁅N, N⁆ (frattini G) (MonoidHom.id G)
        (by simpa using QuotientGroup.mk_surjective) hcomap)
  exact isNilpotent_of_quotient_frattini_isNilpotent

/-- Frattini 論法の一般化: 有限群 `K` の正規部分群 `M` について商 `K / M` が冪零ならば、各 Sylow
`p`-部分群 `P` について `N_K(P) ⊔ M = ⊤`。`P` の像 `θ(P)` (`θ = K ↠ K/M`) は `K/M` の Sylow ゆえ
冪零性から正規、逆像 `P ⊔ M` が `K` で正規、Frattini 論法 `normalizer_sup_eq_top'` で `P` を吸収。
`isNilpotent_of_quotient_frattini_isNilpotent` の核を `M` 一般に取り出したもの。 -/
theorem sylow_normalizer_sup_eq_top_of_quotient_nilpotent {K : Type*} [Group K] [Finite K]
    {M : Subgroup K} [M.Normal] (hquot : Group.IsNilpotent (K ⧸ M)) {p : ℕ} [Fact p.Prime]
    (P : Sylow p K) : Subgroup.normalizer ↑P ⊔ M = ⊤ := by
  haveI := hquot
  obtain ⟨Q, hQ⟩ := exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (IsHallSubgroup.map_of_surjective (QuotientGroup.mk'_surjective M)
      (sylow_isHallSubgroup_singleton P))
  have hmapnorm : ((↑P : Subgroup K).map (QuotientGroup.mk' M)).Normal :=
    hQ ▸ (inferInstance : (Q : Subgroup (K ⧸ M)).Normal)
  haveI hPMnorm : ((↑P : Subgroup K) ⊔ M).Normal := by
    have h := hmapnorm.comap (QuotientGroup.mk' M)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have hfr := Sylow.normalizer_sup_eq_top' (N := (↑P : Subgroup K) ⊔ M) P le_sup_left
  refine le_antisymm le_top ?_
  rw [← hfr]
  exact sup_le le_sup_left (sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)

/-- **Isaacs Problem 1D.15** (一般 `N` 版). `Φ(G) ⊆ N ⊴ G` で商 `N / Φ(G)` が冪零ならば `N` は冪零。
各 Sylow `p`-部分群 `P` について ── (内) `N/Φ(G)` の冪零性から
`sylow_normalizer_sup_eq_top_of_quotient_nilpotent` で `N_N(P) ⊔ Φ(G)ᴺ = ⊤` (`↥N` 内)、`N.subtype`
で押し出して `N = θ(N_N(P)) ⊔ Φ(G) ≤ N_G(P) ⊔ Φ(G)` (`le_normalizer_map`)。(外)
`Sylow.normalizer_sup_eq_top` で `N_G(P) ⊔ N = ⊤`。合わせて `N_G(P) ⊔ Φ(G) = ⊤`、
`frattini_nongenerating` で `N_G(P) = ⊤` ⟹ `P ⊴ G` ⟹ `P ⊴ N`。全 Sylow 正規で `N` 冪零。N=G 版
`isNilpotent_of_quotient_frattini_isNilpotent` の二層版 (Fitting 経由は循環するので Frattini 二段)。 -/
theorem isNilpotent_of_frattini_le_of_quotient_isNilpotent {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hΦN : frattini G ≤ N)
    (hquot : Group.IsNilpotent (↥N ⧸ (frattini G).subgroupOf N)) :
    Group.IsNilpotent ↥N := by
  refine (Group.isNilpotent_of_finite_tfae.out 3 0 rfl rfl).mp ?_
  intro p hp P
  haveI := hp
  have hinner := sylow_normalizer_sup_eq_top_of_quotient_nilpotent hquot P
  have houter := Sylow.normalizer_sup_eq_top P
  -- `hinner` を `N.subtype` で `G` に押し出す
  have hmapeq :
      (Subgroup.normalizer (↑P : Subgroup ↥N)).map N.subtype ⊔ frattini G = N := by
    have h := congrArg (Subgroup.map N.subtype) hinner
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hΦN,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hNle : N ≤ Subgroup.normalizer (P.map N.subtype) ⊔ frattini G :=
    hmapeq.symm.le.trans (sup_le_sup_right (Subgroup.le_normalizer_map N.subtype) _)
  -- 内外を合わせて `N_G(P) ⊔ Φ(G) = ⊤`
  have hcomb : Subgroup.normalizer (P.map N.subtype) ⊔ frattini G = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← houter]
    exact sup_le le_sup_left hNle
  -- 非生成性で `P ⊴ G`、対応で `P ⊴ N`
  have hPmapnorm := Subgroup.normalizer_eq_top_iff.mp (frattini_nongenerating hcomb)
  have hsgof : (P.map N.subtype).subgroupOf N = (↑P : Subgroup ↥N) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  have hsub := hPmapnorm.subgroupOf N
  rwa [hsgof] at hsub

/-- **Isaacs Problem 1D.8** (基本アーベル部分の核). 有限 `p`-群 `P` では任意の `g` について
`g ^ p ∈ Φ(P)`。各極大部分群 `M` は `p`-群の coatom ゆえ指数が素数 (1D.6) かつ `∣ |P| = p^n`、したがって
指数 `= p`。`Subgroup.pow_index_mem` で `g ^ (M.index) = g ^ p ∈ M`、全極大の共通部分をとって
`g ^ p ∈ Φ(P)`。これが `P / Φ(P)` の指数 `p` 性 (基本アーベルの exponent 部分) を与える。 -/
theorem pow_mem_frattini_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (g : P) : g ^ p ∈ frattini P := by
  haveI := hP.isNilpotent
  rw [frattini, Order.radical]
  refine Subgroup.mem_iInf.mpr fun M => Subgroup.mem_iInf.mpr fun hM => ?_
  simp only [Set.mem_setOf_eq] at hM
  haveI : M.Normal := Subgroup.normalizer_eq_top_iff.mp
    (hM.2 _ (Group.normalizerCondition_of_isNilpotent M (lt_top_iff_ne_top.mpr hM.1)))
  have hidx : M.index = p := by
    have hp : M.index.Prime := (isCoatom_iff_index_prime M).mp hM
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hdvd : M.index ∣ p ^ n := hn ▸ M.index_dvd_card
    exact (Nat.prime_dvd_prime_iff_eq hp Fact.out).mp (hp.dvd_of_dvd_pow hdvd)
  rw [← hidx]
  exact Subgroup.pow_index_mem M g

/-- **Isaacs Problem 1D.8** (基本アーベル部分). 有限 `p`-群 `P` では `P / Φ(P)` の各元の `p` 乗が
`1`、すなわち exponent が `p` を割る。`commutator_le_frattini` (可換部分、`p`-群は冪零) とあわせて
`P / Φ(P)` は基本アーベル。`pow_mem_frattini_of_isPGroup` の商への持ち上げ。 -/
theorem pow_eq_one_frattiniQuotient_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) (x : P ⧸ frattini P) : x ^ p = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact pow_mem_frattini_of_isPGroup hP g

/-- `P / Φ(P)` が巡回ならば `P` は巡回 (1D.9 の核). 生成元 `x̄ = xΦ(P)` をとると `⟨x⟩` の像が
`P/Φ(P)` 全体ゆえ `⟨x⟩ ⊔ Φ(P) = ⊤` (`comap_map_eq` + `ker_mk'`)、Frattini 部分群の非生成性
(`frattini_nongenerating`) で `⟨x⟩ = ⊤`、すなわち `x` が `P` を生成。 -/
theorem isCyclic_of_frattiniQuotient_isCyclic {P : Type*} [Group P] [Finite P]
    (h : IsCyclic (P ⧸ frattini P)) : IsCyclic P := by
  obtain ⟨gbar, hgbar⟩ := h.exists_generator
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective gbar
  have himg : (Subgroup.zpowers x).map (QuotientGroup.mk' (frattini P)) = ⊤ := by
    rw [MonoidHom.map_zpowers, eq_top_iff]
    intro y _
    exact hgbar y
  have hsup : Subgroup.zpowers x ⊔ frattini P = ⊤ := by
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini P))) himg
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hc
  have htop : Subgroup.zpowers x = ⊤ := frattini_nongenerating hsup
  exact ⟨⟨x, fun y => htop.ge (Subgroup.mem_top y)⟩⟩

/-- **Isaacs Problem 1D.9** (前半). 非巡回有限 `p`-群 `P` では `p ^ 2 ≤ |P : Φ(P)|`。商 `P / Φ(P)`
は `p`-群 (`IsPGroup.to_quotient`) で位数 `p ^ n`。`P` 非巡回ゆえ
`isCyclic_of_frattiniQuotient_isCyclic` の対偶で `P / Φ(P)` も非巡回、したがって位数 `1` (自明) でも
`p` (`isCyclic_of_prime_card` で巡回) でもない、すなわち `n ≥ 2`。 -/
theorem sq_le_card_frattiniQuotient_of_isPGroup_of_not_isCyclic {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    p ^ 2 ≤ Nat.card (P ⧸ frattini P) := by
  have hncq : ¬ IsCyclic (P ⧸ frattini P) :=
    fun hc => hnc (isCyclic_of_frattiniQuotient_isCyclic hc)
  obtain ⟨n, hn⟩ := (hP.to_quotient (frattini P)).exists_card_eq
  rw [hn]
  refine Nat.pow_le_pow_right (Fact.out : p.Prime).pos ?_
  by_contra hlt
  rw [not_le] at hlt
  interval_cases n
  · rw [pow_zero] at hn
    haveI : Subsingleton (P ⧸ frattini P) := (Nat.card_eq_one_iff_unique.mp hn).1
    refine hncq ⟨⟨1, fun y => Subgroup.mem_zpowers_iff.mpr ⟨0, ?_⟩⟩⟩
    rw [zpow_zero]
    exact Subsingleton.elim _ _
  · rw [pow_one] at hn
    exact hncq (isCyclic_of_prime_card hn)

/-- **Isaacs Problem 1D.9** (後半). 位数 `p²` の群 `P` は巡回であるか、または基本アーベル (可換かつ
全元の `p` 乗が `1`)。非巡回なら前半で `p² ≤ |P : Φ(P)|`、Lagrange (`index_mul_card`) より `|Φ(P)| = 1`
すなわち `Φ(P) = ⊥`。よって `pow_mem_frattini_of_isPGroup` から `g ^ p ∈ ⊥` (exponent p)、
`commutator_le_frattini` から `⁅a, b⁆ ∈ ⊥` (可換)。 -/
theorem isCyclic_or_elementaryAbelian_of_card_eq_prime_sq {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card P = p ^ 2) :
    IsCyclic P ∨ (IsMulCommutative P ∧ ∀ g : P, g ^ p = 1) := by
  haveI hP : IsPGroup p P := IsPGroup.iff_card.mpr ⟨2, hcard⟩
  haveI := hP.isNilpotent
  rcases em (IsCyclic P) with hc | hnc
  · exact Or.inl hc
  refine Or.inr ?_
  have hidx : p ^ 2 ≤ (frattini P).index :=
    sq_le_card_frattiniQuotient_of_isPGroup_of_not_isCyclic hP hnc
  have hΦbot : frattini P = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have hlag := (frattini P).index_mul_card
    rw [hcard] at hlag
    have hk : 0 < (frattini P).index := lt_of_lt_of_le (pow_pos (Fact.out : p.Prime).pos 2) hidx
    have hle : (frattini P).index * Nat.card (frattini P) ≤ (frattini P).index * 1 := by
      rw [mul_one, hlag]; exact hidx
    exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left hle hk) Nat.card_pos
  have hcbot : commutator P = ⊥ := le_bot_iff.mp (hΦbot ▸ commutator_le_frattini)
  refine ⟨(commutator_eq_bot_iff P).mp hcbot, fun g => ?_⟩
  have := pow_mem_frattini_of_isPGroup hP g
  rwa [hΦbot, Subgroup.mem_bot] at this

/-- **Isaacs Problem 1D.10** (前半). 有限 `p`-群 `P` の可換正規部分群のうち極大な `A` は自己中心化的、
すなわち `C_P(A) = A`。`A ⊆ C_P(A)` は `A` 可換ゆえ自明。逆に `A < C_P(A)` なら Lemma 1.23
(`IsPGroup.exists_normal_index_eq_prime`) で `A < L ≤ C_P(A)`, `|L:A| = p`, `L ◁ P` を得る。
`L ⊆ C_P(A)` から `A ⊆ Z(L)`、`L/A` は位数 `p` で巡回ゆえ `L` は可換
(`isMulCommutative_of_isCyclic_of_ker_le_center`) — `A < L` の可換正規部分群は `A` の極大性に反する。 -/
theorem centralizer_eq_self_of_maximal_abelian_normal {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (A : Subgroup P) [A.Normal]
    [IsMulCommutative ↥A]
    (hmax : ∀ B : Subgroup P, B.Normal → IsMulCommutative ↥B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set P) = A := by
  refine le_antisymm ?_ (Subgroup.le_centralizer A)
  by_contra hnle
  haveI : (Subgroup.centralizer (A : Set P)).Normal := Subgroup.normal_centralizer
  have hlt : A < Subgroup.centralizer (A : Set P) :=
    lt_of_le_of_ne (Subgroup.le_centralizer A) (fun heq => hnle heq.ge)
  obtain ⟨L, hLnorm, hAL, hLC, hidx⟩ := IsPGroup.exists_normal_index_eq_prime hP hlt
  -- `L ⊆ C_P(A)` ゆえ `A ⊆ Z(L)`
  have hAcenterL : A.subgroupOf L ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact ((Subgroup.mem_centralizer_iff.mp (hLC l.2)) _ (Subgroup.mem_subgroupOf.mp hx)).symm
  -- `L/A` 位数 `p` で巡回 ⟹ `L` 可換
  haveI hcyc : IsCyclic (↥L ⧸ A.subgroupOf L) :=
    isCyclic_of_prime_card (p := p) (by rw [← Subgroup.index_eq_card]; exact hidx)
  haveI hLab : IsMulCommutative ↥L :=
    (QuotientGroup.mk' (A.subgroupOf L)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']; exact hAcenterL)
  exact absurd (hmax L hLnorm hLab hAL.le) hAL.ne'

/-- **Isaacs Problem 1D.10** (後半). 極大可換正規部分群 `A` について `|P : A|` は `(|A| - 1)!` を割る。
`A = C_P(A)` (前半) なので `P` の共役作用 `P → Sym(A ∖ {1})` の核は `C_P(A) = A`、ゆえに
`P/A ↪ Sym(A ∖ {1})`、`|P : A| = |P/A| ∣ |Sym(A∖{1})| = (|A| - 1)!`。 -/
theorem index_dvd_factorial_of_maximal_abelian_normal {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (A : Subgroup P) [A.Normal]
    [IsMulCommutative ↥A]
    (hmax : ∀ B : Subgroup P, B.Normal → IsMulCommutative ↥B → A ≤ B → B = A) :
    A.index ∣ (Nat.card ↥A - 1).factorial := by
  have hCA : Subgroup.centralizer (A : Set P) = A :=
    centralizer_eq_self_of_maximal_abelian_normal hP A hmax
  -- `P` は共役で `A ∖ {1}` に作用する
  letI act : MulAction P {a : ↥A // a ≠ 1} :=
    { smul := fun g x => ⟨MulAut.conjNormal g x.1,
        fun hc => x.2 ((MulAut.conjNormal g).injective (hc.trans (map_one _).symm))⟩
      one_smul := fun x => Subtype.ext (by
        change MulAut.conjNormal 1 x.1 = x.1
        rw [map_one]; rfl)
      mul_smul := fun g h x => Subtype.ext (by
        change MulAut.conjNormal (g * h) x.1 = MulAut.conjNormal g (MulAut.conjNormal h x.1)
        rw [map_mul]; rfl) }
  have hsmul : ∀ (g : P) (x : {a : ↥A // a ≠ 1}), ((g • x).1 : ↥A) = MulAut.conjNormal g x.1 :=
    fun _ _ => rfl
  set f := MulAction.toPermHom P {a : ↥A // a ≠ 1} with hf
  have hfapp : ∀ (g : P) (x : {a : ↥A // a ≠ 1}), f g x = g • x := fun _ _ => rfl
  -- 核は `C_P(A) = A`
  have hker : f.ker = A := by
    have hkerC : f.ker = Subgroup.centralizer (A : Set P) := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
      constructor
      · intro hg a ha
        rcases eq_or_ne a 1 with rfl | hane
        · simp
        · have hane' : (⟨a, ha⟩ : ↥A) ≠ 1 := fun h => hane (Subtype.ext_iff.mp h)
          have hgx : g • (⟨⟨a, ha⟩, hane'⟩ : {a : ↥A // a ≠ 1}) = ⟨⟨a, ha⟩, hane'⟩ :=
            Equiv.Perm.ext_iff.mp hg ⟨⟨a, ha⟩, hane'⟩
          have h1 : (MulAut.conjNormal g ⟨a, ha⟩ : ↥A) = ⟨a, ha⟩ := by
            have hv := Subtype.ext_iff.mp hgx
            rwa [hsmul] at hv
          have h2 := Subtype.ext_iff.mp h1
          rw [MulAut.conjNormal_apply] at h2
          exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      · intro hg
        rw [Equiv.Perm.ext_iff]
        intro x
        change g • x = x
        apply Subtype.ext
        rw [hsmul]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have hcx := hg (x.1 : P) x.1.2
        rw [← hcx]; group
    exact hkerC.trans hCA
  have hcardX : Nat.card {a : ↥A // a ≠ 1} = Nat.card ↥A - 1 := by
    classical
    have hfin : Fintype ↥A := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : ↥A => x = 1), Fintype.card_subtype_eq]
  calc A.index = f.ker.index := by rw [hker]
    _ = Nat.card f.range := Subgroup.index_ker f
    _ ∣ Nat.card (Equiv.Perm {a : ↥A // a ≠ 1}) := Subgroup.card_subgroup_dvd_card _
    _ = (Nat.card {a : ↥A // a ≠ 1}).factorial := Nat.card_perm
    _ = (Nat.card ↥A - 1).factorial := by rw [hcardX]

/-- 有限群には可換正規部分群のうち極大なもの (`⊥` を含むので存在) がある。1D.10/1D.11 で
Lemma 1.23 を適用するための存在補題 (有限順序集合の極大元)。 -/
theorem exists_maximal_abelian_normal (P : Type*) [Group P] [Finite P] :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative ↥A ∧
      ∀ B : Subgroup P, B.Normal → IsMulCommutative ↥B → A ≤ B → B = A := by
  obtain ⟨A, -, hAmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup P => B.Normal ∧ IsMulCommutative ↥B) (a := Subgroup.center P)
    ⟨inferInstance, inferInstance⟩
  exact ⟨A, hAmax.1.1, hAmax.1.2,
    fun C hCn hCa hAC => le_antisymm (hAmax.2 ⟨hCn, hCa⟩ hAC) hAC⟩

/-- **Isaacs Problem 1D.11**. `n` が有限群 `G` の可換部分群の位数の上界ならば `|G| ∣ n!`。各素数 `p`
について `P ∈ Syl_p(G)` の極大可換正規部分群 `A` (`exists_maximal_abelian_normal`) に 1D.10 後半を適用
すると `|P:A| ∣ (|A|-1)!`、`A` は可換ゆえ像を通して `|A| ≤ n`、したがって
`|P| = |A|·|P:A| ∣ |A|·(|A|-1)! = |A|! ∣ n!`。`|P| = p^{v_p|G|}` は `|G|` の `p`-部分ゆえ、
全素数冪について割り切れ `|G| ∣ n!` (`Nat.dvd_iff_prime_pow_dvd_dvd`)。`n` を最大値でなく上界に
一般化してある (最大値はその特別な場合)。 -/
theorem card_dvd_factorial_of_abelian_bound {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : ∀ B : Subgroup G, IsMulCommutative ↥B → Nat.card ↥B ≤ n) :
    Nat.card G ∣ n.factorial := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPdvd : Nat.card ↥P ∣ n.factorial := by
    obtain ⟨A, hAn, hAa, hAmax⟩ := exists_maximal_abelian_normal ↥P
    haveI := hAn
    haveI := hAa
    haveI hPp : IsPGroup p ↥P := P.isPGroup'
    have hidx : A.index ∣ (Nat.card ↥A - 1).factorial :=
      index_dvd_factorial_of_maximal_abelian_normal hPp A hAmax
    have hAle : Nat.card ↥A ≤ n := by
      have hfinj := (P : Subgroup G).subtype_injective
      haveI : IsMulCommutative ↥(A.map (P : Subgroup G).subtype) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        obtain ⟨a, rfl⟩ :=
          (Subgroup.equivMapOfInjective A (P : Subgroup G).subtype hfinj).surjective x
        obtain ⟨b, rfl⟩ :=
          (Subgroup.equivMapOfInjective A (P : Subgroup G).subtype hfinj).surjective y
        rw [← map_mul, ← map_mul, hAa.is_comm.comm a b]
      have hle := hn (A.map (P : Subgroup G).subtype) inferInstance
      rwa [Subgroup.card_map_of_injective hfinj] at hle
    have hAne : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
    calc Nat.card ↥P = Nat.card ↥A * A.index := (Subgroup.card_mul_index A).symm
      _ ∣ Nat.card ↥A * (Nat.card ↥A - 1).factorial := Nat.mul_dvd_mul_left _ hidx
      _ = (Nat.card ↥A).factorial := Nat.mul_factorial_pred hAne
      _ ∣ n.factorial := Nat.factorial_dvd_factorial hAle
  have hk : p ^ k ∣ Nat.card ↥P := by
    have hmult : Nat.card ↥P = p ^ Nat.factorization (Nat.card G) p := P.card_eq_multiplicity
    rw [hmult]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hpk)
  exact hk.trans hPdvd

open Equiv.Perm in
/-- McKay の数え上げ: 素数 `p ∣ |G|` のとき、`x ^ p = 1` をみたす `x` の個数は `p` の倍数。
`vectorsProdEqOne G p` (積が `1` の `p`-組、個数 `|G|^{p-1}`) に `Multiplicative (ZMod p)` を巡回
シフトで作用させ `IsPGroup.card_modEq_card_fixedPoints` を用いる。固定点は定数ベクトル `(x, …, x)`
(`x ^ p = 1`) と一対一。`|G|^{p-1} ≡ 0` (`p ∣ |G|`) ゆえ固定点数 `≡ 0`。 -/
theorem card_pow_eq_one_modEq_zero {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    Nat.card {x : G // x ^ p = 1} ≡ 0 [MOD p] := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpos : 0 < p := hp.out.pos
  -- `rotate` の `p`-周期性
  have hp1 : ∀ (w : vectorsProdEqOne G p) (s : ℕ),
      VectorsProdEqOne.rotate w (p + s) = VectorsProdEqOne.rotate w s := fun w s => by
    rw [← VectorsProdEqOne.rotate_rotate, VectorsProdEqOne.rotate_length]
  have hper2 : ∀ (w : vectorsProdEqOne G p) (t r : ℕ),
      VectorsProdEqOne.rotate w (p * t + r) = VectorsProdEqOne.rotate w r := by
    intro w t
    induction t with
    | zero => intro r; simp
    | succ k ih => intro r; rw [Nat.mul_succ, show p * k + p + r = p + (p * k + r) by ring, hp1, ih]
  have hper : ∀ (w : vectorsProdEqOne G p) (m : ℕ),
      VectorsProdEqOne.rotate w m = VectorsProdEqOne.rotate w (m % p) := fun w m => by
    conv_lhs => rw [← Nat.div_add_mod m p]
    exact hper2 w (m / p) (m % p)
  -- `Multiplicative (ZMod p)` の巡回シフト作用
  letI act : MulAction (Multiplicative (ZMod p)) (vectorsProdEqOne G p) :=
    { smul := fun k v => VectorsProdEqOne.rotate v (Multiplicative.toAdd k).val
      one_smul := fun v => by
        change VectorsProdEqOne.rotate v
          (Multiplicative.toAdd (1 : Multiplicative (ZMod p))).val = v
        rw [toAdd_one, ZMod.val_zero, VectorsProdEqOne.rotate_zero]
      mul_smul := fun a b v => by
        change VectorsProdEqOne.rotate v (Multiplicative.toAdd (a * b)).val
          = VectorsProdEqOne.rotate (VectorsProdEqOne.rotate v (Multiplicative.toAdd b).val)
              (Multiplicative.toAdd a).val
        rw [VectorsProdEqOne.rotate_rotate, hper v (Multiplicative.toAdd (a * b)).val,
          hper v ((Multiplicative.toAdd b).val + (Multiplicative.toAdd a).val)]
        congr 1
        rw [toAdd_mul, ZMod.val_add, Nat.mod_mod, Nat.add_comm (Multiplicative.toAdd b).val] }
  haveI hPG : IsPGroup p (Multiplicative (ZMod p)) :=
    IsPGroup.of_card (n := 1) (by
      rw [pow_one, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  -- 固定点 (= 定数ベクトル) は `{x // x ^ p = 1}` と一対一
  have hshift : ∀ (v : vectorsProdEqOne G p),
      (Multiplicative.ofAdd (1 : ZMod p)) • v = VectorsProdEqOne.rotate v 1 := fun v => by
    change VectorsProdEqOne.rotate v
      (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = _
    rw [toAdd_ofAdd, ZMod.val_one]
  have hrepl : ∀ (v : vectorsProdEqOne G p),
      (Multiplicative.ofAdd (1 : ZMod p)) • v = v →
      v.1 = List.Vector.replicate p (v.1.get ⟨0, hpos⟩) := by
    intro v hv
    have hrot1 : v.1.toList.rotate 1 = v.1.toList := by
      have h2 := hv
      rw [hshift] at h2
      exact Subtype.ext_iff.mp (Subtype.ext_iff.mp h2)
    obtain ⟨a, ha⟩ := List.rotate_one_eq_self_iff_eq_replicate.mp hrot1
    have hlist : v.1.toList = List.replicate p a := by rw [ha]; congr 1; exact v.1.2
    have hv1 : v.1 = List.Vector.replicate p a := Subtype.ext hlist
    have hget : v.1.get ⟨0, hpos⟩ = a := by rw [hv1, List.Vector.get_replicate]
    rw [hget]; exact hv1
  have hfixcard :
      Nat.card (MulAction.fixedPoints (Multiplicative (ZMod p)) (vectorsProdEqOne G p))
        = Nat.card {x : G // x ^ p = 1} := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨v.1.1.get ⟨0, hpos⟩, ?_⟩
        invFun := fun x => ⟨⟨List.Vector.replicate p x.1, ?_⟩,
          (MulAction.mem_fixedPoints).2 fun k => Subtype.ext (Subtype.ext ?_)⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- 固定点 head の `p` 乗は `1`
      have hv := hrepl v.1 ((MulAction.mem_fixedPoints).1 v.2 (Multiplicative.ofAdd (1 : ZMod p)))
      have hpr : v.1.1.toList.prod = 1 := v.1.2
      rw [hv] at hpr
      rwa [show (List.Vector.replicate p (v.1.1.get ⟨0, hpos⟩)).toList
        = List.replicate p (v.1.1.get ⟨0, hpos⟩) from rfl, List.prod_replicate] at hpr
    · -- replicate の積は `1`
      change (List.replicate p x.1).prod = 1
      rw [List.prod_replicate, x.2]
    · -- replicate は各 `k` で不変
      exact List.rotate_replicate x.1 p _
    · -- left_inv
      intro v
      apply Subtype.ext; apply Subtype.ext
      exact (hrepl v.1 ((MulAction.mem_fixedPoints).1 v.2 (Multiplicative.ofAdd (1 : ZMod p)))).symm
    · -- right_inv
      intro x
      apply Subtype.ext
      exact List.Vector.get_replicate x.1 ⟨0, hpos⟩
  -- 合流: `|vectorsProdEqOne| = |G|^{p-1} ≡ 0`
  have hmod := hPG.card_modEq_card_fixedPoints (vectorsProdEqOne G p)
  rw [hfixcard] at hmod
  have hVcard : Nat.card (vectorsProdEqOne G p) = Fintype.card G ^ (p - 1) := by
    rw [Nat.card_eq_fintype_card, VectorsProdEqOne.card]
  have hV0 : Nat.card (vectorsProdEqOne G p) ≡ 0 [MOD p] := by
    rw [hVcard, Nat.modEq_zero_iff_dvd]
    exact dvd_pow (by rwa [Nat.card_eq_fintype_card] at hdvd) (by have := hp.out.two_le; omega)
  exact hmod.symm.trans hV0

/-- **Isaacs Problem 1D.12**. 素数 `p ∣ |G|` のとき、位数 `p` の元の個数は `p` を法として `-1`
(個数 `+ 1` が `p` の倍数)。`x ^ p = 1 ⟺ orderOf x ∈ {1, p}` なので位数 `p` の元数は `#{x^p=1} - 1`、
McKay (`card_pow_eq_one_modEq_zero`) で `#{x^p=1} ≡ 0`、単位元 1 個を引いて `≡ -1`。 -/
theorem card_orderOf_eq_prime_add_one_modEq_zero {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    Nat.card {x : G // orderOf x = p} + 1 ≡ 0 [MOD p] := by
  classical
  have hmck := card_pow_eq_one_modEq_zero (G := G) hdvd
  -- `{x // x^p=1} ≃ Option {x // orderOf x = p}` (単位元 1 ↔ none)
  have hpart : Nat.card {x : G // x ^ p = 1} = Nat.card {x : G // orderOf x = p} + 1 := by
    haveI : Fintype G := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_option]
    refine Fintype.card_congr
      { toFun := fun x => if h : x.1 = 1 then none else some ⟨x.1, orderOf_eq_prime x.2 h⟩
        invFun := fun o => o.elim ⟨1, one_pow p⟩
          (fun y => ⟨y.1, orderOf_dvd_iff_pow_eq_one.mp y.2.dvd⟩)
        left_inv := fun x => ?_
        right_inv := fun o => ?_ }
    · by_cases h : x.1 = 1
      · simp only [dif_pos h, Option.elim]; exact Subtype.ext h.symm
      · simp only [dif_neg h, Option.elim]
    · rcases o with _ | y
      · simp only [Option.elim, dif_pos]
      · have hy1 : y.1 ≠ 1 :=
          fun h => hp.out.one_lt.ne' (y.2.symm.trans (orderOf_eq_one_iff.mpr h))
        simp only [Option.elim, dif_neg hy1]
  rw [hpart] at hmck
  exact hmck

open Pointwise in
/-- **Isaacs Problem 1D.5**. `H ≤ G` について「全素数 `q` と全非自明 `q`-部分群 `P ≤ H` で
`N_G(P) ⊆ H`」ならば `H` は Frobenius complement (`∀ g ∉ H`, `H ⊓ H^g = 1`)。

Isaacs は `H < G` (真部分群) と仮定するが、証明には不要 (`H = G` なら結論が空虚に成立)
なので落とす。仮説の `P ≠ ⊥` は Isaacs では暗黙 (`P = ⊥` を許すと `N_G(1) = G ⊆ H` で
`H = G` に退化するため)。

証明 (Isaacs hint + 片側 normalizer growth):
`D := H ⊓ H^g ≠ ⊥` と仮定し、素数 `q ∣ |D|` と `Q ∈ Syl_q(D)` を取る。
**仮説は `D` に遺伝**: `N_G(Q) ≤ H` (仮説) かつ `Q^{g⁻¹} ≤ H` 非自明ゆえ
`N_G(Q^{g⁻¹}) ≤ H` を `g` で共役して `N_G(Q) ≤ H^g`、あわせて `N_G(Q) ≤ D`。
**`Q` は `H` の Sylow**: `Q ⊆ S ∈ Syl_q(H)` で `Q ≠ S` なら `q`-群 `S` 内の正規化群成長
(Thm 1.22) で `Q < N_S(Q) ≤ N_G(Q) ⊓ H ≤ D` — `Q` の `D`-Sylow 極大性に矛盾。
**共役で締め**: `Q' := Q^{g⁻¹} ≤ H` は位数が同じゆえやはり `H` の Sylow、Sylow C で
`k ∈ H`, `(Q')^k = Q` ⟹ `k·g⁻¹ ∈ N_G(Q) ≤ H` ⟹ `g ∈ H`、矛盾。 -/
theorem disjoint_conj_of_forall_normalizer_le {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hyp : ∀ q : ℕ, q.Prime → ∀ P : Subgroup G, IsPGroup q P → P ≠ ⊥ → P ≤ H →
      Subgroup.normalizer P ≤ H) :
    ∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥ := by
  intro g hg
  by_contra hD
  set D : Subgroup G := H ⊓ MulAut.conj g • H with hDdef
  have hDH : D ≤ H := inf_le_left
  have hDHg : D ≤ MulAut.conj g • H := inf_le_right
  -- 素数 q ∣ |D| と Q ∈ Syl_q(D)
  have hDcard : Nat.card D ≠ 1 := fun h => hD (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hDcard
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q₀⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥D))
  set Q : Subgroup G := (Q₀ : Subgroup ↥D).map D.subtype with hQdef
  have hQD : Q ≤ D := Subgroup.map_subtype_le _
  have hQH : Q ≤ H := hQD.trans hDH
  have hQp : IsPGroup q Q := Q₀.isPGroup'.map _
  have hQ₀Q : Nat.card Q = Nat.card (Q₀ : Subgroup ↥D) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ D.subtype_injective).toEquiv).symm
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Q₀ : Subgroup ↥D) = 1 := by
      rw [← hQ₀Q, hbot, Subgroup.card_bot]
    rw [Sylow.card_eq_multiplicity] at h1
    rcases Nat.pow_eq_one.mp h1 with h | h
    · exact hq.one_lt.ne' h
    · have hpos : 0 < (Nat.card ↥D).factorization q :=
        hq.factorization_pos_of_dvd Nat.card_pos.ne' hqdvd
      omega
  -- 共役側: Q' := Q^{g⁻¹} ≤ H
  set Q' : Subgroup G := MulAut.conj g⁻¹ • Q with hQ'def
  have hconj_inv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv _ g
  have hQ'H : Q' ≤ H := by
    rw [hQ'def, hconj_inv]
    have h1 : (MulAut.conj g)⁻¹ • Q ≤ (MulAut.conj g)⁻¹ • (MulAut.conj g • H) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hQD.trans hDHg)
    rwa [inv_smul_smul] at h1
  have hQ'p : IsPGroup q Q' := by
    rw [hQ'def, Subgroup.pointwise_smul_def]
    exact hQp.map _
  have hQ'card : Nat.card Q' = Nat.card Q :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) Q).toEquiv).symm
  have hQ'1 : Q' ≠ ⊥ := by
    intro hbot
    apply hQ1
    rw [← Subgroup.card_eq_one] at hbot ⊢
    rw [← hQ'card, hbot]
  -- 仮説の遺伝: N_G(Q) ≤ D
  have hNQD : Subgroup.normalizer Q ≤ D := by
    refine le_inf (hyp q hq Q hQp hQ1 hQH) ?_
    have h1 : MulAut.conj g⁻¹ • Subgroup.normalizer (Q : Set G)
        ≤ Subgroup.normalizer (Q' : Set G) := by
      rw [hQ'def, Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact Subgroup.le_normalizer_map _
    have h2 : MulAut.conj g⁻¹ • Subgroup.normalizer Q ≤ H :=
      h1.trans (hyp q hq Q' hQ'p hQ'1 hQ'H)
    have h3 : MulAut.conj g • (MulAut.conj g⁻¹ • Subgroup.normalizer Q)
        ≤ MulAut.conj g • H :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h2
    rwa [hconj_inv, smul_inv_smul] at h3
  -- Q の D-極大性 (Q₀ の Sylow 極大性の transport)
  have hQmax : ∀ R : Subgroup G, IsPGroup q R → Q ≤ R → R ≤ D → R = Q := by
    intro R hRp hQR hRD
    have hR₀p : IsPGroup q (R.subgroupOf D) :=
      hRp.comap_of_injective D.subtype D.subtype_injective
    have hQ₀le : (Q₀ : Subgroup ↥D) ≤ R.subgroupOf D := by
      have h1 : Q.subgroupOf D ≤ R.subgroupOf D := Subgroup.comap_mono hQR
      -- Q.subgroupOf D = Q₀ (map along injective subtype を戻す; subgroupOf = comap は defeq)
      have h2 : Q.subgroupOf D = (Q₀ : Subgroup ↥D) := by
        rw [hQdef]
        exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
      rwa [h2] at h1
    have hR₀eq : R.subgroupOf D = Q₀ := Q₀.3 hR₀p hQ₀le
    calc R = (R.subgroupOf D).map D.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRD]
      _ = Q := by rw [hR₀eq, ← hQdef]
  -- Q₁ := Q.subgroupOf H は ↥H の Sylow (normalizer growth)
  set Q₁ : Subgroup ↥H := Q.subgroupOf H with hQ₁def
  have hQ₁p : IsPGroup q Q₁ := hQp.comap_of_injective H.subtype H.subtype_injective
  have hQ₁map : Q₁.map H.subtype = Q := by
    rw [hQ₁def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH]
  obtain ⟨S, hQ₁S⟩ := hQ₁p.exists_le_sylow
  have hQ₁_eq_S : Q₁ = ↑S := by
    by_contra hne
    have hlt : Q₁ < ↑S := lt_of_le_of_ne hQ₁S hne
    haveI : Group.IsNilpotent ↥(S : Subgroup ↥H) := S.isPGroup'.isNilpotent
    have hlt_top : Q₁.subgroupOf ↑S < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun hle => hlt.ne (le_antisymm hlt.le hle)
    have hgrow := lt_normalizer_of_isNilpotent_of_lt_top hlt_top
    rw [← Subgroup.subgroupOf_normalizer_eq hQ₁S] at hgrow
    obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt hgrow
    have hynN : (y : ↥H) ∈ Subgroup.normalizer Q₁ := Subgroup.mem_subgroupOf.mp hyN
    have hynQ₁ : (y : ↥H) ∉ Q₁ := fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)
    -- R := (N_{↥H}(Q₁) ⊓ S).map H.subtype は D 内の q-群で Q を真に含む
    set R₁ : Subgroup ↥H := Subgroup.normalizer Q₁ ⊓ ↑S with hR₁def
    have hR₁p : IsPGroup q R₁ := S.isPGroup'.to_le inf_le_right
    have hQ₁R₁ : Q₁ ≤ R₁ := le_inf Subgroup.le_normalizer hQ₁S
    have hRD : R₁.map H.subtype ≤ D := by
      calc R₁.map H.subtype ≤ (Subgroup.normalizer Q₁).map H.subtype :=
            Subgroup.map_mono inf_le_left
        _ ≤ Subgroup.normalizer (Q₁.map H.subtype) := Subgroup.le_normalizer_map _
        _ = Subgroup.normalizer Q := by rw [hQ₁map]
        _ ≤ D := hNQD
    have hReqQ : R₁.map H.subtype = Q :=
      hQmax _ (hR₁p.map _) (by rw [← hQ₁map]; exact Subgroup.map_mono hQ₁R₁) hRD
    have hymem : ((y : ↥H) : G) ∈ R₁.map H.subtype :=
      ⟨(y : ↥H), ⟨hynN, y.2⟩, rfl⟩
    rw [hReqQ] at hymem
    exact hynQ₁ (by rw [hQ₁def]; exact Subgroup.mem_subgroupOf.mpr hymem)
  -- Q' も ↥H の Sylow (位数同一)
  have hQ'₁card : Nat.card (Q'.subgroupOf H) = Nat.card ↥(S : Subgroup ↥H) := by
    calc Nat.card (Q'.subgroupOf H) = Nat.card Q' :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'H).toEquiv
      _ = Nat.card Q := hQ'card
      _ = Nat.card Q₁ :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv).symm
      _ = Nat.card ↥(S : Subgroup ↥H) := by rw [hQ₁_eq_S]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥H)
    (Sylow.ofCard (Q'.subgroupOf H) (hQ'₁card.trans S.card_eq_multiplicity)) S
  -- coe に落として G へ map (1C.1 と同じ transport)
  have hAB : MulAut.conj k • (Q'.subgroupOf H) = Q₁ := by
    have h := congrArg (fun T : Sylow q ↥H => (T : Subgroup ↥H)) hk
    simpa only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, ← hQ₁_eq_S] using h
  have hkey : MulAut.conj (k : G) • Q' = Q := by
    have h := congrArg (Subgroup.map H.subtype) hAB
    rwa [map_conj_smul, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ'H, hQ₁map,
      show (H.subtype k : G) = ↑k from rfl] at h
  -- 仕上げ: k·g⁻¹ ∈ N_G(Q) ≤ D ≤ H ⟹ g ∈ H 矛盾
  have hcomb : MulAut.conj ((k : G) * g⁻¹) • Q = Q := by
    rw [map_mul, mul_smul, ← hQ'def, hkey]
  have hmemH : (k : G) * g⁻¹ ∈ H :=
    hDH (hNQD (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcomb))
  have hginv : g⁻¹ ∈ H := by
    have h := H.mul_mem (H.inv_mem k.2) hmemH
    rwa [inv_mul_cancel_left] at h
  exact hg (by simpa using H.inv_mem hginv)

end

end OddOrder.Isaacs.Ch01
