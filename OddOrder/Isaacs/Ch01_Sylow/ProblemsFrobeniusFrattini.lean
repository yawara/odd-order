/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Frattini

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

end

end OddOrder.Isaacs.Ch01
