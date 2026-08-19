/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt

/-!
# Isaacs Chapter 2 — Problems §2C: N-群 (p. 61)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 §2C (Problem 2C.1)。
**N-群** = 全ての local 部分群が可解な有限群 (`IsLocal` の定義は §2C 本文の
`Theorem211Wielandt.lean`)。

- **2C.1(a)** `isSolvable_quotient_of_isNGroup`: N-群の**真の**準同型像は可解。
- **2C.1(b)**: 非可解 N-群は一意な minimal normal subgroup `S` をもち、`S` は非可換単純
  (`exists_isMinimalNormal_of_not_isSolvable` / `isMinimalNormal_unique_of_isNGroup` /
  `isSimpleGroup_of_isMinimalNormal_of_isNGroup` /
  `not_isMulCommutative_of_isMinimalNormal_of_isNGroup`)。

Note (書籍): 非可解 N-群の分類は Thompson の仕事で、有限単純群分類への大きな一歩だった。
minimal simple group (真部分群がすべて可解な非可換有限単純群) は明らかに N-群である。
-/

open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02

variable {G : Type*} [Group G]

section /- Problems 2C: N-groups (p. 61) -/

/-- **N-群** (Isaacs p. 61): 全ての local 部分群 (`IsLocal`) が可解な群。 -/
def IsNGroup (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsLocal H → Group.IsSolvable ↥H

/-- **Isaacs Problem 2C.1(a)**. N-群の**真の**準同型像 (`G ⧸ N`, `N ≠ ⊥`) は可解。

`p ∣ |N|` なる素数を取り `P ∈ Syl_p(N)` (`≠ ⊥`) とすると、Frattini argument
(`Sylow.normalizer_sup_eq_top`) で `N_G(P) ⊔ N = ⊤`。`N_G(P)` は local ゆえ可解で、
`N` が正規だから `↑(N_G(P) ⊔ N) = ↑N_G(P) · ↑N`、すなわち `N_G(P) → G ⧸ N` は全射。
よって `G ⧸ N` は可解群の準同型像で可解 (`Group.isSolvable_of_surjective`)。 -/
theorem isSolvable_quotient_of_isNGroup [Finite G] (hG : IsNGroup G)
    {N : Subgroup G} [N.Normal] (hNe : N ≠ ⊥) : Group.IsSolvable (G ⧸ N) := by
  classical
  -- `|N| > 1` ゆえ素因子 `p` と位数 `p` の元が取れる
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNe
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥N)).ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpdvd
  have hxpg : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hxpg.exists_le_sylow
  -- `P` を `G` の部分群として見たものは非自明な `p`-部分群
  set Q : Subgroup G := (P : Subgroup ↥N).map N.subtype with hQ
  have hQne : Q ≠ ⊥ := by
    intro h
    have hPbot : (P : Subgroup ↥N) = ⊥ := by
      have hle := (Subgroup.map_eq_bot_iff _).mp (hQ.symm.trans h)
      rwa [Subgroup.ker_subtype, le_bot_iff] at hle
    have hxb : x ∈ (⊥ : Subgroup ↥N) := hPbot ▸ hP (Subgroup.mem_zpowers x)
    rw [Subgroup.mem_bot] at hxb
    rw [hxb, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hQpg : IsPGroup p ↥Q := by
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [hQ, ← hn]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ _ N.subtype_injective).toEquiv).symm
  -- Frattini argument
  have hfr : Subgroup.normalizer (Q : Set G) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top P
  -- `N_G(Q)` は local ゆえ可解
  have : Group.IsSolvable ↥(Subgroup.normalizer (Q : Set G)) :=
    hG _ ⟨p, hp, Q, hQne, hQpg, rfl⟩
  -- `N_G(Q) → G ⧸ N` は全射
  refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp
    (Subgroup.normalizer (Q : Set G)).subtype) ?_
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hg : g ∈ ((Subgroup.normalizer (Q : Set G) ⊔ N : Subgroup G) : Set G) := by
    rw [hfr]; trivial
  rw [Subgroup.mul_normal] at hg
  obtain ⟨a, ha, n, hn, rfl⟩ := hg
  exact ⟨⟨a, ha⟩, (QuotientGroup.mk_mul_of_mem a hn).symm⟩

/-- **Isaacs Problem 2C.1(b)** (minimal normal は非可解). 非可解 N-群の minimal normal
subgroup `S` は非可解 — したがって非可換。

`S` が可解なら (a) の `G ⧸ S` 可解と合わせて `G` が可解 (`Group.isSolvable_of_ker_le_range`)。 -/
theorem not_isSolvable_of_isMinimalNormal_of_isNGroup [Finite G] (hG : IsNGroup G)
    (hns : ¬ Group.IsSolvable G) {S : Subgroup G} (hS : IsMinimalNormal S) :
    ¬ Group.IsSolvable ↥S := by
  have := hS.1
  intro h
  have := h
  have : Group.IsSolvable (G ⧸ S) := isSolvable_quotient_of_isNGroup hG hS.2.1
  exact hns (Group.isSolvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- **Isaacs Problem 2C.1(b)** (存在). 非可解群は非自明ゆえ minimal normal subgroup をもつ。 -/
theorem exists_isMinimalNormal_of_not_isSolvable [Finite G] (hns : ¬ Group.IsSolvable G) :
    ∃ S : Subgroup G, IsMinimalNormal S := by
  have : Nontrivial G := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hns inferInstance
  obtain ⟨S, hS, -⟩ := exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  exact ⟨S, hS⟩

/-- **Isaacs Problem 2C.1(b)** (一意性). 非可解 N-群の minimal normal subgroup は一意。

相異なる minimal normal `S₁ ≠ S₂` があれば `S₁ ⊓ S₂ = ⊥` ゆえ
`G ↪ (G ⧸ S₁) × (G ⧸ S₂)`、(a) で両因子が可解だから `G` も可解で仮定に反する。 -/
theorem isMinimalNormal_unique_of_isNGroup [Finite G] (hG : IsNGroup G)
    (hns : ¬ Group.IsSolvable G) {S₁ S₂ : Subgroup G}
    (h₁ : IsMinimalNormal S₁) (h₂ : IsMinimalNormal S₂) : S₁ = S₂ := by
  by_contra hne
  have := h₁.1
  have := h₂.1
  have hinf : S₁ ⊓ S₂ = ⊥ := by
    rcases h₁.2.2 (S₁ ⊓ S₂) (Subgroup.normal_inf_normal S₁ S₂) inf_le_left with h | h
    · exact h
    · rcases h₂.2.2 S₁ h₁.1 (h ▸ inf_le_right) with h' | h'
      · exact absurd h' h₁.2.1
      · exact absurd h' hne
  have : Group.IsSolvable (G ⧸ S₁) := isSolvable_quotient_of_isNGroup hG h₁.2.1
  have : Group.IsSolvable (G ⧸ S₂) := isSolvable_quotient_of_isNGroup hG h₂.2.1
  refine hns (Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.mk' S₁).prod (QuotientGroup.mk' S₂)) ?_)
  rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod, QuotientGroup.ker_mk',
    QuotientGroup.ker_mk', hinf]

/-- **Isaacs Problem 2C.1(b)** (単純性). 非可解 N-群の minimal normal subgroup `S` は単純。

`↥S` の minimal normal `T` を取る。`T = ⊤` なら `↥S` は単純。`T ≠ ⊤` なら:
1. すべての `g : G` で `T` が `MulAut.conjNormal g` 不変なら `T` を `G` に押し出したものが
   `G`-正規になり、`S` の minimality から `T = ⊥` or `⊤` で矛盾。よって
   `V := T^{conjNormal g} ≠ T` なる `g` が取れる。
2. `V` も `↥S` の minimal normal (`IsMinimalNormal.map_equiv`) で `T ≠ V` ゆえ
   `T ⊓ V = ⊥`、両者は `↥S` で正規だから元ごとに可換。
3. `T` の非単位元 `x` (素数位数) をとり `P := ⟨x⟩`。`V` の押し出しは `x` を中心化するので
   `N_G(P)` に含まれ、`N_G(P)` は local ゆえ可解 ⟹ `V` 可解 ⟹ `T` 可解。
4. `T` 可解 + minimal normal ⟹ `⁅T,T⁆ < T` かつ `⁅T,T⁆ ⊴ ↥S` ゆえ `⁅T,T⁆ = ⊥`、`T` は可換で
   冪零。すると `T ≤ F(↥S)` で `F(↥S) ≠ ⊥`、`F(↥S)` は特性的ゆえ押し出しが `G`-正規、
   `S` の minimality で `F(↥S) = ⊤` ⟹ `↥S` 冪零 ⟹ 可解 — 上の非可解性に矛盾。 -/
theorem isSimpleGroup_of_isMinimalNormal_of_isNGroup [Finite G] (hG : IsNGroup G)
    (hns : ¬ Group.IsSolvable G) {S : Subgroup G} (hS : IsMinimalNormal S) : IsSimpleGroup ↥S := by
  classical
  have := hS.1
  have hSns : ¬ Group.IsSolvable ↥S := not_isSolvable_of_isMinimalNormal_of_isNGroup hG hns hS
  have : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS.2.1
  obtain ⟨T, hT, -⟩ := exists_isMinimalNormal_le_of_normal (⊤ : Subgroup ↥S) top_ne_bot
  by_cases hTtop : T = ⊤
  · exact ⟨fun N hN => hTtop ▸ hT.2.2 N hN (hTtop ▸ le_top)⟩
  exfalso
  have := hT.1
  -- 1. `T` を動かす `g` を取る
  obtain ⟨g, hg⟩ : ∃ g : G, T.map (MulAut.conjNormal g : MulAut ↥S).toMonoidHom ≠ T := by
    by_contra hcon
    push Not at hcon
    -- 全 `g` で不変 ⟹ 押し出し `T.map S.subtype` は `G`-正規
    have hnorm : (T.map S.subtype).Normal := by
      refine ⟨fun y hy c => ?_⟩
      obtain ⟨t, ht, rfl⟩ := hy
      refine ⟨(MulAut.conjNormal c : MulAut ↥S) t, ?_, ?_⟩
      · rw [← hcon c]; exact ⟨t, ht, rfl⟩
      · exact MulAut.conjNormal_apply c t
    have hne : T.map S.subtype ≠ ⊥ := by
      intro h
      apply hT.2.1
      have hle := (Subgroup.map_eq_bot_iff _).mp h
      rwa [Subgroup.ker_subtype, le_bot_iff] at hle
    rcases hS.2.2 _ hnorm (Subgroup.map_subtype_le T) with h | h
    · exact hne h
    · exact hTtop (Subgroup.map_injective S.subtype_injective
        (h.trans (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])))
  -- 2. `V := T^g` も minimal normal で `T ⊓ V = ⊥`、元ごとに可換
  obtain ⟨V, hVmin, hVne, hVsolT⟩ : ∃ V : Subgroup ↥S, IsMinimalNormal V ∧ V ≠ T ∧
      (Group.IsSolvable ↥V → Group.IsSolvable ↥T) := by
    refine ⟨T.map (MulAut.conjNormal g : MulAut ↥S).toMonoidHom,
      hT.map_equiv (MulAut.conjNormal g), hg, fun h => ?_⟩
    have := h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (T.equivMapOfInjective (MulAut.conjNormal g : MulAut ↥S).toMonoidHom
        (MulAut.conjNormal g).injective).toMonoidHom)
      (T.equivMapOfInjective (MulAut.conjNormal g : MulAut ↥S).toMonoidHom
        (MulAut.conjNormal g).injective).injective
  have := hVmin.1
  have hTV : T ⊓ V = ⊥ := by
    rcases hT.2.2 (T ⊓ V) (Subgroup.normal_inf_normal T V) inf_le_left with h | h
    · exact h
    · rcases hVmin.2.2 T hT.1 (h ▸ inf_le_right) with h' | h'
      · exact absurd h' hT.2.1
      · exact absurd h'.symm hVne
  have hcomm : ∀ a ∈ T, ∀ b ∈ V, Commute a b := fun a ha b hb =>
    Subgroup.commute_of_normal_of_disjoint T V hT.1 hVmin.1 (disjoint_iff.mpr hTV) a b ha hb
  -- 3. `T` の素数位数の元 `x` と `P := ⟨x⟩`; `V` の押し出しは `N_G(P)` に入る
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT.2.1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥T)).ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) p hpdvd
  set xG : G := ((x : ↥S) : G) with hxG
  have hxT : (x : ↥S) ∈ T := x.2
  have hxord : orderOf xG = p := by
    rw [hxG, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hx
  set P : Subgroup G := Subgroup.zpowers xG with hP
  have hPne : P ≠ ⊥ := by
    intro h
    have : xG ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers xG
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hxord
    exact hp.one_lt.ne hxord
  have hPpg : IsPGroup p ↥P :=
    IsPGroup.of_card (n := 1) (by rw [hP, Nat.card_zpowers, hxord, pow_one])
  have : Group.IsSolvable ↥(Subgroup.normalizer (P : Set G)) := hG _ ⟨p, hp, P, hPne, hPpg, rfl⟩
  -- `V.map S.subtype ≤ N_G(P)`
  have hVle : V.map S.subtype ≤ Subgroup.normalizer (P : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact (((hcomm (x : ↥S) hxT b hb).map S.subtype).zpow_left k).eq
  -- 4. `V` 可解 ⟹ `T` 可解 ⟹ `T` 可換 ⟹ `F(↥S) = ⊤` ⟹ `↥S` 可解 (矛盾)
  have hTsol : Group.IsSolvable ↥T := hVsolT (by
    have : Group.IsSolvable ↥(V.map S.subtype) := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hVle) (Subgroup.inclusion_injective hVle)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (V.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom)
      (V.equivMapOfInjective S.subtype S.subtype_injective).injective)
  have hcomm_bot : ⁅T, T⁆ = ⊥ := by
    rcases hT.2.2 ⁅T, T⁆ (Subgroup.commutator_normal T T)
      (Subgroup.commutator_le_left T T) with h | h
    · exact h
    · exfalso
      have htop : commutator ↥T = ⊤ := by
        apply Subgroup.map_injective T.subtype_injective
        rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      exact absurd htop (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥T)).ne
  have hTcomm : IsMulCommutative ↥T :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot)
  have hTnilp : Group.IsNilpotent ↥T :=
    ⟨⟨1, Subgroup.upperCentralSeries_one_eq_top_iff.mpr hTcomm⟩⟩
  have hTfit : T ≤ fitting ↥S :=
    (le_fitting_iff_isNilpotent_and_isSubnormal T).mpr ⟨hTnilp, hT.1.isSubnormal⟩
  have hfitne : (fitting ↥S).map S.subtype ≠ ⊥ := by
    intro h
    apply hT.2.1
    have hle := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype, le_bot_iff] at hle
    exact le_bot_iff.mp (hTfit.trans hle.le)
  have hfittop : fitting ↥S = ⊤ := by
    rcases hS.2.2 ((fitting ↥S).map S.subtype) inferInstance
      (Subgroup.map_subtype_le _) with h | h
    · exact absurd h hfitne
    · exact Subgroup.map_injective S.subtype_injective
        (h.trans (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]))
  have : Group.IsNilpotent ↥S :=
    Group.nilpotent_of_mulEquiv (G := ↥(fitting ↥S)) (by rw [hfittop]; exact Subgroup.topEquiv)
  exact hSns inferInstance

/-- **Isaacs Problem 2C.1(b)** (非可換性). 非可解 N-群の minimal normal subgroup は非可換。 -/
theorem not_isMulCommutative_of_isMinimalNormal_of_isNGroup [Finite G] (hG : IsNGroup G)
    (hns : ¬ Group.IsSolvable G) {S : Subgroup G} (hS : IsMinimalNormal S) :
    ¬ IsMulCommutative ↥S := fun h =>
  not_isSolvable_of_isMinimalNormal_of_isNGroup hG hns hS
    (Group.isSolvable_of_comm fun a b => h.is_comm.comm a b)

end

end OddOrder.Isaacs.Ch02
