/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.PointStabilizers

/-!
# 点安定化群が単純な推移作用 (Isaacs Problems 8C.3 / 8C.4 の共通部分)

点安定化群 `G_α` が単純な推移作用では, 推移的な真の正規部分群は **regular** になる。
Isaacs Problem 8C.3 (`M₁₂`) と 8C.4 (`HS`) が共通に使う一歩。

## Main results

- `stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer` — `N ◁ G` が推移的で
  `N ≠ ⊤` なら `N` の点安定化群は自明。
- `card_eq_card_of_stabilizer_eq_bot` — そのとき `|N| = |Ω|` (regular)。
- `isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer` — 2-transitive で
  点安定化群が単純, かつ次数が相異なる 2 素数で割れるなら `G` は単純。
- `isSimpleGroup_of_two_transitive_of_prime_card` — 次数が素数 `r` の場合の版
  (`|G_α| ≠ r - 1` を仮定; `G_α ↪ Aut(Z_r)` と `G_α` の `Ω ∖ {α}` 上の推移性から)。
- `faithfulSMul_ofStabilizer` / `card_ofStabilizer` — 点安定化群の `Ω ∖ {α}` への作用。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 点安定化群が単純な作用 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **点安定化群が単純なら, 推移的な真の正規部分群は semiregular**。

`N ∩ G_α` は `G_α` の正規部分群なので単純性から `1` か `G_α`。後者だと `G_α ≤ N` と
`N` の推移性から `N = ⊤` になってしまうので, 前者。 -/
theorem stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer (α : Ω)
    (hsimple : IsSimpleGroup ↥(stabilizer G α))
    {N : Subgroup G} [hN : N.Normal] [IsPretransitive ↥N Ω] (hNtop : N ≠ ⊤) :
    stabilizer ↥N α = ⊥ := by
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (stabilizer G α))
      inferInstance with hbot | htop
  · have hdisj : Disjoint N (stabilizer G α) := Subgroup.subgroupOf_eq_bot.mp hbot
    have h : (stabilizer G α).subgroupOf N = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj.symm
    rw [← h]
    ext y
    rfl
  · exact absurd (eq_top_iff.mpr fun g _ => by
      have hle : stabilizer G α ≤ N := fun y hy =>
        show (⟨y, hy⟩ : ↥(stabilizer G α)) ∈ N.subgroupOf (stabilizer G α) by rw [htop]; trivial
      obtain ⟨m, hm⟩ := exists_smul_eq ↥N α (g • α)
      have hm' : ((m : ↥N) : G) • α = g • α := hm
      have hmem : (m : G)⁻¹ * g ∈ stabilizer G α := by
        rw [mem_stabilizer_iff, mul_smul, ← hm', inv_smul_smul]
      have hg : g = (m : G) * ((m : G)⁻¹ * g) := by group
      rw [hg]
      exact N.mul_mem m.2 (hle hmem)) hNtop

/-- 点安定化群が自明な推移作用 (= regular) では `|N| = |Ω|`。 -/
theorem card_eq_card_of_stabilizer_eq_bot (α : Ω) {N : Subgroup G} [IsPretransitive ↥N Ω]
    (h : stabilizer ↥N α = ⊥) : Nat.card ↥N = Nat.card Ω := by
  have hidx := index_stabilizer_of_transitive (G := ↥N) (x := α)
  rwa [h, Subgroup.index_bot] at hidx

end -- 点安定化群が単純な作用

section /- 2-transitive で点安定化群が単純な作用 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] in
/-- 忠実な作用では `1 ≠ N ◁ G` は非自明に作用するので, 2-transitivity から推移的
(**Problem 8A.9**)。 -/
theorem isPretransitive_of_normal_ne_bot_of_two_transitive [IsPretransitive G Ω]
    (h2 : ∀ a b c : Ω, b ≠ a → c ≠ a → ∃ g : G, g • a = a ∧ g • b = c)
    {N : Subgroup G} [N.Normal] (hNbot : N ≠ ⊥) :
    IsPretransitive ↥N Ω := by
  obtain ⟨n, hn1⟩ : ∃ n : ↥N, n ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hNbot (le_antisymm (fun x hx => Subgroup.mem_bot.mpr
      (congrArg Subtype.val (hc ⟨x, hx⟩))) bot_le)
  obtain ⟨x, hx⟩ : ∃ x : Ω, (n : G) • x ≠ x := by
    by_contra hc
    push Not at hc
    exact hn1 (Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => by
      rw [show ((1 : ↥N) : G) = 1 from rfl, one_smul]; exact hc β))
  exact isPretransitive_of_normal_of_two_transitive h2 hx

/-- **2-transitive + 点安定化群が単純 + 次数が素数冪でない ⟹ `G` は単純**。

`1 ≠ N ◁ G` は 2-transitivity から推移的 (**Problem 8A.9**), 点安定化群の単純性から
semiregular (`stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer`) なので
`|N| = |Ω|` (regular)。このとき `n ↦ n • α` は `N ≃ Ω` を与え, 2-transitivity から
`N ∖ {1}` の元はすべて `G` で共役 — 位数が一致してしまう。`|Ω|` が相異なる素数
`p ≠ q` で割れれば Cauchy が位数 `p` と `q` の元を同時に与えるので矛盾。

Isaacs Problem 8C.3 (次数 12) と 8C.5 (次数 22, 24) が共通に使う。 -/
theorem isSimpleGroup_of_two_transitive_of_isSimpleGroup_stabilizer
    [IsPretransitive G Ω] (α : Ω)
    (h2 : ∀ a b c : Ω, b ≠ a → c ≠ a → ∃ g : G, g • a = a ∧ g • b = c)
    (hsimple : IsSimpleGroup ↥(stabilizer G α))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpΩ : p ∣ Nat.card Ω) (hqΩ : q ∣ Nat.card Ω) :
    IsSimpleGroup G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nonempty G := ⟨1⟩
  -- `|Ω| ∣ |G|` なので `G` は非自明
  have hdvdG : Nat.card Ω ∣ Nat.card G := by
    have h := index_stabilizer_of_transitive (G := G) (x := α)
    exact h ▸ Subgroup.index_dvd_card _
  have hΩpos : 0 < Nat.card Ω := by
    rcases Nat.eq_zero_or_pos (Nat.card Ω) with h | h
    · rw [h, zero_dvd_iff] at hdvdG
      exact absurd hdvdG Nat.card_pos.ne'
    · exact h
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le hp.one_lt ((Nat.le_of_dvd hΩpos hpΩ).trans (Nat.le_of_dvd Nat.card_pos hdvdG)))
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  haveI : IsPretransitive ↥N Ω := isPretransitive_of_normal_ne_bot_of_two_transitive h2 hNbot
  -- `N` は regular
  have hstabN : stabilizer ↥N α = ⊥ :=
    stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer α hsimple hNtop
  have hNcard : Nat.card ↥N = Nat.card Ω := card_eq_card_of_stabilizer_eq_bot α hstabN
  -- `m ↦ m • α` は単射
  have hinj : ∀ u v : ↥N, (u : G) • α = (v : G) • α → u = v := by
    intro u v huv
    have hmem : v⁻¹ * u ∈ stabilizer ↥N α := by
      rw [mem_stabilizer_iff]
      change ((v⁻¹ * u : ↥N) : G) • α = α
      rw [Subgroup.coe_mul, mul_smul, huv, Subgroup.coe_inv, inv_smul_smul]
    rw [hstabN, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  have hne : ∀ u : ↥N, u ≠ 1 → (u : G) • α ≠ α := by
    intro u hu hc
    refine hu (hinj u 1 ?_)
    rw [hc, Subgroup.coe_one, one_smul]
  -- `N ∖ {1}` の元はすべて `G` で共役
  have hconj : ∀ u v : ↥N, u ≠ 1 → v ≠ 1 → ∃ g : G, g * (u : G) * g⁻¹ = (v : G) := by
    intro u v hu hv
    obtain ⟨g, hgα, hgβ⟩ := h2 α ((u : G) • α) ((v : G) • α) (hne u hu) (hne v hv)
    refine ⟨g, ?_⟩
    have hmem : g * (u : G) * g⁻¹ ∈ N := hN.conj_mem (u : G) u.2 g
    have hact : ((⟨g * (u : G) * g⁻¹, hmem⟩ : ↥N) : G) • α = (v : G) • α := by
      have hginv : g⁻¹ • α = α := inv_smul_eq_iff.mpr hgα.symm
      change (g * (u : G) * g⁻¹) • α = (v : G) • α
      rw [mul_smul, mul_smul, hginv, hgβ]
    exact congrArg Subtype.val (hinj ⟨g * (u : G) * g⁻¹, hmem⟩ v hact)
  -- 位数 `p` の元と位数 `q` の元が共役になり `p = q`
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p (hNcard ▸ hpΩ)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) q (hNcard ▸ hqΩ)
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact hp.one_lt.ne ha
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact hq.one_lt.ne hb
  obtain ⟨g, hg⟩ := hconj a b ha1 hb1
  have hoa : orderOf ((a : G)) = p := by rw [Subgroup.orderOf_coe, ha]
  have hob : orderOf ((b : G)) = q := by rw [Subgroup.orderOf_coe, hb]
  have hconjord : orderOf (g * (a : G) * g⁻¹) = orderOf ((a : G)) :=
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  rw [hg, hob, hoa] at hconjord
  exact hpq hconjord.symm

omit [Finite G] [FaithfulSMul G Ω] in
/-- 2-transitivity から, 点安定化群は `Ω ∖ {α}` に推移的。 -/
theorem isPretransitive_ofStabilizer_of_two_transitive (α : Ω)
    (h2 : ∀ a b c : Ω, b ≠ a → c ≠ a → ∃ g : G, g • a = a ∧ g • b = c) :
    IsPretransitive ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hgα, hgxy⟩ := h2 α x y ((SubMulAction.mem_ofStabilizer_iff G α).mp x.2)
    ((SubMulAction.mem_ofStabilizer_iff G α).mp y.2)
  exact ⟨⟨g, mem_stabilizer_iff.mpr hgα⟩, Subtype.ext hgxy⟩

omit [Finite G] in
/-- 点安定化群 `G_α` の `Ω ∖ {α}` への作用は忠実。 -/
theorem faithfulSMul_ofStabilizer (α : Ω) :
    FaithfulSMul ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) := by
  refine ⟨fun {g h} hgh => ?_⟩
  refine Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => ?_)
  rcases eq_or_ne β α with rfl | hβ
  · rw [mem_stabilizer_iff.mp g.2, mem_stabilizer_iff.mp h.2]
  · exact congrArg Subtype.val (hgh ⟨β, (SubMulAction.mem_ofStabilizer_iff G α).mpr hβ⟩)

omit [Finite G] [FaithfulSMul G Ω] in
/-- `Ω ∖ {α}` の濃度は `|Ω| - 1`。 -/
theorem card_ofStabilizer [Finite Ω] (α : Ω) :
    Nat.card ↥(SubMulAction.ofStabilizer G α) = Nat.card Ω - 1 := by
  have h1 : Nat.card ↥(SubMulAction.ofStabilizer G α) = ({α}ᶜ : Set Ω).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp [SubMulAction.mem_ofStabilizer_iff])
  have h2 := Set.ncard_add_ncard_compl ({α} : Set Ω)
  rw [Set.ncard_singleton] at h2
  omega

/-- **素数次数版**: `|Ω| = r` が素数で 2-transitive, 点安定化群が単純, かつ
`|G_α| ≠ r - 1` なら `G` は単純。

`1 ≠ N ◁ G` は regular で `|N| = r`。`G_α` の `N` への共役 `MulAut.conjNormal` は
`G_α` 上単射 (核の元は `ω = n • α` の形の全点を固定するので忠実性から `1`) なので
`|G_α| ∣ |Aut(N)| = φ(r) = r - 1`。他方 2-transitivity で `G_α` は `Ω ∖ {α}`
(`r - 1` 点) に推移的だから `(r - 1) ∣ |G_α|`。ゆえに `|G_α| = r - 1` となり仮定に反する。

Isaacs Problem 8C.5 の「次数 23 の段」で使う (`r - 1 = 22` で位数 22 の単純群は無い)。 -/
theorem isSimpleGroup_of_two_transitive_of_prime_card [Finite Ω]
    [IsPretransitive G Ω] (α : Ω)
    (h2 : ∀ a b c : Ω, b ≠ a → c ≠ a → ∃ g : G, g • a = a ∧ g • b = c)
    (hsimple : IsSimpleGroup ↥(stabilizer G α))
    {r : ℕ} (hr : r.Prime) (hΩ : Nat.card Ω = r)
    (hne : Nat.card ↥(stabilizer G α) ≠ r - 1) :
    IsSimpleGroup G := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Nonempty G := ⟨1⟩
  haveI := faithfulSMul_ofStabilizer (G := G) α
  haveI := isPretransitive_ofStabilizer_of_two_transitive (G := G) α h2
  -- `(r - 1) ∣ |G_α|`: `G_α` は `Ω ∖ {α}` に推移的
  have hcard1 : Nat.card ↥(SubMulAction.ofStabilizer G α) = r - 1 := by
    rw [card_ofStabilizer, hΩ]
  have hr2 : 2 ≤ r := hr.two_le
  have hdvd1 : r - 1 ∣ Nat.card ↥(stabilizer G α) := by
    haveI : Nonempty ↥(SubMulAction.ofStabilizer G α) :=
      (Nat.card_pos_iff.mp (by omega : 0 < Nat.card ↥(SubMulAction.ofStabilizer G α))).1
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥(SubMulAction.ofStabilizer G α))
    have h := index_stabilizer_of_transitive
      (G := ↥(stabilizer G α)) (X := ↥(SubMulAction.ofStabilizer G α)) (x := x)
    rw [hcard1] at h
    exact h ▸ Subgroup.index_dvd_card _
  -- `G` は非自明
  have hdvdG : Nat.card Ω ∣ Nat.card G :=
    (index_stabilizer_of_transitive (G := G) (x := α)) ▸ Subgroup.index_dvd_card _
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le hr.one_lt (hΩ ▸ Nat.le_of_dvd Nat.card_pos hdvdG))
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  haveI : IsPretransitive ↥N Ω := isPretransitive_of_normal_ne_bot_of_two_transitive h2 hNbot
  have hstabN : stabilizer ↥N α = ⊥ :=
    stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer α hsimple hNtop
  have hNcard : Nat.card ↥N = r := by
    rw [card_eq_card_of_stabilizer_eq_bot α hstabN, hΩ]
  haveI : IsCyclic ↥N := isCyclic_of_prime_card hNcard
  -- `G_α ↪ Aut(N)`
  set f : ↥(stabilizer G α) →* MulAut ↥N :=
    (MulAut.conjNormal (H := N)).comp (stabilizer G α).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hconj : ∀ n : ↥N, (c : G) * (n : G) * (c : G)⁻¹ = (n : G) := by
      intro n
      have := congrArg (fun φ => ((φ n : ↥N) : G)) hc
      simpa [hf, MulAut.conjNormal_apply] using this
    refine Subgroup.mem_bot.mpr (Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
      fun ω => ?_))
    rw [show ((1 : ↥(stabilizer G α)) : G) = 1 from rfl, one_smul]
    obtain ⟨n, hn⟩ := exists_smul_eq ↥N α ω
    have hn' : ((n : ↥N) : G) • α = ω := hn
    have hcomm : (c : G) * (n : G) = (n : G) * (c : G) := mul_inv_eq_iff_eq_mul.mp (hconj n)
    calc (c : G) • ω = ((c : G) * (n : G)) • α := by rw [← hn', mul_smul]
      _ = ((n : G) * (c : G)) • α := by rw [hcomm]
      _ = ω := by rw [mul_smul, mem_stabilizer_iff.mp c.2, hn']
  have hdvd2 : Nat.card ↥(stabilizer G α) ∣ r - 1 := by
    have hrange : Nat.card ↥(stabilizer G α) = Nat.card f.range :=
      (Nat.card_range_of_injective hfinj).symm
    rw [hrange]
    refine dvd_trans (Subgroup.card_subgroup_dvd_card _) ?_
    rw [IsCyclic.card_mulAut ↥N, hNcard, Nat.totient_prime hr]
  exact hne (Nat.dvd_antisymm hdvd2 hdvd1)

end -- 2-transitive で点安定化群が単純な作用

end OddOrder.Isaacs.Ch08
