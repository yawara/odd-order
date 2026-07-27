/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.PointStabilizers
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuEleven

/-!
# Isaacs Problem 8C.3 (p. 256) — 次数 12, 位数 95040 の推移置換群は単純

`Ω` を 12 点集合, `G` を `Ω` 上忠実かつ推移的に作用する位数
`95040 = 12·11·10·9·8` の群とすると `G` は単純。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₂` に同型。

## 証明の流れ (Isaacs のヒント)

1. 点安定化群 `G_α` は位数 `7920` で `Ω ∖ {α}` (11 点) に忠実に作用する。Sylow
   `11`-部分群が regular なので `G_α` は `Ω ∖ {α}` に推移的, すなわち `G` は
   **2-transitive**。さらに **Problem 8C.2** より `G_α` は**単純**。
2. `1 ≠ N ◁ G` なら `N ∩ G_α ◁ G_α` は `1` か `G_α`。後者なら `G_α ≤ N` と
   `N` の推移性 (**Problem 8A.9**) から `N = G`。よって `N ∩ G_α = 1`,
   つまり `N` は **regular** (`|N| = 12`)。
3. `N` が regular だと `n ↦ n • α` が `N ≃ Ω` を与え, 2-transitivity から
   `N ∖ {1}` の元はすべて `G` で共役 — 位数が等しくなければならない。しかし
   `|N| = 12` は位数 2 と位数 3 の元をともにもつ (Cauchy)。矛盾。
   (Isaacs の「位数 12 の群は極小正規部分群になり得ない」に対応。)

## Main results

- `isSimpleGroup_of_card_eq_95040` — **Problem 8C.3** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 点安定化群の補集合への作用 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- 点安定化群 `G_α` の `Ω ∖ {α}` への作用は忠実。 -/
theorem faithfulSMul_ofStabilizer (α : Ω) :
    FaithfulSMul ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) := by
  refine ⟨fun {g h} hgh => ?_⟩
  refine Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => ?_)
  rcases eq_or_ne β α with rfl | hβ
  · rw [mem_stabilizer_iff.mp g.2, mem_stabilizer_iff.mp h.2]
  · exact congrArg Subtype.val
      (hgh ⟨β, (SubMulAction.mem_ofStabilizer_iff G α).mpr hβ⟩)

omit [FaithfulSMul G Ω] in
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

end -- 点安定化群の補集合への作用

section /- Problem 8C.3 本体 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- **Isaacs Problem 8C.3** (p. 256)。次数 12, 位数 `95040 = 12·11·10·9·8` の
**推移**置換群は単純。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₂` に同型。 -/
theorem isSimpleGroup_of_card_eq_95040 [IsPretransitive G Ω]
    (hΩ : Nat.card Ω = 12) (hG : Nat.card G = 95040) :
    IsSimpleGroup G := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- (1) 点安定化群は位数 7920
  have hstabcard : ∀ α : Ω, Nat.card ↥(stabilizer G α) = 7920 := by
    intro α
    have h := index_stabilizer_of_transitive (G := G) (x := α)
    rw [hΩ] at h
    have h2 := Subgroup.card_mul_index (stabilizer G α)
    rw [h, hG] at h2
    omega
  -- 点安定化群は `Ω ∖ {α}` に忠実・推移的に作用し, さらに単純 (Problem 8C.2)
  have hcard11 : ∀ α : Ω, Nat.card ↥(SubMulAction.ofStabilizer G α) = 11 := by
    intro α
    rw [card_ofStabilizer, hΩ]
  have htrans : ∀ α : Ω,
      IsPretransitive ↥(stabilizer G α) ↥(SubMulAction.ofStabilizer G α) := by
    intro α
    haveI := faithfulSMul_ofStabilizer (G := G) α
    obtain ⟨S⟩ := Sylow.nonempty (p := 11) (G := ↥(stabilizer G α))
    have hS : Nat.card (S : Subgroup ↥(stabilizer G α)) = 11 :=
      card_sylow_eq_prime_of_not_dvd_sq S (by rw [hstabcard α]; norm_num)
        (by rw [hstabcard α]; norm_num)
    haveI := isPretransitive_of_card_eq_prime (by norm_num) (hcard11 α) _ hS
    refine ⟨fun a b => ?_⟩
    obtain ⟨s, hs⟩ := exists_smul_eq ↥(S : Subgroup ↥(stabilizer G α)) a b
    exact ⟨s, hs⟩
  have hsimple : ∀ α : Ω, IsSimpleGroup ↥(stabilizer G α) := by
    intro α
    haveI := faithfulSMul_ofStabilizer (G := G) α
    exact isSimpleGroup_of_card_eq_7920 (hcard11 α) (hstabcard α)
  -- (2) `G` は 2-transitive (Problem 8A.9 が要求する形)
  have h2 : ∀ α β γ : Ω, β ≠ α → γ ≠ α → ∃ g : G, g • α = α ∧ g • β = γ := by
    intro α β γ hβ hγ
    haveI := htrans α
    obtain ⟨g, hg⟩ := exists_smul_eq ↥(stabilizer G α)
      (⟨β, (SubMulAction.mem_ofStabilizer_iff G α).mpr hβ⟩ :
        ↥(SubMulAction.ofStabilizer G α))
      ⟨γ, (SubMulAction.mem_ofStabilizer_iff G α).mpr hγ⟩
    exact ⟨(g : G), mem_stabilizer_iff.mp g.2, congrArg Subtype.val hg⟩
  -- (3) 単純性
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  haveI hneΩ : Nonempty Ω := (Nat.card_pos_iff.mp (by omega)).1
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  obtain ⟨α⟩ := hneΩ
  -- `N` は非自明に作用するので推移的 (Problem 8A.9)
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
  haveI hNtrans : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_two_transitive h2 hx
  -- `N ∩ G_α` は `G_α` の正規部分群なので `1` か `G_α`
  haveI := hsimple α
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (stabilizer G α))
    inferInstance with hbot | htop
  · -- `N` は semiregular, 推移性から regular: `|N| = 12`
    have hstabN : stabilizer ↥N α = ⊥ := by
      have hdisj : Disjoint N (stabilizer G α) := Subgroup.subgroupOf_eq_bot.mp hbot
      have : (stabilizer G α).subgroupOf N = ⊥ :=
        Subgroup.subgroupOf_eq_bot.mpr hdisj.symm
      rw [← this]
      ext y
      rfl
    have hNcard : Nat.card ↥N = 12 := by
      have h := index_stabilizer_of_transitive (G := ↥N) (x := α)
      rw [hΩ, hstabN, Subgroup.index_bot] at h
      exact h
    -- `m ↦ m • α` は単射
    have hinj : ∀ u v : ↥N, (u : G) • α = (v : G) • α → u = v := by
      intro u v huv
      have : v⁻¹ * u ∈ stabilizer ↥N α := by
        rw [mem_stabilizer_iff]
        change ((v⁻¹ * u : ↥N) : G) • α = α
        rw [Subgroup.coe_mul, mul_smul, huv, Subgroup.coe_inv, inv_smul_smul]
      rw [hstabN, Subgroup.mem_bot] at this
      exact (inv_mul_eq_one.mp this).symm
    have hne : ∀ u : ↥N, u ≠ 1 → (u : G) • α ≠ α := by
      intro u hu hc
      refine hu (hinj u 1 ?_)
      rw [hc, Subgroup.coe_one, one_smul]
    -- `N ∖ {1}` の元はすべて `G` で共役
    have hconj : ∀ u v : ↥N, u ≠ 1 → v ≠ 1 →
        ∃ g : G, g * (u : G) * g⁻¹ = (v : G) := by
      intro u v hu hv
      obtain ⟨g, hgα, hgβ⟩ := h2 α ((u : G) • α) ((v : G) • α) (hne u hu) (hne v hv)
      refine ⟨g, ?_⟩
      have hmem : g * (u : G) * g⁻¹ ∈ N := hN.conj_mem (u : G) u.2 g
      have hact : ((⟨g * (u : G) * g⁻¹, hmem⟩ : ↥N) : G) • α = (v : G) • α := by
        have hginv : g⁻¹ • α = α := inv_smul_eq_iff.mpr hgα.symm
        change (g * (u : G) * g⁻¹) • α = (v : G) • α
        rw [mul_smul, mul_smul, hginv, hgβ]
      exact congrArg Subtype.val (hinj ⟨g * (u : G) * g⁻¹, hmem⟩ v hact)
    -- 位数 2 と位数 3 の元がともに存在するので矛盾
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [hNcard]; norm_num)
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 (by rw [hNcard]; norm_num)
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
    obtain ⟨g, hg⟩ := hconj a b ha1 hb1
    have hoa : orderOf ((a : G)) = 2 := by rw [Subgroup.orderOf_coe, ha]
    have hob : orderOf ((b : G)) = 3 := by rw [Subgroup.orderOf_coe, hb]
    have hconjord : orderOf (g * (a : G) * g⁻¹) = orderOf ((a : G)) :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
    rw [hg, hob, hoa] at hconjord
    omega
  · -- `G_α ≤ N` と `N` の推移性から `N = G`
    refine hNtop (eq_top_iff.mpr fun g _ => ?_)
    have hle : stabilizer G α ≤ N := by
      intro y hy
      have : (⟨y, hy⟩ : ↥(stabilizer G α)) ∈ N.subgroupOf (stabilizer G α) := by
        rw [htop]; trivial
      exact this
    obtain ⟨m, hm⟩ := exists_smul_eq ↥N α (g • α)
    have hm' : ((m : ↥N) : G) • α = g • α := hm
    have hmem : (m : G)⁻¹ * g ∈ stabilizer G α := by
      rw [mem_stabilizer_iff, mul_smul, ← hm', inv_smul_smul]
    have : g = (m : G) * ((m : G)⁻¹ * g) := by group
    rw [this]
    exact N.mul_mem m.2 (hle hmem)

end -- Problem 8C.3

end OddOrder.Isaacs.Ch08
