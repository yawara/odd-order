/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.Isaacs.Ch02_Subnormality.Main

/-!
# BG §3D: toward Theorem 3.7 (Frobenius kernel nilpotency)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_, Ch. I §3D,
mmd `references/bg/local-analysis.mmd` L1199-1219. plan = `notes/bg/s03_thm37_plan.md`.

Thm 3.7 の chief-factor 解析の **same-prime case** をここで証明する (group-theoretic,
BG の「K̄ ⊆ O_q(Ḡ) acts trivially」を回避): 有限群の正規 `q`-部分群 `K` は、任意の
minimal-normal `q`-部分群 `V` を中心化する。`q`-群 `K ⊔ V` 内で非自明正規部分群 `V` が
中心と交わること (`exists_mem_center_of_normal_ne_bot`) を使う。
-/

namespace OddOrder.BG.Ch1.S03c

open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

/-- **Same-prime case** of BG Thm 3.7's chief-factor analysis: a normal `q`-subgroup `K` of a
finite group `H` centralizes every minimal-normal `q`-subgroup `V`.

Proof: `K ⊔ V` is a `q`-group in which `V` is a nontrivial normal subgroup, so `V` meets the
center (`exists_mem_center_of_normal_ne_bot`), giving a nonidentity element of `V` that
centralizes `K`. Thus `V ⊓ C_H(K)` is a nonzero normal subgroup `≤ V`, hence `= V` by
minimality, i.e. `V ≤ C_H(K)`, i.e. `⁅K, V⁆ = ⊥`. -/
theorem commutator_eq_bot_of_normal_pgroup_minimalNormal {q : ℕ} [Fact q.Prime]
    {K V : Subgroup H} [K.Normal] (hK : IsPGroup q K) (hV : IsPGroup q V)
    (hVmin : OddOrder.Isaacs.Ch02.IsMinimalNormal V) :
    ⁅K, V⁆ = ⊥ := by
  haveI hVnorm : V.Normal := hVmin.1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
  -- goal: `V ≤ centralizer K`
  haveI : (Subgroup.centralizer (K : Set H)).Normal := Subgroup.normal_centralizer
  have hCne : V ⊓ Subgroup.centralizer (K : Set H) ≠ ⊥ := by
    have hKV : IsPGroup q (K ⊔ V : Subgroup H) := hK.to_sup_of_normal_left hV
    haveI : (V.subgroupOf (K ⊔ V)).Normal := Subgroup.normal_subgroupOf
    have hV'ne : V.subgroupOf (K ⊔ V) ≠ ⊥ := by
      rw [Ne, Subgroup.subgroupOf_eq_bot]
      exact fun hdisj => hVmin.2.1 (hdisj.eq_bot_of_le le_sup_right)
    obtain ⟨x, hxV', hxZ, hxne⟩ :=
      OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hKV hV'ne
    refine fun hbot => hxne ?_
    have hxV : (x : H) ∈ V := Subgroup.mem_subgroupOf.mp hxV'
    have hxC : (x : H) ∈ Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hc := Subgroup.mem_center_iff.mp hxZ ⟨k, Subgroup.mem_sup_left hk⟩
      have := congrArg (Subgroup.subtype (K ⊔ V)) hc
      simpa using this
    have hxmem : (x : H) ∈ V ⊓ Subgroup.centralizer (K : Set H) := ⟨hxV, hxC⟩
    rw [hbot, Subgroup.mem_bot] at hxmem
    exact Subtype.ext hxmem
  haveI hCnorm : (V ⊓ Subgroup.centralizer (K : Set H)).Normal := inferInstance
  rcases hVmin.2.2 (V ⊓ Subgroup.centralizer (K : Set H)) hCnorm inf_le_left with h | h
  · exact absurd h hCne
  · rw [← h]; exact inf_le_right

end OddOrder.BG.Ch1.S03c
