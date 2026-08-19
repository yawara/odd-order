/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5D4

/-!
# Isaacs Problem 5D.3(a) — 単純群の極大 `p`-部分群は Sylow (書籍 pp. 169-170)

**主張 (a)**: `G` が非可換単純群で `P ≤ G` が極大部分群でもある `p`-部分群なら `P ∈ Syl_p(G)`。

**証明**: `P ≤ S` なる Sylow `p`-部分群 `S` を取る。`P < S` なら `p`-群の正規化群成長
(Isaacs Thm 1.22, `lt_normalizer_of_isNilpotent_of_lt_top`) で `P < N_S(P) ≤ N_G(P)`、
`P` は極大 (coatom) ゆえ `N_G(P) = ⊤`, すなわち `P ⊴ G`。単純性から `P = ⊥` か `P = ⊤`:

* `P = ⊤` は `P < S ≤ ⊤` に矛盾。
* `P = ⊥` なら `⊥ < S` と coatom 性から `S = ⊤`, すなわち `G` は `p`-群。しかし非自明な
  `p`-群の中心は非自明 (`IsPGroup.center_nontrivial`) で、単純性から `Z(G) = ⊤` ⟹ `G` 可換 —
  非可換の仮定に矛盾。

⟹ `P = S`。

⚠ (b) (`1 < N ⊴ P` で `P/N` 可換 ⟹ `P` は `N` を含む唯一の Sylow ⟹ `N` は weakly closed) と
(c) (`P` の冪零類 ≥ 3) は **Problem 5C.6 (weak closure)** に依存するので、hub レーンの
`OddOrder/GroupTheory/WeaklyClosed.lean` (issue 9503) が landing してから着手する。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5D.3(a): 単純群の極大 `p`-部分群は Sylow (p. 169) -/

/-- **Isaacs Problem 5D.3(a)** (p. 169) ⭐: 非可換単純群 `G` の極大部分群でもある
`p`-部分群 `P` は Sylow `p`-部分群である。 -/
theorem exists_sylow_coe_eq_of_isCoatom_of_isPGroup [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (hnonab : ∃ x y : G, x * y ≠ y * x)
    {P : Subgroup G} (hPp : IsPGroup p P) (hmax : IsCoatom P) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  classical
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : P < (S : Subgroup G) := lt_of_le_of_ne hPS (Ne.symm hne)
  -- `p`-群の正規化群成長で `P < N_G(P)`
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt_top : P.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun hle => hlt.ne (le_antisymm hlt.le hle)
  have hgrow := Ch01.lt_normalizer_of_isNilpotent_of_lt_top hlt_top
  rw [← Subgroup.subgroupOf_normalizer_eq hPS] at hgrow
  obtain ⟨y, hyN, hyP⟩ := SetLike.exists_of_lt hgrow
  have hyN' : (y : G) ∈ Subgroup.normalizer (P : Set G) := Subgroup.mem_subgroupOf.mp hyN
  have hyP' : (y : G) ∉ P := fun h => hyP (Subgroup.mem_subgroupOf.mpr h)
  have hPltN : P < Subgroup.normalizer (P : Set G) :=
    lt_of_le_of_ne Subgroup.le_normalizer fun heq => hyP' (heq ▸ hyN')
  have hPnormal : P.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (hmax.2 _ hPltN)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P hPnormal with hbot | htop
  · -- `P = ⊥` ⟹ `S = ⊤` ⟹ `G` は `p`-群 ⟹ 単純性で可換 ⟹ 矛盾
    have hStop : (S : Subgroup G) = ⊤ := hmax.2 _ (hbot ▸ hlt)
    have hGp : IsPGroup p G := by
      have hSp := S.isPGroup'
      rw [hStop] at hSp
      exact hSp.of_equiv Subgroup.topEquiv
    have hcenter : Nontrivial ↥(Subgroup.center G) := hGp.center_nontrivial
    have hZtop : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
      · rw [h] at hcenter
        obtain ⟨a, b, hab⟩ := hcenter.exists_pair_ne
        exact absurd (Subtype.ext
          ((Subgroup.mem_bot.mp a.2).trans (Subgroup.mem_bot.mp b.2).symm)) hab
      · exact h
    obtain ⟨x, y', hxy⟩ := hnonab
    exact hxy (Subgroup.mem_center_iff.mp (hZtop.ge (Subgroup.mem_top y')) x)
  · exact absurd (le_top : (S : Subgroup G) ≤ ⊤) (not_le_of_gt (htop ▸ hlt))

end

end OddOrder.Isaacs.Ch05
