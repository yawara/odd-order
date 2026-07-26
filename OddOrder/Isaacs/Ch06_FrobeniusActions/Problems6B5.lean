/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B4

/-!
# Isaacs Problem 6B.5 — subnormal 部分群からなる分割を持つ群は冪零 (書籍 p. 196)

**主張**: 群 `G` が subnormal 部分群からなる分割を持つなら `G` は冪零。

**本形式化の経路** (書籍の hint とは別ルート; 6B.4 が使える):

1. **Wielandt**: subnormal 部分群 `H`, `K` が `H ⊓ K = ⊥` をみたせば `⁅H, K⁆ = ⊥`。
2. 分割の相異なる部分は `SubgroupPartition.inf_eq_bot_of_ne` で交わりが自明なので, 1 から
   **互いに可換**。
3. **6B.4(a)** (`mul_comm_of_partition_of_commutator_eq_bot`) で `G` は可換, ゆえに冪零。
   (6B.4(b) を併せると `G` は基本可換までわかる。)

書籍の hint (「分割のどの部分にも含まれない `H < G` は冪零」→「`F(G)` に含まれない部分は
正規で素数指数」) は 1 を経由しない別証明。

⚠ ステップ 1 の Wielandt 補題は古典的だが証明が長い (subnormal 部分群の join の理論)。
現状は statement のみ (`sorry`) で, 2-3 の還元は実証明済み。
一般補題なので, 証明が入った時点で `OddOrder/Isaacs/Ch02_Subnormality/` 側へ移設してよい
(既存の normal 版は `Ch02_Subnormality/Basic.lean` の `commute_of_disjoint_normal`)。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.5: subnormal 分割 (p. 196) -/

/-- **Isaacs Ch.2**: `F(G)` は subnormal な冪零部分群をすべて含む。

`|G|` に関する帰納法: `H ≠ ⊤` なら `H ≤ M ⊴ G`, `M < ⊤` を取り, `M` の中で帰納法を使って
`H ≤ F(M)`。`F(M)` は `M` の特性部分群ゆえ `G` で正規かつ冪零なので `F(M) ≤ F(G)`
(`fitting_map_subtype_le_fitting`)。

repo にあった可換版 (Isaacs Thm 2.11, `Ch02_Subnormality/Theorem211Wielandt.lean`) の
冪零版にあたる汎用補題。 -/
theorem isSubnormal_le_fitting_of_isNilpotent :
    ∀ (n : ℕ) {G : Type*} [Group G] [Finite G] (H : Subgroup G),
      Nat.card G = n → H.IsSubnormal → Group.IsNilpotent ↥H → H ≤ Ch01.fitting G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ H hcard hsub hnil
  classical
  rcases eq_or_ne H ⊤ with rfl | hne
  · haveI := hnil
    exact Ch01.nilpotent_normal_le_fitting
  obtain ⟨M, hMnormal, hHM, hMlt⟩ := hsub.exists_normal_and_le_and_lt_top_of_ne hne
  haveI := hMnormal
  have hMcard : Nat.card ↥M < n := by
    subst hcard
    have hmul := Subgroup.card_mul_index M
    have h1 : M.index ≠ 1 := fun h => (ne_of_lt hMlt) (Subgroup.index_eq_one.mp h)
    have h0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    calc Nat.card ↥M < Nat.card ↥M * M.index :=
          (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr (by omega)
      _ = Nat.card G := hmul
  have hsubM : (H.subgroupOf M).IsSubnormal := hsub.subgroupOf
  have hnilM : Group.IsNilpotent ↥(H.subgroupOf M) :=
    Group.nilpotent_of_surjective (G := ↥H)
      (Subgroup.subgroupOfEquivOfLe hHM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHM).symm.surjective
  have hle := ih (Nat.card ↥M) hMcard (H.subgroupOf M) rfl hsubM hnilM
  have hmap : H = (H.subgroupOf M).map M.subtype := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype, inf_eq_right.mpr hHM]
  rw [hmap]
  exact le_trans (Subgroup.map_mono hle) Ch01.fitting_map_subtype_le_fitting

/-- 分割のどの部分にも含まれない部分群 `H` には, `{(Y ⊓ H) ∩ H : Y ∈ Π}` が
**`H` の分割として乗る** (各部分が `H` の真部分群になるのが `H ⊄ Y` の効き所)。

書籍 hint の第一段「分割のどの部分にも含まれない `H < G` は冪零」の土台。 -/
noncomputable def restrictPartition {G : Type*} [Group G] (P : SubgroupPartition G)
    {H : Subgroup G} (hH : ∀ Y ∈ P.parts, ¬ H ≤ Y) : SubgroupPartition ↥H := by
  classical
  refine
    { parts := (P.parts.image fun Y => (Y ⊓ H).subgroupOf H).filter fun Z => Z ≠ ⊥
      nontrivial := fun X hX => (Finset.mem_filter.mp hX).2
      proper := ?_
      cover := ?_
      inf_eq_bot_of_ne := ?_ }
  · rintro X hX htop
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hX).1
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hH Y hY (le_trans htop inf_le_left)
  · -- `H ≠ ⊥` (さもないと `H ≤ Y` になってしまう) なので非自明な部分が必ず取れる
    have hHne : ∃ h : G, h ∈ H ∧ h ≠ 1 := by
      by_contra hcon
      obtain ⟨Y, hY, _⟩ := P.cover (1 : G)
      refine hH Y hY fun x hx => ?_
      have : x = 1 := by
        by_contra hx1
        exact hcon ⟨x, hx, hx1⟩
      rw [this]
      exact Y.one_mem
    intro g
    rcases eq_or_ne (g : G) 1 with hg1 | hg1
    · obtain ⟨h, hhH, hh1⟩ := hHne
      obtain ⟨Y, hY, hhY⟩ := P.cover h
      have hgone : g = 1 := Subtype.ext hg1
      refine ⟨(Y ⊓ H).subgroupOf H, Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ hY, ?_⟩, hgone ▸ Subgroup.one_mem _⟩
      intro hbot
      have hmem : (⟨h, hhH⟩ : ↥H) ∈ (Y ⊓ H).subgroupOf H := ⟨hhY, hhH⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hh1 (congrArg Subtype.val hmem)
    · obtain ⟨Y, hY, hgY⟩ := P.cover (g : G)
      refine ⟨(Y ⊓ H).subgroupOf H, Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ hY, ?_⟩, ⟨hgY, g.2⟩⟩
      intro hbot
      have hmem : g ∈ (Y ⊓ H).subgroupOf H := ⟨hgY, g.2⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hg1 (congrArg Subtype.val hmem)
  · intro X X' hX hX' hne
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hX).1
    obtain ⟨Y', hY', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hX').1
    have hYY' : Y ≠ Y' := fun h => hne (by rw [h])
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf]
    have : Y ⊓ H ⊓ (Y' ⊓ H) = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      have : x ∈ Y ⊓ Y' := ⟨hx.1.1, hx.2.1⟩
      rwa [P.inf_eq_bot_of_ne hY hY' hYY'] at this
    rw [this]
    simp

/-- `restrictPartition` の各部分も subnormal。 -/
theorem isSubnormal_restrictPartition_parts {G : Type*} [Group G] (P : SubgroupPartition G)
    {H : Subgroup G} (hH : ∀ Y ∈ P.parts, ¬ H ≤ Y) (hsub : ∀ Y ∈ P.parts, Y.IsSubnormal) :
    ∀ Z ∈ (restrictPartition P hH).parts, Z.IsSubnormal := by
  classical
  intro Z hZ
  simp only [restrictPartition, Finset.mem_filter, Finset.mem_image] at hZ
  obtain ⟨⟨Y, hY, rfl⟩, _⟩ := hZ
  exact Ch02.inf_isSubnormal_subgroupOf (hsub Y hY) H

/-- **Wielandt**: 交わりが自明な二つの subnormal 部分群は元ごとに可換。

`H` が正規な場合は `⁅H, K⁆ ≤ H ⊓ K^G` から従うが, subnormal な場合は
`H^G`, `K^G` が真の正規部分群であることを使う `|G|`-帰納法が要る。 -/
theorem commutator_eq_bot_of_isSubnormal_of_inf_eq_bot {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hH : H.IsSubnormal) (hK : K.IsSubnormal) (hHK : H ⊓ K = ⊥) :
    ⁅H, K⁆ = ⊥ := by
  sorry

/-- **Isaacs Problem 6B.5** (p. 196) ⭐: subnormal 部分群からなる分割を持つ群は冪零。

実際には (6B.4 経由で) **可換**であることまで従う。 -/
theorem isNilpotent_of_subnormal_partition {G : Type*} [Group G] [Finite G]
    (P : SubgroupPartition G) (hsub : ∀ X ∈ P.parts, X.IsSubnormal) :
    Group.IsNilpotent G := by
  have hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥ := fun X hX Y hY hne =>
    commutator_eq_bot_of_isSubnormal_of_inf_eq_bot (hsub X hX) (hsub Y hY)
      (P.inf_eq_bot_of_ne hX hY hne)
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := mul_comm_of_partition_of_commutator_eq_bot P hcomm }
  infer_instance

end

end OddOrder.Isaacs.Ch06
