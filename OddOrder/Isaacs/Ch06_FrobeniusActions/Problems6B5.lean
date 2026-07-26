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

**証明** (書籍 hint の経路; `|G|` に関する強帰納法):

1. 分割のどの部分にも含まれない真部分群 `H` には `{Y ⊓ H}` が分割として乗る
   (`restrictPartition`; `H ⊄ Y` ゆえ各部分が `H` の真部分群) ので帰納法で **`H` は冪零**。
2. すべての部分が `F(G)` に入るなら, 部分は `G` を被覆するので `G = F(G)` で冪零。
   よって `X ⊄ F(G)` なる部分 `X` が取れる。
3. `X` は冪零でない (冪零なら `isSubnormal_le_fitting_of_isNilpotent` で `X ≤ F(G)`)。
   `X < H < ⊤` なる `H` はどの部分にも含まれない (含まれれば `X` と一致してしまう) ので
   1 より冪零, すると部分群 `X` も冪零で矛盾。ゆえに **`X` は極大**。
   `X` は subnormal かつ真なので `X ≤ M ⊴ G`, `M < ⊤` が取れ, 極大性から **`X = M ⊴ G`**。
4. 他の部分 `Y` は `Y ⊓ X = ⊥` かつ極大性から `Y ⊔ X = ⊤`。`X` が正規なので
   任意の `1 ≠ y ∈ Y` について `⟨y⟩ ⊔ X = ⊤` となり `Y = ⟨y⟩` — つまり **`Y` は巡回**、
   ゆえに冪零で `Y ≤ F(G)`。
5. したがって `G = X ∪ F(G)` (集合として)。**群は二つの真部分群の合併にならない**
   (`le_or_le_of_forall_mem_or`) ので `X ≤ F(G)` か `F(G) ≤ X`, どちらも矛盾。

⭐ 当初考えていた Wielandt 補題 (subnormal + 交わり自明 ⟹ 可換) は**不要**だった。
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

/-- 群は二つの真部分群の合併にならない (どちらかが他方に含まれる)。 -/
theorem le_or_le_of_forall_mem_or {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ g : G, g ∈ A ∨ g ∈ B) : A ≤ B ∨ B ≤ A := by
  by_cases hAB : A ≤ B
  · exact Or.inl hAB
  refine Or.inr fun b hb => ?_
  by_contra hbA
  obtain ⟨a, haA, haB⟩ : ∃ a, a ∈ A ∧ a ∉ B := by
    by_contra hcon
    exact hAB fun a ha => by
      by_contra h'
      exact hcon ⟨a, ha, h'⟩
  rcases h (a * b) with hab | hab
  · refine hbA ?_
    have hb' : b = a⁻¹ * (a * b) := by group
    rw [hb']
    exact A.mul_mem (A.inv_mem haA) hab
  · refine haB ?_
    have ha' : a = (a * b) * b⁻¹ := by group
    rw [ha']
    exact B.mul_mem hab (B.inv_mem hb)

/-- **Isaacs Problem 6B.5** (p. 196) の帰納版 (`|G| = n` に関する強帰納法)。 -/
theorem isNilpotent_of_subnormal_partition_aux :
    ∀ (n : ℕ) {G : Type*} [Group G] [Finite G] (P : SubgroupPartition G),
      Nat.card G = n → (∀ X ∈ P.parts, X.IsSubnormal) → Group.IsNilpotent G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ P hcard hsub
  classical
  subst hcard
  -- 段 1: どの部分にも含まれない真部分群は冪零
  have step1 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ Y ∈ P.parts, ¬ H ≤ Y) → Group.IsNilpotent ↥H := by
    intro H hHtop hH
    have hlt : Nat.card ↥H < Nat.card G := by
      have hmul := Subgroup.card_mul_index H
      have h1 : H.index ≠ 1 := fun h => hHtop (Subgroup.index_eq_one.mp h)
      have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      calc Nat.card ↥H < Nat.card ↥H * H.index :=
            (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr (by omega)
        _ = Nat.card G := hmul
    exact ih (Nat.card ↥H) hlt (restrictPartition P hH) rfl
      (isSubnormal_restrictPartition_parts P hH hsub)
  -- 段 2: `F(G) = ⊤` なら終わり
  by_cases hftop : Ch01.fitting G = ⊤
  · haveI hfn : Group.IsNilpotent ↥(Ch01.fitting G) := Ch01.fitting.isNilpotent
    rw [hftop] at hfn
    exact Group.nilpotent_of_surjective (G := ↥(⊤ : Subgroup G))
      Subgroup.topEquiv.toMonoidHom (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  -- 段 3: `F(G)` に含まれない部分 `X` を取る
  by_cases hall : ∀ Y ∈ P.parts, Y ≤ Ch01.fitting G
  · exfalso
    refine hftop (eq_top_iff.mpr fun g _ => ?_)
    obtain ⟨Y, hY, hgY⟩ := P.cover g
    exact hall Y hY hgY
  obtain ⟨X, hX, hXf⟩ : ∃ X ∈ P.parts, ¬ X ≤ Ch01.fitting G := by
    by_contra hcon
    exact hall fun Y hY => by
      by_contra h'
      exact hcon ⟨Y, hY, h'⟩
  have hXtop : X ≠ ⊤ := P.proper X hX
  have hXnil : ¬ Group.IsNilpotent ↥X := fun hnil =>
    hXf (isSubnormal_le_fitting_of_isNilpotent (Nat.card G) X rfl (hsub X hX) hnil)
  -- 段 3': `X` は極大
  have hmax : ∀ H : Subgroup G, X < H → H = ⊤ := by
    intro H hXH
    by_contra hHtop
    have hHY : ∀ Y ∈ P.parts, ¬ H ≤ Y := by
      intro Y hY hle
      have hXY : X = Y := by
        by_contra hne
        have : X ⊓ Y = ⊥ := P.inf_eq_bot_of_ne hX hY hne
        have hXle : X ≤ X ⊓ Y := le_inf le_rfl (le_trans hXH.le hle)
        rw [this, le_bot_iff] at hXle
        exact P.nontrivial X hX hXle
      exact absurd (hXY ▸ hle : H ≤ X) (not_le_of_gt hXH)
    haveI := step1 H hHtop hHY
    refine hXnil ?_
    haveI : Group.IsNilpotent ↥(X.subgroupOf H) := inferInstance
    exact Group.nilpotent_of_surjective (G := ↥(X.subgroupOf H))
      (Subgroup.subgroupOfEquivOfLe hXH.le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXH.le).surjective
  -- 段 3'': `X ⊴ G` (subnormal + 極大)
  obtain ⟨M, hMn, hXM, hMlt⟩ := (hsub X hX).exists_normal_and_le_and_lt_top_of_ne hXtop
  have hXM' : X = M := by
    rcases lt_or_eq_of_le hXM with hlt | heq
    · exact absurd (hmax M hlt) (ne_of_lt hMlt)
    · exact heq
  haveI : X.Normal := hXM' ▸ hMn
  -- 段 4: 他の部分は `X` の補群ゆえ `F(G)` に入る
  have hother : ∀ Y ∈ P.parts, Y ≠ X → Y ≤ Ch01.fitting G := by
    intro Y hY hYX
    have hYX' : Y ⊓ X = ⊥ := P.inf_eq_bot_of_ne hY hX hYX
    obtain ⟨y, hyY, hy1⟩ : ∃ y : G, y ∈ Y ∧ y ≠ 1 := by
      by_contra hcon
      refine P.nontrivial Y hY (le_antisymm (fun x hx => ?_) bot_le)
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    have hSY : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hyY
    have hsupS : Subgroup.zpowers y ⊔ X = ⊤ := by
      refine hmax (Subgroup.zpowers y ⊔ X) (lt_of_le_of_ne le_sup_right fun h => ?_)
      have hSle : Subgroup.zpowers y ≤ X := by rw [h]; exact le_sup_left
      have hyYX : y ∈ Y ⊓ X := ⟨hyY, hSle (Subgroup.mem_zpowers y)⟩
      rw [hYX', Subgroup.mem_bot] at hyYX
      exact hy1 hyYX
    have hYS : Y = Subgroup.zpowers y := by
      refine le_antisymm (fun w hw => ?_) hSY
      have hwtop : w ∈ X ⊔ Subgroup.zpowers y := by
        rw [sup_comm, hsupS]; exact Subgroup.mem_top w
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hwtop
      obtain ⟨x, hx, t, ht, rfl⟩ := hwtop
      have hxY : x ∈ Y := by
        have heq : x = (x * t) * t⁻¹ := by group
        rw [heq]
        exact Y.mul_mem hw (Y.inv_mem (hSY ht))
      have hx1 : x ∈ Y ⊓ X := ⟨hxY, hx⟩
      rw [hYX', Subgroup.mem_bot] at hx1
      change x * t ∈ Subgroup.zpowers y
      rw [hx1, one_mul]
      exact ht
    haveI : IsCyclic ↥Y := hYS ▸ Subgroup.isCyclic_zpowers y
    letI : CommGroup ↥Y := IsCyclic.commGroup
    haveI : Group.IsNilpotent ↥Y := inferInstance
    exact isSubnormal_le_fitting_of_isNilpotent (Nat.card G) Y rfl (hsub Y hY) inferInstance
  -- 段 5: `G = X ∪ F(G)` で矛盾
  exfalso
  have hunion : ∀ g : G, g ∈ X ∨ g ∈ Ch01.fitting G := by
    intro g
    obtain ⟨Y, hY, hgY⟩ := P.cover g
    rcases eq_or_ne Y X with rfl | hne
    · exact Or.inl hgY
    · exact Or.inr (hother Y hY hne hgY)
  rcases le_or_le_of_forall_mem_or hunion with h | h
  · exact hXf h
  · exact hXtop (eq_top_iff.mpr fun g _ => by
      rcases hunion g with hg | hg
      · exact hg
      · exact h hg)

/-- **Isaacs Problem 6B.5** (p. 196) ⭐: subnormal 部分群からなる分割を持つ群は冪零。 -/
theorem isNilpotent_of_subnormal_partition {G : Type*} [Group G] [Finite G]
    (P : SubgroupPartition G) (hsub : ∀ X ∈ P.parts, X.IsSubnormal) :
    Group.IsNilpotent G :=
  isNilpotent_of_subnormal_partition_aux (Nat.card G) P rfl hsub

end

end OddOrder.Isaacs.Ch06
