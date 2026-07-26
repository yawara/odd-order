/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient

/-!
# Isaacs Problem 6B.1 — Frobenius 補群は Frobenius 群を含まない (書籍 p. 195)

**主張**: 任意の Frobenius 群は**可解**な Frobenius 部分群を含む。したがって Frobenius 補群
(= Frobenius 作用の作用側) は Frobenius 群を部分群として持てない。

**構成**:

* **前半** `exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup`:
  Frobenius 群 `G` (核 `N`, 補群 `A`) から素数位数 `p` の元 `y ∈ A` を取り, `⟨y⟩` 不変な
  非自明可換部分群 `M ≤ N` を取る (Isaacs Thm 3.23 経由の既存 API)。`M⟨y⟩` は可解
  (可換 `M` の上に巡回商) な Frobenius 群。
* **後半** `false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup`:
  Frobenius 補群 `A` の部分群 `B` が Frobenius 群なら, 前半で得た可解 Frobenius 部分群を
  `A` の部分群へ移して (`IsFrobeniusGroup.mapEquiv`), **Isaacs Thm 6.9 の可解分岐**
  `false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup` に流し込むと矛盾。

書籍が「deduce」と書いているのはこの合成のこと — 可解性の仮定は前半で外れる。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.1: 可解 Frobenius 部分群 (p. 195) -/

/-- **Isaacs Problem 6B.1 の前半** (p. 195): 任意の有限 Frobenius 群は**可解**な Frobenius
部分群を含む。

素数位数の元 `y` を補群 `A` から取り, `⟨y⟩` 不変な非自明可換部分群 `M ≤ N` に対し `M⟨y⟩` を
とればよい。 -/
theorem exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G} (hF : IsFrobeniusGroup G N A) :
    ∃ (H : Subgroup G) (K L : Subgroup ↥H), IsSolvable ↥H ∧ IsFrobeniusGroup ↥H K L := by
  sorry

/-- **Isaacs Problem 6B.1 の後半** (p. 195) ⭐: Frobenius 補群は Frobenius 群を部分群として
持てない (可解性の仮定なし)。

`false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup` (Isaacs Thm 6.9 の
可解分岐) の可解仮定を, 前半の「可解 Frobenius 部分群の存在」で除去したもの。 -/
theorem false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) {N C : Subgroup ↥B} (hGroup : IsFrobeniusGroup ↥B N C) :
    False := by
  obtain ⟨H, K, L, hHsol, hHF⟩ := exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup hGroup
  have e : ↥H ≃* ↥(H.map B.subtype) :=
    Subgroup.equivMapOfInjective H B.subtype (Subgroup.subtype_injective B)
  haveI := hHsol
  haveI : IsSolvable ↥(H.map B.subtype) :=
    solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  exact false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup hFrob
    (H.map B.subtype) (hHF.mapEquiv e)

end

end OddOrder.Isaacs.Ch06
