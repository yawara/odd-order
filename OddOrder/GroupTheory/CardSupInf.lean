/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring

/-!
# 第二同型定理の位数式

`OddOrder.GroupTheory` shared module (**mathlib のみに依存する最上流**):

* `card_sup_mul_card_inf_eq` — `N` 正規なら `|H ⊔ N| · |H ⊓ N| = |H| · |N|`
* `card_sup_eq_mul_of_disjoint_normal` — さらに `H ⊓ N = ⊥` なら `|H ⊔ N| = |H| · |N|`

本 leaf は mathlib しか import しないので全ての下流から使える。

⚠ 重複の状況 (issue 9209): `OddOrder/GroupTheory/CNGroupStructure.lean` にあった同名 public
定理は **2026-08-06 に削除**し、同ファイルは本 leaf を import するようにした (`ThreeStepGroup`
が本 leaf を import した時点で名前衝突してビルドが落ちたため)。残るは
`OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean` の `private` 版 2 つ
(`private` なので衝突しない) と `Ch03_SplitExtensions/Problems3B.lean` のインライン 2 か所。
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **第二同型定理 (位数版)**: `N` が正規なら `|H ⊔ N| · |H ⊓ N| = |H| · |N|`。 -/
theorem card_sup_mul_card_inf_eq [Finite G] (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
  have h1 : Nat.card ↥H =
      Nat.card (↥H ⧸ (N.subgroupOf H)) * Nat.card ↥(N.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥(H ⊔ N) =
      Nat.card (↥(H ⊔ N) ⧸ (N.subgroupOf (H ⊔ N))) * Nat.card ↥(N.subgroupOf (H ⊔ N)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H ⊓ N) :=
    Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have h5 : Nat.card (↥H ⧸ (N.subgroupOf H)) =
      Nat.card (↥(H ⊔ N) ⧸ (N.subgroupOf (H ⊔ N))) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
  rw [h2, h3, ← h4, ← h5, h1]
  ring

/-- `N` 正規かつ `H ⊓ N = ⊥` なら `|H ⊔ N| = |H| · |N|`。 -/
theorem card_sup_eq_mul_of_disjoint_normal [Finite G] {H N : Subgroup G} [N.Normal]
    (hdisj : H ⊓ N = ⊥) : Nat.card ↥(H ⊔ N) = Nat.card ↥H * Nat.card ↥N := by
  have h := card_sup_mul_card_inf_eq H N
  rw [hdisj, Subgroup.card_bot, mul_one] at h
  exact h

/-- `H ≤ K` なら `|H| ∣ |K|` (ラグランジュ)。 -/
theorem card_dvd_card_of_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥H ∣ Nat.card ↥K := by
  have hd := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at hd

end OddOrder.GroupTheory
