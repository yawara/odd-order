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
