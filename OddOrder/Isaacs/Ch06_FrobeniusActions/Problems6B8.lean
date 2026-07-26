/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B7

/-!
# Isaacs Problem 6B.8 — Taussky-Todd (書籍 p. 196)

**主張**: `|P| ≥ 8` の `2`-群 `P` が `|P : P'| = 4` をみたすなら, `P` は二面体群・半二面体群・
一般四元数群のいずれか (O. Taussky-Todd の定理)。

**書籍 hint の筋** (`|P|` に関する帰納法):

1. `Z ≤ P' ⊓ Z(P)` で `|Z| = 2` なるものを取る (`P` は `2`-群で `P' ≠ 1` なので
   `P' ⊓ Z(P)` は非自明 — `IsPGroup.normal_inf_center_nontrivial`)。
2. `(P/Z)' = P'/Z` なので `|P/Z : (P/Z)'| = |P : P'| = 4` が保たれる。`|P/Z| = |P|/2`。
3. 帰納法で `P/Z` が二面体・半二面体・一般四元数, とくに**指数 2 の巡回部分群を持つ**。
   その引き戻し `A ≤ P` は指数 2 で `A/Z` 巡回, `Z ≤ Z(P)` なので **`A` は可換**。
4. `A` は巡回か `Z × (巡回)`。前者なら **6B.7** (`|P : Z(P)| > 4` を確認して) で終わり。
   後者で `|P| > 16` なら `Z < Z(P)` が出て矛盾。

現状はステップ 1 を実証明で提供し, 主定理は statement のみ。
-/

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

section /- 6B.8: Taussky-Todd (p. 196) -/

/-- **書籍 hint のステップ 1**: 非可換な有限 `2`-群 `P` には `P' ⊓ Z(P)` の中に位数 `2` の
元が取れる。

`P'` は非自明な正規部分群なので `IsPGroup.normal_inf_center_nontrivial` で `P' ⊓ Z(P)` が
非自明。その非単位元 `x` は位数 `2^k` (`k ≥ 1`) なので `x ^ (2^(k-1))` が位数 `2`。 -/
theorem exists_orderOf_eq_two_mem_commutator_center {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcomm : (commutator P) ≠ ⊥) :
    ∃ z : P, z ∈ commutator P ∧ z ∈ Subgroup.center P ∧ orderOf z = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnt : Nontrivial ↥(commutator P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hcomm
  have hK := Ch01.IsPGroup.normal_inf_center_nontrivial hP (N := commutator P) hnt
  obtain ⟨⟨x, hx⟩, hxne⟩ := exists_ne (1 : ↥(commutator P ⊓ Subgroup.center P))
  have hxP : x ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) x
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero] at hk
      exact absurd (orderOf_eq_one_iff.mp hk) hxP
    · exact h
  refine ⟨x ^ (2 ^ (k - 1)), Subgroup.pow_mem _ hx.1 _, Subgroup.pow_mem _ hx.2 _, ?_⟩
  rw [orderOf_pow, hk]
  have hdvd : (2 : ℕ) ^ (k - 1) ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  rw [Nat.gcd_eq_right hdvd]
  have hsplit : (2 : ℕ) ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [hsplit, Nat.mul_div_cancel_left _ (by positivity)]

/-- **書籍 hint のステップ 2**: `Z ⊴ P` が `Z ≤ P'` をみたすなら剰余群で指数が保たれる:
`|P/Z : (P/Z)'| = |P : P'|`。

`(P/Z)' = P'/Z` (全射準同型で交換子群は像に写る) と, 核を含む部分群の指数が像で保たれる
ことから。帰納法が回る鍵。 -/
theorem index_commutator_quotient {P : Type*} [Group P] {Z : Subgroup P} [Z.Normal]
    (hZ : Z ≤ commutator P) :
    (commutator (P ⧸ Z)).index = (commutator P).index := by
  have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hmap : commutator (P ⧸ Z) = (commutator P).map (QuotientGroup.mk' Z) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj]
  rw [hmap]
  exact Subgroup.index_map_eq _ hsurj (by rwa [QuotientGroup.ker_mk'])

/-- **Isaacs Problem 6B.8** (p. 196, O. Taussky-Todd) ⭐: `|P| ≥ 8` の `2`-群 `P` が
`|P : P'| = 4` をみたすなら, `P` は二面体・半二面体・一般四元数のいずれか。 -/
theorem tausskyTodd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    (∃ n : ℕ, Nonempty (P ≃* DihedralGroup n)) ∨
      (∃ n : ℕ, Nonempty (P ≃* QuaternionGroup n)) ∨
      (∃ k : ℕ, Nonempty (P ≃* SemiDihedralGroup k)) := by
  sorry

end

end OddOrder.Isaacs.Ch06
