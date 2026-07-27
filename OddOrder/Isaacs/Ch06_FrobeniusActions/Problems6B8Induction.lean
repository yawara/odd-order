/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B8

/-!
# Isaacs Problem 6B.8 — 帰納法本体と主定理の組み立て (書籍 p. 196)

`Problems6B8.lean` の部品を使って **Taussky-Todd の定理**を完成させる。

**帰納する命題** (書籍 hint の帰納法を「指数 `2` の巡回部分群の存在」に差し替えたもの):

> `P` が `2`-群, `|P| ≥ 8`, `|P : P'| = 4` ⟹ `∃ c, |P : ⟨c⟩| = 2`

* **base (`|P| = 8`)**: 非可換な位数 `8` の群には位数 `4` の元がある
  (`exists_index_two_zpowers_of_card_eight`)。
* **step (`|P| ≥ 16`)**: `Z ≤ P' ⊓ Z(P)` で `|Z| = 2` なるものを取ると
  `|P/Z : (P/Z)'| = 4`, `|P/Z| = |P|/2 ≥ 8` なので帰納法で `P/Z` に指数 `2` の
  巡回部分群 `⟨c̄⟩` がある。その引き戻し `A` は指数 `2` で `Z ≤ Z(P)` から**可換**,
  さらに `isCyclic_of_index_two_of_index_commutator_eq_four` で**巡回**。

こうして得た `⟨c⟩` に **6B.7** (`|P : Z(P)| > 4` は `four_lt_index_center`) を適用すると
`P` は二面体・半二面体・一般四元数のいずれかになる。書籍 hint が経由する
「`P/Z` が D/SD/Q だからその指数 `2` の巡回部分群を引き戻す」という段を避けられるので,
具体群 D/SD/Q の構造 (指数 `2` の巡回部分群を持つこと) を証明せずに済む。
-/

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

universe u

section /- 6B.8: Taussky-Todd の帰納法 (p. 196) -/

/-- 中心に含まれる部分群は正規。 -/
theorem normal_of_le_center {P : Type*} [Group P] {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) : Z.Normal where
  conj_mem n hn g := by
    have hc := Subgroup.mem_center_iff.mp (hZ hn) g
    have hfix : g * n * g⁻¹ = n := by rw [hc]; group
    rw [hfix]
    exact hn

/-- `|P : P'| = 4` かつ `|P| ≥ 8` なら `P` は非可換 (`|P'| = |P|/4 ≥ 2`)。 -/
theorem exists_ne_mul_comm_of_index_commutator_eq_four {P : Type*} [Group P] [Finite P]
    (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    ∃ x y : P, x * y ≠ y * x := by
  by_contra hcon
  have hall : ∀ x y : P, x * y = y * x := fun x y => by
    by_contra h
    exact hcon ⟨x, y, h⟩
  have hbot : commutator P = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    exact Subgroup.mem_centralizer_iff.mpr fun y _ => hall y x
  rw [hbot, Subgroup.index_bot] at hidx
  omega

/-- `|P : P'| = 4` かつ `|P| ≥ 8` なら `P' ≠ 1`。 -/
theorem commutator_ne_bot_of_index_commutator_eq_four {P : Type*} [Group P] [Finite P]
    (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) : commutator P ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.index_bot] at hidx
  omega

/-- `2`-群で `8 ≤ |P| < 16` なら `|P| = 8`。 -/
theorem card_eq_eight_of_lt_sixteen {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h8 : 8 ≤ Nat.card P) (h16 : Nat.card P < 16) : Nat.card P = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rcases Nat.lt_or_ge k 3 with h | h
  · exfalso
    have hle : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk] at hle
    omega
  · rcases Nat.lt_or_ge k 4 with h' | h'
    · rw [hk, show k = 3 by omega]
      norm_num
    · exfalso
      have hle : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h'
      rw [← hk] at hle
      omega

/-- **6B.8 の帰納法 engine**: `|P| ≤ n` で括った形。

`n` に関する帰納法で回す (`P/Z` は位数が半分になるので `n` が減る)。 -/
theorem exists_index_two_zpowers_of_card_le (n : ℕ) :
    ∀ (P : Type u) [Group P] [Finite P], Nat.card P ≤ n → IsPGroup 2 P →
      8 ≤ Nat.card P → (commutator P).index = 4 →
      ∃ c : P, (Subgroup.zpowers c).index = 2 := by
  induction n with
  | zero =>
    intro P _ _ hle _ h8 _
    omega
  | succ n ih =>
    intro P _ _ hle hP h8 hidx
    rcases Nat.lt_or_ge (Nat.card P) 16 with hlt | hge
    · -- base case: `|P| = 8`
      exact exists_index_two_zpowers_of_card_eight
        (card_eq_eight_of_lt_sixteen hP h8 hlt)
        (exists_ne_mul_comm_of_index_commutator_eq_four h8 hidx)
    · -- step: `Z ≤ P' ⊓ Z(P)` で `|Z| = 2` を取り `P/Z` に帰納法
      obtain ⟨z, hzP', hzZ, hzord⟩ := exists_orderOf_eq_two_mem_commutator_center hP
        (commutator_ne_bot_of_index_commutator_eq_four h8 hidx)
      have hZcenter : Subgroup.zpowers z ≤ Subgroup.center P := Subgroup.zpowers_le.mpr hzZ
      haveI hZn : (Subgroup.zpowers z).Normal := normal_of_le_center hZcenter
      have hZcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
      have hZle : Subgroup.zpowers z ≤ commutator P := Subgroup.zpowers_le.mpr hzP'
      -- `|P/Z| = |P|/2`
      have hQcard : Nat.card (P ⧸ Subgroup.zpowers z) * 2 = Nat.card P := by
        have h := Subgroup.card_mul_index (Subgroup.zpowers z)
        rw [hZcard] at h
        have hidxZ : (Subgroup.zpowers z).index = Nat.card (P ⧸ Subgroup.zpowers z) := rfl
        omega
      -- 帰納法の仮定を `P/Z` に適用
      obtain ⟨cbar, hcbar⟩ := ih (P ⧸ Subgroup.zpowers z) (by omega) (hP.to_quotient _)
        (by omega) (by rw [index_commutator_quotient hZle, hidx])
      -- 引き戻し `A` は指数 `2` の可換部分群, したがって巡回
      have hAidx : ((Subgroup.zpowers cbar).comap
          (QuotientGroup.mk' (Subgroup.zpowers z))).index = 2 := by
        rw [index_comap_of_surjective (QuotientGroup.mk'_surjective _), hcbar]
      have hAab : ∀ x y : P, x ∈ (Subgroup.zpowers cbar).comap
          (QuotientGroup.mk' (Subgroup.zpowers z)) →
          y ∈ (Subgroup.zpowers cbar).comap (QuotientGroup.mk' (Subgroup.zpowers z)) →
          x * y = y * x := by
        intro x y hx hy
        have h := (isMulCommutative_comap_zpowers hZcenter cbar).is_comm.comm
          (⟨x, hx⟩ : ↥((Subgroup.zpowers cbar).comap
            (QuotientGroup.mk' (Subgroup.zpowers z)))) ⟨y, hy⟩
        simpa using congrArg Subtype.val h
      obtain ⟨c, _, hczp⟩ := exists_zpowers_eq_of_isCyclic
        (isCyclic_of_index_two_of_index_commutator_eq_four hP hAab hAidx hidx hge)
      exact ⟨c, by rw [hczp]; exact hAidx⟩

/-- **6B.8 の帰納法**: `2`-群 `P` が `|P| ≥ 8` かつ `|P : P'| = 4` をみたすなら
`P` は**指数 `2` の巡回部分群**を持つ。 -/
theorem exists_index_two_zpowers_of_index_commutator_eq_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    ∃ c : P, (Subgroup.zpowers c).index = 2 :=
  exists_index_two_zpowers_of_card_le (Nat.card P) P le_rfl hP hcard hidx

/-- **Isaacs Problem 6B.8** (p. 196, O. Taussky-Todd) ⭐: `|P| ≥ 8` の `2`-群 `P` が
`|P : P'| = 4` をみたすなら, `P` は二面体・半二面体・一般四元数のいずれか。

`|P| = 8` は Cor 6.14 (`tausskyTodd_card_eight`) で `D_8` か `Q_8`。`|P| ≥ 16` では
帰納法で得た指数 `2` の巡回部分群 `⟨c⟩` (位数 `2^m`, `m ≥ 3`) と
`|P : Z(P)| > 4` (`four_lt_index_center`) を **6B.7** に食わせる。 -/
theorem tausskyTodd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    (∃ n : ℕ, Nonempty (P ≃* DihedralGroup n)) ∨
      (∃ n : ℕ, Nonempty (P ≃* QuaternionGroup n)) ∨
      (∃ k : ℕ, Nonempty (P ≃* SemiDihedralGroup k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge (Nat.card P) 16 with hlt | hge
  · -- `|P| = 8`: `D_8` か `Q_8`
    rcases tausskyTodd_card_eight (card_eq_eight_of_lt_sixteen hP hcard hlt) hidx with h | h
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr (Or.inl ⟨2, h⟩)
  · -- `|P| ≥ 16`: 指数 `2` の巡回部分群を取って 6B.7 を適用
    obtain ⟨c, hc⟩ := exists_index_two_zpowers_of_index_commutator_eq_four hP hcard hidx
    have hcmul : orderOf c * 2 = Nat.card P := by
      have h := Subgroup.card_mul_index (Subgroup.zpowers c)
      rwa [Nat.card_zpowers, hc] at h
    obtain ⟨m, hm⟩ := (hP.to_subgroup (Subgroup.zpowers c)).exists_card_eq
    rw [Nat.card_zpowers] at hm
    have hm3 : 3 ≤ m := by
      by_contra hcon
      have hle : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hm] at hle
      omega
    obtain ⟨a, ha⟩ : ∃ a : P, a ∉ Subgroup.zpowers c := by
      by_contra hcon
      have htop : Subgroup.zpowers c = ⊤ :=
        eq_top_iff.mpr fun x _ => not_not.mp fun h => hcon ⟨x, h⟩
      rw [htop, Subgroup.index_top] at hc
      omega
    rcases dihedralOrQuaternionOrSemiDihedral_of_index_two_cyclic hP
      (exists_ne_mul_comm_of_index_commutator_eq_four hcard hidx) hm3 hm hc ha
      (four_lt_index_center hge hidx) with h | h | ⟨k, _, h⟩
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · exact Or.inr (Or.inr ⟨k, h⟩)

end

end OddOrder.Isaacs.Ch06
