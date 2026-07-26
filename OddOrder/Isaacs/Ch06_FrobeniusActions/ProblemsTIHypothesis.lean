/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs Problems 6A.6 / 6A.11 — Lemma 6.5 の仮説 (TI 条件) をめぐる演習 (書籍 pp. 185-186)

Lemma 6.5 の仮説は **TI 条件** `A ⊓ A^g = 1` (`g ∉ A`) であり, そのとき
`X = notConjugateSet A` (`A` の非単位元に共役でない元全体) は `|X| = |G : A|` をみたす。

⚠ 書籍の Note のとおり, これらの問題では **Frobenius の定理 (`X` が部分群であること) は
使ってはならない**。以下の証明も使っていない。

## 6A.6

**主張**: `A > 1`, `B > 1` がともに `G` で Lemma 6.5 の仮説をみたすなら, ある `g ∈ G` で
`A ⊓ B^g > 1`。

**証明** (hint の `X`, `Y` を使う計数): もし全ての `g` で `A ⊓ B^g = 1` なら, `A` の非単位元は
`B` の非単位元と共役になれないので `X ∪ Y = G`。一方 `1 ∈ X ⊓ Y` なので
`|G| + 1 ≤ |X| + |Y| = |G:A| + |G:B| ≤ |G|/2 + |G|/2 = |G|` で矛盾。

## 6A.11

**主張**: `A ≤ G` が Lemma 6.5 の仮説をみたす ⟺ `A` の任意の非自明部分群 `T` について
`N_G(T) ⊆ A`。

**証明**:
* (⟹) `1 ≠ T ≤ A`, `g ∈ N_G(T)` なら `1 ≠ T ≤ A ⊓ A^g` なので TI から `g ∈ A`。
* (⟸) `D := A ⊓ A^g ≠ 1` とする。`1 ≠ T ≤ D` について `N_G(T) ≤ A` かつ
  (`g⁻¹Tg ≤ A` に仮説を使って) `N_G(T) ≤ A^g`, ゆえに **`N_G(T) ≤ D`**。
  素数 `p ∣ |D|` と `P ∈ Syl_p(D)` を取ると, `P` は実は **`G` の Sylow `p`-部分群**
  (そうでなければ `p`-群の正規化群成長 `P < N_S(P) ≤ N_G(P) ≤ D` が `D` 内でより大きい
  `p`-部分群を与えて矛盾)。`P ≤ A` と `g⁻¹Pg ≤ A` はともに `A` の Sylow `p`-部分群なので
  Sylow C で `a ∈ A` があって `a(g⁻¹Pg)a⁻¹ = P`, つまり `a g⁻¹ ∈ N_G(P) ≤ A` ⟹ `g ∈ A`。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.6 / 6A.11: Lemma 6.5 の TI 仮説 (pp. 185-186) -/

variable {G : Type*} [Group G]

theorem one_mem_notConjugateSet (A : Subgroup G) : (1 : G) ∈ notConjugateSet A := by
  intro a ha hane hconj
  exact hane (by simpa using hconj)

/-- **Isaacs Problem 6A.6** (p. 185) ⭐: `A > 1`, `B > 1` がともに Lemma 6.5 の TI 仮説を
みたすなら, ある `g` で `A ⊓ B^g > 1`。 -/
theorem exists_inf_conj_ne_bot_of_TI [Finite G] {A B : Subgroup G}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hATI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    (hBTI : ∀ g : G, g ∉ B → B ⊓ (MulAut.conj g • B) = ⊥) :
    ∃ g : G, A ⊓ (MulAut.conj g • B) ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  -- `X ∪ Y = G`: `x` が `A` の非単位元とも `B` の非単位元とも共役なら矛盾
  have hcover : notConjugateSet A ∪ notConjugateSet B = (Set.univ : Set G) := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_contra hx
    rw [Set.mem_union] at hx
    push Not at hx
    obtain ⟨hxA, hxB⟩ := hx
    simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hxA hxB
    obtain ⟨a, ha, hane, hcja⟩ := hxA
    obtain ⟨b, hb, hbne, hcjb⟩ := hxB
    -- `a` と `b` は共役: `a = h b h⁻¹`
    obtain ⟨h, hh⟩ := isConj_iff.mp (hcjb.trans hcja.symm)
    refine hane ?_
    have hmem : a ∈ A ⊓ (MulAut.conj h • B) := by
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change (MulAut.conj h).symm a ∈ B
      rw [MulAut.conj_symm_apply, ← hh]
      simpa [mul_assoc] using hb
    rw [hcon h, Subgroup.mem_bot] at hmem
    exact hmem
  -- `1 ∈ X ⊓ Y`
  have hone : (1 : G) ∈ notConjugateSet A ∩ notConjugateSet B :=
    ⟨one_mem_notConjugateSet A, one_mem_notConjugateSet B⟩
  -- 計数
  have hXcard : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
  have hYcard : (notConjugateSet B).ncard = B.index := card_notConjugateSet_eq_index B hBTI
  have hunion := Set.ncard_union_add_ncard_inter (notConjugateSet A) (notConjugateSet B)
    (Set.toFinite _) (Set.toFinite _)
  rw [hcover, Set.ncard_univ, hXcard, hYcard] at hunion
  have hinter : 0 < (notConjugateSet A ∩ notConjugateSet B).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, hone⟩
  -- `|A| ≥ 2` から `2 · |G:A| ≤ |G|`, 同様に `B`
  have hcardA : 2 * A.index ≤ Nat.card G := by
    have hmul : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
    have h2 : 2 ≤ Nat.card ↥A := by
      rcases Nat.lt_or_ge (Nat.card ↥A) 2 with h | h
      · exact absurd (Subgroup.card_eq_one.mp (by
          have := Nat.card_pos (α := ↥A); omega)) hA
      · exact h
    calc 2 * A.index ≤ Nat.card ↥A * A.index := Nat.mul_le_mul_right _ h2
      _ = Nat.card G := hmul
  have hcardB : 2 * B.index ≤ Nat.card G := by
    have hmul : Nat.card ↥B * B.index = Nat.card G := Subgroup.card_mul_index B
    have h2 : 2 ≤ Nat.card ↥B := by
      rcases Nat.lt_or_ge (Nat.card ↥B) 2 with h | h
      · exact absurd (Subgroup.card_eq_one.mp (by
          have := Nat.card_pos (α := ↥B); omega)) hB
      · exact h
    calc 2 * B.index ≤ Nat.card ↥B * B.index := Nat.mul_le_mul_right _ h2
      _ = Nat.card G := hmul
  omega

/-! ### 6A.11: TI 仮説の正規化群による特徴づけ -/

/-- **6A.11 (⟹)**: TI 仮説をみたす `A` では, 非自明部分群の正規化群は `A` に含まれる。 -/
theorem normalizer_le_of_TI {A : Subgroup G}
    (hATI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    {T : Subgroup G} (hT : T ≠ ⊥) (hTA : T ≤ A) :
    Subgroup.normalizer T ≤ A := by
  intro g hg
  by_contra hgA
  refine hT (le_antisymm ?_ bot_le)
  rw [← hATI g hgA]
  refine le_inf hTA fun x hx => ?_
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj g).symm x ∈ A
  rw [MulAut.conj_symm_apply]
  exact hTA (((Subgroup.mem_normalizer_iff''.mp hg) x).mp hx)

end

end OddOrder.Isaacs.Ch06
