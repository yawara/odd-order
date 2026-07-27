/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6A8

/-!
# Isaacs Problem 6A.10(c) — 可解な場合の Frobenius の定理 (書籍 p. 186)

**主張**: `A` が `G` で Lemma 6.5 の TI 仮説をみたし `A` が**可解**なら,
`X = notConjugateSet A` は `G` の部分群である。

これは **Frobenius の定理の可解な場合** (Frobenius 核の存在) にあたる。一般の場合は指標理論
(Thm 7.2) を要するが, `A` が可解なら群論だけで, `|G|` に関する帰納法で示せる。

**証明** (`|G|` に関する強帰納法):

* `A = 1` なら `X = G` で `⊤` が答え。
* 以下 `A ≠ 1`。`A` 可解ゆえ **`A' < A`** (`IsSolvable.commutator_lt_top_of_nontrivial`)。
  6A.10(b) (`inf_commutator_eq_commutator_self_of_TI`) より **`G' ⊓ A = A'`**。
* **`A` が非可換のとき** (`A' ≠ 1`): `A ⊓ G' = A' ≠ 1` なので 6A.7(a) から `AG' = G`。
  また `G' = G` なら `A = A ⊓ G' = A'` で `A' < A` に反するので **`G' < G`**。
  6A.8 の道具 (`TI_subgroupOf_normal`, `image_notConjugateSet_subgroupOf_eq`) で
  `A ⊓ G'` は `G'` の中で TI 仮説をみたし可解, かつ `X` は `X_{G'}(A ⊓ G')` の像。
  帰納法の仮定を `G'` に適用すればよい。
* **`A` が可換のとき** (`A' = 1`): `A ⊓ G' = 1` なので 6A.8 の第 1 場合から **`G' ⊆ X`**。
  さらに `M := AG'` は `G'` を含むので正規で, `A ≤ M`, `A ≠ 1` から `M ⊄ X`。6A.8 より
  `X ⊆ M` で, `G = X ∪ ⋃ A^g ⊆ M` すなわち **`AG' = G`**。このとき
  `|X| = |G : A| = |G' : A ⊓ G'| = |G'|` なので **`X = G'`**。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.10(c): `A` 可解なら `X` は部分群 (p. 186) -/

variable {G : Type*} [Group G]

/-- **Isaacs Problem 6A.10(c)** の帰納版 (`|G| = n` に関する強帰納法)。 -/
theorem exists_subgroup_coe_eq_notConjugateSet_of_solvable_aux (n : ℕ) :
    ∀ {G : Type*} [Group G] [Finite G] (A : Subgroup G),
      Nat.card G = n → (∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) → IsSolvable ↥A →
      ∃ K : Subgroup G, (K : Set G) = notConjugateSet A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ A hcard hATI hsol
  classical
  rcases eq_or_ne A ⊥ with rfl | hAne
  · -- `A = 1`: すべての元が `X` に入る
    refine ⟨⊤, ?_⟩
    ext g
    simp only [Subgroup.coe_top, Set.mem_univ, true_iff]
    intro a ha hane _
    exact hane (Subgroup.mem_bot.mp ha)
  haveI hAnt : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  haveI := hsol
  -- `A` 可解 + `A ≠ 1` ⟹ `A' < A`
  have hAlt : ⁅A, A⁆ < A := by
    rw [← A.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
    exact IsSolvable.commutator_lt_top_of_nontrivial ↥A
  -- 6A.10(b)
  have hb : commutator G ⊓ A = ⁅A, A⁆ := inf_commutator_eq_commutator_self_of_TI hATI
  rcases eq_or_ne (⁅A, A⁆ : Subgroup G) ⊥ with habel | hnonab
  · -- `A` 可換: `X = G'`
    have hAG : A ⊓ commutator G = ⊥ := by rw [inf_comm, hb]; exact habel
    have hGsub : ((commutator G : Subgroup G) : Set G) ⊆ notConjugateSet A :=
      subset_notConjugateSet_of_inf_eq_bot hAG
    obtain ⟨a₀, ha₀A, ha₀ne⟩ : ∃ a ∈ A, a ≠ 1 := by
      obtain ⟨⟨a, haA⟩, ha1⟩ := exists_ne (1 : ↥A)
      exact ⟨a, haA, fun h => ha1 (Subtype.ext h)⟩
    -- `AG' = G`
    have hsup : A ⊔ commutator G = ⊤ := by
      haveI hMn : (A ⊔ commutator G).Normal := normal_of_commutator_le le_sup_right
      rcases subset_notConjugateSet_or_subset_of_normal (A := A) (M := A ⊔ commutator G)
        hATI with h1 | h2
      · exact absurd (h1 ((le_sup_left : A ≤ A ⊔ commutator G) ha₀A) a₀ ha₀A ha₀ne
          (IsConj.refl a₀)) not_false
      · refine le_antisymm le_top fun g _ => ?_
        by_cases hgX : g ∈ notConjugateSet A
        · exact h2 hgX
        · simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hgX
          obtain ⟨a, haA, hane, hconj⟩ := hgX
          obtain ⟨c, hc⟩ := isConj_iff.mp hconj
          rw [← hc]
          exact hMn.conj_mem _ ((le_sup_left : A ≤ A ⊔ commutator G) haA) c
    refine ⟨commutator G, ?_⟩
    refine Set.eq_of_subset_of_ncard_le hGsub ?_ (Set.toFinite _)
    have hcardX : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
    have hsubbot : A.subgroupOf (commutator G) = ⊥ :=
      Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hAG)
    have hidx : A.index = Nat.card ↥(commutator G) := by
      rw [index_eq_relIndex_of_sup_eq_top hsup, Subgroup.relIndex, hsubbot, Subgroup.index_bot]
    rw [hcardX, hidx]
    exact le_rfl
  · -- `A` 非可換: `G'` に帰納法
    have hAM : A ⊓ commutator G ≠ ⊥ := by rw [inf_comm, hb]; exact hnonab
    have hsup : A ⊔ commutator G = ⊤ := sup_eq_top_of_inf_ne_bot hATI hAM
    have hGtop : commutator G ≠ ⊤ := by
      intro h
      rw [h, top_inf_eq] at hb
      exact hAlt.ne hb.symm
    have hlt : Nat.card ↥(commutator G) < n := by
      subst hcard
      have hmul := Subgroup.card_mul_index (commutator G)
      have h1 : (commutator G).index ≠ 1 := fun h => hGtop (Subgroup.index_eq_one.mp h)
      have h0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hpos : 0 < Nat.card ↥(commutator G) := Nat.card_pos
      calc Nat.card ↥(commutator G) < Nat.card ↥(commutator G) * (commutator G).index :=
            (Nat.lt_mul_iff_one_lt_right hpos).mpr (by omega)
        _ = Nat.card G := hmul
    have hTIsub := TI_subgroupOf_normal (A := A) (M := commutator G) hATI
    have hsolsub : IsSolvable ↥(A.subgroupOf (commutator G)) :=
      solvable_of_solvable_injective
        (f := { toFun := fun z : ↥(A.subgroupOf (commutator G)) =>
                  (⟨((z : ↥(commutator G)) : G), z.2⟩ : ↥A)
                map_one' := rfl
                map_mul' := fun _ _ => rfl })
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun w : ↥A => (w : G)) h)))
    obtain ⟨K, hK⟩ := ih (Nat.card ↥(commutator G)) hlt (A.subgroupOf (commutator G)) rfl
      hTIsub hsolsub
    refine ⟨K.map (commutator G).subtype, ?_⟩
    rw [Subgroup.coe_map, hK, image_notConjugateSet_subgroupOf_eq hATI hsup]

/-- **Isaacs Problem 6A.10(c)** (p. 186) ⭐ (= **可解な場合の Frobenius の定理**):
`A` が `G` で Lemma 6.5 の TI 仮説をみたし `A` が可解なら, `X = notConjugateSet A` は
`G` の部分群 (の台集合) である。

`A` が `G` の Frobenius 補群のとき `X ∪ {1}` が Frobenius 核にあたる。一般の `A` に対する
主張は Thm 7.2 (指標理論) を要するが, ここでは `A` の可解性から群論だけで導ける。 -/
theorem exists_subgroup_coe_eq_notConjugateSet_of_solvable [Finite G] (A : Subgroup G)
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) (hsol : IsSolvable ↥A) :
    ∃ K : Subgroup G, (K : Set G) = notConjugateSet A :=
  exists_subgroup_coe_eq_notConjugateSet_of_solvable_aux (Nat.card G) A rfl hATI hsol

end

end OddOrder.Isaacs.Ch06
