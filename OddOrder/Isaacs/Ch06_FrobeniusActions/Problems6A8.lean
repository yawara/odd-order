/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsTIHypothesis

/-!
# Isaacs Problem 6A.8 — 正規部分群と Lemma 6.5 の集合 `X` (書籍 p. 186)

**主張**: `A` が `G` で Lemma 6.5 の TI 仮説をみたし `X = notConjugateSet A`, `M ⊴ G` とすると,
**`M ⊆ X` または `X ⊆ M`**。

**証明** (書籍 hint: `M ⊓ A > 1` なら前問 6A.7 で `AM = G`):

* **`M ⊓ A = 1` の場合**: `m ∈ M` が `A` の非単位元 `a` と共役なら, `M ⊴ G` より
  `a ∈ M ⊓ A = 1` で矛盾。ゆえに `M ⊆ X`。
* **`M ⊓ A ≠ 1` の場合**: 任意の `g` で `A^g ⊓ M = (A ⊓ M)^g ≠ 1` なので **6A.7(a)** から
  `g ∈ A ⊔ M`, すなわち **`A ⊔ M = ⊤`** (`AM = G`)。このとき
  1. `C := A ⊓ M` は **`M` の中で TI 仮説をみたす** (`1 ≠ T ≤ C` について
     `N_M(T) = M ⊓ N_G(T) ≤ M ⊓ A = C`, 6A.11 を `↥M` で使う)。
  2. Lemma 6.5 を `↥M` で使うと `|X_M(C)| = |M : C|`, 一方 `AM = G` から `|M : C| = |G : A|`
     なので `|X_M(C)| = |X|`。
  3. `X_M(C) ⊆ X` (`y ∈ M` が `A` の非単位元 `a` と `G` で共役なら, `a ∈ M` ゆえ `a ∈ C` で,
     `g = m a₁` と分解すると `y` は `M` の中で `a₁ a a₁⁻¹ ∈ C` と共役)。
  4. 濃度が等しく包含があるので `X = X_M(C) ⊆ M`。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.8: 正規部分群と `X` (p. 186) -/

variable {G : Type*} [Group G]

/-- `A ⊔ M = ⊤` (`M ⊴ G`) のとき `|G : A| = |M : A ⊓ M|` (第 2 同型定理の指数版)。 -/
theorem index_eq_relIndex_of_sup_eq_top [Finite G] {A M : Subgroup G} [M.Normal]
    (hsup : A ⊔ M = ⊤) : A.index = A.relIndex M := by
  have hMA : M.relIndex A = M.index := by
    rw [← Subgroup.relIndex_sup_right (H := A) (K := M), hsup, Subgroup.relIndex_top_right]
  have hinfA : (A ⊓ M).subgroupOf A = M.subgroupOf A := Subgroup.inf_subgroupOf_left M A
  have hinfM : (A ⊓ M).subgroupOf M = A.subgroupOf M := Subgroup.inf_subgroupOf_right A M
  have e1 : Nat.card ↥(A ⊓ M) * M.relIndex A = Nat.card ↥A := by
    have h := Subgroup.card_mul_index ((A ⊓ M).subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ M ≤ A)).toEquiv,
      hinfA] at h
    exact h
  have e2 : Nat.card ↥(A ⊓ M) * A.relIndex M = Nat.card ↥M := by
    have h := Subgroup.card_mul_index ((A ⊓ M).subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ M ≤ M)).toEquiv,
      hinfM] at h
    exact h
  rw [hMA] at e1
  have hA := Subgroup.card_mul_index A
  have hM := Subgroup.card_mul_index M
  have key : Nat.card ↥(A ⊓ M) * (M.index * A.index)
      = Nat.card ↥(A ⊓ M) * (A.relIndex M * M.index) := by
    rw [← mul_assoc, ← mul_assoc, e1, e2, hA, hM]
  have key2 := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(A ⊓ M))) key
  rw [mul_comm (A.relIndex M) M.index] at key2
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) key2

/-- `A` が `G` で TI 仮説をみたし `M ⊴ G` なら, `A ⊓ M` は `M` の中で TI 仮説をみたす。 -/
theorem TI_subgroupOf_normal [Finite G] {A M : Subgroup G} [M.Normal]
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) :
    ∀ k : ↥M, k ∉ A.subgroupOf M →
      (A.subgroupOf M) ⊓ (MulAut.conj k • (A.subgroupOf M)) = ⊥ :=
  fun k hk => TI_subgroupOf_of_TI hATI k hk

/-- `M ⊴ G` のときの `X` の `M` 側の記述: `M` の中で `A ⊓ M` の非単位元に共役でない元は,
`G` の中で `A` の非単位元に共役でない。 -/
theorem image_notConjugateSet_subgroupOf_subset {A M : Subgroup G} [M.Normal]
    (hsup : A ⊔ M = ⊤) :
    (M.subtype '' notConjugateSet (A.subgroupOf M)) ⊆ notConjugateSet A := by
  rintro _ ⟨y, hy, rfl⟩ a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  -- `a ∈ M` (M 正規, y ∈ M) ゆえ `a ∈ A ⊓ M`
  simp only [Subgroup.coe_subtype] at hg
  have haM : a ∈ M := by
    have hin : g⁻¹ * ((y : G)) * g ∈ M := by
      simpa using ‹M.Normal›.conj_mem _ y.2 g⁻¹
    rwa [← hg, show g⁻¹ * (g * a * g⁻¹) * g = a by group] at hin
  -- `g = m * a₁` と分解
  have hgmem : g ∈ M ⊔ A := by rw [sup_comm, hsup]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgmem
  obtain ⟨m, hm, a₁, ha₁, rfl⟩ := hgmem
  -- `c := a₁ a a₁⁻¹ ∈ A ⊓ M`, `y = m c m⁻¹`
  have hcA : a₁ * a * a₁⁻¹ ∈ A := A.mul_mem (A.mul_mem ha₁ ha) (A.inv_mem ha₁)
  have hcM : a₁ * a * a₁⁻¹ ∈ M := ‹M.Normal›.conj_mem _ haM a₁
  have hcne : (⟨a₁ * a * a₁⁻¹, hcM⟩ : ↥M) ≠ 1 := by
    intro h
    exact hane (by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      have h2 : a₁ * a * a₁⁻¹ = 1 := this
      calc a = a₁⁻¹ * (a₁ * a * a₁⁻¹) * a₁ := by group
        _ = 1 := by rw [h2]; group)
  refine hy ⟨a₁ * a * a₁⁻¹, hcM⟩ (by rwa [Subgroup.mem_subgroupOf]) hcne ?_
  refine isConj_iff.mpr ⟨⟨m, hm⟩, ?_⟩
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hg]
  group

/-- `A ⊓ M = ⊥` (`M ⊴ G`) なら `M ⊆ X` (`X = notConjugateSet A`)。

`m ∈ M` が `A` の非単位元 `a` と共役なら `M ⊴ G` から `a ∈ M`, ゆえに `a ∈ A ⊓ M = 1`。 -/
theorem subset_notConjugateSet_of_inf_eq_bot {A M : Subgroup G} [M.Normal]
    (hAM : A ⊓ M = ⊥) : (M : Set G) ⊆ notConjugateSet A := by
  intro m hm a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have haM : a ∈ M := by
    have hin : g⁻¹ * m * g ∈ M := by simpa using ‹M.Normal›.conj_mem _ hm g⁻¹
    rwa [← hg, show g⁻¹ * (g * a * g⁻¹) * g = a by group] at hin
  have hmem : a ∈ A ⊓ M := ⟨ha, haM⟩
  rw [hAM, Subgroup.mem_bot] at hmem
  exact hane hmem

/-- `A` が TI 仮説をみたし `M ⊴ G` で `A ⊓ M ≠ ⊥` なら **`AM = G`** (6A.7(a) の帰結)。

任意の `g` について `A^g ⊓ (A ⊔ M) ⊇ (A ⊓ M)^g ≠ 1` なので 6A.7(a) から `g ∈ A ⊔ M`。 -/
theorem sup_eq_top_of_inf_ne_bot [Finite G] {A M : Subgroup G} [M.Normal]
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) (hAM : A ⊓ M ≠ ⊥) :
    A ⊔ M = ⊤ := by
  refine le_antisymm le_top fun g _ => ?_
  refine mem_of_conj_inf_ne_bot (le_sup_left : A ≤ A ⊔ M) hATI (g := g) ?_
  intro h
  refine hAM (le_antisymm (fun x hx => ?_) bot_le)
  have hxg : MulAut.conj g x ∈ (MulAut.conj g • A) ⊓ (A ⊔ M) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change (MulAut.conj g).symm ((MulAut.conj g) x) ∈ A
      rw [MulEquiv.symm_apply_apply]
      exact hx.1
    · exact (le_sup_right : M ≤ A ⊔ M) (‹M.Normal›.conj_mem _ hx.2 g)
  rw [h, Subgroup.mem_bot] at hxg
  have hx1 : x = 1 := by
    have h2 := congrArg (fun y : G => g⁻¹ * y * g) hxg
    simpa [MulAut.conj_apply, mul_assoc] using h2
  simp [hx1]

/-- `AM = G` (`M ⊴ G`, TI) のとき `X` は `M` の中の `X_M(A ⊓ M)` の像に**一致**する。

包含 `⊆` は `image_notConjugateSet_subgroupOf_subset`, 逆向きは Lemma 6.5 の濃度計算
(`|X| = |G : A| = |M : A ⊓ M| = |X_M(A ⊓ M)|`) から。 -/
theorem image_notConjugateSet_subgroupOf_eq [Finite G] {A M : Subgroup G} [M.Normal]
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) (hsup : A ⊔ M = ⊤) :
    M.subtype '' notConjugateSet (A.subgroupOf M) = notConjugateSet A := by
  have hsubset := image_notConjugateSet_subgroupOf_subset (A := A) (M := M) hsup
  have hcardX : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
  have hcardXM : (notConjugateSet (A.subgroupOf M)).ncard = (A.subgroupOf M).index :=
    card_notConjugateSet_eq_index _ (TI_subgroupOf_normal hATI)
  have hcardimg : (M.subtype '' notConjugateSet (A.subgroupOf M)).ncard
      = (notConjugateSet (A.subgroupOf M)).ncard :=
    Set.ncard_image_of_injective _ (Subgroup.subtype_injective M)
  refine Set.eq_of_subset_of_ncard_le hsubset ?_ (Set.toFinite _)
  rw [hcardX, hcardimg, hcardXM, ← Subgroup.relIndex, ← index_eq_relIndex_of_sup_eq_top hsup]

/-- **Isaacs Problem 6A.8** (p. 186) ⭐: `A` が `G` で Lemma 6.5 の TI 仮説をみたし `M ⊴ G` なら,
`M ⊆ X` または `X ⊆ M` (`X = notConjugateSet A`)。 -/
theorem subset_notConjugateSet_or_subset_of_normal [Finite G] {A M : Subgroup G} [M.Normal]
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) :
    (M : Set G) ⊆ notConjugateSet A ∨ notConjugateSet A ⊆ (M : Set G) := by
  classical
  by_cases hAM : A ⊓ M = ⊥
  · exact Or.inl (subset_notConjugateSet_of_inf_eq_bot hAM)
  · refine Or.inr ?_
    rw [← image_notConjugateSet_subgroupOf_eq hATI (sup_eq_top_of_inf_ne_bot hATI hAM)]
    rintro _ ⟨y, _, rfl⟩
    exact y.2

end

end OddOrder.Isaacs.Ch06
