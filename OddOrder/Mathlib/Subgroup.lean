/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finite.Card
import Mathlib.Data.Setoid.Basic

/-!
# Auxiliary `Subgroup` lemmas

mathlib v4.29.1 に不在の汎用 `Subgroup` 補題. 主に
[`OddOrder/GroupTheory/ChermakDelgado.lean`](../GroupTheory/ChermakDelgado.lean) の
支援目的だが, 他章でも独立に使う可能性があるため `OddOrder.Mathlib` 配下に切り出す
("mathlib upstream 候補" の慣用 dir).

## Main results

* `Subgroup.card_HK_mul_card_inf_eq_card_mul_card`: 古典的
  `|HK| · |H ∩ K| = |H| · |K|` (集合積 `HK ⊆ G` は一般に部分群ではない).
* `Subgroup.le_centralizer_centralizer`: `H ≤ C_G(C_G(H))`
  (`IsMulCommutative` 仮定なし; 既存 `Subgroup.le_centralizer` は仮定あり版).
* `Subgroup.centralizer_centralizer_centralizer`: Galois closure idempotency
  `C_G(C_G(C_G(H))) = C_G(H)`.
* `Subgroup.centralizer_sup`: `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`
  (mathlib には Subalgebra 版のみ).

将来 mathlib 本体へ寄与する際の配置候補:

* `card_HK_mul_card_inf_eq_card_mul_card` → `Mathlib/GroupTheory/Coset/Card.lean`
* `le_centralizer_centralizer`, `centralizer_centralizer_centralizer`,
  `centralizer_sup` → `Mathlib/GroupTheory/Subgroup/Centralizer.lean`
-/

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Classical identity**: `|HK| · |H ∩ K| = |H| · |K|` for subgroups `H, K` of a
group `G`, where `HK ⊆ G` is the set product (not generally a subgroup).
無限群でも両辺はゼロで成立する.

mathlib v4.29.1 不在 ── 関連 `index_inf_le`, `relIndex_inf_mul_relIndex` は部分対応のみ.

**証明戦略**: `H × K → HK` の準同型 (の corestriction) は H ⊓ K 加群作用で fiber が
`|H ∩ K|` と分かる. mathlib 流には:
1. `card_mul_eq_card_subgroup_mul_card_quotient` で `|HK| = |K| · |(↑H).image mk|`.
2. `H ⧸ K.subgroupOf H ≃ (↑H).image mk` (本証明内で構成).
3. Lagrange `|H| = |H ⧸ K.subgroupOf H| · |K.subgroupOf H|`.
4. `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で `≃ H ⊓ K`. -/
theorem card_HK_mul_card_inf_eq_card_mul_card (H K : Subgroup G) :
    Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  classical
  -- Step 1: `|HK| = |K| · |(↑H).image mk|` (mathlib 既存)
  rw [card_mul_eq_card_subgroup_mul_card_quotient K (↑H : Set G)]
  -- Step 2: 補助 — corestricted projection `f : H → img` は全射
  set img := (↑H : Set G).image (QuotientGroup.mk : G → G ⧸ K) with himg
  let f : H → ↥img := fun h => ⟨QuotientGroup.mk h.val, h.val, h.property, rfl⟩
  have hf_surj : Function.Surjective f := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  -- Step 3: Setoid.ker f は QuotientGroup.leftRel (K.subgroupOf H) と関係が一致
  have hsetoid_rel :
      ∀ h₁ h₂ : H,
        (QuotientGroup.leftRel (K.subgroupOf H)) h₁ h₂ ↔ (Setoid.ker f) h₁ h₂ := by
    intro h₁ h₂
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf, Setoid.ker_def]
    constructor
    · intro hrel
      apply Subtype.ext
      change QuotientGroup.mk h₁.val = QuotientGroup.mk h₂.val
      rw [QuotientGroup.eq]
      exact hrel
    · intro hrel
      have : QuotientGroup.mk h₁.val = (QuotientGroup.mk h₂.val : G ⧸ K) :=
        congrArg Subtype.val hrel
      rwa [QuotientGroup.eq] at this
  -- Step 4: H ⧸ K.subgroupOf H ≃ ↥img (合成)
  have hquot_img_card : Nat.card (H ⧸ K.subgroupOf H) = Nat.card ↥img :=
    (Nat.card_congr (Quotient.congrRight hsetoid_rel)).trans
      (Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf_surj))
  -- Step 5: Lagrange in H
  have hH_split : Nat.card H = Nat.card (H ⧸ K.subgroupOf H) * Nat.card ↥(K.subgroupOf H) :=
    (K.subgroupOf H).card_eq_card_quotient_mul_card_subgroup
  -- Step 6: `K.subgroupOf H = (H ⊓ K).subgroupOf H`, `subgroupOfEquivOfLe` で
  -- `|K.subgroupOf H| = |H ⊓ K|`
  have hKHinf : K.subgroupOf H = (H ⊓ K).subgroupOf H := by
    ext x
    simp only [mem_subgroupOf, mem_inf, and_iff_right x.property]
  have hker_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [hKHinf]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : H ⊓ K ≤ H)).toEquiv
  -- Step 7: 合算
  rw [hquot_img_card, hker_card] at hH_split
  -- hH_split : Nat.card H = Nat.card ↥img * Nat.card ↥(H ⊓ K)
  -- Goal: Nat.card K * Nat.card ↥img * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K
  rw [mul_assoc, ← hH_split, Nat.mul_comm]

/-- `H ≤ C_G(C_G(H))` for any subgroup `H` ── classical Galois connection (`le_centralizer_iff`).

mathlib v4.29.1 不在: 既存 `Subgroup.le_centralizer` は `IsMulCommutative H` 仮定が必要だが,
本補題は仮定なし. `Subgroup.closure_le_centralizer_centralizer` を `H = closure ↑H` に適用. -/
theorem le_centralizer_centralizer (H : Subgroup G) :
    H ≤ centralizer (centralizer (H : Set G) : Set G) := by
  conv_lhs => rw [← H.closure_eq]
  exact closure_le_centralizer_centralizer _

/-- `C_G(C_G(C_G(H))) = C_G(H)` (Galois closure idempotency). 系として Cor 1.45 で
`C_G(M) ∈ L(G)` の確認に使う. -/
theorem centralizer_centralizer_centralizer (H : Subgroup G) :
    centralizer
        ((centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) : Subgroup G) : Set G)
      = centralizer (H : Set G) := by
  apply le_antisymm
  · -- `C(C(C(H))) ≤ C(H)`: `H ≤ C(C(H))` に `centralizer_le` (反単調) を適用
    exact centralizer_le (SetLike.coe_subset_coe.mpr H.le_centralizer_centralizer)
  · -- `C(H) ≤ C(C(C(H)))`: `X ≤ C(C(X))` を `X = C(H)` に適用
    exact (centralizer (H : Set G) : Subgroup G).le_centralizer_centralizer

/-- `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`.

mathlib v4.29.1 では `Subalgebra` 版 (`Algebra/Subalgebra/Centralizer.lean:19`) のみで,
`Subgroup` 版は不在. `Set.centralizer_union` + `Subgroup.centralizer_closure` から従う. -/
theorem centralizer_sup (H K : Subgroup G) :
    centralizer ((H ⊔ K : Subgroup G) : Set G)
      = centralizer (H : Set G) ⊓ centralizer (K : Set G) := by
  have hHK : (H ⊔ K : Subgroup G) = closure ((H : Set G) ∪ (K : Set G)) := by
    rw [closure_union, closure_eq, closure_eq]
  rw [hHK, centralizer_closure]
  ext g
  simp only [mem_centralizer_iff, Set.mem_union, mem_inf, or_imp, forall_and]

/-- **`p`-th power subgroup is characteristic** in CommGroup: for any `n : ℕ`, the range
of `powMonoidHom n` (= `{x^n : x : M}` as subgroup of M) is characteristic in M.

mathlib v4.29.1 不在の generic lemma. Lucchini K=⊥ (M abelian case で `φ(M) ⊴ G` を
`characteristic in normal` 経由で得る) で使用. -/
instance powMonoidHom_range_characteristic
    {M : Type*} [CommGroup M] (n : ℕ) :
    ((powMonoidHom (α := M) n).range).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hφx
    obtain ⟨y, hy⟩ := hφx
    refine ⟨φ.symm y, ?_⟩
    have : φ ((φ.symm y) ^ n) = φ x := by
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact hy
    exact φ.injective this
  · intro hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨φ y, ?_⟩
    change (φ y) ^ n = φ x
    rw [← map_pow]
    exact congrArg φ hy

/-- **`G ⧸ N` nontrivial iff `N ≠ ⊤`** (有限 G で): mathlib `Subgroup.index_eq_one`
+ `Finite.one_lt_card_iff_nontrivial` を結合.

用途: Hall-Higman 3.21 で C/B nontrivial を `B < C` から導出. -/
theorem nontrivial_quotient_of_ne_top {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (h : N ≠ ⊤) : Nontrivial (G ⧸ N) := by
  rw [← Finite.one_lt_card_iff_nontrivial]
  change 1 < N.index
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    ⟨Subgroup.index_ne_zero_of_finite, mt Subgroup.index_eq_one.mp h⟩

/-- **normalCore = ⊥ ⇒ no nontrivial G-normal subgroup of H**:
`B ⊴ G + B ≤ H + H.normalCore = ⊥ ⇒ B = ⊥`.

`H.normalCore` は G-normal subgroups of G contained in H の最大. 仮定 `H.normalCore = ⊥`
は H が G-core を持たない (= 「core-free」) を意味する. このとき H の任意の G-normal
sub は ⊥ に強制される.

**用途**: Lucchini Thm 2.20 (K=⊥ case) で `M ⊴ G + M ≤ A + core_G(A) = ⊥ ⇒ M = ⊥` の
最終矛盾導出に使用. -/
theorem eq_bot_of_le_of_normal_of_normalCore_eq_bot {H B : Subgroup G} [B.Normal]
    (hBH : B ≤ H) (hCore : H.normalCore = ⊥) : B = ⊥ := by
  rw [← le_bot_iff, ← hCore]
  exact (normal_le_normalCore (N := B) (H := H)).mpr hBH

/-- **Dedekind / modular law for subgroups** (with normality of one summand).
`E, A, M ≤ G`, `E ⊴ G`, `E ≤ M` ⇒ `M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A)`.

mathlib v4.29.1 では `IsModularLattice (Subgroup G)` instance は `[CommGroup G]` 限定で,
非可換群版は不在 (実際は片方正規で modular).

**用途**: Lucchini Thm 2.20 (K=⊥ case) で `M ⊆ AE ⇒ M = E(A ∩ M)` を導出. -/
theorem inf_sup_eq_sup_inf_of_normal_of_le
    {E A M : Subgroup G} [E.Normal] (hEM : E ≤ M) :
    M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A) := by
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ M := hx.1
    have hxEA : x ∈ E ⊔ A := hx.2
    obtain ⟨e, he, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxEA
    -- x = e * a, a = e⁻¹ * x ∈ M.
    have ha_in_M : a ∈ M := by
      have : e⁻¹ * (e * a) ∈ M := M.mul_mem (M.inv_mem (hEM he)) hxM
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem_sup he ⟨ha_in_M, ha⟩
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨hEM hx, Subgroup.mem_sup_left hx⟩
    · intro x ⟨hxM, hxA⟩
      exact ⟨hxM, Subgroup.mem_sup_right hxA⟩

/-- **Dedekind 直接形** (`M ⊆ E ⊔ A` 仮定下): `E, A, M ≤ G`, `E ⊴ G`, `E ≤ M ≤ E ⊔ A`
⇒ `M = E ⊔ (M ⊓ A)`.

Lucchini Thm 2.20 (K=⊥ case) で **直接** 使う形: `M ⊆ AE ⇒ M = E·(A ∩ M) = E ⊔ B`
where `B = A ⊓ M`. `inf_sup_eq_sup_inf_of_normal_of_le` + `inf_eq_left.mpr hMle` で
合成. -/
theorem eq_sup_inf_of_le_sup_of_normal_of_le
    {E A M : Subgroup G} [E.Normal] (hEM : E ≤ M) (hMle : M ≤ E ⊔ A) :
    M = E ⊔ (M ⊓ A) := by
  rw [← inf_sup_eq_sup_inf_of_normal_of_le hEM]
  exact (inf_eq_left.mpr hMle).symm

end Subgroup
