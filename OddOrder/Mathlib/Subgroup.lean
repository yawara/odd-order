/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Finite.Card
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Group

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
* `Subgroup.card_quotient_lt_of_ne_bot`: a finite quotient by a nontrivial subgroup
  has strictly smaller cardinality.

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

/-- If `K ≤ C_G(F)`, then `K ∩ F`, viewed as a subgroup of `K`, lies in `Z(K)`. -/
theorem inf_subgroupOf_le_center_of_le_centralizer {K F : Subgroup G}
    (hK_le_C : K ≤ centralizer (F : Set G)) :
    (K ⊓ F).subgroupOf K ≤ center K := by
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  have hx_inf : (x : G) ∈ K ⊓ F := hx
  have hxF : (x : G) ∈ F := hx_inf.2
  have hyC : (y : G) ∈ centralizer (F : Set G) := hK_le_C y.2
  exact (mem_centralizer_iff.mp hyC (x : G) hxF).symm

/-- **`MulAut` 作用の固定点部分群**: `φ : A →* MulAut G` の下で `∀ a, (φ a) g = g` を
満たす要素全体. mathlib `MulAction.fixedPoints` は Set だが, MulAut 作用の場合は
group 構造を持つので Subgroup として bundle.

下流: Isaacs Lem 4.32 後半 (P p-group on G p-group ⇒ fixedPoints > 1) で使用. -/
def fixedPointsOfMulAut {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    Subgroup G where
  carrier := {g | ∀ a : A, (φ a) g = g}
  one_mem' := fun a => map_one (φ a)
  mul_mem' := fun {x y} hx hy a => by rw [map_mul, hx, hy]
  inv_mem' := fun {x} hx a => by rw [map_inv, hx]

@[simp]
theorem mem_fixedPointsOfMulAut {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {g : G} :
    g ∈ fixedPointsOfMulAut φ ↔ ∀ a : A, (φ a) g = g := Iff.rfl

/-- 自明作用 (`1 : A →* MulAut G`) の固定点は `⊤` (全要素が固定). -/
@[simp]
theorem fixedPointsOfMulAut_one_eq_top {A G : Type*} [Group A] [Group G] :
    fixedPointsOfMulAut (1 : A →* MulAut G) = ⊤ := by
  ext g
  simp only [mem_fixedPointsOfMulAut, Subgroup.mem_top, iff_true]
  intro a
  rfl

/-- **`fixedPointsOfMulAut` の monotonicity (反変)**: B → A の hom があれば
`fixedPoints φ ≤ fixedPoints (φ ∘ f)`. より小さい acting group では固定点が増える. -/
theorem fixedPointsOfMulAut_mono {A B G : Type*} [Group A] [Group B] [Group G]
    (f : B →* A) (φ : A →* MulAut G) :
    fixedPointsOfMulAut φ ≤ fixedPointsOfMulAut (φ.comp f) := by
  intro x hx b
  exact hx (f b)

/-- 内自己同型作用 (`MulAut.conj : G →* MulAut G`) の固定点は `Subgroup.center G`. -/
theorem fixedPointsOfMulAut_conj_eq_center {G : Type*} [Group G] :
    fixedPointsOfMulAut (MulAut.conj : G →* MulAut G) = Subgroup.center G := by
  ext x
  rw [mem_fixedPointsOfMulAut, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg := h g
    rw [MulAut.conj_apply] at hg
    -- hg : g * x * g⁻¹ = x
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hg]
  · intro h g
    rw [MulAut.conj_apply]
    -- want: g * x * g⁻¹ = x
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h g]
      _ = x := by group

/-- **`Subgroup.centralizer` の bijective hom 像**: bijective `f : G →* G'` で
`(centralizer s).map f = centralizer (f '' s)`. mathlib v4.29.1 では `≤` 方向のみ
(`map_centralizer_le_centralizer_image`). -/
theorem map_centralizer_eq_of_bijective {G G' : Type*} [Group G] [Group G']
    (s : Set G) (f : G →* G') (hf : Function.Bijective f) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f)
  intro y hy
  obtain ⟨g, rfl⟩ := hf.surjective y
  refine ⟨g, ?_, rfl⟩
  change g ∈ Subgroup.centralizer s
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp hy (f x) hfx
  rw [← map_mul, ← map_mul] at this
  exact hf.injective this

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

/-- The subgroup generated by all `n`-th powers is characteristic in any group. -/
theorem pow_closure_characteristic {G : Type*} [Group G] (n : ℕ) :
    (closure (Set.range fun x : G => x ^ n)).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact subset_closure ⟨φ x, by simp [map_pow]⟩

/-- In a finite subgroup of prime order, every nonidentity element generates the subgroup. -/
theorem zpowers_eq_of_prime_card {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (hp : (Nat.card R).Prime) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    zpowers r = R := by
  have hle : zpowers r ≤ R := (zpowers_le).mpr hr
  have hord : orderOf r = Nat.card R := by
    rcases (Nat.dvd_prime hp).mp (R.orderOf_dvd_natCard hr) with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hr1
    · exact h
  exact eq_of_le_of_card_ge hle (le_of_eq (by rw [Nat.card_zpowers, hord]))

/-- **`Nat.card (↥K ⧸ N.subgroupOf K) = Nat.card (K.map qmk_N)`** via first iso.
`f := (QuotientGroup.mk' N).comp K.subtype` has `ker = N.subgroupOf K`, `range = K.map qmk_N`.
`quotientKerEquivRange` gives the equiv, take Nat.card_congr. -/
theorem nat_card_quotient_subgroupOf_eq_card_map {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (K : Subgroup G) :
    Nat.card ((↥K) ⧸ (N.subgroupOf K)) = Nat.card (K.map (QuotientGroup.mk' N)) := by
  let f0 : ↥K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hker : f0.ker = N.subgroupOf K := by
    ext ⟨x, hx⟩
    simp only [f0, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f0.range = K.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, hxy⟩
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, hxy⟩
  have hEq : Nat.card ((↥K) ⧸ f0.ker) = Nat.card ↥(f0.range) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f0).toEquiv
  -- Substitute the equal subgroups.
  conv_lhs => rw [show N.subgroupOf K = f0.ker from hker.symm]
  conv_rhs => rw [show K.map (QuotientGroup.mk' N) = f0.range from hrange.symm]
  exact hEq

/-- The image under `K.subtype` of a proper subgroup of `K` is still proper in `K`,
viewed as a subgroup of the ambient group. -/
theorem map_subtype_lt_of_ne_top {G : Type*} [Group G] {K : Subgroup G}
    {N : Subgroup K} (hN : N ≠ ⊤) : N.map K.subtype < K := by
  refine lt_of_le_of_ne (map_subtype_le N) (fun heq => hN ?_)
  have hKeq : K = (⊤ : Subgroup K).map K.subtype := by
    rw [← MonoidHom.range_eq_map, K.range_subtype]
  exact map_injective K.subtype_injective (heq.trans hKeq)

/-- If `K` and `R` complement each other in `G`, and `N ◁ G` lies in `K`, then their
images in `G / N` still complement each other. -/
theorem IsComplement'.map_quotient_of_normal_le_left {G : Type*} [Group G]
    {K R N : Subgroup G} [K.Normal] [N.Normal] (hC : IsComplement' K R) (hNK : N ≤ K) :
    IsComplement' (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  haveI : (K.map (QuotientGroup.mk' N)).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    rintro y hy
    rw [mem_inf] at hy
    obtain ⟨⟨k, hkK, hk⟩, ⟨r, hrR, hr⟩⟩ := hy
    rw [mem_bot]
    have heq : (QuotientGroup.mk' N) k = (QuotientGroup.mk' N) r := hk.trans hr.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at heq
    have hrK : r ∈ K := by
      have hmem : k * (k⁻¹ * r) ∈ K := mul_mem hkK (hNK heq)
      simpa using hmem
    have hrKR : r ∈ K ⊓ R := ⟨hrK, hrR⟩
    rw [disjoint_iff.mp hC.disjoint, mem_bot] at hrKR
    rw [← hr, hrKR, map_one]
  · have hsup : K.map (QuotientGroup.mk' N) ⊔ R.map (QuotientGroup.mk' N) = ⊤ := by
      rw [← map_sup, hC.sup_eq_top,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have hmul := normal_mul (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N))
    rw [hsup, coe_top] at hmul
    exact hmul.symm

/-- Mapping `B ≤ A ≤ H` through `H.subtype` commutes with viewing `B` as a subgroup
of `A`. -/
theorem subgroupOf_map_subtype_eq_map_subgroupOf {H : Subgroup G} {A B : Subgroup H}
    (hBA : B ≤ A) :
    (B.subgroupOf A).map
        (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective).toMonoidHom =
      (B.map H.subtype).subgroupOf (A.map H.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hyB, rfl⟩
    rw [mem_subgroupOf]
    exact ⟨(y : H), hyB, rfl⟩
  · intro hx
    rw [mem_subgroupOf] at hx
    rcases hx with ⟨y, hyB, hyx⟩
    refine ⟨⟨y, hBA hyB⟩, hyB, ?_⟩
    apply Subtype.ext
    exact hyx

/-- Normality of `B.subgroupOf A` is preserved when `B ≤ A ≤ H` is mapped through
`H.subtype`. -/
theorem normal_subgroupOf_map_subtype {H : Subgroup G} {A B : Subgroup H}
    (hBA : B ≤ A) [((B.subgroupOf A) : Subgroup A).Normal] :
    ((B.map H.subtype).subgroupOf (A.map H.subtype)).Normal := by
  let eA : A ≃* A.map H.subtype :=
    Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
  have hmap :
      (B.subgroupOf A).map eA.toMonoidHom =
        (B.map H.subtype).subgroupOf (A.map H.subtype) := by
    simpa [eA] using subgroupOf_map_subtype_eq_map_subgroupOf (H := H) hBA
  rw [← hmap]
  exact (inferInstance : ((B.subgroupOf A) : Subgroup A).Normal).map
    eA.toMonoidHom eA.surjective

/-- Mapping `B ≤ A ≤ H` through `H.subtype` preserves the cardinality of the
quotient layer `A/B`. -/
theorem nat_card_quotient_subgroupOf_map_subtype_eq {H : Subgroup G}
    {A B : Subgroup H} (hBA : B ≤ A)
    [((B.subgroupOf A) : Subgroup A).Normal] :
    Nat.card
        ((A.map H.subtype) ⧸ ((B.map H.subtype).subgroupOf (A.map H.subtype))) =
      Nat.card (A ⧸ B.subgroupOf A) := by
  let eA : A ≃* A.map H.subtype :=
    Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
  have hmap :
      (B.subgroupOf A).map eA.toMonoidHom =
        (B.map H.subtype).subgroupOf (A.map H.subtype) := by
    simpa [eA] using subgroupOf_map_subtype_eq_map_subgroupOf (H := H) hBA
  haveI : ((B.map H.subtype).subgroupOf (A.map H.subtype)).Normal :=
    normal_subgroupOf_map_subtype (H := H) hBA
  exact (Nat.card_congr
    (QuotientGroup.congr (B.subgroupOf A)
      ((B.map H.subtype).subgroupOf (A.map H.subtype)) eA hmap).toEquiv).symm

/-- Quotienting a subgroup by the ambient bottom subgroup preserves cardinality. -/
theorem nat_card_quotient_bot_subgroupOf_eq {H : Subgroup G} :
    Nat.card (H ⧸ ((⊥ : Subgroup G).subgroupOf H)) = Nat.card H := by
  rw [bot_subgroupOf]
  exact Nat.card_congr QuotientGroup.quotientBot.toEquiv

/-- Nilpotence is inherited by the image of a subgroup. -/
theorem isNilpotent_map {H : Type*} [Group H] (K : Subgroup G) [Group.IsNilpotent K]
    (f : G →* H) :
    Group.IsNilpotent (K.map f) := by
  let φ : K →* K.map f :=
    { toFun := fun k => ⟨f k.1, ⟨k.1, k.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.1 y.1) }
  exact nilpotent_of_surjective φ (by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)

/-- A subgroup `V` complementing the normal `N` in `G` (`N ⊓ V = ⊥`, `N ⊔ V = ⊤`) has
`|N| * |V| = |G|`. -/
theorem card_mul_card_of_complement_normal {G : Type*} [Group G] [Finite G] {N V : Subgroup G}
    [N.Normal] (hinf : N ⊓ V = ⊥) (hsup : N ⊔ V = ⊤) :
    Nat.card N * Nat.card V = Nat.card G :=
  (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
    (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])).card_mul

/-- Package complementary subgroups inside a specified ambient subgroup. -/
theorem isComplement'_subgroupOf_of_disjoint_mul_eq_univ {G : Type*} [Group G]
    {U H M : Subgroup G} (hH_le_U : H ≤ U) (hM_le_U : M ≤ U)
    (hHM_bot : H ⊓ M = ⊥)
    (hmul : ∀ x ∈ U, ∃ m ∈ M, ∃ h ∈ H, m * h = x) :
    IsComplement' (M.subgroupOf U) (H.subgroupOf U) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    ext x
    simp only [mem_inf, mem_subgroupOf, mem_bot, Subtype.ext_iff, OneMemClass.coe_one]
    refine ⟨?_, fun hx => by simp [hx]⟩
    rintro ⟨hxM, hxH⟩
    have hx : (x : G) ∈ H ⊓ M := ⟨hxH, hxM⟩
    rw [hHM_bot, mem_bot] at hx
    exact hx
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨m, hmM, h, hhH, hmh⟩ := hmul x x.2
    refine ⟨⟨m, hM_le_U hmM⟩, hmM, ⟨h, hH_le_U hhH⟩, hhH, ?_⟩
    ext
    exact hmh

/-- If `A` is normal and disjoint from `B`, then the restrictions of `A` and `B`
to `A ⊔ B` are complements. -/
theorem isComplement'_subgroupOf_sup_of_normal {G : Type*} [Group G]
    {A B : Subgroup G} [A.Normal] (hAB : Disjoint A B) :
    (A.subgroupOf (A ⊔ B)).IsComplement' (B.subgroupOf (A ⊔ B)) := by
  refine isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (U := A ⊔ B) (H := B) (M := A) le_sup_right le_sup_left ?_ ?_
  · rw [inf_comm, hAB.eq_bot]
  · intro x hx
    have hxmul : (x : G) ∈ (↑A : Set G) * (↑B : Set G) := by
      rw [← Subgroup.normal_mul A B]
      exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := hxmul
    exact ⟨a, ha, b, hb, hab⟩

/-- For a surjective homomorphism `f : G →* H`, the preimage of a subgroup has cardinality
`|K.comap f| = |K| * |ker f|`. -/
theorem card_comap_eq_card_mul_card_ker {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have h1 : (K.comap f).index = K.index := K.index_comap_of_surjective hf
  have h2 : (K.comap f).index * Nat.card (K.comap f) = Nat.card G :=
    (K.comap f).index_mul_card
  have h3 : K.index * Nat.card K = Nat.card H := K.index_mul_card
  have h4 : Nat.card G = Nat.card H * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker]
    exact congrArg (· * _)
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)
  have hidx_ne : K.index ≠ 0 := by
    rw [index_eq_card]
    exact Nat.ne_of_gt Nat.card_pos
  have hstep : K.index * Nat.card (K.comap f) = K.index * (Nat.card K * Nat.card f.ker) := by
    calc
      K.index * Nat.card (K.comap f)
          = (K.comap f).index * Nat.card (K.comap f) := by rw [h1]
      _ = Nat.card G := h2
      _ = Nat.card H * Nat.card f.ker := h4
      _ = (K.index * Nat.card K) * Nat.card f.ker := by rw [h3]
      _ = K.index * (Nat.card K * Nat.card f.ker) := mul_assoc _ _ _
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx_ne) hstep

/-- A finite quotient by a nontrivial subgroup has strictly smaller cardinality.

This is the induction/minimal-counterexample termination bridge used repeatedly when passing
from `G` to `G/K`. Normality is intentionally not required for the cardinal statement. -/
theorem card_quotient_lt_of_ne_bot {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hK : K ≠ ⊥) :
    Nat.card (G ⧸ K) < Nat.card G := by
  have h_eq : Nat.card (G ⧸ K) * Nat.card K = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup K).symm
  have hK_gt : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hK
  have hQ_pos : 0 < Nat.card (G ⧸ K) := Nat.card_pos
  calc
    Nat.card (G ⧸ K) = Nat.card (G ⧸ K) * 1 := (mul_one _).symm
    _ < Nat.card (G ⧸ K) * Nat.card K :=
      (Nat.mul_lt_mul_left hQ_pos).mpr hK_gt
    _ = Nat.card G := h_eq

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem card_lt_card_of_ne_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hindex_ne_one : H.index ≠ 1 := fun hidx => hH (Subgroup.index_eq_one.mp hidx)
  have hindex_gt_one : 1 < H.index :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Subgroup.index_ne_zero_of_finite, hindex_ne_one⟩
  calc
    Nat.card H < Nat.card H * H.index := lt_mul_of_one_lt_right Nat.card_pos hindex_gt_one
    _ = Nat.card G := Subgroup.card_mul_index H

/-- If a finite group's order is coprime to `|A|`, then every subgroup order is too. -/
theorem coprime_card_subgroup_right {A G : Type*} [Group A] [Group G] [Finite G]
    (H : Subgroup G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card H) :=
  hCop.coprime_dvd_right (card_subgroup_dvd_card H)

/-- If a finite group's order is coprime to `|A|`, then every quotient order is too. -/
theorem coprime_card_quotient_right {A G : Type*} [Group A] [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card (G ⧸ N)) :=
  hCop.coprime_dvd_right (card_quotient_dvd_card N)

/-- **`H` is normal when complement of normal `N` with elementwise commute**:
`N ⊴ G`, `H` complement of `N`, `∀ n ∈ N h ∈ H, n*h = h*n` ⇒ `H ⊴ G`.

直積構造 `G ≃ N × H` を導出する古典的事実. Hall-Higman 3.21 case π' で
`H' ⊴ K` 導出に使用. -/
theorem normal_complement_of_commute {G : Type*} [Group G]
    {N H : Subgroup G} [N.Normal] (hCompl : N.IsComplement' H)
    (hCommute : ∀ n ∈ N, ∀ h ∈ H, n * h = h * n) :
    H.Normal := by
  refine ⟨fun h hh g => ?_⟩
  have hsurj : Function.Surjective (fun x : N × H => (x.1 : G) * x.2) := hCompl.surjective
  obtain ⟨⟨⟨n, hn⟩, ⟨h', hh'⟩⟩, hg⟩ := hsurj g
  simp only at hg
  rw [← hg]
  have hy_in_H : h' * h * h'⁻¹ ∈ H := H.mul_mem (H.mul_mem hh' hh) (H.inv_mem hh')
  have heq : (n * h') * h * (n * h')⁻¹ = h' * h * h'⁻¹ := by
    calc (n * h') * h * (n * h')⁻¹
        = n * (h' * h * h'⁻¹) * n⁻¹ := by group
      _ = (h' * h * h'⁻¹) * n * n⁻¹ := by
          rw [hCommute n hn (h' * h * h'⁻¹) hy_in_H]
      _ = h' * h * h'⁻¹ := by group
  rw [heq]
  exact hy_in_H

/-- **comap of subgroup of `C.map qmk` is ≤ C** when `B ≤ C` (`B = ker qmk`).
`K_GB ≤ C.map qmk ⇒ K_GB.comap qmk ≤ B ⊔ C = C`. -/
theorem comap_le_of_le_map_quotient {G : Type*} [Group G]
    {B C : Subgroup G} [B.Normal] (hBC : B ≤ C)
    {K_GB : Subgroup (G ⧸ B)} (hK : K_GB ≤ C.map (QuotientGroup.mk' B)) :
    K_GB.comap (QuotientGroup.mk' B) ≤ C := by
  calc K_GB.comap (QuotientGroup.mk' B)
      ≤ (C.map (QuotientGroup.mk' B)).comap (QuotientGroup.mk' B) :=
        Subgroup.comap_mono hK
    _ = B ⊔ C := QuotientGroup.comap_map_mk' B C
    _ = C := by rw [sup_comm]; exact sup_of_le_left hBC

/-- If `K / N` is a `p`-group, then the image of `K` in the ambient quotient by
`N.map K.subtype` is a `p`-group. -/
theorem isPGroup_map_quotient_subtype_of_isPGroup_quotient {G : Type*} [Group G]
    {K : Subgroup G} {N : Subgroup K} [N.Normal] [(N.map K.subtype).Normal] {p : ℕ}
    (hN : IsPGroup p (K ⧸ N)) :
    IsPGroup p (K.map (QuotientGroup.mk' (N.map K.subtype))) := by
  intro x
  obtain ⟨g, hgK, hgx⟩ := x.2
  obtain ⟨n, hn⟩ := hN (QuotientGroup.mk' N ⟨g, hgK⟩)
  refine ⟨n, ?_⟩
  have hgN : (⟨g, hgK⟩ : K) ^ p ^ n ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hn
  have hgL : (g : G) ^ p ^ n ∈ N.map K.subtype := by
    simpa using Subgroup.mem_map_of_mem K.subtype hgN
  apply Subtype.ext
  change ((x : G ⧸ N.map K.subtype)) ^ p ^ n = 1
  rw [← hgx, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hgL

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

/-- **Dedekind / modular law, normalizer form**: if `W ≤ L`, `A ⊓ L = ⊥`, and `A` normalizes `W`,
then `(W ⊔ A) ⊓ L = W`.  Unlike `inf_sup_eq_sup_inf_of_normal_of_le`, this needs only that `A`
*normalizes* `W` (so `W` is normal in `W ⊔ A`), not global normality — fitting the BG step 3(ii)
situation `(Q₁ ⊔ D) ⊓ Q = Q₁` (`Q₁ ≤ Q`, `D ⊓ Q = ⊥`, `D ≤ N_G(Q₁)`).  The noncommutative case is
handled via the product representation `W·A` of `W ⊔ A`. -/
theorem inf_sup_eq_of_le_normalizer_of_inf_eq_bot
    {W A L : Subgroup G} (hW_le : W ≤ L) (hA_inf : A ⊓ L = ⊥)
    (hAnorm : A ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊔ A) ⊓ L = W := by
  apply le_antisymm
  · intro x ⟨hxWA, hxL⟩
    haveI : (W.subgroupOf (A ⊔ W)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hAnorm
    have hx_AW : x ∈ A ⊔ W := by rw [sup_comm]; exact hxWA
    have hmem : (⟨x, hx_AW⟩ : ↥(A ⊔ W)) ∈ (W.subgroupOf (A ⊔ W)) ⊔ (A.subgroupOf (A ⊔ W)) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right) (le_sup_left), sup_comm W A,
        Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨⟨w, hw_AW⟩, hw, ⟨a, ha_AW⟩, ha, heq⟩ := hmem
    have hxeq : x = w * a := congrArg (Subtype.val) heq |>.symm
    have ha_L : a ∈ L := by
      have : w⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hW_le hw)) hxL
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have ha_one : a = 1 := by
      have : a ∈ A ⊓ L := ⟨ha, ha_L⟩
      rw [hA_inf, Subgroup.mem_bot] at this; exact this
    rw [hxeq, ha_one, mul_one]; exact hw
  · exact le_inf le_sup_left hW_le

end Subgroup
