/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Isaacs Problem 3C.7 (書籍 p. 91) — Carter 部分群の定義と基本性質

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 3C.7 の形式化
(campaign issue 1055)。**書籍は証明を与えない** (challenge problem) ので、証明は自前。

**Carter 部分群** = 冪零かつ自己正規化 (`C = N_G(C)`) な部分群。3C.7 は
(a) 可解群には Carter 部分群が存在する / (b) 全て共役 / (c) `G/N` 冪零なら `NC = G`
を主張する。本ファイルは定義と、3 つの主張すべてが土台にする基本補題を置く。

## Main results

- `IsCarterSubgroup` — 定義。
- `IsCarterSubgroup.eq_top_of_isNilpotent` — 冪零群の Carter 部分群は `⊤` のみ。
- `isCarterSubgroup_top_of_isNilpotent` — 冪零群では `⊤` が Carter 部分群。
- `IsCarterSubgroup.map_conj` — Carter 性は共役で保たれる。
- `IsCarterSubgroup.subgroupOf` — `C ≤ K` なら `C` は `↥K` の Carter 部分群。
- `map_conj_eq_iff_subgroupOf` — `↥K` 内の共役と `G` 内の共役の翻訳。
- `map_conj_trans` / `map_conj_one` / `map_conj_eq_self_iff_mem_normalizer` /
  `map_conj_le_of_mem_normalizer` — 共役操作そのものの基本補題。

⚠ 「`N ⊴ G` なら `N_G(C) ≤ N_G(C ⊔ N)`」(3C.7 の帰納全体が使う土台) は mathlib に
`Subgroup.normalizer_le_normalizer_sup_normal` として既にあるので, ここでは重複させない
(ラッパー方針)。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C: Problem 3C.7 — Carter 部分群 (p. 91) -/

variable {G : Type*} [Group G]

/-- **Carter 部分群** (Isaacs Problem 3C.7, 書籍 p. 91): 冪零かつ自己正規化な部分群。

書籍の定義は「`C` nilpotent かつ `C = N_G(C)`」。mathlib の `Subgroup.normalizer` は
`Set G` を取るので `Subgroup.normalizer (C : Set G) = C` と書く。 -/
def IsCarterSubgroup (C : Subgroup G) : Prop :=
  Group.IsNilpotent ↥C ∧ Subgroup.normalizer (C : Set G) = C

theorem IsCarterSubgroup.isNilpotent {C : Subgroup G} (h : IsCarterSubgroup C) :
    Group.IsNilpotent ↥C := h.1

theorem IsCarterSubgroup.normalizer_eq {C : Subgroup G} (h : IsCarterSubgroup C) :
    Subgroup.normalizer (C : Set G) = C := h.2

/-- 冪零群では自己正規化部分群は `⊤` だけなので, Carter 部分群は `⊤` に限る。

`Group.normalizerCondition_of_isNilpotent` +
`normalizerCondition_iff_only_full_group_self_normalizing`。 -/
theorem IsCarterSubgroup.eq_top_of_isNilpotent [Group.IsNilpotent G] {C : Subgroup G}
    (h : IsCarterSubgroup C) : C = ⊤ :=
  normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent C h.2

/-- 冪零群では `⊤` が Carter 部分群。 -/
theorem isCarterSubgroup_top_of_isNilpotent [Group.IsNilpotent G] :
    IsCarterSubgroup (⊤ : Subgroup G) :=
  ⟨Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm,
    Subgroup.normalizer_eq_top_iff.mpr inferInstance⟩

/-- Carter 性は共役で保たれる。 -/
theorem IsCarterSubgroup.map_conj {C : Subgroup G} (h : IsCarterSubgroup C) (g : G) :
    IsCarterSubgroup (C.map (MulAut.conj g).toMonoidHom) := by
  haveI := h.1
  refine ⟨Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective), ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq C (MulAut.conj g), h.2]

/-- `C ≤ K` で `C` が `G` の Carter 部分群なら, `C` は `↥K` の Carter 部分群
(`N_K(C) = N_G(C) ⊓ K = C`)。

`Subgroup.subgroupOf_normalizer_eq` (`(N_G(C)).subgroupOf K = N_K(C.subgroupOf K)`) で
正規化群を移し, 冪零性は `Subgroup.subgroupOfEquivOfLe` で移す。 -/
theorem IsCarterSubgroup.subgroupOf {C K : Subgroup G} (h : IsCarterSubgroup C) (hCK : C ≤ K) :
    IsCarterSubgroup (C.subgroupOf K) := by
  haveI := h.1
  exact ⟨Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCK).symm,
    by rw [← Subgroup.subgroupOf_normalizer_eq hCK, h.2]⟩

/-- 共役の合成: `(C^a)^b = C^(b * a)`。 -/
theorem map_conj_trans (C : Subgroup G) (a b : G) :
    (C.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom
      = C.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

@[simp]
theorem map_conj_one (C : Subgroup G) :
    C.map (MulAut.conj (1 : G)).toMonoidHom = C := by
  ext x
  simp

/-- `C^a = C` ⟺ `a ∈ N_G(C)` (`.toMonoidHom` 綴り版)。 -/
theorem map_conj_eq_self_iff_mem_normalizer {C : Subgroup G} {a : G} :
    C.map (MulAut.conj a).toMonoidHom = C ↔ a ∈ Subgroup.normalizer (C : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

/-- 共役部分群は元の部分群を含む部分群に写る: `C ≤ K`, `g ∈ N_G(K)` なら `C^g ≤ K`。 -/
theorem map_conj_le_of_mem_normalizer {C K : Subgroup G} (hCK : C ≤ K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    C.map (MulAut.conj g).toMonoidHom ≤ K := by
  calc C.map (MulAut.conj g).toMonoidHom
      ≤ K.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hCK
    _ = K := map_conj_eq_self_iff_mem_normalizer.mpr hg

/-- `C ≤ K` のとき, `↥K` の中の共役は `G` の中の共役の `subgroupOf` に一致する。 -/
theorem map_conj_subgroupOf {C K : Subgroup G} (hC : C ≤ K) (y : ↥K) :
    (C.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf K
      = (C.subgroupOf K).map (MulAut.conj y).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, hcx⟩
    exact ⟨⟨c, hC hc⟩, by simpa [Subgroup.mem_subgroupOf] using hc,
      Subtype.ext (by simpa using hcx)⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨(c : G), by simpa [Subgroup.mem_subgroupOf] using hc,
      by simpa using congrArg Subtype.val hcx⟩

/-- `C, C' ≤ K` のとき, `↥K` 内での共役 `C^y = C'` と `G` 内での共役 `C^{↑y} = C'` は同値。

3C.7 の帰納が部分群 `↥K` へ降りて戻るときの翻訳。 -/
theorem map_conj_eq_iff_subgroupOf {C C' K : Subgroup G} (hC : C ≤ K) (hC' : C' ≤ K) (y : ↥K) :
    (C.subgroupOf K).map (MulAut.conj y).toMonoidHom = C'.subgroupOf K ↔
      C.map (MulAut.conj (y : G)).toMonoidHom = C' := by
  have hle : C.map (MulAut.conj (y : G)).toMonoidHom ≤ K := by
    rintro - ⟨c, hc, rfl⟩
    exact K.mul_mem (K.mul_mem y.2 (hC hc)) (K.inv_mem y.2)
  rw [← map_conj_subgroupOf hC y, Subgroup.subgroupOf_inj, inf_of_le_left hle,
    inf_of_le_left hC']

end -- Problem 3C.7 定義

end OddOrder.Isaacs.Ch03
