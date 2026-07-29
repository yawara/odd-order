/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.Conjugacy

/-!
# Isaacs Problem 3C.7(c) — 冪零商と Carter 部分群

有限可解群 `G` の Carter 部分群 `C` と正規部分群 `N` について, `G ⧸ N` が冪零なら
`NC = G` (`sup_eq_top_of_isNilpotent_quotient`)。

要は **Carter 部分群を含む部分群はすべて自己正規化**
(`normalizer_eq_self_of_isCarterSubgroup_le`) という事実で, これは (b) の共役性
(`exists_conj_of_isCarterSubgroup`) から直ちに従う: `g` が `K ⊇ C` を正規化すれば
`C` と `C^g` はどちらも `↥K` の Carter 部分群なので `K` 内で共役, それを `N_G(C) = C` に
流し込むと `g ∈ K`。

`K := NC` に適用すると `K` は自己正規化, 対応定理で `K/N` も `G/N` で自己正規化,
`G/N` は冪零なので自己正規化部分群は `⊤` のみ, ゆえに `K/N = ⊤` で `K = ⊤`。

## Main results

- `normalizer_eq_self_of_isCarterSubgroup_le` — Carter 部分群を含む部分群は自己正規化。
- `sup_eq_top_of_isNilpotent_quotient` — **Problem 3C.7(c)**。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.7(c): 冪零商 -/

variable {G : Type*} [Group G]

/-- **Carter 部分群を含む部分群は自己正規化** (Carter 部分群は abnormal)。

`g ∈ N_G(K)` とすると `C ≤ K` から `C^g ≤ K^g = K` で, `C` と `C^g` はともに `↥K` の
Carter 部分群 (`IsCarterSubgroup.subgroupOf`)。3C.7(b) を `↥K` に適用して
`y ∈ K` で `C^y = C^g` を得ると `C^(g⁻¹y) = C`, つまり `g⁻¹y ∈ N_G(C) = C ≤ K`,
`y ∈ K` と合わせて `g ∈ K`。 -/
theorem normalizer_eq_self_of_isCarterSubgroup_le [Finite G] [IsSolvable G]
    {C K : Subgroup G} (hC : IsCarterSubgroup C) (hCK : C ≤ K) :
    Subgroup.normalizer (K : Set G) = K := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  have hCgK : C.map (MulAut.conj g).toMonoidHom ≤ K := map_conj_le_of_mem_normalizer hCK hg
  obtain ⟨y, hy⟩ := exists_conj_of_isCarterSubgroup (hC.subgroupOf hCK)
    ((hC.map_conj g).subgroupOf hCgK)
  rw [map_conj_eq_iff_subgroupOf hCK hCgK y] at hy
  have hgy : C.map (MulAut.conj (g⁻¹ * (y : G))).toMonoidHom = C := by
    rw [← map_conj_trans, hy, map_conj_trans, inv_mul_cancel, map_conj_one]
  have hmem : g⁻¹ * (y : G) ∈ C := by
    rw [← hC.normalizer_eq]
    exact map_conj_eq_self_iff_mem_normalizer.mp hgy
  have hinv : g⁻¹ ∈ K := by
    have := K.mul_mem (hCK hmem) (K.inv_mem y.2)
    simpa [mul_assoc] using this
  simpa using K.inv_mem hinv

/-- **Isaacs Problem 3C.7(c)** (書籍 p. 91): `C` が有限可解群 `G` の Carter 部分群で
`G ⧸ N` が冪零なら `NC = G`。

`K := NC` は `C` を含むので自己正規化 (`normalizer_eq_self_of_isCarterSubgroup_le`)。
`N ≤ K` なので対応定理 (`normalizer_eq_iff_map_mk'`) で `K/N` も `G/N` で自己正規化,
`G/N` は冪零なので `K/N = ⊤`, `N ≤ K` から `K = ⊤`。 -/
theorem sup_eq_top_of_isNilpotent_quotient [Finite G] [IsSolvable G] {C N : Subgroup G}
    [N.Normal] (hC : IsCarterSubgroup C) (hnil : Group.IsNilpotent (G ⧸ N)) :
    N ⊔ C = ⊤ := by
  haveI := hnil
  have hNK : N ≤ N ⊔ C := le_sup_left
  have hbar : Subgroup.normalizer
      (((N ⊔ C).map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (N ⊔ C).map (QuotientGroup.mk' N) :=
    (normalizer_eq_iff_map_mk' (N ⊔ C) hNK).mpr
      (normalizer_eq_self_of_isCarterSubgroup_le hC le_sup_right)
  have htop : (N ⊔ C).map (QuotientGroup.mk' N) = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ hbar
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' N)) htop
  rwa [Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNK),
    Subgroup.comap_top] at hcomap

end -- 3C.7(c)

end OddOrder.Isaacs.Ch03
