/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalClosure

/-!
# Isaacs §9D の演習 (書籍 p. 294)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9D
(subnormal closure / strong conjugacy 周辺)。

* **9D.1** `exists_unique_greatest_isSubnormal_le` — `X ≤ G` に対し「`X` の部分群であって
  `G` に subnormal なもの」のうち一意最大のもの (= **subnormal core** `subnormalCore X`)
  が存在し, それは `X` に normal。

## 9D.1 について

subnormal closure (`strongClosure`, Thm 9.28 = Bartels) の双対。存在は
**Wielandt の結合定理の族版** (`Ch02.isSubnormal_sSup_of_isSubnormal`: 有限群では
subnormal 部分群の任意集合の `sSup` が subnormal) から直ちに従うので,
`subnormalCore X := sSup {S | S ≤ X ∧ S.IsSubnormal}` と定義してよい。

`X` での正規性は「共役 `(subnormalCore X)^x` (`x ∈ X`) も `X` に含まれる subnormal 部分群
だから最大性で `≤ subnormalCore X`」という定型。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9D.1: subnormal core の存在と X-正規性 (p. 294) -/

/-- **subnormal core** `X_{(G)}` (Isaacs Problem 9D.1, p. 294): `X` に含まれ `G` に
subnormal な部分群すべての join。

有限群では Wielandt の結合定理 (族版) によりこれ自身が subnormal なので,
「`X` の subnormal 部分群のうち最大のもの」になる。 -/
def subnormalCore (X : Subgroup G) : Subgroup G :=
  sSup {S : Subgroup G | S ≤ X ∧ S.IsSubnormal}

theorem subnormalCore_le (X : Subgroup G) : subnormalCore X ≤ X :=
  sSup_le fun _ hS => hS.1

/-- 最大性: `X` に含まれる subnormal 部分群は `subnormalCore X` に入る。 -/
theorem le_subnormalCore {X S : Subgroup G} (hSX : S ≤ X) (hS : S.IsSubnormal) :
    S ≤ subnormalCore X :=
  le_sSup ⟨hSX, hS⟩

/-- `subnormalCore X` 自身が `G` に subnormal (Wielandt の結合定理の族版)。 -/
theorem isSubnormal_subnormalCore [Finite G] (X : Subgroup G) :
    (subnormalCore X).IsSubnormal :=
  Ch02.isSubnormal_sSup_of_isSubnormal fun _ hS => hS.2

/-- `X` は `subnormalCore X` を正規化する: `x ∈ X` による共役も `X` に含まれる subnormal
部分群なので最大性で `subnormalCore X` に戻る。 -/
theorem le_normalizer_subnormalCore [Finite G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer (subnormalCore X) := by
  have key : ∀ x ∈ X, (subnormalCore X).map (MulAut.conj x : G →* G) ≤ subnormalCore X := by
    intro x hx
    refine le_subnormalCore ?_
      (Subgroup.IsSubnormal.map (MulAut.conj x).surjective (isSubnormal_subnormalCore X))
    rintro _ ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem hx (subnormalCore_le X hy)) (X.inv_mem hx)
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  -- 包含は上で得た。共役は単射なので位数が等しく, 包含から等号が出る。
  refine Subgroup.eq_of_le_of_card_ge (key x hx) (ge_of_eq ?_)
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj x : G →* G)
    (MulAut.conj x).injective).toEquiv).symm

/-- **9D.1 の後半**: subnormal core は `X` に normal。 -/
theorem normal_subnormalCore_subgroupOf [Finite G] (X : Subgroup G) :
    ((subnormalCore X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (subnormalCore_le X)).mpr
    (le_normalizer_subnormalCore X)

/-- **Isaacs Problem 9D.1** (書籍 p. 294) ⭐: `X ≤ G` に対し, `X` の部分群であって `G` に
subnormal なもののうち**一意最大**のもの (subnormal core) が存在する。

`subnormalCore X` がそれであり (`subnormalCore_le` / `isSubnormal_subnormalCore` /
`le_subnormalCore`), さらに `X` に normal (`normal_subnormalCore_subgroupOf`)。 -/
theorem exists_unique_greatest_isSubnormal_le [Finite G] (X : Subgroup G) :
    ∃! S : Subgroup G, (S ≤ X ∧ S.IsSubnormal) ∧
      ∀ T : Subgroup G, T ≤ X → T.IsSubnormal → T ≤ S := by
  refine ⟨subnormalCore X,
    ⟨⟨subnormalCore_le X, isSubnormal_subnormalCore X⟩, fun _ h₁ h₂ => le_subnormalCore h₁ h₂⟩,
    fun S hS => ?_⟩
  exact le_antisymm (le_subnormalCore hS.1.1 hS.1.2)
    (hS.2 _ (subnormalCore_le X) (isSubnormal_subnormalCore X))

end -- 9D.1

end OddOrder.Isaacs.Ch09
