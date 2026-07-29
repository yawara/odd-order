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
* **9D.2** `isSubnormal_strongCore` / `normal_strongCore_subgroupOf` — `X` の強共役すべての
  交わり `L` (= `strongCore X`) は `X` に normal かつ `G` に **subnormal**。
  書籍 hint の `L^{(G)} ⊆ X` は `strongClosure_strongCore_le`。

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

section /- 9D.2: 強共役全体の交わりは X に normal かつ G に subnormal (p. 294) -/

open scoped Pointwise

/-- **強共役核** `L`: `X` の強共役すべての交わり (`strongClosure` = `X^{(G)}` の双対)。

Isaacs Problem 9D.2 (p. 294) の主役。 -/
def strongCore (X : Subgroup G) : Subgroup G :=
  sInf {Y : Subgroup G | IsStronglyConjugate X Y}

theorem strongCore_le_of_isStronglyConjugate {X Y : Subgroup G}
    (h : IsStronglyConjugate X Y) : strongCore X ≤ Y :=
  sInf_le h

theorem strongCore_le (X : Subgroup G) : strongCore X ≤ X :=
  strongCore_le_of_isStronglyConjugate (IsStronglyConjugate.rfl X)

/-- `x ∈ X` による共役は `X` 自身を保つ。 -/
theorem conjAct_smul_eq_self_of_mem {X : Subgroup G} {y : G} (hy : y ∈ X) :
    ConjAct.toConjAct y • X = X :=
  (conjAct_smul_eq_map y X).trans
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy))

/-- `x ∈ X` による共役は `X` の強共役全体を置換するので, `L` を保つ。 -/
theorem smul_strongCore_le {X : Subgroup G} {x : G} (hx : x ∈ X) :
    ConjAct.toConjAct x • strongCore X ≤ strongCore X := by
  refine le_sInf fun Y hY => ?_
  have hconj : IsStronglyConjugate X (ConjAct.toConjAct x⁻¹ • Y) := by
    have h := hY.conjAct_smul (ConjAct.toConjAct x⁻¹)
    rwa [conjAct_smul_eq_self_of_mem (X.inv_mem hx)] at h
  have hle := (Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := ConjAct.toConjAct x)).mpr (strongCore_le_of_isStronglyConjugate hconj)
  rwa [map_inv, smul_inv_smul] at hle

/-- `X` は `L` を正規化する。 -/
theorem le_normalizer_strongCore (X : Subgroup G) :
    X ≤ Subgroup.normalizer (strongCore X) := by
  intro x hx
  have hge : strongCore X ≤ ConjAct.toConjAct x • strongCore X := by
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := ConjAct.toConjAct x)).mpr (smul_strongCore_le (X := X) (X.inv_mem hx))
    rwa [map_inv, smul_inv_smul] at h
  have heq : ConjAct.toConjAct x • strongCore X = strongCore X :=
    le_antisymm (smul_strongCore_le hx) hge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    ((conjAct_smul_eq_map x (strongCore X)).symm.trans heq)

/-- **9D.2 の hint** ⭐: `L^{(G)} ≤ X`。

`M = g • L` が `L` の強共役 (`g ∈ L ⊔ M`) なら, その関係を `g⁻¹` で共役して
`g ∈ L ⊔ (g⁻¹ • L)` を得る。`L ≤ X` なので `g⁻¹ ∈ X ⊔ (g⁻¹ • X)`, すなわち
**`g⁻¹ • X` は `X` の強共役**。ゆえに `L ≤ g⁻¹ • X`, つまり `M = g • L ≤ X`。 -/
theorem strongClosure_strongCore_le (X : Subgroup G) :
    strongClosure (strongCore X) ≤ X := by
  refine strongClosure_le fun M hM => ?_
  obtain ⟨g, hg, rfl⟩ := hM
  set c : ConjAct G := ConjAct.toConjAct g with hc
  -- `g ∈ L ⊔ c • L` を `c⁻¹` で共役して `g ∈ (c⁻¹ • L) ⊔ L`
  have hg' : g ∈ (c⁻¹ • strongCore X) ⊔ strongCore X := by
    have hmem : g ∈ c⁻¹ • (strongCore X ⊔ c • strongCore X) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc]
      simpa [ConjAct.toConjAct_smul] using hg
    rwa [conjAct_smul_sup, inv_smul_smul] at hmem
  -- ゆえに `g⁻¹ ∈ X ⊔ c⁻¹ • X`, すなわち `c⁻¹ • X` は `X` の強共役
  have hsub : (c⁻¹ • strongCore X) ⊔ strongCore X ≤ X ⊔ c⁻¹ • X :=
    sup_le (le_sup_of_le_right (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (strongCore_le X)))
      (le_sup_of_le_left (strongCore_le X))
  have hgX : g⁻¹ ∈ X ⊔ c⁻¹ • X := Subgroup.inv_mem _ (hsub hg')
  have hSC : IsStronglyConjugate X (c⁻¹ • X) := by
    refine ⟨g⁻¹, hgX, ?_⟩
    rw [hc, ← map_inv]
  -- `L ≤ c⁻¹ • X` を `c` で戻す
  have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := c)).mpr
    (strongCore_le_of_isStronglyConjugate hSC)
  rwa [smul_inv_smul] at h

/-- **Isaacs Problem 9D.2** (書籍 p. 294) ⭐: `X` の強共役すべての交わり `L` は
`X` に normal かつ `G` に **subnormal**。

subnormal 性: `L ≤ L^{(G)} ≤ X` (hint) と `L ◁ X` から `L ◁ L^{(G)}`, そして
`L^{(G)} ◁◁ G` (Theorem 9.28 = Bartels) なので `L ◁◁ G`。 -/
theorem isSubnormal_strongCore [Finite G] (X : Subgroup G) : (strongCore X).IsSubnormal := by
  refine Subgroup.IsSubnormal.step _ (strongClosure (strongCore X))
    (le_strongClosure _) (strongClosure_isSubnormal _) ?_
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_strongClosure _)).mpr ?_
  exact (strongClosure_strongCore_le X).trans (le_normalizer_strongCore X)

/-- **9D.2 の前半**: `L` は `X` に normal。 -/
theorem normal_strongCore_subgroupOf (X : Subgroup G) :
    ((strongCore X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (strongCore_le X)).mpr
    (le_normalizer_strongCore X)

end -- 9D.2

end OddOrder.Isaacs.Ch09
