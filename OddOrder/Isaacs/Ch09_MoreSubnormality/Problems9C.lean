/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.ThompsonWielandt

/-!
# Isaacs §9C の演習 (書籍 pp. 288-289)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9C
(Thompson–Wielandt 周辺)。statement はページ画像
`references/isaacs/pages/isaacs-p288-301.png` / `isaacs-p289-302.png` で確定。

* **9C.1** `relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal` — Thm 9.24 の設定で
  `H`, `K` がともに `G` で **subnormal** なら `U = 1` または `V = 1`。

## 9C.1 の証明 (書籍 hint に沿う)

`U ≠ 1` かつ `V ≠ 1` と仮定する。Thm 9.24 (`thompsonWielandt`) からある素数 `p` で
`U` または `V` が `p`-群。`U ◁ H ◁◁ G` なので `U ◁◁ G`、同様に `V ◁◁ G`。
非自明な subnormal `p`-部分群は `O_p(G)` に入る (`le_oPiCore_of_isSubnormal`, issue 9216)
ので **`O_p(G) > 1`**。

`Z := Z(O_p(G))` (ambient で `centerPCore p G`) は `O_p(G)` に characteristic ゆえ `G` に
normal で、非自明 (非自明な `p`-群の中心)。書籍 hint の核心は **`Z ≤ H`**:

* `U` が `p`-群のとき: `U ≤ O_p(G)` なので `Z` は `U` を中心化する。よって
  `Z ≤ C_G(U) ≤ N_G(U) = H`。
* `U` が `p`-群でないとき: `X := O^p(U) ≠ 1` で `X ≤ U ≤ D`, `N_G(U) ≤ N_G(X)` ゆえ
  `N_G(X) = H`。Corollary 9.27 (`le_normalizer_pResidualOf_of_isSubnormal`) が
  `O_p(G) ≤ N_G(O^p(U)) = H` を与えるので `Z ≤ O_p(G) ≤ H`。

`V` について同じ議論で `Z ≤ K`、すなわち `1 ≠ Z ≤ D` が `G` に normal。`H ≠ K` なので
`H` か `K` の一方は `⊤` より真に小さく、`NoNormalInSupergroup` に矛盾する。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

section /- 9C.1: H, K がともに subnormal なら U = 1 または V = 1 (p. 288) -/

/-- **`Z(O_p(G))`** を ambient 群 `G` の部分群として実現したもの。 -/
def centerPCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (Subgroup.center ↥(Ch03.oPiCore ({p} : Set ℕ) G)).map
    (Ch03.oPiCore ({p} : Set ℕ) G).subtype

theorem centerPCore_le {p : ℕ} : centerPCore p G ≤ Ch03.oPiCore ({p} : Set ℕ) G :=
  Subgroup.map_subtype_le _

/-- `O_p(G)` は `p`-群 (`oPiCore` が `π`-群であることの singleton 版)。 -/
theorem isPGroup_oPiCore [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
  isPGroup_of_isPiSubgroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))

/-- `Z(O_p(G))` は `G` に normal (`O_p(G) ◁ G` の characteristic 部分群)。 -/
instance centerPCore_normal {p : ℕ} : (centerPCore p G).Normal :=
  map_subtype_normal_of_characteristic _

/-- `Z(O_p(G))` の元は `O_p(G)` の元と可換。 -/
theorem centerPCore_commute {p : ℕ} {z u : G} (hz : z ∈ centerPCore p G)
    (hu : u ∈ Ch03.oPiCore ({p} : Set ℕ) G) : u * z = z * u := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨u, hu⟩)

/-- `O_p(G) ≠ 1` なら `Z(O_p(G)) ≠ 1` (非自明な `p`-群の中心は非自明)。 -/
theorem centerPCore_ne_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (hP : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥) : centerPCore p G ≠ ⊥ := by
  haveI : Nontrivial ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  have hcenter : Subgroup.center ↥(Ch03.oPiCore ({p} : Set ℕ) G) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp isPGroup_oPiCore.center_nontrivial
  intro hbot
  exact hcenter ((Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.subtype_injective _)).mp hbot)

/-- **9C.1 の核** ⭐: `D` に含まれ `H` に normal な非自明部分群 `U` があり `H ◁◁ G` なら
`Z(O_p(G)) ≤ H`。

書籍 hint の「`U` が `p`-群であるかどうかで場合分け」がここ。`hnorm` は
`NoNormalInSupergroup` から取れる形 (`normalizer_eq_left_of_noNormal` /
`normalizer_eq_right_of_noNormal`) で渡す。 -/
theorem centerPCore_le_of_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {H U D : Subgroup G}
    (hUbot : U ≠ ⊥) (hUH : U ≤ H) (hUD : U ≤ D)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hHsn : H.IsSubnormal)
    (hnorm : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ D →
      H ≤ Subgroup.normalizer (W : Set G) → Subgroup.normalizer (W : Set G) = H) :
    centerPCore p G ≤ H := by
  have hUsn : U.IsSubnormal :=
    Subgroup.IsSubnormal.step U H hUH hHsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn)
  by_cases hUp : IsPGroup p ↥U
  · -- `U ≤ O_p(G)`; `Z(O_p(G))` は `U` を中心化するので `N_G(U) = H` に入る
    have hUP : U ≤ Ch03.oPiCore ({p} : Set ℕ) G :=
      le_oPiCore_of_isSubnormal hUsn (Subgroup.isPiSubgroup_of_isPGroup_of_mem hUp rfl)
    rw [← hnorm U hUbot hUD hUn]
    refine le_trans (fun z hz => ?_) (Subgroup.centralizer_le_normalizer (U : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => centerPCore_commute hz (hUP hu)
  · -- `X = O^p(U) ≠ 1`; Corollary 9.27 で `O_p(G) ≤ N_G(X) = H`
    have hX : pResidualOf p U ≠ ⊥ := fun h => hUp ((pResidualOf_eq_bot_iff_isPGroup U).mp h)
    have hXn : H ≤ Subgroup.normalizer (pResidualOf p U : Set G) :=
      hUn.trans (normalizer_le_normalizer_pResidualOf p U)
    have hNX := hnorm _ hX ((pResidualOf_le p U).trans hUD) hXn
    have hPX := le_normalizer_pResidualOf_of_isSubnormal (p := p)
      (P := Ch03.oPiCore ({p} : Set ℕ) G) hUsn isPGroup_oPiCore
    rw [hNX] at hPX
    exact centerPCore_le.trans hPX

/-- **Isaacs Problem 9C.1** (書籍 p. 288) ⭐: Theorem 9.24 の設定に加えて `H`, `K` が
ともに `G` で **subnormal** なら, `U = 1` または `V = 1`
(`U = core_H(E)`, `V = core_K(E)`, `E = thompsonWielandtCore H K`)。

すなわち Thm 9.24 の結論「`U` か `V` が `p`-群」は subnormal な場合には
「`U` か `V` が自明」まで強まる。 -/
theorem relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal [Finite G] {H K : Subgroup G}
    (hHK : H ≠ K) (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hHsn : H.IsSubnormal) (hKsn : K.IsSubnormal) :
    relCore H (thompsonWielandtCore H K) = ⊥ ∨ relCore K (thompsonWielandtCore H K) = ⊥ := by
  by_contra hcon
  obtain ⟨hU, hV⟩ := not_or.mp hcon
  set E := thompsonWielandtCore H K with hE
  -- `U`, `V` の基本性質
  have hUH : relCore H E ≤ H := relCore_le_left H E
  have hKV : relCore K E ≤ K := relCore_le_left K E
  have hUD : relCore H E ≤ H ⊓ K := (relCore_le H E).trans (thompsonWielandtCore_le H K)
  have hVD : relCore K E ≤ H ⊓ K := (relCore_le K E).trans (thompsonWielandtCore_le H K)
  have hUn : H ≤ Subgroup.normalizer (relCore H E : Set G) := le_normalizer_relCore H E
  have hVn : K ≤ Subgroup.normalizer (relCore K E : Set G) := le_normalizer_relCore K E
  have hUsn : (relCore H E).IsSubnormal :=
    Subgroup.IsSubnormal.step _ H hUH hHsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn)
  have hVsn : (relCore K E).IsSubnormal :=
    Subgroup.IsSubnormal.step _ K hKV hKsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKV).mpr hVn)
  -- Thm 9.24: ある `p` で `U` か `V` が `p`-群 ⟹ `O_p(G) > 1`
  obtain ⟨p, hp, hpg⟩ := thompsonWielandt H K hHK hyp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPbot : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥ := by
    rcases hpg with hg | hg
    · exact fun h => hU (le_bot_iff.mp (h ▸ le_oPiCore_of_isSubnormal hUsn
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem hg rfl)))
    · exact fun h => hV (le_bot_iff.mp (h ▸ le_oPiCore_of_isSubnormal hVsn
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem hg rfl)))
  -- `Z = Z(O_p(G))` は非自明・`G`-normal で `H` にも `K` にも入る
  have hZH : centerPCore p G ≤ H :=
    centerPCore_le_of_ne_bot hU hUH hUD hUn hHsn
      fun W hW hWD hWn => normalizer_eq_left_of_noNormal hyp hW hWD hWn
  have hZK : centerPCore p G ≤ K :=
    centerPCore_le_of_ne_bot hV hKV hVD hVn hKsn
      fun W hW hWD hWn => normalizer_eq_right_of_noNormal hyp hW hWD hWn
  -- `H ≠ K` なので一方は `⊤` より真に小さい: `NoNormalInSupergroup` に矛盾
  have hlt : H < ⊤ ∨ K < ⊤ := by
    rcases eq_or_ne H ⊤ with rfl | h
    · exact Or.inr (lt_top_iff_ne_top.mpr fun hKtop => hHK hKtop.symm)
    · exact Or.inl (lt_top_iff_ne_top.mpr h)
  refine hyp ⊤ hlt (centerPCore p G) (centerPCore_ne_bot hPbot) (le_inf hZH hZK) ?_
  rw [Subgroup.normalizer_eq_top]

end -- 9C.1

end OddOrder.Isaacs.Ch09
