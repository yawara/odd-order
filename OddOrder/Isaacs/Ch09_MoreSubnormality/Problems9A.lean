/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.NoncommCoprod
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.Holomorph
import OddOrder.Isaacs.Ch09_MoreSubnormality.LayerRestriction

/-!
# Isaacs §9A の演習 (書籍 p. 277)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9A
(component / layer `E(G)` / generalized Fitting subgroup `F*(G)` 周辺)。

* **9A.1** `map_layer_eq_layer_of_genFitting_le` / `layerInG_eq_layer_of_genFitting_le` —
  `F*(G) ≤ H ≤ G` なら `E(H) = E(G)`。
* **9A.2** `exists_socle_mulEquiv_prod_abelian_semisimple` — `Soc(G)` は
  「abelian 群」と「semisimple 群」の直積 (`abelianSocle` × `semisimpleSocle`)。
* **9A.3** `eq_iSup_isMinimalNormal_le_of_isSemisimpleGroup` — `G` semisimple, `N ⊴ G` なら
  `N` は `N` に含まれる極小正規部分群の join。
* **9A.4** `eq_iSup_component_sup_inf_center` — `N ⊴ E(G)` なら `N = M Y`
  (`M` = `N` に含まれる component の積, `Y = N ∩ Z(E)`)。⚠ 書籍の `Y = M ∩ Z(E)` は誤植。
* **9A.5** `commutator_eq_bot_of_isComponent_notLe` — `H ⊴ G` で component `C ⊄ H` なら
  `⁅H, C⁆ = 1`。⚠ 書籍 hint の `E = E(H)` は `E = E(G)` の誤植。
* **9A.6** `layer_le_of_centralizer_le` — `H ⊴ G` で `C_G(H) ≤ H` なら `E(G) ≤ H`。
* **9A.7** `exists_conj_map_eq_of_isSimpleFactorOf` — 非可換な極小正規部分群 `N` の
  単純直積因子 (`IsSimpleFactorOf`) たちに `G` は共役で推移的に作用する。
* **9A.8** `exists_simpleFamily_of_isCharacteristicallySimple` — characteristically simple
  な有限群は互いに同型な単純群の直積。書籍 hint の holomorph `Hol(G) = G ⋊ Aut(G)`
  (`OddOrder/GroupTheory/Holomorph.lean`) で `G` の像が極小正規部分群になることから
  Lemma 9.6 で「abelian か semisimple」に二分し, semisimple 枝は 9A.7 (共役の推移性),
  abelian 枝は elementary abelian 化 + `ZMod p`-基底分解で片付ける。

## 実装ノート (9A.1)

9A.1 は同ファイル群の **Lemma 9.25** (`map_layer_eq_layer_of_fitting_eq_bot`,
`F(G) = 1` の場合) の一般化で, 証明の骨格は共通:

* `E(G) ≤ E(H)`: `G` の component `K` は `K ≤ E(G) ≤ H` かつ subnormal なので `↥H` の
  component (`IsComponent.subgroupOf`)。
* `E(H) ≤ E(G)`: `↥H` の component `V` が `E(G)` に入らないとする。
  - `E(G) ≤ C_G(V)`: `G` の各 component `K` は `↥H` の中で `V` と**異なる** component
    なので Thm 9.4 (`IsComponent.commutator_eq_bot_of_ne`) で可換。
  - `F(G) ≤ C_G(V)`: `F(G) ≤ F*(G) ≤ H` かつ `F(G) ◁ G` なので `F(G)` は `↥H` でも
    solvable normal, よって **Thm 9.7(c) を `↥H` で**適用して `⁅E(H), F(G)⁆ = 1`。
  - あわせて `F*(G) = F(G) E(G) ≤ C_G(V)`, Thm 9.8 (`C_G(F*) ≤ F*`) で `V ≤ F*(G)`。
  - すると `V ≤ C_G(V)` すなわち `⁅V,V⁆ = 1` だが `V` は quasisimple ゆえ perfect
    (`⁅V,V⁆ = V`) なので `V = 1`, これは `V ≰ E(G)` に矛盾。

`F(G) = 1` の場合 (Lemma 9.25) は `F*(G) = E(G)` なので 2 番目の箇条が要らず,
`V ≤ C_G(E(G)) = C_G(F*) ≤ F* = E(G)` で直ちに矛盾していた。

## 実装ノート (9A.2)

`A := abelianSocle G` (abelian な極小正規の join), `S := semisimpleSocle G`
(非可換な極小正規の join) と取る。要点は **相異なる極小正規部分群は互いに中心化する**
(`⁅M,N⁆ ≤ M ⊓ N = 1`) こと:

* `A ⊔ S = Soc(G)`: Lemma 9.6 で極小正規は abelian か semisimple (= 非可換) の 2 択。
* `IsMulCommutative ↥A`: 上の中心化性 + 各因子が abelian。
* `IsSemisimpleGroup ↥S`: 各非可換極小正規 `M` を Lemma 9.6 で `↥M` の単純正規因子の
  join に分解し (`exists_simpleFamily_of_isMinimalNormal`), ambient に押し出す。押し出した
  `T` は `M` に正規化され, 他の極小正規には中心化されるので **`S` 全体で正規**になり,
  `↥S` の semisimple 族をなす。
* `Disjoint A S`: `A ⊓ S ≤ Z(S) = 1` (semisimple 群は centerless)。
* 直積の同型は `MonoidHom.noncommCoprod` (単射性 = 両者単射 + range が disjoint,
  range = `A ⊔ S`) から `MonoidHom.ofInjective` で得る。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9A.1: F*(G) ≤ H なら E(H) = E(G) (p. 277) -/

/-- **Isaacs Problem 9A.1** (書籍 p. 277) ⭐: `F*(G) ⊆ H ⊆ G` ならば `E(H) = E(G)`。

`Lemma 9.25` (`map_layer_eq_layer_of_fitting_eq_bot`) の一般化 —
そちらは `F(G) = 1` (このとき `F*(G) = E(G)`) を仮定していた。 -/
theorem map_layer_eq_layer_of_genFitting_le [Finite G] {H : Subgroup G}
    (hle : genFitting G ≤ H) : (layer ↥H).map H.subtype = layer G := by
  have hFH : Ch01.fitting G ≤ H := fitting_le_genFitting.trans hle
  have hEH : layer G ≤ H := layer_le_genFitting.trans hle
  -- `F(G)` を `↥H` の部分群として見たもの: solvable normal。
  set M : Subgroup ↥H := (Ch01.fitting G).subgroupOf H with hMdef
  have : M.Normal := Subgroup.Normal.subgroupOf inferInstance H
  have : Group.IsSolvable ↥M := by
    have := Ch01.fitting.isNilpotent (G := G)
    have : Group.IsSolvable ↥(Ch01.fitting G) := IsNilpotent.to_isSolvable
    have hinj : Function.Injective
        ((Subgroup.subgroupOfEquivOfLe hFH).toMonoidHom : ↥M →* ↥(Ch01.fitting G)) :=
      (Subgroup.subgroupOfEquivOfLe hFH).injective
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hMmap : M.map H.subtype = Ch01.fitting G := by
    rw [hMdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFH]
  -- **Thm 9.7(c) を `↥H` で**: `⁅E(H), F(G)⁆ = 1`。
  have h97c : ⁅layer ↥H, M⁆ = ⊥ := commutator_layer_eq_bot_of_normal_isSolvable inferInstance
  apply le_antisymm
  · -- `E(H) ≤ E(G)`
    have key : ∀ V : Subgroup ↥H, IsComponent V → V.map H.subtype ≤ layer G := by
      intro V hV
      by_contra hVnle
      -- (1) `E(G) ≤ C_G(V)`: `G` の component は `↥H` の中で `V` と異なる component。
      have hcentE : layer G ≤ Subgroup.centralizer (V.map H.subtype : Set G) := by
        refine sSup_le fun K hK => ?_
        have hcompK : IsComponent K := hK
        have hKH : K ≤ H := hcompK.le_layer.trans hEH
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        have hne : K.subgroupOf H ≠ V := by
          intro heq
          apply hVnle
          rw [← heq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH]
          exact hcompK.le_layer
        have h94 : ⁅K.subgroupOf H, V⁆ = ⊥ :=
          (hcompK.subgroupOf hKH).commutator_eq_bot_of_ne hV hne
        have h := congrArg (Subgroup.map H.subtype) h94
        rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hKH, Subgroup.map_bot] at h
      -- (2) `F(G) ≤ C_G(V)`: Thm 9.7(c) を `↥H` で使う。
      have hcentF : Ch01.fitting G ≤ Subgroup.centralizer (V.map H.subtype : Set G) := by
        have hVM : ⁅V, M⁆ = ⊥ := by
          refine le_bot_iff.mp ?_
          rw [← h97c]
          exact Subgroup.commutator_mono hV.le_layer le_rfl
        have h := congrArg (Subgroup.map H.subtype) hVM
        rw [Subgroup.map_commutator, hMmap, Subgroup.map_bot] at h
        exact Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      -- (3) `F*(G) ≤ C_G(V)`, ゆえに Thm 9.8 で `V ≤ F*(G)`。
      have hcent : genFitting G ≤ Subgroup.centralizer (V.map H.subtype : Set G) := by
        rw [genFitting]
        exact sup_le hcentF hcentE
      have hVle : V.map H.subtype ≤ genFitting G :=
        (Subgroup.le_centralizer_iff.mp hcent).trans centralizer_genFitting_le_genFitting
      -- (4) `V` は自身を中心化する = 可換, しかし perfect なので `V = 1`。
      have := hV.isQuasisimple.isPerfect
      have hVperf : ⁅V.map H.subtype, V.map H.subtype⁆ = V.map H.subtype := by
        rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
      have hVbot : V.map H.subtype = ⊥ := by
        rw [← hVperf]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hVle.trans hcent)
      exact hVnle (hVbot ▸ bot_le)
    rw [Subgroup.map_le_iff_le_comap,
      show layer (↥H) = sSup {V : Subgroup ↥H | IsComponent V} from rfl]
    refine sSup_le fun V hV => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact key V hV
  · -- `E(G) ≤ E(H)`
    refine sSup_le fun K hK => ?_
    have hcompK : IsComponent K := hK
    have hKH : K ≤ H := hcompK.le_layer.trans hEH
    calc K = (K.subgroupOf H).map H.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH]
      _ ≤ (layer ↥H).map H.subtype := Subgroup.map_mono (hcompK.subgroupOf hKH).le_layer

/-- **Isaacs Problem 9A.1 (ambient 版)** (書籍 p. 277): `F*(G) ≤ H` なら `E(H) = E(G)`
(`layerInG` で `Subgroup G` の元として比較した形)。 -/
theorem layerInG_eq_layer_of_genFitting_le [Finite G] {H : Subgroup G}
    (hle : genFitting G ≤ H) : layerInG H = layer G :=
  map_layer_eq_layer_of_genFitting_le hle

end -- 9A.1

section /- 9A.2: Soc(G) = (abelian) × (semisimple) (p. 277) -/

/-- 相異なる極小正規部分群の元は可換 (`⁅M,N⁆ ≤ M ⊓ N = 1`)。 -/
theorem commute_of_isMinimalNormal_of_ne {M N : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hN : Ch02.IsMinimalNormal N) (hne : M ≠ N)
    {x y : G} (hx : x ∈ M) (hy : y ∈ N) : Commute x y :=
  Subgroup.commute_of_normal_of_disjoint M N hM.1 hN.1
    (disjoint_of_isMinimalNormal_of_ne hM hN hne) x y hx hy

/-- 相異なる極小正規部分群は互いに中心化する。 -/
theorem isMinimalNormal_le_centralizer_of_ne {M N : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hN : Ch02.IsMinimalNormal N) (hne : M ≠ N) :
    N ≤ Subgroup.centralizer (M : Set G) := fun _ hy =>
  Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (commute_of_isMinimalNormal_of_ne hM hN hne hx hy).eq

variable (G) in
/-- `Soc(G)` の **abelian 部分**: abelian な極小正規部分群の join。 -/
def abelianSocle : Subgroup G :=
  ⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ IsMulCommutative ↥M}, (M : Subgroup G)

variable (G) in
/-- `Soc(G)` の **semisimple 部分**: 非可換な極小正規部分群の join
(Lemma 9.6 でそれらは semisimple)。 -/
def semisimpleSocle : Subgroup G :=
  ⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ ¬IsMulCommutative ↥M}, (M : Subgroup G)

theorem le_abelianSocle {M : Subgroup G} (hM : Ch02.IsMinimalNormal M)
    (hab : IsMulCommutative ↥M) : M ≤ abelianSocle G :=
  le_iSup (fun M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ IsMulCommutative ↥M} =>
    (M : Subgroup G)) ⟨M, hM, hab⟩

theorem le_semisimpleSocle {M : Subgroup G} (hM : Ch02.IsMinimalNormal M)
    (hnab : ¬IsMulCommutative ↥M) : M ≤ semisimpleSocle G :=
  le_iSup (fun M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ ¬IsMulCommutative ↥M} =>
    (M : Subgroup G)) ⟨M, hM, hnab⟩

theorem abelianSocle_le_socle : abelianSocle G ≤ Ch02.socle G :=
  iSup_le fun M => Ch02.isMinimalNormal_le_socle M.2.1

theorem semisimpleSocle_le_socle : semisimpleSocle G ≤ Ch02.socle G :=
  iSup_le fun M => Ch02.isMinimalNormal_le_socle M.2.1

/-- `Soc(G) = A S`: 極小正規部分群は abelian か否かで 2 分される。 -/
theorem abelianSocle_sup_semisimpleSocle : abelianSocle G ⊔ semisimpleSocle G = Ch02.socle G := by
  refine le_antisymm (sup_le abelianSocle_le_socle semisimpleSocle_le_socle) ?_
  refine iSup_le fun M => ?_
  by_cases hab : IsMulCommutative ↥(M : Subgroup G)
  · exact (le_abelianSocle M.2 hab).trans le_sup_left
  · exact (le_semisimpleSocle M.2 hab).trans le_sup_right

/-- **`A` は abelian**: 極小正規部分群どうしは (等しければ可換性から, 異なれば
disjoint 性から) 元ごとに可換。 -/
theorem isMulCommutative_abelianSocle : IsMulCommutative ↥(abelianSocle G) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  refine iSup_le fun M => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun N => ?_
  by_cases hMN : (M : Subgroup G) = (N : Subgroup G)
  · have : IsMulCommutative ↥(N : Subgroup G) := N.2.2
    rw [hMN]
    exact Subgroup.le_centralizer (H := (N : Subgroup G))
  · exact isMinimalNormal_le_centralizer_of_ne M.2.1 N.2.1 hMN

/-- **`A` は `S` を中心化する** (abelian な極小正規と非可換な極小正規は相異なるから)。 -/
theorem abelianSocle_le_centralizer_semisimpleSocle :
    abelianSocle G ≤ Subgroup.centralizer (semisimpleSocle G : Set G) := by
  refine iSup_le fun M => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun N => ?_
  refine isMinimalNormal_le_centralizer_of_ne M.2.1 N.2.1 fun h => ?_
  exact N.2.2 (h ▸ M.2.2)

/-- **`N` の単純直積因子**: `N` に含まれ, `N` に正規化される非可換単純部分群。

`N` が非可換な極小正規部分群のとき, `↥N` は semisimple (Lemma 9.6) でその単純正規因子を
ambient に押し出したものがちょうどこれ (`exists_simpleFamily_of_isMinimalNormal`)。
9A.7 で `G` がこの族に共役で推移的に作用することを示す。 -/
structure IsSimpleFactorOf (N T : Subgroup G) : Prop where
  le : T ≤ N
  le_normalizer : N ≤ Subgroup.normalizer (T : Set G)
  isSimpleGroup : IsSimpleGroup ↥T
  not_isMulCommutative : ¬IsMulCommutative ↥T

theorem IsSimpleFactorOf.ne_bot {N T : Subgroup G} (h : IsSimpleFactorOf N T) : T ≠ ⊥ := by
  have := h.isSimpleGroup
  exact (Subgroup.nontrivial_iff_ne_bot T).mp inferInstance

/-- 非可換な極小正規部分群 `M` を, `M` で正規な非可換単純部分群たちの join に分解する
(Lemma 9.6 で `↥M` は semisimple, その族を ambient に押し出したもの)。 -/
theorem exists_simpleFamily_of_isMinimalNormal [Finite G] {M : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hnab : ¬IsMulCommutative ↥M) :
    ∃ 𝒵 : Set (Subgroup G), (∀ T ∈ 𝒵, IsSimpleFactorOf M T) ∧ sSup 𝒵 = M := by
  have := hM.1
  obtain ⟨𝒳, h𝒳, hsup⟩ :=
    (isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hM).resolve_left hnab
  refine ⟨(fun T : Subgroup ↥M => T.map M.subtype) '' 𝒳, ?_, ?_⟩
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hTnormal, hTsimple, hTnab⟩ := h𝒳 T hT
    have hTle : T.map M.subtype ≤ M := Subgroup.map_subtype_le T
    have he : ↥T ≃* ↥(T.map M.subtype) :=
      Subgroup.equivMapOfInjective T M.subtype (Subgroup.subtype_injective M)
    refine ⟨hTle, ?_, ?_, ?_⟩
    · -- `M ≤ N_G(T.map subtype)`: `T ⊴ ↥M` を ambient に落とす
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨y, hyT, rfl⟩
        exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hTnormal.conj_mem y hyT ⟨g, hg⟩, rfl⟩
      · rintro ⟨y, hyT, hyeq⟩
        refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩, ?_, ?_⟩
        · have hc := hTnormal.conj_mem y hyT ⟨g, hg⟩⁻¹
          rwa [inv_inv] at hc
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hyeq ⊢
          rw [hyeq]
          group
    · have := hTsimple
      exact he.symm.isSimpleGroup
    · exact fun hcomm => hTnab (isMulCommutative_of_surjective he.symm.toMonoidHom
        he.symm.surjective)
  · refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨T, -, rfl⟩
      exact Subgroup.map_subtype_le T
    · calc M = (⊤ : Subgroup ↥M).map M.subtype := by
              rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        _ = (sSup 𝒳).map M.subtype := by rw [hsup]
        _ ≤ sSup ((fun T : Subgroup ↥M => T.map M.subtype) '' 𝒳) := by
              rw [(Subgroup.gc_map_comap M.subtype).l_sSup]
              exact iSup₂_le fun T hT => le_sSup ⟨T, hT, rfl⟩

/-- **`S` は semisimple**: 各非可換極小正規部分群を単純因子に分解すると, それらは `S` 全体で
正規 (自分を含む極小正規は正規化し, 相異なる極小正規は中心化するので)。 -/
theorem isSemisimpleGroup_semisimpleSocle [Finite G] :
    IsSemisimpleGroup ↥(semisimpleSocle G) := by
  set 𝒴 := {T : Subgroup ↥(semisimpleSocle G) |
    T.Normal ∧ IsSimpleGroup ↥T ∧ ¬IsMulCommutative ↥T} with h𝒴
  refine ⟨𝒴, fun T hT => hT, ?_⟩
  have hkey : semisimpleSocle G ≤ (sSup 𝒴).map (semisimpleSocle G).subtype := by
    refine iSup_le fun M => ?_
    obtain ⟨𝒵, h𝒵, hsupZ⟩ := exists_simpleFamily_of_isMinimalNormal M.2.1 M.2.2
    rw [← hsupZ]
    refine sSup_le fun T hT => ?_
    obtain ⟨hTM, hTnorm, hTsimple, hTnab⟩ := h𝒵 T hT
    have hTS : T ≤ semisimpleSocle G := hTM.trans (le_semisimpleSocle M.2.1 M.2.2)
    -- `S ≤ N_G(T)`: `M` は `T` を正規化し, 他の極小正規は `M ⊇ T` を中心化する。
    have hSnorm : semisimpleSocle G ≤ Subgroup.normalizer (T : Set G) := by
      refine iSup_le fun N => ?_
      by_cases hNM : (N : Subgroup G) = (M : Subgroup G)
      · rw [hNM]; exact hTnorm
      · refine (isMinimalNormal_le_centralizer_of_ne M.2.1 N.2.1 fun h => hNM h.symm).trans ?_
        exact (Subgroup.centralizer_le (by exact_mod_cast hTM)).trans
          (Subgroup.centralizer_le_normalizer _)
    have he : ↥(T.subgroupOf (semisimpleSocle G)) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTS
    have hmem : T.subgroupOf (semisimpleSocle G) ∈ 𝒴 := by
      refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr hSnorm, ?_, ?_⟩
      · have := hTsimple
        exact he.isSimpleGroup
      · exact fun _ => hTnab (isMulCommutative_of_surjective he.toMonoidHom he.surjective)
    calc T = (T.subgroupOf (semisimpleSocle G)).map (semisimpleSocle G).subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTS]
      _ ≤ (sSup 𝒴).map (semisimpleSocle G).subtype := Subgroup.map_mono (le_sSup hmem)
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hkey x.2
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- **`A ⊓ S = 1`**: `A` は `S` を中心化するので `A ⊓ S ≤ Z(S)`, ところが semisimple 群は
centerless。 -/
theorem disjoint_abelianSocle_semisimpleSocle [Finite G] :
    Disjoint (abelianSocle G) (semisimpleSocle G) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxS : x ∈ semisimpleSocle G := hx.2
  have hcent := abelianSocle_le_centralizer_semisimpleSocle hx.1
  have hmem : (⟨x, hxS⟩ : ↥(semisimpleSocle G)) ∈ center ↥(semisimpleSocle G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent y y.2)
  rw [IsSemisimpleGroup.center_eq_bot isSemisimpleGroup_semisimpleSocle,
    Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

/-- **Isaacs Problem 9A.2** (書籍 p. 277) ⭐: 有限群の socle は
「abelian 群」と「semisimple 群」の直積。

`A` = abelian な極小正規部分群の join, `S` = 非可換な極小正規部分群の join と取る。
極小正規部分群は Lemma 9.6 で abelian か semisimple のいずれかなので `A S = Soc(G)`,
相異なる極小正規部分群は互いに中心化するので `A` は abelian で `⁅A,S⁆ = 1`,
`S` は semisimple ゆえ centerless なので `A ⊓ S ≤ Z(S) = 1`。 -/
theorem exists_socle_mulEquiv_prod_abelian_semisimple [Finite G] :
    ∃ A S : Subgroup G, IsMulCommutative ↥A ∧ IsSemisimpleGroup ↥S ∧
      A ⊔ S = Ch02.socle G ∧ Disjoint A S ∧
      Nonempty (↥A × ↥S ≃* ↥(Ch02.socle G)) := by
  refine ⟨abelianSocle G, semisimpleSocle G, isMulCommutative_abelianSocle,
    isSemisimpleGroup_semisimpleSocle, abelianSocle_sup_semisimpleSocle,
    disjoint_abelianSocle_semisimpleSocle, ?_⟩
  have hcomm : ∀ (a : ↥(abelianSocle G)) (s : ↥(semisimpleSocle G)),
      Commute ((abelianSocle G).subtype a) ((semisimpleSocle G).subtype s) := fun a s =>
    (Subgroup.mem_centralizer_iff.mp
      (abelianSocle_le_centralizer_semisimpleSocle a.2) s s.2).symm
  have hinj : Function.Injective
      (MonoidHom.noncommCoprod (abelianSocle G).subtype (semisimpleSocle G).subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_abelianSocle_semisimpleSocle
  have hrange :
      (MonoidHom.noncommCoprod (abelianSocle G).subtype (semisimpleSocle G).subtype
        hcomm).range = Ch02.socle G := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact abelianSocle_sup_semisimpleSocle
  exact ⟨hrange ▸ MonoidHom.ofInjective hinj⟩

end -- 9A.2

section /- 9A.3: semisimple 群の正規部分群は極小正規部分群の積 (p. 277) -/

/-- `p` を満たす極小正規部分群は, それらの join に含まれる (`⨆` の添字が subtype なので
`le_iSup` を当てるだけだが, 9A.3 で 2 つの述語について使うので切り出す)。 -/
theorem le_iSup_isMinimalNormal {p : Subgroup G → Prop} {M : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hp : p M) :
    M ≤ ⨆ M' : {M' : Subgroup G // Ch02.IsMinimalNormal M' ∧ p M'}, (M' : Subgroup G) :=
  le_iSup (fun M' : {M' : Subgroup G // Ch02.IsMinimalNormal M' ∧ p M'} => (M' : Subgroup G))
    ⟨M, hM, hp⟩

/-- **semisimple 群では `W ⊓ C_G(W) = 1`**: それは abelian な正規部分群なので, 中に入る
極小正規部分群が abelian になってしまい Lemma 9.5 の帰結
(`IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal`) に反する。 -/
theorem inf_centralizer_eq_bot_of_isSemisimpleGroup [Finite G] (hss : IsSemisimpleGroup G)
    (W : Subgroup G) [W.Normal] : W ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨M, hMmin, hMle⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (W ⊓ Subgroup.centralizer (W : Set G)) hne
  have hMab : M ≤ Subgroup.centralizer (M : Set G) :=
    (hMle.trans inf_le_right).trans
      (Subgroup.centralizer_le (by exact_mod_cast hMle.trans inf_le_left))
  have := Subgroup.le_centralizer_iff_isMulCommutative.mp hMab
  exact (hss.isSimpleGroup_of_isMinimalNormal hMmin).2 inferInstance

/-- `N` に**含まれない**極小正規部分群の join (9A.3 の `V`; 書籍の hint の `G = U × V`)。 -/
private def minimalNormalNotLe (N : Subgroup G) : Subgroup G :=
  ⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ ¬(M ≤ N)}, (M : Subgroup G)

private theorem minimalNormalNotLe_normal (N : Subgroup G) : (minimalNormalNotLe N).Normal := by
  have : ∀ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ ¬(M ≤ N)},
      ((M : Subgroup G)).Normal := fun M => M.2.1.1
  exact Subgroup.iSup_normal _

/-- `V ≤ C_G(N)`: `N` に含まれない極小正規 `M` は `M ⊓ N ⊴ G` と極小性から `N` と disjoint,
よって元ごとに可換。 -/
private theorem minimalNormalNotLe_le_centralizer (N : Subgroup G) [N.Normal] :
    minimalNormalNotLe N ≤ Subgroup.centralizer (N : Set G) := by
  refine iSup_le fun M => ?_
  have := M.2.1.1
  have hdisj : Disjoint (M : Subgroup G) N := by
    rcases M.2.1.2.2 ((M : Subgroup G) ⊓ N) inferInstance inf_le_left with h | h
    · rw [disjoint_iff]; exact h
    · exact absurd (h ▸ (inf_le_right : (M : Subgroup G) ⊓ N ≤ N)) M.2.2
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.commute_of_normal_of_disjoint _ N M.2.1.1 inferInstance hdisj y x hy hx).symm.eq

/-- **Isaacs Problem 9A.3** (書籍 p. 277) ⭐: `G` が semisimple で `N ⊴ G` なら, `N` は
`N` に含まれる `G` の極小正規部分群たちの積 (join)。

**証明** (書籍の hint に沿う): `U` = `N` に含まれる極小正規の join,
`V` = 含まれない極小正規の join とすると, 極小正規全体が `G` を生成する (Lemma 9.5) ので
`U ⊔ V = ⊤`。`V ≤ C_G(N)` (極小性から `M ⊓ N = 1`) ゆえ `N ≤ C_G(V)`, したがって
`U ≤ N ≤ C_G(V)`。`n ∈ N` を `n = u v` (`u ∈ U`, `v ∈ V`) と書くと
`v = u⁻¹ n ∈ V ⊓ C_G(V) = 1` (semisimple 群では abelian normal が自明) なので `n = u ∈ U`。 -/
theorem eq_iSup_isMinimalNormal_le_of_isSemisimpleGroup [Finite G] (hss : IsSemisimpleGroup G)
    (N : Subgroup G) [N.Normal] :
    N = ⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ M ≤ N}, (M : Subgroup G) := by
  have := minimalNormalNotLe_normal (G := G) N
  have hUN : (⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ M ≤ N}, (M : Subgroup G)) ≤ N :=
    iSup_le fun M => M.2.2
  -- 極小正規全体が `G` を生成するので `U ⊔ V = ⊤`。
  have hUV : (⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ M ≤ N}, (M : Subgroup G))
      ⊔ minimalNormalNotLe N = ⊤ := by
    refine top_le_iff.mp ?_
    obtain ⟨𝒳, h𝒳, hsup⟩ := hss
    rw [← hsup]
    refine sSup_le fun S hS => ?_
    have hSmin : Ch02.IsMinimalNormal S := isMinimalNormal_of_mem_semisimpleFamily h𝒳 hS
    by_cases hSN : S ≤ N
    · exact le_sup_of_le_left (le_iSup_isMinimalNormal hSmin hSN)
    · exact le_sup_of_le_right (le_iSup_isMinimalNormal hSmin hSN)
  have hNC : N ≤ Subgroup.centralizer (minimalNormalNotLe N : Set G) :=
    Subgroup.le_centralizer_iff.mp (minimalNormalNotLe_le_centralizer N)
  refine le_antisymm (fun n hn => ?_) hUN
  have hntop : n ∈ (⨆ M : {M : Subgroup G // Ch02.IsMinimalNormal M ∧ M ≤ N},
      (M : Subgroup G)) ⊔ minimalNormalNotLe N := by rw [hUV]; exact Subgroup.mem_top n
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hntop
  obtain ⟨u, hu, v, hv, rfl⟩ := hntop
  have hvC : v ∈ Subgroup.centralizer (minimalNormalNotLe N : Set G) := by
    have hveq : v = u⁻¹ * (u * v) := by group
    rw [hveq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hNC (hUN hu))) (hNC hn)
  have hvbot : v ∈ (⊥ : Subgroup G) := by
    rw [← inf_centralizer_eq_bot_of_isSemisimpleGroup hss (minimalNormalNotLe N)]
    exact ⟨hv, hvC⟩
  rw [Subgroup.mem_bot] at hvbot
  subst hvbot
  simpa using hu

end -- 9A.3

section /- 9A.4: E の正規部分群は component の積と N ∩ Z(E) の積 (p. 277) -/

/-- **`E/Z(E)` の極小正規部分群は component の像に限る** (Lemma 9.5 後半を Thm 9.7(b) の
族 `componentImageFamily` に当てたもの)。 -/
theorem exists_isComponent_map_eq_of_isMinimalNormal [Finite G]
    {K : Subgroup (↥(layer G) ⧸ center ↥(layer G))} (hK : Ch02.IsMinimalNormal K) :
    ∃ C : Subgroup G, IsComponent C ∧
      (C.subgroupOf (layer G)).map (QuotientGroup.mk' (center ↥(layer G))) = K := by
  obtain ⟨C, hC⟩ :=
    mem_semisimpleFamily_of_isMinimalNormal componentImageFamily_spec sSup_componentImageFamily hK
  exact ⟨C, C.2, hC⟩

/-- **perfect な部分群は「`N` と中心の join」に入るなら `N` に入る**:
`E/N` の中で像が中心的かつ perfect ⟹ 像は自明。9A.4 で `C̄ ≤ N̄` から `C ≤ N` を出す step。 -/
theorem le_of_le_sup_center_of_isPerfect {E : Type*} [Group E] {C N : Subgroup E} [N.Normal]
    [Group.IsPerfect ↥C] (h : C ≤ N ⊔ center E) : C ≤ N := by
  have hcent : C.map (QuotientGroup.mk' N) ≤ center (E ⧸ N) := by
    calc C.map (QuotientGroup.mk' N) ≤ (N ⊔ center E).map (QuotientGroup.mk' N) :=
          Subgroup.map_mono h
      _ = N.map (QuotientGroup.mk' N) ⊔ (center E).map (QuotientGroup.mk' N) :=
          Subgroup.map_sup _ _ _
      _ ≤ center (E ⧸ N) := by
          rw [(Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
          exact map_center_le_center_of_surjective (QuotientGroup.mk'_surjective N)
  have hperf : ⁅C.map (QuotientGroup.mk' N), C.map (QuotientGroup.mk' N)⁆
      = C.map (QuotientGroup.mk' N) := by
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hbot : C.map (QuotientGroup.mk' N) = ⊥ := by
    rw [← hperf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcent.trans (Subgroup.center_le_centralizer _))
  have := (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [QuotientGroup.ker_mk'] at this

/-- **Isaacs Problem 9A.4** (書籍 p. 277) ⭐: `E = E(G)` で `N ⊴ E` なら `N = M Y`,
ここで `M` は `N` に含まれる `G` の component たちの積, `Y = N ∩ Z(E)`。

⚠ 書籍は `Y = M ∩ Z(E)` と書いているが**誤植** (それだと `Y ≤ M` で `M Y = M` となり,
`E` が quasisimple で `N = Z(E)` の場合に `M = 1 ≠ N` で偽になる)。正しくは `N ∩ Z(E)`。

**証明**: `π : E → E/Z(E)` とすると `E/Z(E)` は semisimple (Thm 9.7(b))。9A.3 を
`N̄ = π(N) ⊴ E/Z(E)` に適用すると `N̄` は含まれる極小正規部分群の join, そして
`E/Z(E)` の極小正規部分群は component の像 `C̄` に限る
(`exists_isComponent_map_eq_of_isMinimalNormal`)。`C̄ ≤ N̄` から `C ≤ N Z(E)`,
`C` は perfect なので `C ≤ N` (`le_of_le_sup_center_of_isPerfect`)。
よって `N̄ ≤ π(M)`, したがって `n ∈ N` に対し `π n = π m` なる `m ∈ M ≤ N` が取れて
`m⁻¹ n ∈ N ∩ ker π = N ∩ Z(E) = Y`, すなわち `n ∈ M Y`。 -/
theorem eq_iSup_component_sup_inf_center [Finite G] (N : Subgroup ↥(layer G)) [N.Normal] :
    N = (⨆ C : {C : Subgroup G // IsComponent C ∧ C.subgroupOf (layer G) ≤ N},
          ((C : Subgroup G).subgroupOf (layer G))) ⊔ (N ⊓ center ↥(layer G)) := by
  set π := QuotientGroup.mk' (center ↥(layer G)) with hπ
  set M := ⨆ C : {C : Subgroup G // IsComponent C ∧ C.subgroupOf (layer G) ≤ N},
    ((C : Subgroup G).subgroupOf (layer G)) with hM
  have hMN : M ≤ N := iSup_le fun C => C.2.2
  refine le_antisymm ?_ (sup_le hMN inf_le_left)
  -- `π(N) ≤ π(M)`
  have : (N.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hNM : N.map π ≤ M.map π := by
    rw [eq_iSup_isMinimalNormal_le_of_isSemisimpleGroup isSemisimpleGroup_layer_quotient_center
      (N.map π)]
    refine iSup_le fun K => ?_
    obtain ⟨C, hCcomp, hCeq⟩ := exists_isComponent_map_eq_of_isMinimalNormal K.2.1
    -- `C̄ ≤ N̄` ⟹ `C ≤ N ⊔ Z(E)` ⟹ (perfect) `C ≤ N`
    have hCle : C.subgroupOf (layer G) ≤ N ⊔ center ↥(layer G) := by
      have h1 : (C.subgroupOf (layer G)).map π ≤ N.map π := hCeq ▸ K.2.2
      have h2 := Subgroup.map_le_iff_le_comap.mp h1
      rwa [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h2
    have := hCcomp.isQuasisimple.isPerfect
    have : Group.IsPerfect ↥(C.subgroupOf (layer G)) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hCcomp.le_layer).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hCcomp.le_layer).symm.surjective
    have hCN : C.subgroupOf (layer G) ≤ N := le_of_le_sup_center_of_isPerfect hCle
    rw [← hCeq, hM]
    exact Subgroup.map_mono
      (le_iSup (fun C : {C : Subgroup G // IsComponent C ∧ C.subgroupOf (layer G) ≤ N} =>
        ((C : Subgroup G).subgroupOf (layer G))) ⟨C, hCcomp, hCN⟩)
  -- `n ∈ N` を `m y` (`m ∈ M`, `y ∈ N ⊓ Z(E)`) に分解
  intro n hn
  obtain ⟨m, hm, hmn⟩ := hNM ⟨n, hn, rfl⟩
  have hy : m⁻¹ * n ∈ N ⊓ center ↥(layer G) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMN hm)) hn, ?_⟩
    have : π (m⁻¹ * n) = 1 := by rw [map_mul, map_inv, hmn, inv_mul_cancel]
    rw [← QuotientGroup.ker_mk' (center ↥(layer G))]
    exact this
  have hne : n = m * (m⁻¹ * n) := by group
  rw [hne]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hy)

end -- 9A.4

section /- 9A.5: H ⊴ G, C ⊄ H component なら ⁅H,C⁆ = 1 (p. 277) -/

/-- `Z(K)` を ambient に落としたものは `K` を中心化する。 -/
theorem map_center_le_centralizer (K : Subgroup G) :
    (center ↥K).map K.subtype ≤ Subgroup.centralizer (K : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)

/-- **9A.5 の核** (書籍 hint): `⁅H ∩ E, C⁆ = 1` (`E = E(G)`)。

9A.4 で `H ∩ E = M Y` (`M` = `H` に含まれる component の積, `Y ≤ Z(E)`) と書けるので,
`C` と `M` の各因子は**相異なる** component (`C ⊄ H`) ゆえ Thm 9.4 で可換, `Y ≤ Z(E)` は
`C ≤ E` を中心化する。

⚠ 書籍の hint は "where `E = E(H)`" と書いているが, `H ∩ E` という書き方から
`E = E(G)` の誤植 (`E(H) ≤ H` なら `H ∩ E(H) = E(H)` で `H ∩` が無意味)。 -/
theorem commutator_inf_layer_isComponent_eq_bot [Finite G] {H C : Subgroup G} [H.Normal]
    (hC : IsComponent C) (hCH : ¬C ≤ H) : ⁅H ⊓ layer G, C⁆ = ⊥ := by
  have : (H.subgroupOf (layer G)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    ← Subgroup.subgroupOf_map_subtype H (layer G),
    eq_iSup_component_sup_inf_center (H.subgroupOf (layer G)), Subgroup.map_sup]
  refine sup_le ?_ ?_
  · -- `M` の各 component は `H` に入るので `C` と異なる ⟹ Thm 9.4
    rw [Subgroup.map_iSup]
    refine iSup_le fun C' => ?_
    have hC'E : (C' : Subgroup G) ≤ layer G := C'.2.1.le_layer
    have hC'H : (C' : Subgroup G) ≤ H := by
      have := Subgroup.map_mono (f := (layer G).subtype) C'.2.2
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hC'E] at this
      exact this.trans inf_le_left
    have hne : (C' : Subgroup G) ≠ C := fun h => hCH (h ▸ hC'H)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC'E,
      ← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact C'.2.1.commutator_eq_bot_of_ne hC hne
  · -- `Y ≤ Z(E)` は `C ≤ E` を中心化する
    refine (Subgroup.map_mono inf_le_right).trans ?_
    exact (map_center_le_centralizer (layer G)).trans
      (Subgroup.centralizer_le (by exact_mod_cast hC.le_layer))

/-- **Isaacs Problem 9A.5** (書籍 p. 277) ⭐: `H ⊴ G` で `C` が `H` に含まれない `G` の
component なら `⁅H, C⁆ = 1`。

**証明**: `⁅H,C⁆ ≤ H ∩ E` (`H ◁ G`, `E = E(G) ◁ G`, `C ≤ E`) なので前補題から
`⁅⁅H,C⁆, C⁆ = 1`。三部分群補題 (`commutator_commutator_eq_bot_of_rotate`) で
`⁅⁅C,C⁆, H⁆ = 1`, `C` は perfect (`⁅C,C⁆ = C`) なので `⁅C,H⁆ = 1`。 -/
theorem commutator_eq_bot_of_isComponent_notLe [Finite G] {H C : Subgroup G} [H.Normal]
    (hC : IsComponent C) (hCH : ¬C ≤ H) : ⁅H, C⁆ = ⊥ := by
  have hHC : ⁅H, C⁆ ≤ H ⊓ layer G :=
    le_inf (Subgroup.commutator_le_left H C)
      ((Subgroup.commutator_mono le_rfl hC.le_layer).trans
        (Subgroup.commutator_le_right H (layer G)))
  have h3 : ⁅⁅H, C⁆, C⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← commutator_inf_layer_isComponent_eq_bot hC hCH]
    exact Subgroup.commutator_mono hHC le_rfl
  have := hC.isQuasisimple.isPerfect
  have h4 : ⁅⁅C, C⁆, H⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (by rw [Subgroup.commutator_comm C H]; exact h3) h3
  rw [Subgroup.commutator_eq_self] at h4
  rw [Subgroup.commutator_comm]
  exact h4

end -- 9A.5

section /- 9A.6: C_G(H) ≤ H なら E(G) ≤ H (p. 277) -/

/-- **Isaacs Problem 9A.6** (書籍 p. 277): `H ⊴ G` で `C_G(H) ⊆ H` なら `E(G) ⊆ H`。

component `C` が `H` に入らないとすると 9A.5 で `⁅H, C⁆ = 1`, すなわち
`C ≤ C_G(H) ≤ H` となって矛盾。 -/
theorem layer_le_of_centralizer_le [Finite G] {H : Subgroup G} [H.Normal]
    (h : Subgroup.centralizer (H : Set G) ≤ H) : layer G ≤ H := by
  refine sSup_le fun C hC => ?_
  by_contra hCH
  have h1 : H ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_isComponent_notLe hC hCH)
  exact hCH ((Subgroup.le_centralizer_iff.mp h1).trans h)

end -- 9A.6

section /- 9A.7: 単純直積因子への G の共役作用は推移的 (p. 277) -/

/-- `C` が `A` と `B` の両方を正規化するなら `A ⊓ B` も正規化する。 -/
theorem le_normalizer_inf {A B C : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) h).mp h1,
      (Subgroup.mem_normalizer_iff.mp (hB hx) h).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) h).mpr h1,
      (Subgroup.mem_normalizer_iff.mp (hB hx) h).mpr h2⟩

/-- 互いに正規化しあう disjoint な部分群の元は可換:
`⁅a,b⁆ = a (b a⁻¹ b⁻¹) ∈ A` かつ `⁅a,b⁆ = (a b a⁻¹) b⁻¹ ∈ B` なので `⁅a,b⁆ ∈ A ⊓ B = 1`。 -/
theorem commute_of_le_normalizer_of_disjoint {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hdisj : Disjoint A B) {a b : G} (ha : a ∈ A) (hb : b ∈ B) : Commute a b := by
  have hmemA : ⁅a, b⁆ ∈ A := by
    have hba : b * a⁻¹ * b⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hBA hb) a⁻¹).mp (A.inv_mem ha)
    have heq : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [heq]
    exact A.mul_mem ha hba
  have hmemB : ⁅a, b⁆ ∈ B := by
    have hab : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb
    rw [commutatorElement_def]
    exact B.mul_mem hab (B.inv_mem hb)
  have hmem : ⁅a, b⁆ ∈ A ⊓ B := ⟨hmemA, hmemB⟩
  rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_commute.mp hmem

/-- 単純直積因子の共役はまた単純直積因子 (`N ⊴ G` なので `N^g = N`)。 -/
theorem IsSimpleFactorOf.conj {N T : Subgroup G} [hN : N.Normal] (h : IsSimpleFactorOf N T)
    (g : G) : IsSimpleFactorOf N (T.map (MulAut.conj g).toMonoidHom) := by
  have he : ↥T ≃* ↥(T.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective T _ (MulAut.conj g).injective
  have hNg : N.map (MulAut.conj g).toMonoidHom = N := by
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hN.conj_mem x hx g
    · refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have := hN.conj_mem x hx g⁻¹
        rwa [inv_inv] at this
      · change MulAut.conj g _ = x
        simp only [MulAut.conj_apply]
        group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hN.conj_mem x (h.le hx) g
  · calc N = N.map (MulAut.conj g).toMonoidHom := hNg.symm
      _ ≤ (Subgroup.normalizer (T : Set G)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono h.le_normalizer
      _ = Subgroup.normalizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
          Subgroup.map_equiv_normalizer_eq T (MulAut.conj g)
  · have := h.isSimpleGroup
    exact he.symm.isSimpleGroup
  · exact fun _ => h.not_isMulCommutative
      (isMulCommutative_of_surjective he.symm.toMonoidHom he.symm.surjective)

/-- semisimple な部分群は自身の中心化群と自明にしか交わらない (`Z(↥N) = 1` ゆえ)。 -/
theorem inf_centralizer_eq_bot_of_isSemisimpleGroup_coe {N : Subgroup G} [Finite G]
    (hss : IsSemisimpleGroup ↥N) : N ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  have hmem : (⟨x, hx.1⟩ : ↥N) ∈ center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [hss.center_eq_bot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

/-- **Isaacs Problem 9A.7** (書籍 p. 277) ⭐: 非可換な極小正規部分群 `N` の単純直積因子
たちに `G` は共役で推移的に作用する。

**証明**: `S^g ≠ T` がすべての `g` で成り立つと仮定する。`S^g ⊓ T` は `T` に含まれ `T` で
正規なので `T` の単純性から `⊥` か `T`; 後者だと `T ≤ S^g` から `S^g` の単純性で
`T = S^g` となり仮定に反する。よって `S^g` と `T` は disjoint で互いを正規化するので可換
(`commute_of_le_normalizer_of_disjoint`)。`S` の共役全体が生成する正規部分群は `N` の
極小性から `N` に等しいので `N ≤ C_G(T)`, すなわち `T ≤ N ⊓ C_G(N) = 1`
(`↥N` は semisimple ゆえ centerless) となり `T ≠ 1` に矛盾。 -/
theorem exists_conj_map_eq_of_isSimpleFactorOf [Finite G] {N : Subgroup G}
    (hN : Ch02.IsMinimalNormal N) (hnab : ¬IsMulCommutative ↥N)
    {S T : Subgroup G} (hS : IsSimpleFactorOf N S) (hT : IsSimpleFactorOf N T) :
    ∃ g : G, S.map (MulAut.conj g).toMonoidHom = T := by
  have := hN.1
  by_contra hcon0
  have hcon : ∀ g : G, S.map (MulAut.conj g).toMonoidHom ≠ T := fun g h => hcon0 ⟨g, h⟩
  -- 各共役 `S^g` は `T` を中心化する。
  have hcentSg : ∀ g : G,
      S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (T : Set G) := by
    intro g
    have hSg := hS.conj (N := N) g
    obtain ⟨-, hTmin⟩ := Subgroup.isSimpleGroup_iff.mp hT.isSimpleGroup
    have hinfnorm : T ≤ Subgroup.normalizer
        ((S.map (MulAut.conj g).toMonoidHom ⊓ T : Subgroup G) : Set G) :=
      le_normalizer_inf (hT.le.trans hSg.le_normalizer) Subgroup.le_normalizer
    have hdisj : Disjoint (S.map (MulAut.conj g).toMonoidHom) T := by
      rcases hTmin _ inf_le_right
        ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hinfnorm) with h | h
      · exact disjoint_iff.mpr h
      · -- `T ≤ S^g` ⟹ `S^g` の単純性で `T = S^g`, 仮定に反する
        exfalso
        have hTS : T ≤ S.map (MulAut.conj g).toMonoidHom := h ▸ inf_le_left
        obtain ⟨-, hSmin⟩ := Subgroup.isSimpleGroup_iff.mp hSg.isSimpleGroup
        rcases hSmin T hTS
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr
            (hSg.le.trans hT.le_normalizer)) with h' | h'
        · exact hT.ne_bot h'
        · exact hcon g h'.symm
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_le_normalizer_of_disjoint (hSg.le.trans hT.le_normalizer)
      (hT.le.trans hSg.le_normalizer) hdisj hx hy).symm.eq
  -- `S` の正規閉包は `N` (極小性), よって `N ≤ C_G(T)`。
  have hNC : N ≤ Subgroup.centralizer (T : Set G) := by
    have hNS : Subgroup.normalClosure (S : Set G) = N := by
      rcases hN.2.2 (Subgroup.normalClosure (S : Set G)) inferInstance
        (Subgroup.normalClosure_le_normal (by exact_mod_cast hS.le)) with h | h
      · exact absurd (le_bot_iff.mp fun x hx =>
          h ▸ Subgroup.subset_normalClosure (s := (S : Set G)) hx) hS.ne_bot
      · exact h
    rw [← hNS]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    rw [isConj_iff] at hconj
    obtain ⟨c, rfl⟩ := hconj
    exact hcentSg c ⟨a, ha, rfl⟩
  -- `T ≤ N ⊓ C_G(N) = 1`, 矛盾。
  have hss : IsSemisimpleGroup ↥N :=
    (isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hN).resolve_left hnab
  have hTle : T ≤ N ⊓ Subgroup.centralizer (N : Set G) :=
    le_inf hT.le (Subgroup.le_centralizer_iff.mp hNC)
  rw [inf_centralizer_eq_bot_of_isSemisimpleGroup_coe hss] at hTle
  exact hT.ne_bot (le_bot_iff.mp hTle)

end -- 9A.7

section /- 9A.8: characteristically simple 群 (p. 277) -/

open OddOrder.GroupTheory

/-- `G` が characteristically simple なら, holomorph `Hol(G) = G ⋊ Aut(G)` の中で
`G` の像は**極小正規部分群**になる (`Holomorph.normal_iff_characteristic` の帰結)。 -/
theorem isMinimalNormal_range_inl_of_isCharacteristicallySimple
    (h : IsCharacteristicallySimple G) :
    Ch02.IsMinimalNormal ((SemidirectProduct.inl : G →* Holomorph G)).range := by
  have := h.1
  exact ⟨Holomorph.normal_range_inl, Holomorph.range_inl_ne_bot,
    fun _ hKnormal hKle => Holomorph.eq_bot_or_eq_range_inl_of_normal h hKnormal hKle⟩

/-- **Isaacs Problem 9A.8 の骨格** (書籍 p. 277): characteristically simple な有限群は
abelian か semisimple のいずれか。

書籍 hint の `G ⋊ Aut(G)` を使う: `G` の像は `Hol(G)` の極小正規部分群なので
Lemma 9.6 (`isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal`) が二分を与える。 -/
theorem isMulCommutative_or_isSemisimpleGroup_of_isCharacteristicallySimple [Finite G]
    (h : IsCharacteristicallySimple G) :
    IsMulCommutative G ∨ IsSemisimpleGroup G := by
  have hmin := isMinimalNormal_range_inl_of_isCharacteristicallySimple h
  have e : G ≃* ↥((SemidirectProduct.inl : G →* Holomorph G)).range :=
    MonoidHom.ofInjective SemidirectProduct.inl_injective
  rcases isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hmin with hab | hss
  · have := hab
    exact Or.inl (isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · exact Or.inr (hss.of_mulEquiv e.symm)

/-- 正規部分群は共役自己同型で不変。 -/
theorem map_conj_eq_self_of_normal {T : Subgroup G} [hT : T.Normal] (a : G) :
    T.map (MulAut.conj a).toMonoidHom = T := by
  have ha : a ∈ Subgroup.normalizer T := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hT]
    trivial
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp ha

/-- `G` の正規部分群 `T` の像は `Hol(G)` の中で `inl.range` の**単純直積因子**
(`T` が非可換単純なら)。9A.8 の semisimple 枝で 9A.7 を当てるための橋。 -/
theorem isSimpleFactorOf_map_inl {T : Subgroup G} [T.Normal] (hsimple : IsSimpleGroup ↥T)
    (hnab : ¬IsMulCommutative ↥T) :
    IsSimpleFactorOf ((SemidirectProduct.inl : G →* Holomorph G)).range
      (T.map (SemidirectProduct.inl : G →* Holomorph G)) := by
  have ee : ↥T ≃* ↥(T.map (SemidirectProduct.inl : G →* Holomorph G)) :=
    Subgroup.equivMapOfInjective T _ SemidirectProduct.inl_injective
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
    have hcomp : ((MulAut.conj (SemidirectProduct.inl a : Holomorph G)).toMonoidHom.comp
        (SemidirectProduct.inl : G →* Holomorph G))
        = (SemidirectProduct.inl : G →* Holomorph G).comp (MulAut.conj a).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      exact Holomorph.conj_inl_general (SemidirectProduct.inl a) x
    rw [show ((MulAut.conj (SemidirectProduct.inl a : Holomorph G)) :
        Holomorph G →* Holomorph G) = (MulAut.conj
          (SemidirectProduct.inl a : Holomorph G)).toMonoidHom from rfl, hcomp,
      ← Subgroup.map_map, map_conj_eq_self_of_normal]
  · have := hsimple
    exact ee.symm.isSimpleGroup
  · exact fun _ => hnab (isMulCommutative_of_surjective ee.symm.toMonoidHom ee.symm.surjective)

/-- **Isaacs Problem 9A.8 (semisimple 枝)** (書籍 p. 277): characteristically simple かつ
semisimple な有限群は, 互いに同型な非可換単純正規部分群の直積。

同型性が 9A.7 の帰結: 各因子を `Hol(G)` の中で `inl.range` の単純直積因子と見ると,
`inl.range` は極小正規部分群なので `Hol(G)` の共役で互いに移り合う。 -/
theorem exists_simpleFamily_of_isSemisimpleGroup_of_isCharacteristicallySimple [Finite G]
    (h : IsCharacteristicallySimple G) (hss : IsSemisimpleGroup G) :
    ∃ 𝒵 : Set (Subgroup G), 𝒵.Nonempty ∧
      (∀ T ∈ 𝒵, T.Normal ∧ IsSimpleGroup ↥T) ∧
      (∀ T ∈ 𝒵, ∀ U ∈ 𝒵, Nonempty (↥T ≃* ↥U)) ∧
      iSupIndep (fun T : ↥𝒵 => (T : Subgroup G)) ∧ sSup 𝒵 = ⊤ := by
  have := h.1
  obtain ⟨𝒳, h𝒳, hsup⟩ := hss
  -- 族は空でない (空なら `sSup ∅ = ⊥ = ⊤`)。
  have hne : 𝒳.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝒳 with rfl | hne
    · rw [sSup_empty] at hsup
      exact absurd hsup bot_ne_top
    · exact hne
  refine ⟨𝒳, hne, fun T hT => ⟨(h𝒳 T hT).1, (h𝒳 T hT).2.1⟩, ?_,
    iSupIndep_of_semisimpleFamily h𝒳, hsup⟩
  -- `G` は非可換 (族のメンバーが非可換だから), したがって `inl.range` も非可換。
  obtain ⟨S₀, hS₀⟩ := hne
  have hnabG : ¬IsMulCommutative G := by
    intro hc
    have := hc
    exact (h𝒳 S₀ hS₀).2.2 (Subgroup.le_centralizer_iff_isMulCommutative.mp
      fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => mul_comm' y x)
  have e : G ≃* ↥((SemidirectProduct.inl : G →* Holomorph G)).range :=
    MonoidHom.ofInjective SemidirectProduct.inl_injective
  have hnabN : ¬IsMulCommutative ↥((SemidirectProduct.inl : G →* Holomorph G)).range :=
    fun hc => hnabG (isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hmin := isMinimalNormal_range_inl_of_isCharacteristicallySimple h
  intro T hT U hU
  have := (h𝒳 T hT).1
  have := (h𝒳 U hU).1
  obtain ⟨γ, hγ⟩ := exists_conj_map_eq_of_isSimpleFactorOf hmin hnabN
    (isSimpleFactorOf_map_inl (h𝒳 T hT).2.1 (h𝒳 T hT).2.2)
    (isSimpleFactorOf_map_inl (h𝒳 U hU).2.1 (h𝒳 U hU).2.2)
  exact ⟨(Subgroup.equivMapOfInjective T _ SemidirectProduct.inl_injective).trans
    (((Subgroup.equivMapOfInjective _ _ (MulAut.conj γ).injective).trans
      (MulEquiv.subgroupCongr hγ)).trans
      (Subgroup.equivMapOfInjective U _ SemidirectProduct.inl_injective).symm)⟩

/-- **9A.8 の abelian 枝 (step 1)**: characteristically simple な可換有限群は
elementary abelian。

`p` を `|G|` の素因数とすると `K = {x | x ^ p = 1}` は (可換ゆえ) 部分群で,
自己同型が `x ^ p = 1` を保つので **characteristic**。Cauchy で `K ≠ 1` なので `K = ⊤`,
すなわち `∀ x, x ^ p = 1`。 -/
theorem exists_isElementaryAbelian_of_isCharacteristicallySimple [Finite G]
    (h : IsCharacteristicallySimple G) (hcomm : IsMulCommutative G) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p G := by
  have := h.1
  have := hcomm
  have hcard : Nat.card G ≠ 1 := fun hc =>
    (not_subsingleton G) (Nat.card_eq_one_iff_unique.mp hc).1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, fun x y => mul_comm' x y, ?_⟩
  -- `K = {x | x ^ p = 1}` は characteristic な部分群。
  let K : Subgroup G :=
    { carrier := {x : G | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := fun {a b} ha hb => by
        change (a * b) ^ p = 1
        rw [Commute.mul_pow (mul_comm' a b), ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        change (a⁻¹) ^ p = 1
        rw [inv_pow, show a ^ p = 1 from ha, inv_one] }
  have hKchar : K.Characteristic := by
    rw [Subgroup.characteristic_iff_comap_le]
    intro σ x hx
    have hσ : σ (x ^ p) = 1 := by
      rw [map_pow]
      exact hx
    change x ^ p = 1
    exact σ.injective (by rw [hσ, map_one])
  have hKne : K ≠ ⊥ := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    intro hbot
    have hmem : g ∈ K := by
      change g ^ p = 1
      rw [← hg]
      exact pow_orderOf_eq_one g
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hg
    exact hp.one_lt.ne hg
  rcases h.2 K hKchar with hbot | htop
  · exact absurd hbot hKne
  · intro x
    have : x ∈ K := htop ▸ Subgroup.mem_top x
    exact this

/-- **抽象モジュール版**: 有限非自明な `ZMod p`-ベクトル空間は 1 次元部分空間 (位数 `p`)
の直和。`Module` を抽象のまま保つのが要点 — `letI` 束縛の `zmodModule` 上で基底の
instance 合成を走らせると詰まる (`PRank.lean` の `addAutEquivGL` の注記)。 -/
theorem exists_addSubgroup_basis_family.{u} {p : ℕ} [Fact p.Prime] {M : Type u}
    [AddCommGroup M] [Module (ZMod p) M] [Finite M] [Nontrivial M] :
    ∃ (ι : Type u) (_ : Nonempty ι) (N : ι → AddSubgroup M),
      (∀ i, Nat.card ↥(N i) = p) ∧ iSupIndep N ∧ ⨆ i, N i = ⊤ := by
  let e : AddSubgroup M ≃o Submodule (ZMod p) M := AddSubgroup.toZModSubmodule p
  let b := Module.Basis.ofVectorSpace (ZMod p) M
  refine ⟨_, b.index_nonempty, fun i => e.symm (Submodule.span (ZMod p) {b i}), ?_, ?_, ?_⟩
  · intro i
    have hcong : Nat.card ↥(e.symm (Submodule.span (ZMod p) {b i}))
        = Nat.card ↥(Submodule.span (ZMod p) {b i}) :=
      Nat.card_congr ⟨fun x => ⟨x.1, x.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hcong, ← FiniteField.pow_finrank_eq_natCard p ↥(Submodule.span (ZMod p) {b i}),
      finrank_span_singleton (b.ne_zero i), pow_one]
  · exact (iSupIndep_map_orderIso_iff e.symm).mpr b.linearIndependent.iSupIndep_span_singleton
  · rw [← OrderIso.map_iSup e.symm, ← Submodule.span_range_eq_iSup, b.span_eq, OrderIso.map_top]

open scoped IsMulCommutative in
/-- **9A.8 の abelian 枝 (step 2)**: elementary abelian な有限群は位数 `p` の部分群
(どれも互いに同型) の直積。

`Additive G` を `ZMod p`-ベクトル空間と見て `exists_addSubgroup_basis_family` を当て,
`Subgroup.toAddSubgroup` の order iso で `G` に戻す (`PRank.lean` の
`IsElementaryAbelian.exists_isComplement'` と同じ橋渡し)。 -/
theorem exists_simpleFamily_of_isElementaryAbelian.{u} {G : Type u} [Group G] [Finite G]
    [Nontrivial G] {p : ℕ} [Fact p.Prime] (h : IsElementaryAbelian p G) :
    ∃ (ι : Type u) (_ : Nonempty ι) (T : ι → Subgroup G),
      (∀ i, (T i).Normal ∧ IsSimpleGroup ↥(T i)) ∧
      (∀ i j, Nonempty (↥(T i) ≃* ↥(T j))) ∧
      iSupIndep T ∧ ⨆ i, T i = ⊤ := by
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  let : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  let : CommGroup G := inferInstance
  let := IsElementaryAbelian.zmodModule (p := p) (G := G) h
  have : Finite (Additive G) := Finite.of_equiv G Additive.ofMul
  have : Nontrivial (Additive G) := Additive.ofMul.symm.injective.nontrivial
  obtain ⟨ι, hι, N, hcardN, hindep, hsupN⟩ :=
    exists_addSubgroup_basis_family (p := p) (M := Additive G)
  have hcardT : ∀ i, Nat.card ↥(Subgroup.toAddSubgroup.symm (N i)) = p := fun i => by
    rw [← hcardN i]
    exact Nat.card_congr ⟨fun x => ⟨Additive.ofMul (x : G), x.2⟩,
      fun y => ⟨Additive.toMul (y : Additive G), y.2⟩, fun _ => rfl, fun _ => rfl⟩
  refine ⟨ι, hι, fun i => Subgroup.toAddSubgroup.symm (N i), ?_, ?_, ?_, ?_⟩
  · exact fun i => ⟨⟨fun n hn g => by rwa [mul_comm' g n, mul_assoc, mul_inv_cancel, mul_one]⟩,
      isSimpleGroup_of_prime_card (p := p) (hcardT i)⟩
  · exact fun i j => ⟨mulEquivOfPrimeCardEq (hcardT i) (hcardT j)⟩
  · exact (iSupIndep_map_orderIso_iff Subgroup.toAddSubgroup.symm).mpr hindep
  · rw [← OrderIso.map_iSup Subgroup.toAddSubgroup.symm, hsupN, OrderIso.map_top]

/-- **Isaacs Problem 9A.8** (書籍 p. 277) ⭐: characteristically simple な有限群は,
互いに同型な単純群の直積。

書籍 hint の holomorph `G ⋊ Aut(G)` で `G` を極小正規部分群にすると Lemma 9.6 が
「abelian か semisimple」の二分を与える (`isMulCommutative_or_isSemisimpleGroup_…`)。

* **semisimple 枝**: 非可換単純正規部分群の族が取れ, 9A.7 (`Hol(G)` の共役の推移性) で
  互いに同型。
* **abelian 枝**: `{x | x ^ p = 1}` が characteristic なので elementary abelian になり,
  `ZMod p`-基底から位数 `p` の部分群の族が取れる (どれも `ZMod p` に同型)。 -/
theorem exists_simpleFamily_of_isCharacteristicallySimple.{u} {G : Type u} [Group G] [Finite G]
    (h : IsCharacteristicallySimple G) :
    ∃ (ι : Type u) (_ : Nonempty ι) (T : ι → Subgroup G),
      (∀ i, (T i).Normal ∧ IsSimpleGroup ↥(T i)) ∧
      (∀ i j, Nonempty (↥(T i) ≃* ↥(T j))) ∧
      iSupIndep T ∧ ⨆ i, T i = ⊤ := by
  have := h.1
  rcases isMulCommutative_or_isSemisimpleGroup_of_isCharacteristicallySimple h with hab | hss
  · obtain ⟨p, hp, hea⟩ := exists_isElementaryAbelian_of_isCharacteristicallySimple h hab
    have : Fact p.Prime := ⟨hp⟩
    exact exists_simpleFamily_of_isElementaryAbelian hea
  · obtain ⟨𝒵, hne, hsimple, hiso, hindep, hsup⟩ :=
      exists_simpleFamily_of_isSemisimpleGroup_of_isCharacteristicallySimple h hss
    refine ⟨↥𝒵, hne.to_subtype, fun S => (S : Subgroup G), fun S => hsimple S S.2,
      fun S U => hiso S S.2 U U.2, hindep, ?_⟩
    rw [← sSup_eq_iSup']
    exact hsup

end -- 9A.8

end OddOrder.Isaacs.Ch09
