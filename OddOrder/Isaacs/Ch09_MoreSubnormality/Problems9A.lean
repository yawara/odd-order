/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.NoncommCoprod
import OddOrder.Isaacs.Ch09_MoreSubnormality.LayerRestriction

/-!
# Isaacs §9A の演習 (書籍 p. 277)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9A
(component / layer `E(G)` / generalized Fitting subgroup `F*(G)` 周辺)。

* **9A.1** `map_layer_eq_layer_of_genFitting_le` / `layerInG_eq_layer_of_genFitting_le` —
  `F*(G) ≤ H ≤ G` なら `E(H) = E(G)`。
* **9A.2** `exists_socle_mulEquiv_prod_abelian_semisimple` — `Soc(G)` は
  「abelian 群」と「semisimple 群」の直積 (`abelianSocle` × `semisimpleSocle`)。

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
  haveI : M.Normal := Subgroup.Normal.subgroupOf inferInstance H
  haveI : IsSolvable ↥M := by
    haveI := Ch01.fitting.isNilpotent (G := G)
    haveI : IsSolvable ↥(Ch01.fitting G) := IsNilpotent.to_isSolvable
    have hinj : Function.Injective
        ((Subgroup.subgroupOfEquivOfLe hFH).toMonoidHom : ↥M →* ↥(Ch01.fitting G)) :=
      (Subgroup.subgroupOfEquivOfLe hFH).injective
    exact solvable_of_solvable_injective hinj
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
      haveI := hV.isQuasisimple.isPerfect
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
  · haveI : IsMulCommutative ↥(N : Subgroup G) := N.2.2
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

/-- 非可換な極小正規部分群 `M` を, `M` で正規な非可換単純部分群たちの join に分解する
(Lemma 9.6 で `↥M` は semisimple, その族を ambient に押し出したもの)。 -/
theorem exists_simpleFamily_of_isMinimalNormal [Finite G] {M : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hnab : ¬IsMulCommutative ↥M) :
    ∃ 𝒵 : Set (Subgroup G),
      (∀ T ∈ 𝒵, T ≤ M ∧ M ≤ Subgroup.normalizer T ∧ IsSimpleGroup ↥T ∧
        ¬IsMulCommutative ↥T) ∧
      sSup 𝒵 = M := by
  haveI := hM.1
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
    · haveI := hTsimple
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
      · haveI := hTsimple
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

end OddOrder.Isaacs.Ch09
