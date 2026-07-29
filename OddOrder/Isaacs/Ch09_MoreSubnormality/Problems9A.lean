/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.LayerRestriction

/-!
# Isaacs §9A の演習 (書籍 p. 277)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9A
(component / layer `E(G)` / generalized Fitting subgroup `F*(G)` 周辺)。

* **9A.1** `map_layerInG_eq_layer_of_genFitting_le` — `F*(G) ≤ H ≤ G` なら `E(H) = E(G)`。

## 実装ノート

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

end OddOrder.Isaacs.Ch09
