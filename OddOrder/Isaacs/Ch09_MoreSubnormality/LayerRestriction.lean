/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.GeneralizedFitting

/-!
# Isaacs Ch. 9 — §9C: Lemma 9.25 (E(G) = E(H) when F(G) = 1), p. 283

- **Lemma 9.25** (`map_layer_eq_layer_of_fitting_eq_bot`): `H ≤ G` (有限群),
  `F(G) = 1`, `E(G) ≤ H` ならば `E(G) = E(H)` (ambient で
  `(layer ↥H).map H.subtype = layer G`).

Thompson-Wielandt (Thm 9.24) の証明で使う補題。

## 実装ノート

`E(G) ≤ E(H)`: `G` の component `K ≤ E(G) ≤ H` は `↥H` の component
(`IsComponent.subgroupOf`)。`E(H) ≤ E(G)`: `↥H` の component `V` が `E(G)` に
入らないと仮定すると、`G` の各 component `K` は `↥H` の `V` と異なる component
(`K.subgroupOf H ≠ V`) なので Thm 9.4 (`↥H` 内) で `V` は `K` を中心化 →
`V` は `E(G) = F*(G)` (F=1) を中心化 → 9.8 で `V ≤ C_G(F*) ≤ F* = E(G)` 矛盾。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9C: Lemma 9.25 (p. 283) -/

/-- `F(G) = 1` ならば `C_G(E(G)) ≤ E(G)` (F*(G) = E(G) + Thm 9.8). -/
theorem centralizer_layer_le_layer_of_fitting_eq_bot [Finite G]
    (hF : Ch01.fitting G = ⊥) :
    Subgroup.centralizer (layer G : Set G) ≤ layer G := by
  have hFstar : genFitting G = layer G := by rw [genFitting, hF, bot_sup_eq]
  rw [← hFstar]
  exact centralizer_genFitting_le_genFitting

/-- **Isaacs Lemma 9.25** (p. 283): `H ≤ G` (有限群), `F(G) = 1`, `E(G) ≤ H` ならば
`E(G) = E(H)`. -/
theorem map_layer_eq_layer_of_fitting_eq_bot [Finite G] {H : Subgroup G}
    (hF : Ch01.fitting G = ⊥) (hle : layer G ≤ H) :
    (layer ↥H).map H.subtype = layer G := by
  apply le_antisymm
  · -- `E(H) ≤ E(G)`
    have key : ∀ V : Subgroup ↥H, IsComponent V → V.map H.subtype ≤ layer G := by
      intro V hV
      by_contra hVnle
      -- `E(G) ≤ C_G(V.map subtype)`: 各 component `K` は `↥H` の `V` と異なり Thm 9.4
      have hcent : layer G ≤ Subgroup.centralizer (V.map H.subtype : Set G) := by
        refine sSup_le fun K hK => ?_
        have hcompK : IsComponent K := hK
        have hKH : K ≤ H := hcompK.le_layer.trans hle
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
      exact hVnle
        ((Subgroup.le_centralizer_iff.mp hcent).trans
          (centralizer_layer_le_layer_of_fitting_eq_bot hF))
    rw [Subgroup.map_le_iff_le_comap,
      show layer (↥H) = sSup {V : Subgroup ↥H | IsComponent V} from rfl]
    refine sSup_le fun V hV => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact key V hV
  · -- `E(G) ≤ E(H)`
    refine sSup_le fun K hK => ?_
    have hcompK : IsComponent K := hK
    have hKH : K ≤ H := hcompK.le_layer.trans hle
    calc K = (K.subgroupOf H).map H.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH]
      _ ≤ (layer ↥H).map H.subtype := Subgroup.map_mono (hcompK.subgroupOf hKH).le_layer

end

end OddOrder.Isaacs.Ch09
