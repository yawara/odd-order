/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Components
import OddOrder.Isaacs.Ch09_MoreSubnormality.Semisimple

/-!
# Isaacs Ch. 9 — §9A: the layer E(G) と Theorem 9.7 (pp. 274-275)

- `layer G` = **layer** `E(G)` = すべての component の生成する部分群 (書籍 p. 274,
  `sSup {H | IsComponent H}`). Thm 9.4 で component は互いを正規化するので各 component は
  `E(G)` で正規, かつ component の集合は共役不変ゆえ `E(G) ◁ G` (characteristic).
- **Theorem 9.7**:
  - (a) `commutator_layer_eq_layer`: `E' = E` (`E` は perfect).
  - (b) `isSemisimpleGroup_layer_quotient_center`: `E/Z(E)` は semisimple.
  - (c) `commutator_layer_eq_bot_of_normal_isSolvable`: `[E,M] = 1` (任意の solvable normal `M`).

Thm 9.8 / Cor 9.9 (F\*(G)) は後続 leaf `GeneralizedFitting.lean`.

## 実装ノート

(b) が最重量。書籍は `Z(H) = H ∩ Z(E)` を示して `Ē = E/Z` を simple 商の積として
semisimple と結論する。`↥E ⧸ center ↥E` の semisimple 族を、各 component `H` について
`(H.subgroupOf E).map (mk' (center ↥E))` で構成する:
- normal: `H ◁ E` の像。
- nonabelian simple: `Subgroup.subgroupOfEquivOfLe` で `H.subgroupOf E ≅ ↥H` を移し、
  第一同型で `H̄ ≅ ↥H/center ↥H` (= quasisimple の simple 商)。核が `center` に一致するのは
  `Z(H) = H ∩ Z(E)` の帰結。
- generate: component が `E` を生成 ⇒ 像が `⊤` を生成。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9A: the layer E(G) (p. 274) -/

/-- **Layer** `E(G)` (Isaacs p. 274): すべての component の生成する部分群. -/
def layer (G : Type*) [Group G] : Subgroup G :=
  sSup {H : Subgroup G | IsComponent H}

/-- component は layer に含まれる. -/
theorem IsComponent.le_layer {H : Subgroup G} (hH : IsComponent H) : H ≤ layer G :=
  le_sSup hH

/-- component の共役はまた component. -/
theorem IsComponent.conj {H : Subgroup G} (hH : IsComponent H) (g : G) :
    IsComponent (H.map (MulAut.conj g).toMonoidHom) where
  isSubnormal := by
    have := hH.isSubnormal.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
    simpa using this
  isQuasisimple :=
    hH.isQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)

/-- `map (conj g) (layer G) ≤ layer G` (component の像がまた component ゆえ). -/
theorem map_conj_layer_le (g : G) :
    (layer G).map (MulAut.conj g).toMonoidHom ≤ layer G := by
  rw [layer, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun H hH => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact (hH.conj g).le_layer

/-- layer は共役で不変. -/
theorem map_conj_layer (g : G) :
    (layer G).map (MulAut.conj g).toMonoidHom = layer G := by
  refine le_antisymm (map_conj_layer_le g) ?_
  have h := map_conj_layer_le (G := G) g⁻¹
  have hmono := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
  rwa [Subgroup.map_map, show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom
      = MonoidHom.id G from by ext y; simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id] at hmono

/-- **layer は `G` で正規** (component の集合が共役不変ゆえ). -/
instance layer.normal : (layer G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have : (MulAut.conj g) n ∈ (layer G).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [map_conj_layer] at this
  simpa [MulAut.conj_apply] using this

/-- **component は layer で正規**: `H.subgroupOf (layer G)` は `↥(layer G)` で正規.
Thm 9.4 で相異なる component は可換ゆえ, 各 component は他の component を正規化する. -/
theorem IsComponent.normal_subgroupOf_layer [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    (H.subgroupOf (layer G)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH.le_layer]
  refine sSup_le fun K hK => ?_
  by_cases heq : K = H
  · rw [heq]; exact Subgroup.le_normalizer
  · have hcomm : ⁅K, H⁆ = ⊥ := hK.commutator_eq_bot_of_ne hH heq
    have hle : K ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact hle.trans (Subgroup.centralizer_le_normalizer _)

end

section /- 9A: Theorem 9.7 (a) (p. 274) -/

/-- **Isaacs Theorem 9.7(a)**: `E' = E` (layer は perfect). -/
theorem commutator_layer_eq_layer [Finite G] :
    ⁅layer G, layer G⁆ = layer G := by
  refine le_antisymm (Subgroup.commutator_le_right _ _) ?_
  refine sSup_le fun H hH => ?_
  -- 各 component `H` は perfect: `H = ⁅H,H⁆ ≤ ⁅layer,layer⁆`
  haveI := hH.isQuasisimple.isPerfect
  calc H = ⁅H, H⁆ := (Subgroup.commutator_eq_self (H := H)).symm
    _ ≤ ⁅layer G, layer G⁆ := Subgroup.commutator_mono hH.le_layer hH.le_layer

/-- **Isaacs Theorem 9.7(a) (perfect 形)**. -/
theorem isPerfect_layer [Finite G] : Group.IsPerfect ↥(layer G) :=
  Subgroup.isPerfect_iff.mpr (commutator_layer_eq_layer)

end

section /- 9A: Theorem 9.7 (b)(c) 補助 — Z(H) = H ∩ Z(E) (p. 274) -/

/-- component `H` の元 `x` が `H` を中心化するなら, layer 全体を中心化する
(`[H,K]=1` for `K ≠ H` (Thm 9.4) + `E = sSup components`). Z(H) = H ∩ Z(E) の核. -/
theorem mem_centralizer_layer_of_component [Finite G] {H : Subgroup G} (hH : IsComponent H)
    {x : G} (hxH : x ∈ H) (hxc : x ∈ Subgroup.centralizer (H : Set G)) :
    x ∈ Subgroup.centralizer (layer G : Set G) := by
  have hle : layer G ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sSup_le fun K hK => fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    by_cases heq : K = H
    · subst heq
      exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
    · have hcomm : ⁅H, K⁆ = ⊥ := hH.commutator_eq_bot_of_ne hK (Ne.symm heq)
      have hxcK : x ∈ Subgroup.centralizer (K : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hxH
      exact (Subgroup.mem_centralizer_iff.mp hxcK y hy).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm

/-- **Z(H) = H ∩ Z(E)** (Thm 9.7 途中): component `H` について
`(center ↥E).subgroupOf Ĥ = center ↥Ĥ` (`Ĥ = H.subgroupOf E`, `E = layer G`). -/
theorem center_subgroupOf_component_layer [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    (center ↥(layer G)).subgroupOf (H.subgroupOf (layer G))
      = center ↥(H.subgroupOf (layer G)) := by
  ext a
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · -- a ∈ center ↥E ⇒ a は Ĥ を中心化
    intro ha b
    apply Subtype.ext
    have h := ha (b : ↥(layer G))
    simpa only [Subgroup.coe_mul] using h
  · -- a が Ĥ を中心化 ⇒ a ∈ center ↥E
    intro ha w
    have haH : ((a : ↥(layer G)) : G) ∈ H := a.2
    -- (a : ↥E).val は H を中心化 (a が Ĥ を中心化するので)
    have hcentH : ((a : ↥(layer G)) : G) ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hcomm := ha ⟨⟨h, hH.le_layer hh⟩,
        by rw [Subgroup.mem_subgroupOf]; exact hh⟩
      have h2 := congrArg (fun t : ↥(H.subgroupOf (layer G)) => ((t : ↥(layer G)) : G)) hcomm
      simpa only [Subgroup.coe_mul] using h2
    -- ゆえに (a : ↥E).val は E 全体を中心化
    have hcentE := mem_centralizer_layer_of_component hH haH hcentH
    apply Subtype.ext
    have hG := Subgroup.mem_centralizer_iff.mp hcentE ((w : G)) w.2
    simpa only [Subgroup.coe_mul] using hG

/-- component の像 `H̄ = (H.subgroupOf E).map (mk' (center ↥E))` は
`↥H ⧸ center ↥H` と同型 (第一同型定理 + `Z(H) = H ∩ Z(E)`). -/
noncomputable def componentImageEquiv [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    ↥(((H.subgroupOf (layer G)).map (QuotientGroup.mk' (center ↥(layer G)))))
      ≃* (↥H ⧸ center ↥H) := by
  set E := layer G
  set Ĥ := H.subgroupOf E
  set π := QuotientGroup.mk' (center ↥E)
  have hker : (π.comp Ĥ.subtype).ker = center ↥Ĥ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact center_subgroupOf_component_layer hH
  have hrange : (π.comp Ĥ.subtype).range = Ĥ.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  set e0 : Ĥ ≃* ↥H := Subgroup.subgroupOfEquivOfLe hH.le_layer
  have e2 : (↥Ĥ ⧸ center ↥Ĥ) ≃* ↥(Ĥ.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange))
  have e3 : (↥Ĥ ⧸ center ↥Ĥ) ≃* (↥H ⧸ center ↥H) :=
    QuotientGroup.congr (center ↥Ĥ) (center ↥H) e0 (map_center_mulEquiv e0)
  exact e2.symm.trans e3

/-- **Isaacs Theorem 9.7(b)**: `E/Z(E)` は semisimple. -/
theorem isSemisimpleGroup_layer_quotient_center [Finite G] :
    IsSemisimpleGroup (↥(layer G) ⧸ center ↥(layer G)) := by
  set E := layer G
  set π := QuotientGroup.mk' (center ↥E)
  refine ⟨Set.range (fun H : {H : Subgroup G // IsComponent H} =>
    ((H : Subgroup G).subgroupOf E).map π), ?_, ?_⟩
  · rintro _ ⟨H, rfl⟩
    have hnormal : (((H : Subgroup G).subgroupOf E).map π).Normal :=
      Subgroup.Normal.map H.2.normal_subgroupOf_layer π (QuotientGroup.mk'_surjective _)
    have e := componentImageEquiv H.2
    haveI := H.2.isQuasisimple.isSimpleGroup_quotient
    refine ⟨hnormal, e.isSimpleGroup, fun hcomm => ?_⟩
    haveI := hcomm
    exact not_isMulCommutative_of_isSimpleGroup_quotient_center
      H.2.isQuasisimple.isSimpleGroup_quotient
      (isMulCommutative_of_surjective e.toMonoidHom e.surjective)
  · -- 族が生成: component が `E` を生成 ⇒ 像が `⊤`
    have hgen : ⨆ H : {H : Subgroup G // IsComponent H}, ((H : Subgroup G).subgroupOf E) = ⊤ := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hcongr : (⨆ H : {H : Subgroup G // IsComponent H},
          ((H : Subgroup G).subgroupOf E).map E.subtype)
          = ⨆ H : {H : Subgroup G // IsComponent H}, (H : Subgroup G) := by
        apply iSup_congr
        intro H
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr H.2.le_layer]
      rw [hcongr, show E = sSup {H : Subgroup G | IsComponent H} from rfl]
      exact (sSup_eq_iSup' _).symm
    apply le_antisymm le_top
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _), ← hgen,
      Subgroup.map_iSup]
    refine iSup_le fun H => le_sSup ⟨H, rfl⟩

end

section /- 9A: Theorem 9.7 (c) (p. 274) -/

/-- **Isaacs Theorem 9.7(c)**: `[E, M] = 1` for every solvable normal subgroup `M`.

`M ⊓ E` は `E/Z(E)` の solvable normal 像を持つが semisimple なので (b) + payload で自明,
すなわち `M ⊓ E ⊆ Z(E)`. ゆえに `[M,E] ≤ M ⊓ E ⊆ C_G(E)`, three subgroups lemma と
`E` perfect で `[E,M] = 1`. -/
theorem commutator_layer_eq_bot_of_normal_isSolvable [Finite G] {M : Subgroup G}
    [M.Normal] (hM : IsSolvable ↥M) : ⁅layer G, M⁆ = ⊥ := by
  set E := layer G with hE
  set π := QuotientGroup.mk' (center ↥E) with hπ
  -- Step 1: M ⊓ E ⊆ C_G(E)
  have hcentME : (M ⊓ E : Subgroup G) ≤ Subgroup.centralizer (E : Set G) := by
    set N : Subgroup ↥E := (M ⊓ E).subgroupOf E with hN
    haveI hNnormal : N.Normal := Subgroup.Normal.subgroupOf inferInstance E
    haveI hMEsolv : IsSolvable ↥(M ⊓ E) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (inf_le_left : M ⊓ E ≤ M))
    haveI hNsolv : IsSolvable ↥N :=
      solvable_of_solvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ E ≤ E)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ E ≤ E)).injective
    have hrange : (π.comp N.subtype).range = N.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    haveI : IsSolvable ↥((π.comp N.subtype).range) :=
      solvable_of_surjective (π.comp N.subtype).rangeRestrict_surjective
    haveI hImgSolv : IsSolvable ↥(N.map π) := hrange ▸ this
    have himg : N.map π = ⊥ :=
      isSemisimpleGroup_layer_quotient_center.eq_bot_of_normal_of_isSolvable
        (Subgroup.Normal.map hNnormal π (QuotientGroup.mk'_surjective _)) hImgSolv
    have hNle : N ≤ center ↥E := by
      have := (Subgroup.map_eq_bot_iff _).mp himg
      rwa [QuotientGroup.ker_mk'] at this
    intro w hw
    have hwmem : (⟨w, hw.2⟩ : ↥E) ∈ center ↥E :=
      hNle (by rw [hN, Subgroup.mem_subgroupOf]; exact hw)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hwmem ⟨y, hy⟩)
    simpa only [Subgroup.coe_mul] using h2
  -- Step 2: ⁅M,E⁆ ≤ M ⊓ E ⊆ C_G(E), so ⁅⁅M,E⁆,E⁆ = ⊥
  have hME_le : ⁅M, E⁆ ≤ Subgroup.centralizer (E : Set G) :=
    (le_inf (Subgroup.commutator_le_left M E) (Subgroup.commutator_le_right M E)).trans hcentME
  have hbot1 : ⁅⁅M, E⁆, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hME_le
  have hbot2 : ⁅⁅E, M⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm E M]; exact hbot1
  -- Step 3: three subgroups + E perfect
  have hrot : ⁅⁅E, E⁆, M⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hbot2 hbot1
  rwa [commutator_layer_eq_layer] at hrot

end

end OddOrder.Isaacs.Ch09
