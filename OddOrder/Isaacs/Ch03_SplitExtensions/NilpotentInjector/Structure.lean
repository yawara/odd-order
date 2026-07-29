/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.Defs

/-!
# Isaacs Problem 3C.8 — Mann の核心補題

`p ≠ q` のとき **`C(p)` は `C(q)` の Sylow `q`-部分群 `S` を正規化する**
(`map_conj_eq_self_of_mem_pCentralizer`)。3C.8 の共役性はこの一点に帰着する:
`S` を素数ごとに `C(p)` の元で共役して揃えるとき、他の素数の成分が動かないことが保証される。

## 証明

`Z := C_G(F(G))` とおく。可解群では `Z ≤ F(G)` (`centralizer_fitting_le_fitting`) なので
`Z` は可換 (したがって冪零) で `G` に正規。

1. `C(p)`, `C(q)` はともに `G` に正規なので, `x ∈ C(p)`, `y ∈ C(q)` について
   交換子 `xyx⁻¹y⁻¹` は `C(p) ⊓ C(q) ≤ Z` に入る
   (`pCentralizer_inf_le_centralizer_fitting`)。
2. `Z` の `{q}`-部分 `Z_q` は `G`-正規な `q`-部分群で `Z ≤ C(q)` だから `Z_q ≤ S`
   (`Subgroup.IsPiGroup.normal_le_hall`)。
3. `Z` の `{q}ᶜ`-部分 `Z_{q'}` は `F(G)` の `{q}ᶜ`-部分 `F_{q'}` に含まれ,
   `S ≤ C(q) = C_G(F_{q'})` なので `S` を中心化する。
4. 1 と 2 から `S^x ≤ S ⊔ Z_{q'}`, 3 から `S ⊔ Z_{q'} ≤ N_G(S)`。よって `S^x` は
   `S` を正規化する `C(q)` 内の `q`-部分群で,
   `isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer` より `S^x ≤ S`, 位数が等しいので `S^x = S`。

## Main results

- `map_conj_eq_self_of_mem_pCentralizer` — 上記。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.8: Mann の核心補題 -/

variable {G : Type*} [Group G]

/-- `Z := C_G(F(G))` は `G` に正規。 -/
instance normal_centralizer_fitting (G : Type*) [Group G] :
    (Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G)).Normal :=
  normal_centralizer inferInstance

/-- 可解群では `Z := C_G(F(G)) ≤ F(G)` なので `Z` は冪零。 -/
theorem isNilpotent_centralizer_fitting [Finite G] [IsSolvable G] :
    Group.IsNilpotent ↥(Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G)) :=
  isNilpotent_of_le inferInstance OddOrder.GroupTheory.centralizer_fitting_le_fitting

/-- `C_G(F(G)) ≤ C(p)` (`F_{p'} ≤ F(G)` の中心化群は逆向きに大きい)。 -/
theorem centralizer_fitting_le_pCentralizer [Finite G] [IsSolvable G] (p : ℕ) :
    Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) ≤ pCentralizer G p :=
  Subgroup.centralizer_le (by exact_mod_cast fittingPPrimePart_le (G := G) p)

/-- `p ≠ q` なら `C(p)` と `C(q)` の元の交換子は `C_G(F(G))` に入る。 -/
theorem commutator_mem_centralizer_fitting [Finite G] [IsSolvable G] {p q : ℕ} (hpq : p ≠ q)
    {x y : G} (hx : x ∈ pCentralizer G p) (hy : y ∈ pCentralizer G q) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) := by
  refine pCentralizer_inf_le_centralizer_fitting hpq (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have hconj : y * x⁻¹ * y⁻¹ ∈ pCentralizer G p :=
      (pCentralizer_normal (G := G) p).conj_mem x⁻¹ (inv_mem hx) y
    have := mul_mem hx hconj
    simpa [mul_assoc] using this
  · exact mul_mem ((pCentralizer_normal (G := G) q).conj_mem y hy x) (inv_mem hy)

/-- **Mann の核心補題**: `p ≠ q` のとき `C(p)` の元は `C(q)` の Sylow `q`-部分群を正規化する。 -/
theorem map_conj_eq_self_of_mem_pCentralizer [Finite G] [IsSolvable G] {p q : ℕ} (hpq : p ≠ q)
    {S : Subgroup G} (hS : IsHallPart (pCentralizer G q) S ({q} : Set ℕ))
    {x : G} (hx : x ∈ pCentralizer G p) :
    S.map (MulAut.conj x).toMonoidHom = S := by
  set Z : Subgroup G := Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) with hZdef
  have hZnil : Group.IsNilpotent ↥Z := isNilpotent_centralizer_fitting
  have hZF : Z ≤ Ch01.fitting G := OddOrder.GroupTheory.centralizer_fitting_le_fitting
  have hZC : Z ≤ pCentralizer G q := centralizer_fitting_le_pCentralizer q
  set Zq : Subgroup G := nilPiPart Z ({q} : Set ℕ) with hZq
  set Zq' : Subgroup G := nilPiPart Z (({q} : Set ℕ)ᶜ) with hZq'
  have hZqPart := isHallPart_nilPiPart (N := Z) ({q} : Set ℕ) hZnil
  have hZq'Part := isHallPart_nilPiPart (N := Z) (({q} : Set ℕ)ᶜ) hZnil
  -- (2) `Z_q ≤ S`
  haveI : Zq.Normal := nilPiPart_normal hZnil _
  have hZq_le_S : Zq ≤ S := by
    have hnorm : (Zq.subgroupOf (pCentralizer G q)).Normal := Subgroup.normal_subgroupOf
    have := Subgroup.IsPiGroup.normal_le_hall (N := Zq.subgroupOf (pCentralizer G q))
      (Subgroup.IsPiGroup.subgroupOf (hZqPart.1.trans hZC) hZqPart.isPiGroup) hS.2
    intro z hz
    exact (Subgroup.mem_subgroupOf (H := S) (K := pCentralizer G q)
      (h := ⟨z, hZC (hZqPart.1 hz)⟩)).mp (this (Subgroup.mem_subgroupOf.mpr hz))
  -- (3) `Z_{q'} ≤ F_{q'}` なので `S` を中心化する
  have hZq'_le : Zq' ≤ fittingPPrimePart G q :=
    le_nilPiPart_of_isPiGroup inferInstance (hZq'Part.1.trans hZF) hZq'Part.isPiGroup
  have hcent : Zq' ≤ Subgroup.centralizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hS.1 hs) z (hZq'_le hz)).symm
  -- (4) `S^x ≤ S ⊔ Z_{q'} ≤ N_G(S)`
  set H : Subgroup G := S ⊔ Zq' with hH
  have hH_le_norm : H ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have hZ_le_H : Z ≤ H := by
    rw [← IsHallPart.sup_eq hZqPart hZq'Part]
    exact sup_le (hZq_le_S.trans le_sup_left) le_sup_right
  have hconj_le_H : S.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro - ⟨y, hy, rfl⟩
    have hc : x * y * x⁻¹ * y⁻¹ ∈ Z :=
      commutator_mem_centralizer_fitting hpq hx (hS.1 hy)
    have hfac : (MulAut.conj x) y = (x * y * x⁻¹ * y⁻¹) * y := by
      simp [MulAut.conj_apply]
    rw [MulEquiv.coe_toMonoidHom, hfac]
    exact mul_mem (hZ_le_H hc) ((le_sup_left : S ≤ H) hy)
  -- `S^x` は `C(q)` 内の `q`-部分群で `S` を正規化する
  have hconj_le_C : S.map (MulAut.conj x).toMonoidHom ≤ pCentralizer G q := by
    have hCconj : (pCentralizer G q).map (MulAut.conj x).toMonoidHom = pCentralizer G q :=
      Subgroup.Normal.map_conj_eq (pCentralizer G q) x
    have hmono := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hS.1
    rwa [hCconj] at hmono
  have hcard : Nat.card ↥((S.map (MulAut.conj x).toMonoidHom : Subgroup G)) = Nat.card ↥S := by
    apply Subgroup.card_map_of_injective
    exact (MulAut.conj x).injective
  have hle : S.map (MulAut.conj x).toMonoidHom ≤ S := by
    have hsub : (S.map (MulAut.conj x).toMonoidHom).subgroupOf (pCentralizer G q)
        ≤ S.subgroupOf (pCentralizer G q) := by
      refine isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer hS.2 ?_ ?_
      · intro r hr
        refine hS.isPiGroup r ?_
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj_le_C).toEquiv, hcard] at hr
      · rw [← Subgroup.subgroupOf_normalizer_eq hS.1]
        intro z hz
        exact Subgroup.mem_subgroupOf.mpr (hH_le_norm (hconj_le_H hz))
    intro z hz
    exact (Subgroup.mem_subgroupOf (H := S) (K := pCentralizer G q)
      (h := ⟨z, hconj_le_C hz⟩)).mp (hsub (Subgroup.mem_subgroupOf.mpr hz))
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

end -- 3C.8: Mann の核心補題

end OddOrder.Isaacs.Ch03
