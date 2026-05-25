/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.ChiefFactor
import OddOrder.GroupTheory.FrattiniPGroup
import Mathlib.Order.Minimal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BG §1: Elementary Properties of Solvable Groups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §1 (pp. 1-8), mmd `references/bg/local-analysis.mmd` L310-585, **22 結果** (Lemma/
Proposition/Theorem/Corollary 1.1-1.22).

## 構造 (BG §1 全 22 結果)

§1 を概念別に 7 つの sub-section に整理:

- **§1A** Solvable group basics (Lem 1.1, Prop 1.2-1.4)
- **§1B** A-invariant Hall theory (Prop 1.5, Prop 1.6) — Peterfalvi で多数引用
- **§1C** Frattini + Burnside operator (Lem 1.7, Thm 1.8, Lem 1.9, Prop 1.10)
- **§1D** p-odd action (Thm 1.11, Cor 1.12, Thm 1.13 Thompson critical)
- **§1E** Sylow lift + Hall-Higman + noncyclic auto (Lem 1.14, Prop 1.15, Prop 1.16)
- **§1F** Focal + Burnside + Maschke (Thm 1.17, Thm 1.18, Cor 1.19, Thm 1.20) — **mathlib 直接**
- **§1G** p-length one + p-group normal series (Lem 1.21, Lem 1.22)

## Isaacs FGT / mathlib 対応表

CLAUDE.md no-mathlib-wrapper policy 準拠: mathlib 直接対応がある §1F の 4 結果は
**section docstring 記載のみで個別 theorem を書かない**.

| BG | Isaacs FGT | mathlib | 本ファイル |
|---|---|---|---|
| **Lem 1.1** | Ch.3 Thm 3.11 + Ch.1 Fitting + Ch.4 Z(F(G)) | — | ✅ **sorry-free** |
| **Prop 1.2 forward** | chief factors + Fitting quotient image | — | ✅ **sorry-free partial** |
| **Prop 1.3** | Ch.1 Fitting maximality + solvable commutator descent | — | ✅ **sorry-free** |
| Thm 1.8 | Thm 1.8 | (Ch.1 §1B TODO) | Phase 1 待ち |
| **Lem 1.7(a)** | — | `frattini_nongenerating` ✅ | ✅ **sorry-free finite 特殊化** |
| **Lem 1.7(b)(c⇒)(d⊇)** | — | `OddOrder.GroupTheory.FrattiniPGroup` ✅ | ✅ **sorry-free shared module** |
| **Lem 1.7(c⇐)** | Isaacs Lem 4.5 | `frattini_le_iff_isElementaryAbelian_quotient_of_pgroup` ✅ | ✅ **sorry-free** |
| **Lem 1.7(d⇐)** | Isaacs Lem 4.5 | `R/K` elementary abelian | ✅ **sorry-free** |
| Thm 1.11 | Thm 4.36 | Phase 1 Ch.4 §4D | Phase 1 待ち |
| Thm 1.13 | (Thompson critical) | (Phase 1 未) | Phase 1 待ち |
| **Lem 1.14** main | — | Sylow II in T·M + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` | ✅ **sorry-free 完成** |
| **Lem 1.14** 易方向 | — | `Subgroup.normalizer_le_normalizer_sup_normal` + `le_normalizer` | ✅ **sorry-free 5 行** |
| **Prop 1.15(a)** | Thm 3.21 | `hall_higman_1_2_3` ✅ | ✅ **sorry-free thin wrap** (π = {p} 特殊化) |
| Thm 1.17 | Thm 5.21 | `commutator_inf_eq_focalSubgroup` ✅ | no-wrapper, docstring 参照 |
| Thm 1.18 | Thm 5.13 | `ker_transferSylow_isComplement'` ✅ | no-wrapper |
| Cor 1.19(b) | — | `IsZGroup.coprime_commutator_index` ✅ | no-wrapper, audit 発見 |
| Thm 1.20 | — | `Maschke` ✅ | no-wrapper |
| **Lem 1.22** | (Ch.1 系) | `IsPGroup.normal_inf_center_nontrivial` + Cauchy + 帰納 | ✅ **proof 完成** |

## Audit context

Phase 2a 第 1 波 audit (2026-05-23) で §1 を 4 視点で再調査済.
詳細: `notes/bg/s01_solvable.md` + `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.

主要 audit 発見 (§1 関連):
- Lem 1.1 "43+ 回引用" → 実測 0 in §2+
- Prop 1.2 "22 回引用" → 実測 6
- Thm 1.13 ↔ Isaacs 4.31 同一視 → 別物 (Thompson critical ≠ P×Q)
- Cor 1.19(b) → mathlib `IsZGroup.coprime_commutator_index` 直接ヒット
- 内部 hub は **Prop 1.5(d)** (6 §1 proofs)

## 実装 status (2026-05-24) — §1E 全 sorry-free 完成 ⭐ + §1A §1B §1C §1G 部分着手

- **Skeleton** + **§1B/§1F docstring mapping** + **18 結果/補題 全 sorry-free**:
  - **Lem 1.1** `isMinimalNormal_le_fitting_and_isElementaryAbelian` ⭐ sorry-free
    (`M ≤ F(G) ∧ M ≤ C_G(F(G)) ∧ M` elementary abelian)
  - **Prop 1.2 forward inclusion** `fitting_map_subtype_le_chiefFactorCentralizer` ⭐
    sorry-free partial (`F(G*)` centralizes every chief factor `U/V`)
  - **Prop 1.3** `centralizer_fitting_le_fitting` ⭐ sorry-free
  - **Lem 1.7(a)** `eq_top_of_sup_frattini_eq_top` ⭐ sorry-free (mathlib finite 特殊化)
  - **Lem 1.7(b)** `quotient_frattini_isElementaryAbelian` ⭐ sorry-free (shared module)
  - **Lem 1.7(c⇒)** `isElementaryAbelian_of_frattini_eq_bot` ⭐ sorry-free (shared module)
  - **Lem 1.7(c)** `frattini_eq_bot_iff_isElementaryAbelian` ⭐ sorry-free (Ch.4 Lem 4.5)
  - **Lem 1.7(d⊇)** `commutator_sup_pow_closure_le_frattini` ⭐ sorry-free (shared module)
  - **Lem 1.7(d⇐)** `frattini_le_commutator_sup_pow_closure` ⭐ sorry-free (Ch.4 Lem 4.5)
  - **Lem 1.7(d)** `commutator_sup_pow_closure_eq_frattini` ⭐ sorry-free
  - **Thm 1.8** `burnside_operator` ⭐ sorry-free (Isaacs Cor 3.29 `aFixed_quotient_frattini` 経由)
  - **Lem 1.9 (2-step)** `coprime_actsTrivially_of_normal_and_quotient` ⭐ sorry-free (Isaacs Cor 3.28 経由)
  - **Lem 1.22** `normal_subgroup_card_pow_le_of_pGroup` ⭐ sorry-free 完成
  - **Lem 1.14 main** `normalizer_sup_eq_normalizer_sup_of_pGroup_coprime` ⭐ **sorry-free 完成**
  - **Lem 1.14 易方向** `le_normalizer_sup_of_normal` ⭐ sorry-free
  - **Prop 1.15(a)** `hall_higman_solvable_specialization` ⭐ sorry-free thin wrap
  - **`card_comap_eq_card_mul_card_ker`** helper sorry-free
  - **`inf_eq_bot_of_pGroup_coprime`** (Step 1) ⭐ sorry-free
  - **`card_sup_eq_card_mul_card_of_disjoint_normal`** (Step 2) ⭐ sorry-free
  - **`subgroupOf_sup_card_eq_and_pGroup`** (Step 3 part 1) ⭐ sorry-free
  - **`subgroupOf_sup_eq_of_pGroup_le_of_card_eq`** (Step 3 part 2 一般版) ⭐ sorry-free
  - **`subgroupOf_sup_eq_of_pGroup_le_of_coprime`** (Step 3 part 2 corollary) ⭐ sorry-free
- Lem 1.14 hard direction proof (~115 LOC inline): TSyl + T_xSyl 構築 + `MulAction.exists_smul_eq`
  (Sylow II in ↥(T ⊔ M)) + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` + `inf_of_le_left`
  で `MulAut.conj y.val • T = T_x` を G で取得 + `mem_sup_of_normal_left` で `y.val = m·t'` 分解
  + `t' ∈ T` で `t' · T · t'⁻¹ = T` + `m⁻¹·x ∈ N_G(T)` で集約.
- Phase 1 完成度: Ch.1 ✅ / Ch.3 ✅ (Hall + Hall-Higman 3.21) / Ch.4 §4D 進行中 / Ch.7 §7A/§7C 着手 / Ch.5/6 進行中.
-/

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01
open Pointwise

/-! ## §1A: Solvable group basics (Lem 1.1, Prop 1.2-1.4) -/

/-- **BG Lemma 1.1**: 有限可解群 `G` の minimal normal `M` は
elementary abelian で `F(G)` の中心に入る.

CLAUDE.md no-wrapper policy 例外: 異なる Ch.3 結果 + nilpotent_normal_le_fitting の合成
+ Ch.4 の `le_centralizer_of_isMinimalNormal` + 仮定特殊化 (`[IsSolvable G]`). -/
theorem isMinimalNormal_le_fitting_and_isElementaryAbelian
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {M : Subgroup G} (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    M ≤ OddOrder.Isaacs.Ch01.fitting G ∧
    M ≤ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) ∧
    ∃ p : ℕ, p.Prime ∧ M.IsElementaryAbelian p := by
  haveI hMnormal : M.Normal := hMin.1
  -- Elementary abelian (Ch.3)
  obtain ⟨p, hp_prime, hM_elem⟩ :=
    OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hMin
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- ↥M is p-group (every x ∈ M satisfies x^p = 1)
  haveI hM_pgroup : IsPGroup p ↥M :=
    fun x => ⟨1, by rw [pow_one]; exact hM_elem.pow_eq_one x⟩
  -- ↥M nilpotent (finite p-group ⇒ nilpotent)
  haveI hM_nilp : Group.IsNilpotent ↥M := hM_pgroup.isNilpotent
  -- M ⊴ G + ↥M nilpotent ⇒ M ≤ F(G)
  have hM_le_fitting : M ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  have hM_le_centralizer :
      M ≤ Subgroup.centralizer
        ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) :=
    OddOrder.Isaacs.Ch04.le_centralizer_of_isMinimalNormal hMin hM_le_fitting
  exact ⟨hM_le_fitting, hM_le_centralizer, p, hp_prime, hM_elem⟩

/-- Minimal `G`-normal subgroup inside `C` but not inside `F`.

This is a finite-lattice helper for BG Prop. 1.3.  It is intentionally local to §1A:
the full chief-factor series API needed for Prop. 1.2 will live in a shared module. -/
private theorem exists_minimal_normal_le_not_le
    {G : Type*} [Group G] [Finite G] {C F : Subgroup G} [C.Normal]
    (hC_not_le_F : ¬ C ≤ F) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ C ∧ ¬ K ≤ F ∧
      ∀ K' : Subgroup G, K'.Normal → K' ≤ K → ¬ K' ≤ F → K ≤ K' := by
  classical
  let S : Set (Subgroup G) := {K | K.Normal ∧ K ≤ C ∧ ¬ K ≤ F}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := ⟨C, inferInstance, le_rfl, hC_not_le_F⟩
  obtain ⟨K, hK_min⟩ := hS_fin.exists_minimal hS_nonempty
  obtain ⟨⟨hK_normal, hK_le_C, hK_not_le_F⟩, hK_minimal⟩ := hK_min
  refine ⟨K, hK_normal, hK_le_C, hK_not_le_F, ?_⟩
  intro K' hK'_normal hK'_le hK'_not_le_F
  have hK'_mem : K' ∈ S := ⟨hK'_normal, hK'_le.trans hK_le_C, hK'_not_le_F⟩
  exact hK_minimal hK'_mem hK'_le

/-- If `K ≤ C_G(F)`, then `K ∩ F` is central in `K`. -/
private theorem inf_subgroupOf_le_center_of_le_centralizer
    {G : Type*} [Group G] {K F : Subgroup G}
    (hK_le_C : K ≤ Subgroup.centralizer (F : Set G)) :
    (K ⊓ F).subgroupOf K ≤ Subgroup.center K := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx_inf : (x : G) ∈ K ⊓ F := hx
  have hxF : (x : G) ∈ F := hx_inf.2
  have hyC : (y : G) ∈ Subgroup.centralizer (F : Set G) := hK_le_C y.2
  exact (Subgroup.mem_centralizer_iff.mp hyC (x : G) hxF).symm

/-- **BG Proposition 1.3** (P. Hall): for a finite solvable group, the Fitting subgroup
self-centralizes: `C_G(F(G)) ≤ F(G)`.

This proof avoids the still-missing chief-factor intersection API of Prop. 1.2.  If
`C_G(F(G))` had a normal subgroup `K` minimal among those not contained in `F(G)`, then
`[K,K] < K` by solvability and minimality forces `[K,K] ≤ F(G)`.  Since `K ≤ C_G(F(G))`,
`K ∩ F(G)` is central in `K`, and `K/(K ∩ F(G))` is abelian; hence `K` is nilpotent,
contradicting maximality of `F(G)`. -/
theorem centralizer_fitting_le_fitting
    {G : Type*} [Group G] [Finite G] [IsSolvable G] :
    Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) ≤
      OddOrder.Isaacs.Ch01.fitting G := by
  classical
  set F : Subgroup G := OddOrder.Isaacs.Ch01.fitting G with hF_def
  set C : Subgroup G := Subgroup.centralizer (F : Set G) with hC_def
  haveI hF_normal : F.Normal := by
    dsimp [F]
    infer_instance
  haveI hC_normal : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer
  by_contra hC_not_le_F
  obtain ⟨K, hK_normal, hK_le_C, hK_not_le_F, hK_min⟩ :=
    exists_minimal_normal_le_not_le (C := C) (F := F) hC_not_le_F
  haveI hK_normal_inst : K.Normal := hK_normal
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hK_not_le_F
    rw [hK_bot]
    exact bot_le
  have hcomm_lt : ⁅K, K⁆ < K := IsSolvable.commutator_lt_of_ne_bot hK_ne_bot
  have hcomm_le_F : ⁅K, K⁆ ≤ F := by
    by_contra hcomm_not_le_F
    have hK_le_comm : K ≤ ⁅K, K⁆ :=
      hK_min ⁅K, K⁆ inferInstance (Subgroup.commutator_le_left K K) hcomm_not_le_F
    exact hcomm_lt.not_ge hK_le_comm
  let N : Subgroup K := (K ⊓ F).subgroupOf K
  haveI hN_normal : N.Normal := by
    dsimp [N]
    infer_instance
  have hN_le_center : N ≤ Subgroup.center K := by
    dsimp [N]
    exact inf_subgroupOf_le_center_of_le_centralizer hK_le_C
  have hcomm_K_le_N : commutator K ≤ N := by
    intro x hx
    have hx_map : (x : G) ∈ (commutator K).map K.subtype := ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hx_map
    exact ⟨x.2, hcomm_le_F hx_map⟩
  have hquot_mul_comm : ∀ x y : K ⧸ N, x * y = y * x :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_K_le_N).comm
  haveI hquot_nilpotent : Group.IsNilpotent (K ⧸ N) := by
    rw [nilpotent_iff_lowerCentralSeries]
    refine ⟨1, ?_⟩
    rw [lowerCentralSeries_one, commutator_eq_bot_iff_center_eq_top, eq_top_iff]
    intro q _
    rw [Subgroup.mem_center_iff]
    intro r
    exact hquot_mul_comm r q
  have hker_le_center : (QuotientGroup.mk' N).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact hN_le_center
  haveI hK_nilpotent : Group.IsNilpotent K :=
    isNilpotent_of_ker_le_center (QuotientGroup.mk' N) hker_le_center
  have hK_le_fitting : K ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  apply hK_not_le_F
  simpa [F, hF_def] using hK_le_fitting

/-- A chief factor `U/V` is a minimal normal subgroup of `G/V`. -/
private theorem isMinimalNormal_map_quotient_of_isChiefFactor
    {G : Type*} [Group G] {U V : Subgroup G} [V.Normal]
    (hChief : OddOrder.GroupTheory.IsChiefFactor U V) :
    OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) := by
  refine ⟨hChief.normal_top.map _ QuotientGroup.mk_surjective, ?_, ?_⟩
  · intro hbot
    have hU_le_V : U ≤ V := by
      intro u hu
      have hu_map : (QuotientGroup.mk' V) u ∈ U.map (QuotientGroup.mk' V) :=
        ⟨u, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hu_map
      exact hu_map
    exact hChief.lt.not_ge hU_le_V
  · intro N hN_normal hN_le_Ubar
    let W : Subgroup G := N.comap (QuotientGroup.mk' V)
    haveI hW_normal : W.Normal := hN_normal.comap _
    have hV_le_W : V ≤ W := by
      intro v hv
      change (QuotientGroup.mk' V) v ∈ N
      rw [show (QuotientGroup.mk' V) v = 1 from (QuotientGroup.eq_one_iff v).mpr hv]
      exact N.one_mem
    have hW_le_U : W ≤ U := by
      intro g hg
      have hqg_Ubar : (QuotientGroup.mk' V) g ∈ U.map (QuotientGroup.mk' V) :=
        hN_le_Ubar hg
      obtain ⟨u, hu, hqu⟩ := hqg_Ubar
      have hg_u_inv : g * u⁻¹ ∈ V := by
        apply (QuotientGroup.eq_one_iff (N := V) (g * u⁻¹)).mp
        change (QuotientGroup.mk' V) (g * u⁻¹) = 1
        rw [map_mul, map_inv, ← hqu, mul_inv_cancel]
      have hgU : (g * u⁻¹) * u ∈ U := U.mul_mem (hChief.le hg_u_inv) hu
      simpa [mul_assoc] using hgU
    rcases hChief.eq_or_eq_of_normal hW_normal hV_le_W hW_le_U with hW_eq_V | hW_eq_U
    · left
      rw [eq_bot_iff]
      intro n hn
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := V) n
      have hgW : g ∈ W := hn
      rw [hW_eq_V] at hgW
      exact (QuotientGroup.eq_one_iff g).mpr hgW
    · right
      apply le_antisymm hN_le_Ubar
      intro x hx
      obtain ⟨g, hgU, rfl⟩ := hx
      have hgW : g ∈ W := by
        rw [hW_eq_U]
        exact hgU
      exact hgW

/-- Nilpotence is inherited by a subgroup image. -/
private theorem isNilpotent_subgroup_map
    {G H : Type*} [Group G] [Group H] (K : Subgroup G) [Group.IsNilpotent K]
    (f : G →* H) :
    Group.IsNilpotent (K.map f) := by
  let φ : K →* K.map f :=
    { toFun := fun k => ⟨f k.1, ⟨k.1, k.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.1 y.1) }
  exact nilpotent_of_surjective φ (by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)

/-- **BG Proposition 1.2, first inclusion**:
`F(G*)` centralizes every chief factor `U/V` of `G`.

This is the forward half of Hall's chief-factor characterization of the Fitting subgroup.
The reverse inclusion still needs chief-series induction over normal intervals. -/
theorem fitting_map_subtype_le_chiefFactorCentralizer
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {Gstar U V : Subgroup G} [Gstar.Normal] [V.Normal]
    (hChief : OddOrder.GroupTheory.IsChiefFactor U V) :
    (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype ≤
      OddOrder.GroupTheory.chiefFactorCentralizer U V := by
  haveI hV_normal : V.Normal := hChief.normal_bot
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let Ubar : Subgroup (G ⧸ V) := U.map q
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal Ubar := by
    dsimp [Ubar, q]
    exact isMinimalNormal_map_quotient_of_isChiefFactor hChief
  have hUbar_le_cent :
      Ubar ≤ Subgroup.centralizer
        ((OddOrder.Isaacs.Ch01.fitting (G ⧸ V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
    (isMinimalNormal_le_fitting_and_isElementaryAbelian (G := G ⧸ V) hMin).2.1
  have hFquot_le_cent_Ubar :
      OddOrder.Isaacs.Ch01.fitting (G ⧸ V) ≤ Subgroup.centralizer (Ubar : Set (G ⧸ V)) :=
    Subgroup.le_centralizer_iff.mp hUbar_le_cent
  let FstarG : Subgroup G := (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype
  haveI hFstarG_normal : FstarG.Normal := by
    dsimp [FstarG]
    infer_instance
  haveI hFstarGq_normal : (FstarG.map q).Normal :=
    hFstarG_normal.map q QuotientGroup.mk_surjective
  haveI hFstarGq_nilpotent : Group.IsNilpotent (FstarG.map q) := by
    have hmap :
        FstarG.map q =
          (OddOrder.Isaacs.Ch01.fitting Gstar).map (q.comp Gstar.subtype) := by
      dsimp [FstarG, q]
      rw [Subgroup.map_map]
    rw [hmap]
    exact isNilpotent_subgroup_map (OddOrder.Isaacs.Ch01.fitting Gstar) (q.comp Gstar.subtype)
  have hFstarGq_le_fitting :
      FstarG.map q ≤ OddOrder.Isaacs.Ch01.fitting (G ⧸ V) :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  have hFstarGq_le_cent_Ubar : FstarG.map q ≤ Subgroup.centralizer (Ubar : Set (G ⧸ V)) :=
    hFstarGq_le_fitting.trans hFquot_le_cent_Ubar
  change FstarG ≤ OddOrder.GroupTheory.chiefFactorCentralizer U V
  exact OddOrder.GroupTheory.chiefFactorCentralizer.le_of_map_le_centralizer
    hFstarGq_le_cent_Ubar

/-!
Prop. 1.2 and 1.4 remain routed through this §1A block.

* Prop. 1.2 now has the basic `OddOrder.GroupTheory.ChiefFactor` vocabulary:
  chief factors `U/V` and ambient `C_G(U/V)`.  The remaining work is the
  composition/chief-series induction over normal intervals.
* Prop. 1.4 should then follow the book route through semidirect products and Prop. 1.3;
  the present file now supplies the required self-centralizing Fitting endpoint.
-/

/-! ## §1B: A-invariant Hall theory (Prop 1.5, Prop 1.6) — Isaacs Ch.4/§3E 既存 API 経由

CLAUDE.md no-wrapper policy 準拠. BG Prop 1.5-1.6 は Isaacs §3E coprime action machinery
で完全カバーされており, 個別 theorem は書かない (mapping は本 docstring に集約).

| BG | Isaacs §3E | Lean (本リポ) | 備考 |
|---|---|---|---|
| Prop 1.5(a)(c) A-inv Hall 存在/共役 | Thm 3.23(a)(b) (Sylow), Lem 3.24 (Glauberman) | `OddOrder.Isaacs.Ch04.exists_aInvariant_sylow`, `aInvariant_sylow_conj`, `glauberman_fixed_point_exists`, `glauberman_fixed_points_conj` | π = {p} 特殊化版が Ch.4 forward に存在; Hall π 一般版は §1B 内 Prop 1.5 完成時 |
| Prop 1.5(b) A-inv π-sub ⊆ A-inv Hall | (Sylow 拡張版) | `OddOrder.Isaacs.Ch04.aInvariant_sylow_containing` | π-sub ⊆ Hall π 一般版は Prop 1.5 完成時 |
| **Prop 1.5(d) C_{G/N}(A) = image C_G(A)** | **Cor 3.28 (商の固定点)** | **`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`** ✅ | §1 hub. 6 §1 proofs で使用. **無 wrapper, 直接呼び** |
| Prop 1.5(e) C_G(A) ⊇ Hall π' ⇒ [G,A] ⊆ O_π | (新規) | (未実装) | Prop 1.5(e) は coprime + commutator structure, Hall API 整備後 |
| Prop 1.6(a) G = C_G(A)[G,A] | Thm 3.27 / Cor 3.28 系 | (未実装) | Prop 1.5(d) を `H = [G,A]` で specialize |
| Prop 1.6(b)(c) [G,A,A]=[G,A], =1 ⇒ trivial | Ch.4 §4C-§4D (lcs + Three-Sub Lemma) 待ち | (未実装) | Ch.4 §4D 完成依存 |
| Prop 1.6(d)(e) abelian 直積分解 | (mathlib `MulAction.fixedPoints` + complement) | (未実装) | abelian 仮定下の direct product, Maschke 風 |

**使用例**: 本ファイル §1C Thm 1.8 (`burnside_operator`) は `aFixed_quotient_frattini`
(= Prop 1.5(d) + Lem 1.7(a) 合成 = Isaacs Cor 3.29) を直接呼び出す.
-/

/-! ## §1C: Frattini + Burnside operator (Lem 1.7-1.10) -/

/-- **BG Lemma 1.7(a)** (Frattini argument, finite specialization):
有限群 `G` で `H ≤ G` かつ `H ⊔ Φ(G) = ⊤` ⇒ `H = ⊤`.

mathlib `frattini_nongenerating` の有限群特殊化. `[Finite G]` から
`Finite (Subgroup G)` → `WellFoundedGT (Subgroup G)` → `IsStronglyCoatomic` →
`IsCoatomic` の instance chain で `frattini_nongenerating` に渡せる.

BG 原 statement は R p-group の文脈だが proof は finite group で成立. -/
theorem eq_top_of_sup_frattini_eq_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h : H ⊔ frattini G = ⊤) : H = ⊤ :=
  frattini_nongenerating h

/-- **BG Lemma 1.7(b)**: For a finite p-group `R`, `R/Φ(R)` is elementary abelian.

The proof lives in the shared `OddOrder.GroupTheory.FrattiniPGroup` module because the same
finite p-group Frattini facts are reused outside BG §1. -/
theorem quotient_frattini_isElementaryAbelian
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) :
    OddOrder.GroupTheory.IsElementaryAbelian p (R ⧸ frattini R) :=
  OddOrder.GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian hR

/-- **BG Lemma 1.7(c) (⇒ direction)**: For a finite p-group `R`,
`Φ(R) = 1` implies that `R` is elementary abelian.

The reverse direction is supplied by `frattini_eq_bot_iff_isElementaryAbelian` below. -/
theorem isElementaryAbelian_of_frattini_eq_bot
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) (hFrat : frattini R = ⊥) :
    OddOrder.GroupTheory.IsElementaryAbelian p R :=
  OddOrder.GroupTheory.IsPGroup.isElementaryAbelian_of_frattini_eq_bot hR hFrat

private theorem quotient_bot_isElementaryAbelian
    {p : ℕ} {R : Type*} [Group R]
    (hR : OddOrder.GroupTheory.IsElementaryAbelian p R) :
    OddOrder.GroupTheory.IsElementaryAbelian p (R ⧸ (⊥ : Subgroup R)) := by
  refine ⟨?_, ?_⟩
  · intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup R) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup R) b
    rw [← map_mul, hR.1 x y, map_mul]
  · intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup R) a
    rw [← map_pow, hR.2 x, map_one]

/-- **BG Lemma 1.7(c)**: For a finite p-group `R`, `Φ(R) = 1` iff `R` is elementary abelian.

Forward direction is the direct Frattini p-group argument. Reverse direction uses Isaacs Lemma 4.5:
`Φ(P) ≤ N ↔ P/N` is elementary abelian, with `N = ⊥`. -/
theorem frattini_eq_bot_iff_isElementaryAbelian
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) :
    frattini R = ⊥ ↔ OddOrder.GroupTheory.IsElementaryAbelian p R := by
  refine ⟨isElementaryAbelian_of_frattini_eq_bot hR, fun hElem => ?_⟩
  have hle : frattini R ≤ (⊥ : Subgroup R) :=
    (OddOrder.Isaacs.Ch04.frattini_le_iff_isElementaryAbelian_quotient_of_pgroup
      (P := R) (p := p) (N := (⊥ : Subgroup R)) hR).2
      (quotient_bot_isElementaryAbelian hElem)
  exact le_antisymm hle bot_le

/-- **BG Lemma 1.7(d) (⊇ direction)**: In a finite p-group `R`, the subgroup generated by
commutators and p-th powers lies in `Φ(R)`.

The reverse inclusion is `frattini_le_commutator_sup_pow_closure` below. -/
theorem commutator_sup_pow_closure_le_frattini
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) :
    commutator R ⊔ Subgroup.closure (Set.range (fun x : R => x ^ p)) ≤ frattini R :=
  OddOrder.GroupTheory.IsPGroup.commutator_sup_pow_closure_le_frattini hR

private theorem pow_closure_characteristic
    {n : ℕ} {R : Type*} [Group R] :
    (Subgroup.closure (Set.range (fun x : R => x ^ n))).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact Subgroup.subset_closure ⟨φ x, by simp [map_pow]⟩

/-- **BG Lemma 1.7(d) (⊆ direction)**: In a finite p-group `R`,
`Φ(R)` lies in the subgroup generated by commutators and p-th powers.

Let `K = R' ⊔ ⟨x^p | x ∈ R⟩`. The p-th-power closure is characteristic, hence normal, so
`K` is normal. Then `R/K` is elementary abelian: commutators and p-th powers vanish in the
quotient. Ch.4 Lemma 4.5 gives `Φ(R) ≤ K`. -/
theorem frattini_le_commutator_sup_pow_closure
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) :
    frattini R ≤ commutator R ⊔ Subgroup.closure (Set.range (fun x : R => x ^ p)) := by
  let Pows : Subgroup R := Subgroup.closure (Set.range (fun x : R => x ^ p))
  let K : Subgroup R := commutator R ⊔ Pows
  haveI hPowsChar : Pows.Characteristic := by
    dsimp [Pows]
    exact pow_closure_characteristic
  haveI hPowsNorm : Pows.Normal := inferInstance
  haveI hKNorm : K.Normal := by
    dsimp [K]
    infer_instance
  have hElem : OddOrder.GroupTheory.IsElementaryAbelian p (R ⧸ K) := by
    refine ⟨?_, ?_⟩
    · have hcomm_le : commutator R ≤ K := by
        dsimp [K]
        exact le_sup_left
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le).comm
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      dsimp [K, Pows]
      exact
        (le_sup_right :
          Subgroup.closure (Set.range (fun x : R => x ^ p)) ≤
            commutator R ⊔ Subgroup.closure (Set.range (fun x : R => x ^ p)))
          (Subgroup.subset_closure ⟨x, rfl⟩)
  have hle : frattini R ≤ K :=
    (OddOrder.Isaacs.Ch04.frattini_le_iff_isElementaryAbelian_quotient_of_pgroup
      (P := R) (p := p) (N := K) hR).2 hElem
  simpa [K, Pows] using hle

/-- **BG Lemma 1.7(d)**: For a finite p-group `R`,
`Φ(R) = ⟨R', x^p | x ∈ R⟩`. -/
theorem commutator_sup_pow_closure_eq_frattini
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) :
    commutator R ⊔ Subgroup.closure (Set.range (fun x : R => x ^ p)) = frattini R :=
  le_antisymm (commutator_sup_pow_closure_le_frattini hR)
    (frattini_le_commutator_sup_pow_closure hR)

/-- **BG Theorem 1.8 (Burnside, operator on p-group)**: `A` を operator group とし,
`R` を p-群とする. `(|A|, |R|) = 1` かつ `A` が `R/Φ(R)` に自明に作用するとき,
`A` は `R` に自明に作用する.

**証明**: `R` p-群 + `[Finite R]` + `[Fact p.Prime]` ⇒ `IsNilpotent R` (`IsPGroup.isNilpotent`)
⇒ `IsSolvable R` (`IsNilpotent.to_isSolvable` instance). よって Isaacs Cor 3.29
(`OddOrder.Isaacs.Ch04.aFixed_quotient_frattini`: Prop 1.5(d) + Lem 1.7(a) 合成形) を
`G ↦ R`, `Or.inr` で適用するだけ.

**Isaacs 対応**: Isaacs FGT Thm 1.8 (完全一致). Phase 1 Ch.1 §1B 側の Thm 1.8 は未実装
だが, 本実装は Ch.4 forward §3E coprime action machinery 経由で独立に成立.

**no-wrapper policy 例外**: 仮定特殊化 (p-群仮定から solvable を導出して
`aFixed_quotient_frattini` の `IsSolvable A ∨ IsSolvable G` 引数を埋める). -/
theorem burnside_operator {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {A : Type*} [Group A] [Finite A]
    (hP : IsPGroup p R) {φ : A →* MulAut R}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card R))
    (h_triv_quot : ∀ a : A, ∀ r : R, ∃ x ∈ _root_.frattini R, (φ a) r = r * x) :
    ∀ a : A, ∀ r : R, (φ a) r = r := by
  haveI : Group.IsNilpotent R := hP.isNilpotent
  exact OddOrder.Isaacs.Ch04.aFixed_quotient_frattini hCop (Or.inr inferInstance) h_triv_quot

/-- **BG Lemma 1.9 (2-step instance, ambient G 形)**: 有限群 `G`, `A` coprime operator,
`N ⊴ G` が `A`-不変. `A` が `N` 上に自明 + `A` が `G/N` 上に自明 ⇒ `A` が `G` 上に自明.

**BG 原 statement との関係**: BG Lem 1.9 は「A が G の normal series を stabilize するとき
A/C_A(G) is π-group (G π-group)」と多段で述べるが, 証明は §1 内の各 induction step で
本 2-step の繰り返し適用. 本実装は §1 で使用される **2-step instance に絞った形** で,
多段版は本 2-step を normal series の長さで induct すれば得られる.

**証明**: 任意の `g : G` に対し Isaacs Cor 3.28 (`coprime_fixedPoints_quotient`) で
`∃ c ∈ C_G(A), c·N = g·N` を取り, `g = c · n⁻¹` (`n ∈ N`) と書く. すると
`φ a g = φ a c · φ a n⁻¹ = c · n⁻¹ = g` (`c ∈ C_G(A)` で `A`-fix, `n ∈ N` で `h_triv_N`).

**Isaacs 対応**: 直接対応無し (Ch.3 §3E coprime action machinery の application).
**no-wrapper policy 例外**: 2-step extension lemma, §1 内 Prop 1.10 等で再利用. -/
theorem coprime_actsTrivially_of_normal_and_quotient
    {G : Type*} [Group G] [Finite G]
    {A : Type*} [Group A] [Finite A]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal]
    (hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    (h_triv_N : ∀ a : A, ∀ n ∈ N, (φ a) n = n)
    (h_triv_quot : ∀ a : A, ∀ g : G, ∃ x ∈ N, (φ a) g = g * x) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  intro a g
  obtain ⟨c, hc_fix, hc_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hCop hSolv hN_inv
      (fun a' => h_triv_quot a' g)
  obtain ⟨n, hn_in, hc_eq⟩ := hc_coset
  have hg_eq : g = c * n⁻¹ := by rw [hc_eq]; group
  rw [hg_eq, map_mul, hc_fix a, map_inv, h_triv_N a n hn_in]

/-! ## §1D: 未実装 (Phase 1 Ch.4 §4D 待ち) -/

/-! ## §1E: Sylow lift + Hall-Higman + noncyclic auto -/

/-! ### Lem 1.14 helpers (Step 1-3 sorry-free, main statement 下方) -/

/-- **Helper for Lem 1.14**: T p-group + M p'-group ⇒ `T ⊓ M = ⊥`.

`T ⊓ M` は T の subgroup として p-group (`hT.of_injective Subgroup.inclusion`) かつ
|T ⊓ M| ∣ |M|. |M| が p と coprime ⇒ p^k ∣ |M| ⇒ k = 0 ⇒ |T ⊓ M| = 1 ⇒ T ⊓ M = ⊥. -/
theorem inf_eq_bot_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} (hM_p' : (Nat.card M).Coprime p) :
    T ⊓ M = ⊥ := by
  have hTM_le_T : T ⊓ M ≤ T := inf_le_left
  have hTM_le_M : T ⊓ M ≤ M := inf_le_right
  have hTM_pgroup : IsPGroup p (T ⊓ M : Subgroup G) :=
    hT.of_injective (Subgroup.inclusion hTM_le_T) (Subgroup.inclusion_injective hTM_le_T)
  have hcard_dvd : Nat.card (T ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hTM_le_M
  obtain ⟨k, hk⟩ := hTM_pgroup.exists_card_eq
  rw [hk] at hcard_dvd
  -- p^k ∣ |M| and (|M|, p) = 1 ⇒ p^k = 1
  have hcop_pow : ((p ^ k).Coprime (Nat.card M)) := (hM_p'.symm).pow_left k
  have hpow_eq_one : p ^ k = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_pow dvd_rfl hcard_dvd
  rw [hpow_eq_one] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

/-- **Helper for Lem 1.14** (Step 2, cardinality): `T ⊓ M = ⊥` + `M ⊴ G` ⇒
`|T ⊔ M| = |T| · |M|`. mathlib 第二同型 `quotientInfEquivProdNormalQuotient` +
`subgroupOfEquivOfLe` + `card_eq_card_quotient_mul_card_subgroup`. -/
theorem card_sup_eq_card_mul_card_of_disjoint_normal
    {G : Type*} [Group G] [Finite G]
    {T M : Subgroup G} [M.Normal] (h_disj : T ⊓ M = ⊥) :
    Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M := by
  -- Step A: M.subgroupOf T = ⊥ (from T ⊓ M = ⊥)
  have hMT_bot : M.subgroupOf T = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxM hxT
    have hx_inf : x ∈ T ⊓ M := Subgroup.mem_inf.mpr ⟨hxT, hxM⟩
    rwa [h_disj, Subgroup.mem_bot] at hx_inf
  -- |M.subgroupOf T| = 1
  have hMT_card_one : Nat.card (M.subgroupOf T) = 1 := by
    rw [hMT_bot]; exact Subgroup.card_bot
  -- |T| = |T ⧸ M.subgroupOf T| * |M.subgroupOf T| = |T ⧸ M.subgroupOf T|
  have hT_quot_card : Nat.card T = Nat.card (T ⧸ M.subgroupOf T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf T)
    rw [hMT_card_one, mul_one] at this
    exact this
  -- Second iso theorem: T ⧸ M.subgroupOf T ≃* (T ⊔ M) ⧸ M.subgroupOf (T ⊔ M)
  have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient T M
  have h_eq_TM : Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) = Nat.card T := by
    rw [hT_quot_card]
    exact (Nat.card_congr h_iso.toEquiv).symm
  -- |M.subgroupOf (T ⊔ M)| = |M|
  have hM_sub_TM_card : Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : M ≤ T ⊔ M)).toEquiv
  -- |T ⊔ M| = |quotient| · |M.subgroupOf (T ⊔ M)| = |T| · |M|
  have h_card : Nat.card ↥(T ⊔ M : Subgroup G) =
      Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) *
      Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h_card, h_eq_TM, hM_sub_TM_card]

/-- **Helper for Lem 1.14** (Step 3 part 1): `T.subgroupOf (T ⊔ M)` is a p-group with
cardinality `|T|`. uses `Subgroup.subgroupOfEquivOfLe` (T ≤ T ⊔ M ⇒ T.subgroupOf (T⊔M) ≃* T). -/
theorem subgroupOf_sup_card_eq_and_pGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T) (M : Subgroup G) :
    Nat.card (T.subgroupOf (T ⊔ M)) = Nat.card T ∧
      IsPGroup p (T.subgroupOf (T ⊔ M : Subgroup G)) := by
  refine ⟨?_, ?_⟩
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toEquiv
  · exact hT.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).injective

/-- **Helper for Lem 1.14** (Step 3 part 2 一般版, Sylow 性): 任意の `S ≤ T ⊔ M` で
`|S| = |T|` ⇒ `S.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p (Q ≥ S.subgroupOf + Q p-group
⇒ Q = S.subgroupOf).

`S = T` の場合 `subgroupOf_sup_eq_of_pGroup_le_of_coprime` (corollary 下記),
`S = xTx⁻¹` (T_x) の場合 Lem 1.14 main proof 内の T_xSyl 構築で使用.

証明: |Q| = p^j ∣ |T ⊔ M| = |T| · |M| with (|M|, p) = 1 ⇒ p^j ∣ p^k = |T|.
`S.subgroupOf ≤ Q` + `|S.subgroupOf| = |S| = |T| = p^k` ⇒ k ≤ j. 両方合わせて j = k,
|Q| = |S.subgroupOf|. `Subgroup.eq_of_le_of_card_ge` で等号. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_card_eq
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {S : Subgroup G} (hS_le : S ≤ T ⊔ M) (hS_card : Nat.card S = Nat.card T)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hS_sub_Q : S.subgroupOf (T ⊔ M) ≤ Q) :
    Q = S.subgroupOf (T ⊔ M) := by
  have hS_sub_card : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le).toEquiv, hS_card]
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  obtain ⟨j, hj⟩ := hQ_pgroup.exists_card_eq
  have hQ_dvd : Nat.card Q ∣ Nat.card ↥(T ⊔ M : Subgroup G) :=
    Subgroup.card_subgroup_dvd_card Q
  rw [h_card_sup, hk, hj] at hQ_dvd
  have hp_cop : (p ^ j).Coprime (Nat.card M) := (hM_p'.symm).pow_left j
  have hpj_dvd_pk : p ^ j ∣ p ^ k := Nat.Coprime.dvd_of_dvd_mul_right hp_cop hQ_dvd
  have hcard_le : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) ≤ Nat.card Q :=
    Subgroup.card_le_of_le hS_sub_Q
  rw [hS_sub_card, hk, hj] at hcard_le
  have hk_le_j : k ≤ j := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard_le
  have hj_le_k : j ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hpj_dvd_pk
  have hjk : j = k := le_antisymm hj_le_k hk_le_j
  symm
  apply Subgroup.eq_of_le_of_card_ge hS_sub_Q
  rw [hS_sub_card, hk, hj, hjk]

/-- **Helper for Lem 1.14** (Step 3 part 2, Sylow 性, S = T 特殊化):
T p-group + M ⊴ G p'-subgroup ⇒ `T.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p.
一般版 `subgroupOf_sup_eq_of_pGroup_le_of_card_eq` (S = T の場合) の corollary. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hT_sub_Q : T.subgroupOf (T ⊔ M) ≤ Q) :
    Q = T.subgroupOf (T ⊔ M) :=
  subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' le_sup_left rfl hQ_pgroup hT_sub_Q

/-- **BG Lemma 1.14 (易 direction, sorry-free)**: `N_G(T)·M ≤ N_G(T·M)`.

- `T.normalizer ≤ (T ⊔ M).normalizer`: x normalizes T ⇒ x normalizes M (M ⊴ G) ⇒ x
  normalizes T ⊔ M.
- `M ≤ (T ⊔ M).normalizer`: M ≤ T ⊔ M and subgroup self-normalizes via inner conjugation. -/
theorem le_normalizer_sup_of_normal
    {G : Type*} [Group G] (T : Subgroup G) (M : Subgroup G) [M.Normal] :
    Subgroup.normalizer T ⊔ M ≤ Subgroup.normalizer (T ⊔ M : Subgroup G) :=
  sup_le Subgroup.normalizer_le_normalizer_sup_normal
    (le_sup_right.trans Subgroup.le_normalizer)

/-- **BG Lemma 1.14 (heart, normalizer-in-G form)**: `T` p-subgroup of `G`, `M ⊴ G` p'-subgroup
(`gcd(|M|, p) = 1` を採用) ⇒ `N_G(T·M) = N_G(T)·M`.

In quotient form: with `f = QuotientGroup.mk' M`,
- `(N_{G/M}(T·M/M)).comap f = N_G(T·M)` (mathlib `comap_normalizer_eq_of_surjective`)
- `N_G(T·M) = N_G(T)·M` (this lemma)

**Proof** (BG p.5, 主要部 = hard direction):
- 易: `M ≤ T·M ≤ N_G(T·M)` (subgroup self-normalization) + `N_G(T) ≤ N_G(T·M)` (M normal
  ⇒ conjugation fixes M, T conjugation fixes T, so T·M fixed).
- 難: `x ∈ N_G(T·M)` ⇒ `xTx⁻¹ ⊆ T·M`. `T ∩ M = ⊥` (coprime orders) ⇒ `|T·M| = |T|·|M|`,
  `|T|` は `|T·M|` の p-part ⇒ `T` Sylow `p` of `T·M`. 同様に `xTx⁻¹` Sylow `p` of `T·M`.
  Sylow II in T·M: `∃ y ∈ T·M, xTx⁻¹ = yTy⁻¹`. `y = m·t` (`m ∈ M`, `t ∈ T`, possible
  since `M·T = T·M` for M normal) ⇒ `xTx⁻¹ = m·T·m⁻¹` ⇒ `m⁻¹x ∈ N_G(T)` ⇒
  `x ∈ M·N_G(T) = N_G(T)·M`.

**実装状態**: ⭐ **sorry-free 完成** (2026-05-24). TSyl + T_xSyl 構築 + Sylow II
(`MulAction.exists_smul_eq`) + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` で
`MulAut.conj y.val • T = T_x` を G で取得. `mem_sup_of_normal_left` で `y.val = m·t'`
分解 + `t' ∈ T ⇒ t'·T·t'⁻¹ = T` + `m⁻¹·x ∈ N_G(T)` で集約. ~115 LOC inline. -/
theorem normalizer_sup_eq_normalizer_sup_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p) :
    Subgroup.normalizer (T ⊔ M : Subgroup G) = Subgroup.normalizer T ⊔ M := by
  apply le_antisymm _ (le_normalizer_sup_of_normal T M)
  intro x hx
  -- === Step 0: setup ===
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  have hT_le_TM : T ≤ (T ⊔ M : Subgroup G) := le_sup_left
  have hM_le_TM : M ≤ (T ⊔ M : Subgroup G) := le_sup_right
  have hx_norm : ∀ s, s ∈ (T ⊔ M : Subgroup G) ↔ x * s * x⁻¹ ∈ T ⊔ M :=
    Subgroup.mem_normalizer_iff.mp hx
  -- === Step 1: TSyl construction ===
  let TSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T.subgroupOf (T ⊔ M),
     (subgroupOf_sup_card_eq_and_pGroup hT M).2,
     fun {Q} hQ hle => subgroupOf_sup_eq_of_pGroup_le_of_coprime hT hM_p' hQ hle⟩
  -- === Step 2: T_x = x · T · x⁻¹ properties ===
  let T_x : Subgroup G := T.map (MulAut.conj x).toMonoidHom
  have hT_x_pg : IsPGroup p T_x :=
    hT.of_equiv (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective)
  have hT_x_card : Nat.card T_x = Nat.card T :=
    (Nat.card_congr (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective).toEquiv).symm
  have hT_x_le : T_x ≤ (T ⊔ M : Subgroup G) := by
    rintro a ⟨t, ht, hta⟩
    rw [← hta]
    change x * t * x⁻¹ ∈ T ⊔ M
    exact (hx_norm t).mp (hT_le_TM ht)
  have hT_x_sub_pg : IsPGroup p (T_x.subgroupOf (T ⊔ M : Subgroup G)) :=
    hT_x_pg.of_injective (Subgroup.subgroupOfEquivOfLe hT_x_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT_x_le).injective
  have hT_x_sub_card : Nat.card (T_x.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_x_le).toEquiv, hT_x_card]
  -- === Step 3: T_xSyl construction (一般 helper 使用) ===
  let T_xSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T_x.subgroupOf (T ⊔ M),
     hT_x_sub_pg,
     fun {Q} hQ_pg hT_x_sub_Q =>
       subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' hT_x_le hT_x_card hQ_pg hT_x_sub_Q⟩
  -- === Step 4: Sylow II — ∃ y : ↥(T ⊔ M), y • TSyl = T_xSyl ===
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥(T ⊔ M : Subgroup G)) TSyl T_xSyl
  -- === Step 5: extract y.val · T · y.val⁻¹ = T_x as subgroups of G ===
  have hy_carrier : (y • TSyl).toSubgroup = T_xSyl.toSubgroup := congrArg Sylow.toSubgroup hy
  have h_conj_T_eq_Tx : MulAut.conj (y : G) • T = T_x := by
    have h1 : (y • TSyl).toSubgroup = MulAut.conj y • T.subgroupOf (T ⊔ M) := rfl
    have h2 : T_xSyl.toSubgroup = T_x.subgroupOf (T ⊔ M : Subgroup G) := rfl
    have h3 : MulAut.conj y • T.subgroupOf (T ⊔ M : Subgroup G) =
        (MulAut.conj (y : G) • T).subgroupOf (T ⊔ M : Subgroup G) :=
      Subgroup.conj_smul_subgroupOf hT_le_TM y
    rw [h1, h2, h3] at hy_carrier
    -- hy_carrier : (MulAut.conj y.val • T).subgroupOf (T ⊔ M) = T_x.subgroupOf (T ⊔ M)
    have h_smul_T_le : MulAut.conj (y : G) • T ≤ (T ⊔ M : Subgroup G) := by
      rintro - ⟨t, ht, rfl⟩
      change (y : G) * t * (y : G)⁻¹ ∈ T ⊔ M
      exact (T ⊔ M).mul_mem ((T ⊔ M).mul_mem y.2 (hT_le_TM ht)) ((T ⊔ M).inv_mem y.2)
    rw [Subgroup.subgroupOf_inj] at hy_carrier
    rwa [inf_of_le_left h_smul_T_le, inf_of_le_left hT_x_le] at hy_carrier
  -- === Step 6: decompose y.val = m · t' (m ∈ M, t' ∈ T) ===
  have hy_in_MT : (y : G) ∈ (M ⊔ T : Subgroup G) := by
    rw [sup_comm]; exact y.2
  obtain ⟨m, hm_M, t', ht'_T, hmt⟩ := Subgroup.mem_sup_of_normal_left.mp hy_in_MT
  -- hmt : m * t' = y.val
  -- === Step 7: m · T · m⁻¹ = T_x (since t' normalizes T) ===
  have h_t'_norm_T : MulAut.conj t' • T = T := by
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      change t' * u * t'⁻¹ ∈ T
      exact T.mul_mem (T.mul_mem ht'_T hu) (T.inv_mem ht'_T)
    · intro hs
      refine ⟨t'⁻¹ * s * t', T.mul_mem (T.mul_mem (T.inv_mem ht'_T) hs) ht'_T, ?_⟩
      change t' * (t'⁻¹ * s * t') * t'⁻¹ = s
      group
  have h_conj_y_eq_conj_m : MulAut.conj (y : G) • T = MulAut.conj m • T := by
    rw [← hmt, map_mul, mul_smul, h_t'_norm_T]
  have h_mT_eq_Tx : MulAut.conj m • T = T_x := h_conj_y_eq_conj_m.symm.trans h_conj_T_eq_Tx
  -- === Step 8: m⁻¹ * x ∈ N_G(T) ===
  have h_mx_in_NT : m⁻¹ * x ∈ Subgroup.normalizer T := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨?_, ?_⟩
    · -- Forward: t ∈ T ⇒ (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T
      intro ht
      -- x·t·x⁻¹ ∈ T_x (definition unfolding)
      have hxtx_in_Tx : x * t * x⁻¹ ∈ T_x := ⟨t, ht, by simp [MulAut.conj_apply]⟩
      rw [← h_mT_eq_Tx] at hxtx_in_Tx
      -- Get s ∈ T with m * s * m⁻¹ = x * t * x⁻¹
      obtain ⟨s, hs, hms⟩ := hxtx_in_Tx
      have hms_eq : m * s * m⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply m s]; exact hms
      -- (m⁻¹x) · t · (m⁻¹x)⁻¹ = m⁻¹ · (x*t*x⁻¹) · m = m⁻¹ · (m*s*m⁻¹) · m = s
      have h_eq : m⁻¹ * x * t * (m⁻¹ * x)⁻¹ = s := by
        have step : m⁻¹ * (x * t * x⁻¹) * m = s := by rw [← hms_eq]; group
        calc m⁻¹ * x * t * (m⁻¹ * x)⁻¹
            = m⁻¹ * (x * t * x⁻¹) * m := by group
          _ = s := step
      rw [h_eq]; exact hs
    · -- Reverse: (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T ⇒ t ∈ T
      intro hut
      set u := m⁻¹ * x * t * (m⁻¹ * x)⁻¹ with hu_def
      -- u ∈ T, and m·u·m⁻¹ = x·t·x⁻¹
      have hmum_eq_xtx : m * u * m⁻¹ = x * t * x⁻¹ := by rw [hu_def]; group
      -- m·u·m⁻¹ ∈ MulAut.conj m • T = T_x
      have hmum_in_mT : m * u * m⁻¹ ∈ MulAut.conj m • T :=
        ⟨u, hut, by simp [MulAut.conj_apply]⟩
      rw [h_mT_eq_Tx, hmum_eq_xtx] at hmum_in_mT
      -- hmum_in_mT : x * t * x⁻¹ ∈ T_x
      obtain ⟨s, hs, hxs⟩ := hmum_in_mT
      have hxs_eq : x * s * x⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply x s]; exact hxs
      have h_st : s = t := mul_left_cancel (mul_right_cancel hxs_eq)
      rw [← h_st]; exact hs
  -- === Step 9: x = m · (m⁻¹ * x) ∈ M · N_G(T) ⊆ N_G(T) ⊔ M ===
  have h_x_eq : x = m * (m⁻¹ * x) := by group
  rw [h_x_eq]
  have h_in_M_NT : m * (m⁻¹ * x) ∈ (M : Subgroup G) ⊔ Subgroup.normalizer T :=
    Subgroup.mul_mem_sup hm_M h_mx_in_NT
  rwa [sup_comm] at h_in_M_NT

/-- **BG Proposition 1.15(a) (P. Hall & G. Higman "Lemma 1.2.3", thin wrap)**: `G` 有限可解 +
`O_{p'}(G) = ⊥` ⇒ `C_G(O_p(G)) ⊆ O_p(G)`.

**形式化**: Phase 1 `OddOrder.Isaacs.Ch03.hall_higman_1_2_3` の π = {p} 特殊化.
Ch.3 §3D の Hall-Higman は `[IsPiSeparable π G]` 版で, ここでは `[IsSolvable G]`
から `isPiSeparable_of_solvable` instance を使って適用する.

**BG 原 statement (`T` Sylow p of `O_{p',p}(G)` ⇒ `C_G(T) ⊆ O_{p',p}(G)`) との関係**:
G を G/O_{p'}(G) に置き換えると `T` は `O_p(G/O_{p'}(G))` に一致 (Sylow p of p-group は
全体). この特殊形が下の statement.

CLAUDE.md no-wrapper policy 例外 (仮定特殊化: `IsSolvable G` instance + π = {p}
specialization). -/
theorem hall_higman_solvable_specialization
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
  OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hp'

/-! ## §1F: Focal + Burnside + Maschke (Thm 1.17-1.20) — mathlib 直接, no-wrapper

CLAUDE.md no-mathlib-wrapper policy により 4 結果とも個別 theorem は書かない.

- **BG Thm 1.17** (Focal Subgroup): mathlib `Subgroup.commutator_inf_eq_focalSubgroup`.
  Phase 1 wrapper: `OddOrder.Isaacs.Ch05.abelian_sylow_commutator_inf_eq_focal`.
- **BG Thm 1.18** (Burnside p-complement): mathlib `MonoidHom.ker_transferSylow_isComplement'`
  (`Mathlib/GroupTheory/Transfer.lean:275`).
- **BG Cor 1.19(b)** (Z-group ⇒ G' Hall): mathlib `IsZGroup.coprime_commutator_index`
  (`Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:280`).
- **BG Thm 1.20** (Maschke): mathlib `Mathlib/RepresentationTheory/Maschke.lean`. -/

/-! ## §1G: p-length one + p-group normal series (Lem 1.21, Lem 1.22)

- **Lem 1.21** (p-length one の 5 性質): BG-unique def, 別ファイル `PLength.lean` (将来).
- **Lem 1.22** (p-group normal series): 本ファイル下記.

### Lem 1.22 implementation -/

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Helper: for a surjective group hom `f : G →* H`, the cardinality of the preimage of a
subgroup `K ≤ H` equals `|K| * |ker f|`. Used in Lem 1.22 induction step. -/
private lemma card_comap_eq_card_mul_card_ker
    {G' H : Type*} [Group G'] [Group H] [Finite G'] [Finite H]
    (f : G' →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have h1 : (K.comap f).index = K.index := K.index_comap_of_surjective hf
  have h2 : (K.comap f).index * Nat.card (K.comap f) = Nat.card G' :=
    (K.comap f).index_mul_card
  have h3 : K.index * Nat.card K = Nat.card H := K.index_mul_card
  have h4 : Nat.card G' = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    exact congrArg (· * _)
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)
  have hidx_ne : K.index ≠ 0 := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'
  have hstep : K.index * Nat.card (K.comap f) = K.index * (Nat.card K * Nat.card f.ker) := by
    calc K.index * Nat.card (K.comap f)
        = (K.comap f).index * Nat.card (K.comap f) := by rw [h1]
      _ = Nat.card G' := h2
      _ = Nat.card H * Nat.card f.ker := h4
      _ = (K.index * Nat.card K) * Nat.card f.ker := by rw [h3]
      _ = K.index * (Nat.card K * Nat.card f.ker) := mul_assoc _ _ _
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx_ne) hstep

/-- **BG Lemma 1.22**: in a finite `p`-group `G`, every normal subgroup `N` contains, for each
`r` with `p^r ∣ |N|`, a normal subgroup of `G` of order `p^r`.

**Proof** (BG p.8): induction on `r`.
- Base `r = 0`: `L = ⊥`.
- Step `r → r+1`: by IH get `L₀ ⊴ G`, `L₀ ≤ N`, `|L₀| = p^r`. Work in quotient
  `G ⧸ L₀` (which is `p`-group by `IsPGroup.to_quotient`). The image `N' = N.map (mk' L₀)`
  is normal, nontrivial since `p ∣ |N'| = |N|/p^r` (by `card_comap_eq_card_mul_card_ker`).
  By Phase 1 `IsPGroup.normal_inf_center_nontrivial`, `N' ⊓ Z(G ⧸ L₀)` is nontrivial. By
  Cauchy, take `x ∈ N' ⊓ Z(G ⧸ L₀)` of order `p`. Then `⟨x⟩` is central (hence normal in
  `G ⧸ L₀`). The preimage `L = ⟨x⟩.comap (mk' L₀)` satisfies `L ⊴ G`, `L ≤ N` (since
  `(N.map f).comap f = N ⊔ ker f = N`), `|L| = p · p^r = p^(r+1)` (helper).

proof 実装は次 commit (技術的詳細: `orderOf_subtype_coe`, `Subgroup.zpowers` 中央化, など
mathlib API の精査要). -/
theorem normal_subgroup_card_pow_le_of_pGroup
    (hG : IsPGroup p G) {N : Subgroup G} [hN : N.Normal] {r : ℕ}
    (hr_dvd : p ^ r ∣ Nat.card N) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ Nat.card L = p ^ r := by
  classical
  induction r with
  | zero =>
    exact ⟨⊥, Subgroup.normal_bot, bot_le, by rw [Subgroup.card_bot, pow_zero]⟩
  | succ r ih =>
    obtain ⟨L₀, hL₀_norm, hL₀_le_N, hL₀_card⟩ :=
      ih (dvd_trans (pow_dvd_pow p (Nat.le_succ _)) hr_dvd)
    haveI : L₀.Normal := hL₀_norm
    let f : G →* G ⧸ L₀ := QuotientGroup.mk' L₀
    have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hf_ker : f.ker = L₀ := QuotientGroup.ker_mk' L₀
    let N' : Subgroup (G ⧸ L₀) := N.map f
    haveI hN'_normal : N'.Normal := hN.map f hf_surj
    have hG'_pgroup : IsPGroup p (G ⧸ L₀) := hG.to_quotient L₀
    have hN'_comap : (N.map f).comap f = N := by
      rw [Subgroup.comap_map_eq, hf_ker, sup_eq_left]; exact hL₀_le_N
    have hN_card_eq : Nat.card N = Nat.card N' * Nat.card L₀ := by
      have h := card_comap_eq_card_mul_card_ker f hf_surj N'
      rwa [hN'_comap, hf_ker] at h
    have hpr_pos : 0 < p ^ r := Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)
    have hp_dvd_N' : p ∣ Nat.card N' := by
      have h1 : p ^ (r + 1) ∣ Nat.card N' * p ^ r := by
        rw [← hL₀_card, ← hN_card_eq]; exact hr_dvd
      have h2 : p * p ^ r ∣ Nat.card N' * p ^ r := by
        rw [show p * p ^ r = p ^ (r + 1) by ring]; exact h1
      exact Nat.dvd_of_mul_dvd_mul_right hpr_pos h2
    have hN'_card_gt : 1 < Nat.card N' :=
      lt_of_lt_of_le hp.out.one_lt (Nat.le_of_dvd Nat.card_pos hp_dvd_N')
    haveI hN'_nontrivial : Nontrivial N' :=
      Finite.one_lt_card_iff_nontrivial.mp hN'_card_gt
    have hinter_nontrivial :
        Nontrivial ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hG'_pgroup hN'_nontrivial
    have hinter_card_gt : 1 < Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      Finite.one_lt_card_iff_nontrivial.mpr hinter_nontrivial
    have hinter_pgroup : IsPGroup p ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      hG'_pgroup.to_subgroup _
    have hp_dvd_inter : p ∣ Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hinter_pgroup
      rw [hn] at hinter_card_gt ⊢
      have : 0 < n := by
        rcases n with _ | n
        · simp at hinter_card_gt
        · exact Nat.succ_pos _
      exact dvd_pow_self p this.ne'
    haveI : Fintype ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := Fintype.ofFinite _
    have hp_dvd_fintype :
        p ∣ Fintype.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨⟨xc, hxc_mem⟩, hxc_order⟩ := exists_prime_orderOf_dvd_card p hp_dvd_fintype
    set x : G ⧸ L₀ := xc with hx_def
    have hx_in_N' : x ∈ N' := (Subgroup.mem_inf.mp hxc_mem).1
    have hx_in_center : x ∈ Subgroup.center (G ⧸ L₀) := (Subgroup.mem_inf.mp hxc_mem).2
    set K : Subgroup (G ⧸ L₀) := Subgroup.zpowers x with hK_def
    have hK_le_N' : K ≤ N' := Subgroup.zpowers_le.mpr hx_in_N'
    have hx_orderOf : orderOf x = p := by
      change orderOf xc = p
      exact (Subgroup.orderOf_coe ⟨xc, hxc_mem⟩).trans hxc_order
    have hK_card : Nat.card K = p := by
      rw [Nat.card_zpowers, hx_orderOf]
    have hx_comm : ∀ g, g * x = x * g := Subgroup.mem_center_iff.mp hx_in_center
    haveI hK_normal : K.Normal := by
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hgx : Commute g x := hx_comm g
      have hgxk : Commute g (x ^ k) := hgx.zpow_right k
      rw [show g * x ^ k * g⁻¹ = x ^ k from by rw [hgxk.eq, mul_inv_cancel_right]]
      exact zpow_mem (Subgroup.mem_zpowers x) k
    refine ⟨K.comap f, hK_normal.comap f, ?_, ?_⟩
    · intro g hg
      have hg_N' : f g ∈ N' := hK_le_N' hg
      have : g ∈ (N.map f).comap f := hg_N'
      rwa [hN'_comap] at this
    · have h := card_comap_eq_card_mul_card_ker f hf_surj K
      rw [hf_ker, hL₀_card, hK_card] at h
      rw [h, pow_succ, mul_comm]

end OddOrder.BG.Ch1.S01
