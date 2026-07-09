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
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.AInvariantPiSubgroups
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
| **Thm 1.13** | (Thompson critical) | `GroupTheory.CriticalSubgroup` ✅ | ✅ **sorry-free** `thompson_critical_omega` |
| **Lem 1.14** main | — | Sylow II in T·M + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` | ✅ **sorry-free 完成** |
| **Lem 1.14** 易方向 | — | `Subgroup.normalizer_le_normalizer_sup_normal` + `le_normalizer` | ✅ **sorry-free 5 行** |
| **Prop 1.15(a)** | Thm 3.21 | `hall_higman_1_2_3` ✅ | ✅ **sorry-free thin wrap** (π = {p} 特殊化) |
| Thm 1.17 | Thm 5.21 | `OddOrder.Isaacs.Ch05.focalSubgroupTheorem` ✅ | Ch05 public entrypoint |
| Thm 1.18 | Thm 5.13 | `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer` ✅ | Ch05 public entrypoint |
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
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_K_le_N).is_comm.comm
  haveI hquot_nilpotent : Group.IsNilpotent (K ⧸ N) := by
    rw [Subgroup.nilpotent_iff_lowerCentralSeries]
    refine ⟨1, ?_⟩
    rw [Subgroup.top_lowerCentralSeries_one, commutator_eq_bot_iff_center_eq_top, eq_top_iff]
    intro q _
    rw [Subgroup.mem_center_iff]
    intro r
    exact hquot_mul_comm r q
  have hker_le_center : (QuotientGroup.mk' N).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact hN_le_center
  haveI hK_nilpotent : Group.IsNilpotent K :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N) hker_le_center
  have hK_le_fitting : K ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  apply hK_not_le_F
  simpa [F, hF_def] using hK_le_fitting

/-- A chief factor `U/V` is a minimal normal subgroup of `G/V`.

(Public: BG §5 Thm 5.7 が `Ū = U/V` の minimal normality と
`isMinimalNormal_le_fitting_and_isElementaryAbelian` 経由の素数同定に使う。) -/
theorem isMinimalNormal_map_quotient_of_isChiefFactor
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
  exact Group.nilpotent_of_surjective φ (by
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

/-- **BG Proposition 1.2, whole-group form**: `F(G)` centralizes every chief factor `U/V` of a
finite solvable group `G`. (The `G* = G` specialization of
`fitting_map_subtype_le_chiefFactorCentralizer`, in the form used by BG Theorem 3.7's chief-factor
induction: a normal nilpotent subgroup `L ≤ F(G)` then centralizes every chief factor via
`nilpotent_normal_le_fitting`.) -/
theorem fitting_le_chiefFactorCentralizer
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {U V : Subgroup G} [V.Normal]
    (hChief : OddOrder.GroupTheory.IsChiefFactor U V) :
    OddOrder.Isaacs.Ch01.fitting G ≤ OddOrder.GroupTheory.chiefFactorCentralizer U V := by
  haveI hV_normal : V.Normal := hChief.normal_bot
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let Ubar : Subgroup (G ⧸ V) := U.map q
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal Ubar :=
    isMinimalNormal_map_quotient_of_isChiefFactor hChief
  have hFquot_le_cent_Ubar :
      OddOrder.Isaacs.Ch01.fitting (G ⧸ V) ≤ Subgroup.centralizer (Ubar : Set (G ⧸ V)) :=
    Subgroup.le_centralizer_iff.mp
      (isMinimalNormal_le_fitting_and_isElementaryAbelian (G := G ⧸ V) hMin).2.1
  haveI hFG_normal : (OddOrder.Isaacs.Ch01.fitting G).Normal := inferInstance
  haveI : ((OddOrder.Isaacs.Ch01.fitting G).map q).Normal :=
    hFG_normal.map q QuotientGroup.mk_surjective
  haveI : Group.IsNilpotent ((OddOrder.Isaacs.Ch01.fitting G).map q) :=
    isNilpotent_subgroup_map (OddOrder.Isaacs.Ch01.fitting G) q
  have hFGq_le_fitting :
      (OddOrder.Isaacs.Ch01.fitting G).map q ≤ OddOrder.Isaacs.Ch01.fitting (G ⧸ V) :=
    nilpotent_normal_le_fitting
  exact OddOrder.GroupTheory.chiefFactorCentralizer.le_of_map_le_centralizer
    (hFGq_le_fitting.trans hFquot_le_cent_Ubar)

/-- **BG Proposition 1.2, reverse inclusion** (P. Hall): every `G`-normal subgroup `H ≤ G*`
that centralizes every chief factor `U/V` of `G` with `U ⊆ F(G*)` is contained in `F(G*)`.

Together with `fitting_map_subtype_le_chiefFactorCentralizer`, this gives the full Hall
characterization `F(G*) = ⋂_{U/V ∈ 𝒟*} C_{G*}(U/V)`.

**Proof strategy** (BG L380-398, well-founded induction reformulation of the book's
minimal-counterexample argument): It suffices to prove, for every `G`-normal `K ≤ H`,
that `K ≤ F(G*)`.  Well-founded induction on `K`: at `K = ⊥` trivial; at `K > ⊥`, let
`V₀ = chiefSeriesInside K 1` be the next step down in the chief series of `G` inside `K`.
`V₀ < K`, so by IH, `V₀ ≤ F(G*)`.

To show `K ≤ F(G*)`, prove `↥K` nilpotent (then `K.subgroupOf G* ⊴ G*` is nilpotent, hence
`≤ F(G*)`).  Nilpotency comes from `isNilpotent_of_chief_factor_centralization`: every step
`⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i+1)` holds, because

* `i = 0`: `K/V₀` is a chief factor of solvable `G`, hence abelian.
* `i ≥ 1`: `chiefSeriesInside K (i+1) ≤ V₀ ≤ F(G*)`, so the chief factor
  `chiefSeriesInside K i / chiefSeriesInside K (i+1)` lies in `𝒟*`, and `K ≤ H`
  centralizes it.

Forward direction is `fitting_map_subtype_le_chiefFactorCentralizer` (already complete). -/
theorem chiefFactorCentralizer_subset_le_fitting_of_isSolvable
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {Gstar H : Subgroup G} [Gstar.Normal] [H.Normal]
    (hH_le_Gstar : H ≤ Gstar)
    (hH_cent : ∀ U V : Subgroup G, [V.Normal] →
      OddOrder.GroupTheory.IsChiefFactor U V →
      U ≤ (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype →
      H ≤ OddOrder.GroupTheory.chiefFactorCentralizer U V) :
    H ≤ (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype := by
  -- Reduce to: ∀ `G`-normal `K ≤ H`, `K ≤ F(G*)`.
  suffices h : ∀ K : Subgroup G, K.Normal → K ≤ H →
      K ≤ (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype by
    exact h H ‹H.Normal› le_rfl
  intro K
  induction K using WellFoundedLT.induction with
  | _ K IH =>
    intro hK_normal hK_le_H
    by_cases hK_bot : K = ⊥
    · rw [hK_bot]; exact bot_le
    have hK_le_Gstar : K ≤ Gstar := hK_le_H.trans hH_le_Gstar
    -- `V₀ = chiefSeriesInside K 1` is the first step down from `K` in the chief series.
    set V₀ : Subgroup G := OddOrder.GroupTheory.chiefSeriesInside K 1 with hV₀_def
    have hV₀_lt_K : V₀ < K :=
      OddOrder.GroupTheory.chiefSeriesInside_lt_of_ne_bot hK_bot
    have hV₀_normal : V₀.Normal :=
      OddOrder.GroupTheory.chiefSeriesInside_instNormal K 1
    have hV₀_le_H : V₀ ≤ H :=
      (OddOrder.GroupTheory.chiefSeriesInside_le K 1).trans hK_le_H
    -- IH gives `V₀ ≤ F(G*)`.
    have hV₀_le_fitting : V₀ ≤ (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype :=
      IH V₀ hV₀_lt_K hV₀_normal hV₀_le_H
    -- Establish the centralization step `⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i+1)`.
    have h_central : ∀ i : ℕ,
        ⁅K, OddOrder.GroupTheory.chiefSeriesInside K i⁆ ≤
          OddOrder.GroupTheory.chiefSeriesInside K (i + 1) := by
      intro i
      by_cases hbot_i : OddOrder.GroupTheory.chiefSeriesInside K i = ⊥
      · rw [hbot_i, Subgroup.commutator_bot_right]; exact bot_le
      · -- chiefSeriesInside K i ≠ ⊥: chief factor + (solvability for i = 0, hypothesis otherwise).
        cases i with
        | zero =>
          -- `⁅K, K⁆ ≤ V₀` from `K/V₀` chief factor + `G` solvable.
          have hK_ne : OddOrder.GroupTheory.chiefSeriesInside K 0 ≠ ⊥ := by
            simpa [OddOrder.GroupTheory.chiefSeriesInside_zero] using hK_bot
          have hChief :
              OddOrder.GroupTheory.IsChiefFactor
                (OddOrder.GroupTheory.chiefSeriesInside K 0)
                (OddOrder.GroupTheory.chiefSeriesInside K 1) :=
            OddOrder.GroupTheory.isChiefFactor_chiefSeriesInside hK_ne
          have h_KK_le :
              ⁅OddOrder.GroupTheory.chiefSeriesInside K 0,
                OddOrder.GroupTheory.chiefSeriesInside K 0⁆ ≤
                OddOrder.GroupTheory.chiefSeriesInside K 1 :=
            hChief.commutator_le_of_isSolvable
          simpa [OddOrder.GroupTheory.chiefSeriesInside_zero] using h_KK_le
        | succ m =>
          -- chiefSeriesInside K (m+1) ≤ V₀ ≤ F(G*); apply BG hypothesis.
          have h1_le : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
          have h_le_V₀ : OddOrder.GroupTheory.chiefSeriesInside K (m + 1) ≤ V₀ := by
            have := OddOrder.GroupTheory.chiefSeriesInside_antitone K h1_le
            simpa [V₀, hV₀_def] using this
          have h_le_fitting :
              OddOrder.GroupTheory.chiefSeriesInside K (m + 1) ≤
                (OddOrder.Isaacs.Ch01.fitting Gstar).map Gstar.subtype :=
            h_le_V₀.trans hV₀_le_fitting
          have hChief :
              OddOrder.GroupTheory.IsChiefFactor
                (OddOrder.GroupTheory.chiefSeriesInside K (m + 1))
                (OddOrder.GroupTheory.chiefSeriesInside K (m + 2)) :=
            OddOrder.GroupTheory.isChiefFactor_chiefSeriesInside hbot_i
          have h_H_cent :
              H ≤ OddOrder.GroupTheory.chiefFactorCentralizer
                  (OddOrder.GroupTheory.chiefSeriesInside K (m + 1))
                  (OddOrder.GroupTheory.chiefSeriesInside K (m + 2)) :=
            hH_cent _ _ hChief h_le_fitting
          have h_K_cent := hK_le_H.trans h_H_cent
          have h_comm := OddOrder.GroupTheory.chiefFactorCentralizer.commutator_le_of_le
            h_K_cent
          rw [Subgroup.commutator_comm]
          exact h_comm
    -- `↥K` is nilpotent.
    have hK_isNilpotent : Group.IsNilpotent ↥K :=
      OddOrder.GroupTheory.isNilpotent_of_chief_factor_centralization h_central
    -- `K.subgroupOf G* ⊴ G*` is nilpotent (via `subgroupOfEquivOfLe`), so it is `≤ F(G*)`.
    have hK_subg_nilp : Group.IsNilpotent ↥(K.subgroupOf Gstar) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_le_Gstar).symm
    have hK_subg_le_fitting :
        K.subgroupOf Gstar ≤ OddOrder.Isaacs.Ch01.fitting Gstar :=
      OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    have h_K_eq :
        (K.subgroupOf Gstar).map Gstar.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hK_le_Gstar
    rw [← h_K_eq]
    exact Subgroup.map_mono hK_subg_le_fitting

/-!
Prop. 1.2 reverse direction (`chiefFactorCentralizer_subset_le_fitting_of_isSolvable`)
combined with the forward direction (`fitting_map_subtype_le_chiefFactorCentralizer`)
recovers Hall's equality `F(G*) = ⋂_{U/V ∈ 𝒟*} C_{G*}(U/V)`.

* Prop. 1.4 is exposed below in the kernel form named
  actionCommutator_eq_bot_of_fitting_le_fixedPoints: if a coprime automorphism group
  fixes the Fitting subgroup pointwise, then it acts trivially on the group.  This is the
  form used in BG §8.
-/

/-- **BG Proposition 1.4** (kernel form): if a finite coprime automorphism group fixes the
Fitting subgroup pointwise, then the action is trivial on the whole finite solvable group.

This combines Prop. 1.3, the self-centralizing Fitting subgroup theorem, with Isaacs Ch.4's
action-commutator decomposition.  It is the practical form needed later: the kernel of the
action on the Fitting subgroup is also the kernel of the action on the whole group. -/
theorem actionCommutator_eq_bot_of_fitting_le_fixedPoints
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hF_le_fixed : OddOrder.Isaacs.Ch01.fitting G ≤ Subgroup.fixedPointsOfMulAut φ) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ := by
  classical
  set F : Subgroup G := OddOrder.Isaacs.Ch01.fitting G with hF_def
  have hAC_le_cent :
      OddOrder.Isaacs.Ch04.actionCommutator φ ≤ Subgroup.centralizer (F : Set G) := by
    rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff_left]
    intro a g
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    let x : G := g⁻¹ * (φ a) g
    change f * x = x * f
    have hgf : g * f * g⁻¹ ∈ F := by
      rw [hF_def]
      exact (OddOrder.Isaacs.Ch01.fitting.normal G).conj_mem f hf g
    have hf_fix : (φ a) f = f :=
      Subgroup.mem_fixedPointsOfMulAut.mp (hF_le_fixed hf) a
    have hfix : (φ a) (g * f * g⁻¹) = g * f * g⁻¹ :=
      Subgroup.mem_fixedPointsOfMulAut.mp (hF_le_fixed hgf) a
    have hxconj : x * f * x⁻¹ = f := by
      calc
        x * f * x⁻¹ = g⁻¹ * (φ a) g * f * ((φ a) g)⁻¹ * g := by
          dsimp [x]
          group
        _ = g⁻¹ * (φ a) g * (φ a) f * ((φ a) g)⁻¹ * g := by rw [hf_fix]
        _ = g⁻¹ * (φ a) (g * f * g⁻¹) * g := by
          rw [map_mul, map_mul, map_inv]
          group
        _ = g⁻¹ * (g * f * g⁻¹) * g := by rw [hfix]
        _ = f := by group
    rw [mul_inv_eq_iff_eq_mul] at hxconj
    exact hxconj.symm
  have hAC_le_F :
      OddOrder.Isaacs.Ch04.actionCommutator φ ≤ F :=
    hAC_le_cent.trans (by
      rw [hF_def]
      exact centralizer_fitting_le_fitting)
  have htriv :
      ∀ a : A, ∀ h ∈ OddOrder.Isaacs.Ch04.actionCommutator φ, (φ a) h = h := by
    intro a h hh
    exact Subgroup.mem_fixedPointsOfMulAut.mp (hF_le_fixed (hAC_le_F hh)) a
  exact OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    hCop (Or.inr inferInstance) htriv

/-! ## §1B: A-invariant Hall theory (Prop 1.5, Prop 1.6)

BG Prop. 1.5(a),(c) are obtained by applying the already-formalized Glauberman fixed-point
lemma to the transitive `G`-set of Hall `π`-subgroups. This is not a pure wrapper: it adapts
the abstract coprime-action fixed-point machinery to Hall subgroups and exposes the BG-facing
Hall statements. Prop. 1.5(d) remains a no-wrapper direct use of Isaacs Cor. 3.28.

| BG | Isaacs §3E / §4D | Lean (本リポ) | 備考 |
|---|---|---|---|
| **Prop 1.5(a)** A-inv Hall 存在 | Hall-E + Hall-C + Lem 3.24(a) | `exists_aInvariant_hall` ✅ | Hall `π` 一般版 |
| **Prop 1.5(b)** A-inv π-sub ⊆ A-inv Hall | Hall induction + Glauberman conjugacy | `aInvariant_piSubgroup_le_aInvariant_hall` ✅ | minimal normal quotient induction + `H = G` complement branch |
| **Prop 1.5(c)** A-inv Hall 共役 | Hall-C + Lem 3.24(b) | `aInvariant_hall_conj` ✅ | 共役元は `C_G(A)` |
| **Prop 1.5(d) C_{G/N}(A) = image C_G(A)** | **Cor 3.28 (商の固定点)** | **`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`** ✅ | §1 hub. 6 §1 proofs で使用. **無 wrapper, 直接呼び** |
| **Prop 1.5(e)** C_G(A) ⊇ Hall π' ⇒ [G,A] ⊆ O_π | Hall product + action commutator | `actionCommutator_le_oPiCore_of_fixedPoints_contains_hallComplement` ✅ | BG L412-L414 を `IsComplement' K H` + `[G,A] ≤ H` で実装 |
| **Prop 1.6(a) G = C_G(A)[G,A]** | **Lem 4.28** | **`OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top`** ✅ | **無 wrapper**: Subgroup.fixedPointsOfMulAut ⊔ actionCommutator = ⊤ |
| **Prop 1.6(b) [G,A,A]=[G,A]** | **Lem 4.29** | **`OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one`** ✅ | **無 wrapper**: SemidirectProduct Γ-form |
| **Prop 1.6(c)** [G,A,A]=1 ⇒ trivial | Lem 4.29 | `iterCommutator_inl_inr_one_eq_bot_of_two_eq_bot` ✅ | BG-facing consequence of Ch04 Γ-form equality |
| **Prop 1.6(d)** abelian 直積分解 | **Thm 4.34 Fitting** | `fixedPoints_isComplement_actionCommutator_of_abelian` ✅ | complement form of `G = C_G(A) × [G,A]` |
| **Prop 1.6(e) abelian p-群 + p'-A** | **Cor 4.35** | **`OddOrder.Isaacs.Ch04.*` (Ch.4 §4D 3422 行)** ✅ | **無 wrapper**: G abelian p-群 + A p'-群 fixes order-p elements |

**使用例**: 本ファイル §1C Thm 1.8 (`burnside_operator`) は `aFixed_quotient_frattini`
(= Prop 1.5(d) + Lem 1.7(a) 合成 = Isaacs Cor 3.29) を直接呼び出す.
-/

section AInvariantHall

private abbrev HallSubgroups (π : Set ℕ) (G : Type*) [Group G] :=
  {H : Subgroup G // OddOrder.Isaacs.Ch03.IsHallSubgroup π H}

/-- The pointwise action of a `MulAut` on a subgroup is its image. -/
private theorem mulAut_smul_eq_map {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- A Hall subgroup stays Hall under any automorphism. -/
private theorem isHallSubgroup_mulAut_smul {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {H : Subgroup G} (φ : MulAut G)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (φ • H) := by
  rw [mulAut_smul_eq_map]
  refine ⟨?_, ?_⟩
  · have hcard :
        Nat.card ↥(H.map (φ : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ φ.injective).toEquiv).symm
    rw [hcard]
    exact hH.1
  · have hidx : (H.map (φ : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H φ
    rw [hidx]
    exact hH.2

private instance hallSubgroupsMulAutAction {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    MulAction (MulAut G) (HallSubgroups π G) where
  smul φ H := ⟨φ • H.1, isHallSubgroup_mulAut_smul φ H.2⟩
  one_smul H := by
    apply Subtype.ext
    change (1 : MulAut G) • H.1 = H.1
    simp
  mul_smul φ ψ H := by
    apply Subtype.ext
    change (φ * ψ) • H.1 = φ • (ψ • H.1)
    simp [mul_smul]

private instance hallSubgroupsConjAction {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    MulAction G (HallSubgroups π G) :=
  MulAction.compHom (HallSubgroups π G) (MulAut.conj : G →* MulAut G)

private theorem hallSubgroups_pretransitive {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (π : Set ℕ) :
    MulAction.IsPretransitive G (HallSubgroups π G) := by
  constructor
  intro H K
  obtain ⟨g, hg⟩ :=
    OddOrder.Isaacs.Ch03.hall_C (G := G) (π := π) H.2 K.2
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change MulAut.conj g • H.1 = K.1
  rw [mulAut_smul_eq_map]
  exact hg

/-- **BG Prop 1.5(a)**: if a finite solvable group `G` is acted on by a finite operator
group `A` with coprime orders, then `A` fixes some Hall `π`-subgroup of `G`.

Proof: let `G` act by conjugation and `A` act through `φ` on the type of Hall `π`-subgroups.
Hall existence makes this type nonempty, Hall conjugacy makes the `G`-action transitive, and
Glauberman's fixed-point lemma gives an `A`-fixed Hall subgroup. -/
theorem exists_aInvariant_hall {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (π : Set ℕ) :
    ∃ H : Subgroup G, OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
      OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  let Ω := HallSubgroups π G
  letI : MulAction A Ω := MulAction.compHom Ω φ
  haveI hΩ_nonempty : Nonempty Ω := by
    obtain ⟨H, hH⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := G) π
    exact ⟨⟨H, hH⟩⟩
  have hcompat : OddOrder.Isaacs.Ch04.IsCompatibleMulAction φ Ω := by
    intro a g H
    apply Subtype.ext
    change (φ a) • (MulAut.conj g • H.1) =
      MulAut.conj ((φ a) g) • ((φ a) • H.1)
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨H, hH_fix⟩ :=
    OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists
      (G := G) (A := A) (φ := φ) hCop (Or.inr inferInstance)
      (Ω := Ω) hcompat (hallSubgroups_pretransitive π)
  refine ⟨H.1, H.2, ?_⟩
  intro a
  exact congrArg Subtype.val (hH_fix a)

/-- **BG Prop 1.5(c)**: two `A`-invariant Hall `π`-subgroups of a finite solvable group
under a coprime operator group are conjugate by an element fixed by every operator in `A`.

This is the Hall-subgroup specialization of Glauberman's conjugacy fixed-point lemma. -/
theorem aInvariant_hall_conj {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) {π : Set ℕ}
    {H K : Subgroup G}
    (hH_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π H)
    (hK_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π K)
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ MulAut.conj c • H = K := by
  let Ω := HallSubgroups π G
  letI : MulAction A Ω := MulAction.compHom Ω φ
  let HΩ : Ω := ⟨H, hH_hall⟩
  let KΩ : Ω := ⟨K, hK_hall⟩
  have hH_fix : ∀ a : A, a • HΩ = HΩ := by
    intro a
    apply Subtype.ext
    exact hH_inv a
  have hK_fix : ∀ a : A, a • KΩ = KΩ := by
    intro a
    apply Subtype.ext
    exact hK_inv a
  have hcompat : OddOrder.Isaacs.Ch04.IsCompatibleMulAction φ Ω := by
    intro a g L
    apply Subtype.ext
    change (φ a) • (MulAut.conj g • L.1) =
      MulAut.conj ((φ a) g) • ((φ a) • L.1)
    rw [← mul_smul, ← mul_smul]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨c, hc_fix, hc_smul⟩ :=
    OddOrder.Isaacs.Ch04.glauberman_fixed_points_conj
      (G := G) (A := A) (φ := φ) hCop (Or.inr inferInstance)
      (Ω := Ω) hcompat (hallSubgroups_pretransitive π)
      hH_fix hK_fix
  refine ⟨c, hc_fix, ?_⟩
  exact congrArg Subtype.val hc_smul

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- An `A`-invariant subgroup maps to an `A`-invariant subgroup in an `A`-invariant
quotient. This is the quotient-action transport used in BG Prop. 1.5(b). -/
private theorem isAInvariant_map_mk'
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hN)
      (H.map (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by rw [quotientMulAutHom_apply_mk']⟩

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- The preimage of an invariant subgroup of an `A`-invariant quotient is invariant in the
original group. -/
private theorem isAInvariant_comap_mk'
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {Y : Subgroup (G ⧸ N)}
    (hY : OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hN) Y) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (Y.comap (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  rw [Subgroup.mem_comap] at hg ⊢
  rw [← quotientMulAutHom_apply_mk']
  exact hY.smul_mem a hg

/-- Restrict an invariant subgroup into an invariant ambient subgroup. -/
private theorem isAInvariant_subgroupOf_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U H : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict (H.subgroupOf U) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val]
  exact hH.smul_mem a hh

/-- Push an invariant subgroup of an invariant ambient subgroup back to the original group. -/
private theorem isAInvariant_map_subtype_of_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {L : Subgroup U} (hL : OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict L) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl,
    OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- A Hall subgroup of an invariant subgroup whose ambient index is a `π'`-number is a Hall
subgroup after pushing it back to the whole group. This is the Hall-index transfer needed in
the `H < G` branch of BG Prop. 1.5(b). -/
private theorem isHallSubgroup_map_subtype_of_index_no_pi
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H : Subgroup G} {L : Subgroup H}
    (hL : OddOrder.Isaacs.Ch03.IsHallSubgroup π L)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (L.map H.subtype) := by
  have hcard : Nat.card ↥(L.map H.subtype) = Nat.card ↥L :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).toEquiv).symm
  have hindex : (L.map H.subtype).index = L.index * H.index := by
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    have hmul : Nat.card ↥L * (L.map H.subtype).index =
        Nat.card ↥L * (L.index * H.index) := by
      calc
        Nat.card ↥L * (L.map H.subtype).index
            = Nat.card ↥(L.map H.subtype) * (L.map H.subtype).index := by rw [hcard]
        _ = Nat.card G := Subgroup.card_mul_index (L.map H.subtype)
        _ = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
        _ = (Nat.card ↥L * L.index) * H.index := by rw [Subgroup.card_mul_index L]
        _ = Nat.card ↥L * (L.index * H.index) := by ring
    exact Nat.mul_left_cancel hpos hmul
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [hcard] at hp
    exact hL.1 p hp
  · intro p hp hp_pi
    rw [hindex] at hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp_prime, hp_dvd, _⟩ := hp
    rcases hp_prime.dvd_mul.mp hp_dvd with hp_L | hp_H
    · exact hL.2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_L, Subgroup.index_ne_zero_of_finite⟩) hp_pi
    · exact hH_index p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_H, Subgroup.index_ne_zero_of_finite⟩) hp_pi


/-- A `π`-subgroup remains a `π`-subgroup after mapping to an invariant quotient. -/
private theorem isPiGroup_map_mk'
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {N K : Subgroup G} [N.Normal]
    (hK : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N)) := by
  intro p hp
  apply hK
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩

/-- Quotienting by a nontrivial normal subgroup strictly lowers finite group order. -/
private theorem card_quotient_lt_card_of_ne_bot
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
  have hN_one_lt : 1 < Nat.card N := Finite.one_lt_card
  have hQ_pos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact lt_mul_of_one_lt_right hQ_pos hN_one_lt

/-- Coprime operator order descends to a quotient of the acted-on group. -/
private theorem coprime_card_quotient_of_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {N : Subgroup G} [N.Normal] (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card (G ⧸ N)) :=
  hCop.coprime_dvd_right (Subgroup.card_quotient_dvd_card N)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom) in
/-- Pull back a quotient Hall subgroup containing the image of `K`.

This packages the quotient/comap step in BG Prop. 1.5(b): once induction in `G/M` gives an
`A`-invariant Hall subgroup containing the image of `K`, its preimage in `G` is
`A`-invariant, contains `K`, and has π-free index. -/
private theorem quotient_hall_preimage_frame
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {Hbar : Subgroup (G ⧸ M)}
    (hHbar_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π Hbar)
    (hHbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom hM_inv) Hbar)
    (hK_image_le : K.map (QuotientGroup.mk' M) ≤ Hbar) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H ∧
        (∀ p ∈ H.index.primeFactors, p ∉ π) ∧
        H = Hbar.comap (QuotientGroup.mk' M) := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let H : Subgroup G := Hbar.comap q
  refine ⟨H, ?_, ?_, ?_, rfl⟩
  · exact isAInvariant_comap_mk' hM_inv hHbar_inv
  · intro k hk
    change q k ∈ Hbar
    exact hK_image_le (by
      rw [Subgroup.mem_map]
      exact ⟨k, hk, rfl⟩)
  · have hindex : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    rw [hindex]
    exact hHbar_hall.2


/-- Coprime operator order descends to a subgroup of the acted-on group. -/
private theorem coprime_card_subgroup_of_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {H : Subgroup G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Nat.Coprime (Nat.card A) (Nat.card H) :=
  hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)

/-- Lift the recursive result from a proper invariant overgroup back to the ambient group.

In the `H < G` branch of BG Prop. 1.5(b), quotient induction first produces an invariant
overgroup `H` of `K` with π-free index.  Applying the main induction hypothesis inside `H`
gives an invariant Hall subgroup `L ≤ H` containing `K`; this helper pushes `L` back to `G`.
-/
private theorem lift_hall_from_invariant_overgroup
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_le_H : K ≤ H) {L : Subgroup H}
    (hL_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π L)
    (hL_inv : OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L)
    (hK_sub_le_L : K.subgroupOf H ≤ L) :
    ∃ Lg : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π Lg ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ Lg ∧ K ≤ Lg := by
  refine ⟨L.map H.subtype, ?_, ?_, ?_⟩
  · exact isHallSubgroup_map_subtype_of_index_no_pi hL_hall hH_index
  · exact isAInvariant_map_subtype_of_restrict hH_inv hL_inv
  · intro k hk
    rw [Subgroup.mem_map]
    refine ⟨⟨k, hK_le_H hk⟩, ?_, rfl⟩
    exact hK_sub_le_L (by
      rw [Subgroup.mem_subgroupOf]
      exact hk)


/-- Assemble the recursive proper-overgroup branch of BG Prop. 1.5(b).

This is the branch after quotient induction has produced an invariant overgroup `H` of `K`
with π-free index.  If the main induction hypothesis has already produced, inside `H`, an
invariant Hall subgroup containing `K.subgroupOf H`, then this packages the lift back to `G`.
-/
private theorem proper_overgroup_branch_frame
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K)
    (hK_le_H : K ≤ H)
    (hIH_H : ∀ {Ksub : Subgroup H},
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub →
        OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub →
        ∃ L : Subgroup H,
          OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
            OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L) :
    ∃ Lg : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π Lg ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ Lg ∧ K ≤ Lg := by
  let Ksub : Subgroup H := K.subgroupOf H
  have hKsub_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hK_le_H hK_pi
  have hKsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub :=
    isAInvariant_subgroupOf_restrict hH_inv hK_inv
  obtain ⟨L, hL_hall, hL_inv, hKsub_le_L⟩ := hIH_H hKsub_pi hKsub_inv
  exact lift_hall_from_invariant_overgroup hH_inv hH_index hK_le_H
    hL_hall hL_inv hKsub_le_L

/-- A nontrivial finite group has a minimal nontrivial `A`-invariant normal subgroup. -/
private theorem exists_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [Nontrivial G]
    [Group A] {φ : A →* MulAut G} :
    ∃ M : Subgroup G, M.Normal ∧ OddOrder.Isaacs.Ch03.IsAInvariant φ M ∧ M ≠ ⊥ ∧
      ∀ N : Subgroup G, N.Normal → OddOrder.Isaacs.Ch03.IsAInvariant φ N →
        N ≤ M → N ≠ ⊥ → M ≤ N := by
  classical
  let S : Set (Subgroup G) :=
    {N | N.Normal ∧ OddOrder.Isaacs.Ch03.IsAInvariant φ N ∧ N ≠ ⊥}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty :=
    ⟨⊤, inferInstance, OddOrder.Isaacs.Ch03.IsAInvariant.top φ, top_ne_bot⟩
  obtain ⟨M, hM_min⟩ := hS_fin.exists_minimal hS_nonempty
  obtain ⟨⟨hM_normal, hM_inv, hM_ne_bot⟩, hM_minimal⟩ := hM_min
  refine ⟨M, hM_normal, hM_inv, hM_ne_bot, ?_⟩
  intro N hN_normal hN_inv hN_le hN_ne_bot
  exact hM_minimal ⟨hN_normal, hN_inv, hN_ne_bot⟩ hN_le

/-- A minimal nontrivial `A`-invariant normal subgroup of a finite solvable group is
commutative.

This is the abelian-chief-factor step needed for the induction in BG Prop. 1.5(b): the
minimality is only among `A`-invariant normal subgroups below `M`, not among all normal
subgroups.  Solvability still forces `⁅M, M⁆ < M`; since `⁅M, M⁆` is again normal and
`A`-invariant, minimality makes the commutator trivial. -/
private theorem isMulCommutative_of_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] {φ : A →* MulAut G} {M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    (hM_ne_bot : M ≠ ⊥)
    (hM_min : ∀ N : Subgroup G, N.Normal →
      OddOrder.Isaacs.Ch03.IsAInvariant φ N → N ≤ M → N ≠ ⊥ → M ≤ N) :
    IsMulCommutative M := by
  have hcomm_lt : ⁅M, M⁆ < M := IsSolvable.commutator_lt_of_ne_bot hM_ne_bot
  have hcomm_bot : (⁅M, M⁆ : Subgroup G) = ⊥ := by
    by_contra hcomm_ne_bot
    have hM_le_comm : M ≤ ⁅M, M⁆ :=
      hM_min ⁅M, M⁆ (Subgroup.commutator_normal M M)
        (hM_inv.commutator hM_inv) hcomm_lt.le hcomm_ne_bot
    exact hcomm_lt.not_ge hM_le_comm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm_bot
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx_cent : (x : G) ∈ Subgroup.centralizer M := hcomm_bot x.2
  rw [Subgroup.mem_centralizer_iff] at hx_cent
  exact Subtype.ext ((hx_cent y y.2).symm)

/-- A minimal nontrivial `A`-invariant normal subgroup of a finite solvable group is a
`p`-group for some prime `p`.

After the preceding commutativity lemma, a Sylow subgroup of `M` is characteristic in `M`;
its image in `G` is therefore again normal and `A`-invariant. Minimality forces that image to
be all of `M`. -/
private theorem exists_prime_isPGroup_of_minimal_normal_aInvariant
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] {φ : A →* MulAut G} {M : Subgroup G} [M.Normal]
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    (hM_ne_bot : M ≠ ⊥)
    (hM_min : ∀ N : Subgroup G, N.Normal →
      OddOrder.Isaacs.Ch03.IsAInvariant φ N → N ≤ M → N ≠ ⊥ → M ≤ N) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M := by
  classical
  haveI hM_comm : IsMulCommutative M :=
    isMulCommutative_of_minimal_normal_aInvariant hM_inv hM_ne_bot hM_min
  have hM_card_ne_one : Nat.card M ≠ 1 := by
    intro hcard
    exact hM_ne_bot ((Subgroup.eq_bot_iff_card M).mpr hcard)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hM_card_ne_one
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p M := default
  have hP_normal : (P : Subgroup M).Normal := Subgroup.normal_of_isMulCommutative (P : Subgroup M)
  haveI hP_char : (P : Subgroup M).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  let Pmap : Subgroup G := (P : Subgroup M).map M.subtype
  have hPmap_normal : Pmap.Normal := by
    dsimp [Pmap]
    infer_instance
  have hPmap_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ Pmap := by
    dsimp [Pmap]
    exact hM_inv.map_subtype_of_characteristic
  have hPmap_le_M : Pmap ≤ M := by
    dsimp [Pmap]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd
  have hPmap_ne_bot : Pmap ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot
    have hmap_bot : (P : Subgroup M).map M.subtype = ⊥ := by
      simpa [Pmap] using hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hmap_bot
  have hM_le_Pmap : M ≤ Pmap :=
    hM_min Pmap hPmap_normal hPmap_inv hPmap_le_M hPmap_ne_bot
  have hPmap_eq_M : Pmap = M := le_antisymm hPmap_le_M hM_le_Pmap
  have hP_eq_top : (P : Subgroup M) = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := M)).mp
    have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc
      (P : Subgroup M).map M.subtype = M := by simpa [Pmap] using hPmap_eq_M
      _ = (⊤ : Subgroup M).map M.subtype := htop_map.symm
  obtain ⟨n, hnP⟩ := (IsPGroup.iff_card (p := p) (G := P)).mp P.2
  have hcardM : Nat.card M = p ^ n := by
    have hcardP : Nat.card P = Nat.card M := by
      rw [hP_eq_top, Subgroup.card_top]
    rwa [← hcardP]
  exact ⟨p, hp_prime, (IsPGroup.iff_card (p := p) (G := M)).mpr ⟨n, hcardM⟩⟩

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
private theorem subgroup_card_lt_card_of_ne_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH_ne_top : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hindex_ne_one : H.index ≠ 1 := fun hidx => hH_ne_top (Subgroup.index_eq_one.mp hidx)
  have hindex_gt_one : 1 < H.index :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Subgroup.index_ne_zero_of_finite, hindex_ne_one⟩
  calc
    Nat.card H < Nat.card H * H.index := lt_mul_of_one_lt_right Nat.card_pos hindex_gt_one
    _ = Nat.card G := Subgroup.card_mul_index H

/-- A `p`-group is a `π`-group once `p ∈ π`. -/
private theorem subgroup_isPiGroup_of_isPGroup_of_mem
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hpπ : p ∈ π) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H := by
  intro q hq
  have hsingle : q ∈ ({p} : Set ℕ) :=
    OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup hH q hq
  rw [Set.mem_singleton_iff] at hsingle
  rw [hsingle]
  exact hpπ

/-- A `π`-subgroup has trivial intersection with a `p`-group for `p ∉ π`. -/
private theorem inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {K M : Subgroup G}
    {p : ℕ} [Fact p.Prime]
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hM_p : IsPGroup p M) (hp_not_pi : p ∉ π) :
    K ⊓ M = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ π} M :=
    subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_not_pi
  have hdvdK : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdM : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card K) (Nat.card M) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK_pi hM_pi'
  have hdvd_gcd : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.gcd (Nat.card K) (Nat.card M) :=
    Nat.dvd_gcd hdvdK hdvdM
  rw [hcop] at hdvd_gcd
  exact Nat.dvd_one.mp hdvd_gcd

/-- Package complementary subgroups inside a specified ambient subgroup. -/
private theorem isComplement_subgroupOf_of_disjoint_mul_eq_univ
    {G : Type*} [Group G] {U H M : Subgroup G}
    (hH_le_U : H ≤ U) (hM_le_U : M ≤ U) (hHM_bot : H ⊓ M = ⊥)
    (hmul : ∀ x ∈ U, ∃ m ∈ M, ∃ h ∈ H, m * h = x) :
    Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
      Subtype.ext_iff, OneMemClass.coe_one]
    refine ⟨?_, fun hx => by simp [hx]⟩
    rintro ⟨hxM, hxH⟩
    have hx : (x : G) ∈ H ⊓ M := ⟨hxH, hxM⟩
    rw [hHM_bot, Subgroup.mem_bot] at hx
    exact hx
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨m, hmM, h, hhH, hmh⟩ := hmul x x.2
    refine ⟨⟨m, hM_le_U hmM⟩, hmM, ⟨h, hH_le_U hhH⟩, hhH, ?_⟩
    ext
    exact hmh

/-- A complement to a `π'`-subgroup is a Hall `π`-subgroup of the ambient subgroup. -/
private theorem isHallSubgroup_subgroupOf_of_complement_pi_pi'
    {G : Type*} [Group G] [Finite G] {π : Set ℕ} {U H M : Subgroup G}
    (hH_le_U : H ≤ U) (hM_le_U : M ≤ U)
    (hH_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H)
    (hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {p | p ∉ π} M)
    (hComp : Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (H.subgroupOf U) := by
  refine ⟨?_, ?_⟩
  · exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hH_le_U hH_pi
  · have hMsub_pi' :
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {p | p ∉ π} (M.subgroupOf U) :=
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hM_le_U hM_pi'
    intro q hq hq_pi
    rw [hComp.index_eq_card] at hq
    exact hMsub_pi' q hq hq_pi

/-- Conjugating an invariant subgroup by an `A`-fixed element preserves invariance. -/
private theorem isAInvariant_mulAut_conj_smul_of_fixed
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    {c : G} (hc : ∀ a : A, (φ a) c = c) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (MulAut.conj c • H) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [mulAut_smul_eq_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(φ a) y, hH.smul_mem a hy, ?_⟩
  simp [MulAut.conj_apply, map_mul, map_inv, hc a]

/-- Assemble the `H = G` branch of BG Prop. 1.5(b).

Here quotient induction has produced the whole preimage, so `G/M` is a `π`-group.
For a minimal normal `p`-subgroup `M`, the non-`π` assumption on `G` forces `p ∉ π`.
An invariant Hall subgroup `Q` complements `M`; inside `K ⊔ M`, the subgroups `K` and
`Q ∩ (K ⊔ M)` are invariant Hall `π`-subgroups, hence are conjugate by an `A`-fixed element
of `K ⊔ M`.  The conjugate of `Q` is the desired invariant Hall overgroup of `K`.
-/
private theorem top_preimage_branch_frame
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hG_not_pi : ¬ ∀ q ∈ (Nat.card G).primeFactors, q ∈ π)
    (hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {p : ℕ} [Fact p.Prime] (hM_p : IsPGroup p M)
    (hquot_pi : ∀ q ∈ (Nat.card (G ⧸ M)).primeFactors, q ∈ π)
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ L : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ L ∧ K ≤ L := by
  classical
  have hp_not_pi : p ∉ π := by
    intro hp_pi
    have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π M :=
      subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_pi
    have hG_pi : OddOrder.Isaacs.Ch03.IsPiGroup π G :=
      OddOrder.Isaacs.Ch03.IsPiGroup.of_normal_quotient (N := M) hM_pi hquot_pi
    exact hG_not_pi hG_pi
  have hM_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ π} M :=
    subgroup_isPiGroup_of_isPGroup_of_mem hM_p hp_not_pi
  obtain ⟨Q, hQ_hall, hQ_inv⟩ := exists_aInvariant_hall hCop π
  have hQ_M_bot : Q ⊓ M = ⊥ :=
    inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem hQ_hall.1 hM_p hp_not_pi
  have hQbar_top : Q.map (QuotientGroup.mk' M) = ⊤ := by
    have htop_pi :
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (⊤ : Subgroup (G ⧸ M)) := by
      intro q hq
      rw [Subgroup.card_top] at hq
      exact hquot_pi q hq
    have hQbar_hall :
        OddOrder.Isaacs.Ch03.IsHallSubgroup π (Q.map (QuotientGroup.mk' M)) :=
      hQ_hall.map_quotient
    exact eq_top_iff.mpr
      (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.normal_le_hall htop_pi hQbar_hall)
  have hQM_top : Q ⊔ M = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hgbar : (QuotientGroup.mk' M) g ∈ Q.map (QuotientGroup.mk' M) := by
      rw [hQbar_top]
      trivial
    rw [Subgroup.mem_map] at hgbar
    obtain ⟨q, hqQ, hqeq⟩ := hgbar
    have hm : q⁻¹ * g ∈ M := by
      apply (QuotientGroup.eq_one_iff (N := M) (q⁻¹ * g)).mp
      change (QuotientGroup.mk' M) (q⁻¹ * g) = 1
      rw [map_mul, map_inv, hqeq, inv_mul_cancel]
    have hg : g = q * (q⁻¹ * g) := by group
    rw [hg]
    exact Subgroup.mul_mem_sup hqQ hm
  let U : Subgroup G := K ⊔ M
  have hK_le_U : K ≤ U := le_sup_left
  have hM_le_U : M ≤ U := le_sup_right
  have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U :=
    OddOrder.Isaacs.Ch03.IsAInvariant.sup hK_inv hM_inv
  have hK_M_bot : K ⊓ M = ⊥ :=
    inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem hK_pi hM_p hp_not_pi
  have hK_comp : Subgroup.IsComplement' (M.subgroupOf U) (K.subgroupOf U) := by
    refine isComplement_subgroupOf_of_disjoint_mul_eq_univ hK_le_U hM_le_U hK_M_bot ?_
    intro x hxU
    have hx : (x : G) ∈ M ⊔ K := by
      rw [sup_comm]
      exact hxU
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨m, hmM, k, hkK, hmk⟩ := hx
    exact ⟨m, hmM, k, hkK, hmk⟩
  have hKsub_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π (K.subgroupOf U) :=
    isHallSubgroup_subgroupOf_of_complement_pi_pi' hK_le_U hM_le_U hK_pi hM_pi' hK_comp
  let QKU : Subgroup G := Q ⊓ U
  have hQKU_le_U : QKU ≤ U := inf_le_right
  have hQKU_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π QKU :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le inf_le_left hQ_hall.1
  have hQKU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ QKU :=
    OddOrder.Isaacs.Ch03.IsAInvariant.inf hQ_inv hU_inv
  have hQKU_M_bot : QKU ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQM : x ∈ Q ⊓ M := ⟨hx.1.1, hx.2⟩
    rw [hQ_M_bot] at hxQM
    exact hxQM
  have hQKU_comp : Subgroup.IsComplement' (M.subgroupOf U) (QKU.subgroupOf U) := by
    refine isComplement_subgroupOf_of_disjoint_mul_eq_univ hQKU_le_U hM_le_U hQKU_M_bot ?_
    intro x hxU
    have hxQM : (x : G) ∈ Q ⊔ M := by
      rw [hQM_top]
      trivial
    rw [Subgroup.mem_sup_of_normal_right] at hxQM
    obtain ⟨q, hqQ, m, hmM, hqm⟩ := hxQM
    have hqU : q ∈ U := by
      have hq_eq : q = (x : G) * m⁻¹ := by
        rw [← hqm]
        group
      rw [hq_eq]
      exact U.mul_mem hxU (U.inv_mem (hM_le_U hmM))
    have hm_conj : q * m * q⁻¹ ∈ M :=
      (inferInstance : M.Normal).conj_mem m hmM q
    refine ⟨q * m * q⁻¹, hm_conj, q, ⟨hqQ, hqU⟩, ?_⟩
    rw [← hqm]
    group
  have hQKUsub_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π (QKU.subgroupOf U) :=
    isHallSubgroup_subgroupOf_of_complement_pi_pi' hQKU_le_U hM_le_U hQKU_pi hM_pi'
      hQKU_comp
  have hKsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hU_inv.restrict (K.subgroupOf U) :=
    isAInvariant_subgroupOf_restrict hU_inv hK_inv
  have hQKUsub_inv : OddOrder.Isaacs.Ch03.IsAInvariant hU_inv.restrict (QKU.subgroupOf U) :=
    isAInvariant_subgroupOf_restrict hU_inv hQKU_inv
  have hCop_U : Nat.Coprime (Nat.card A) (Nat.card U) :=
    coprime_card_subgroup_of_coprime hCop
  obtain ⟨c, hc_fix, hc_conj⟩ :=
    aInvariant_hall_conj (G := U) (A := A) (φ := hU_inv.restrict) hCop_U
      hQKUsub_hall hKsub_hall hQKUsub_inv hKsub_inv
  let cG : G := c
  have hc_fix_G : ∀ a : A, (φ a) cG = cG := by
    intro a
    have h := congrArg Subtype.val (hc_fix a)
    simpa [cG, OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val] using h
  refine ⟨MulAut.conj cG • Q, ?_, ?_, ?_⟩
  · exact isHallSubgroup_mulAut_smul (MulAut.conj cG) hQ_hall
  · exact isAInvariant_mulAut_conj_smul_of_fixed hQ_inv hc_fix_G
  · intro k hkK
    rw [mulAut_smul_eq_map, Subgroup.mem_map]
    let kU : U := ⟨k, hK_le_U hkK⟩
    have hkU : kU ∈ K.subgroupOf U := by
      change (kU : G) ∈ K
      exact hkK
    have hkU_conj : kU ∈ MulAut.conj c • (QKU.subgroupOf U) := by
      rw [hc_conj]
      exact hkU
    rw [mulAut_smul_eq_map, Subgroup.mem_map] at hkU_conj
    obtain ⟨y, hyQKU, hy_eq⟩ := hkU_conj
    refine ⟨(y : G), ?_, ?_⟩
    · have hyQKU_G : (y : G) ∈ QKU := hyQKU
      exact hyQKU_G.1
    · change (MulAut.conj cG) (y : G) = k
      simpa [cG] using congrArg Subtype.val hy_eq


open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom) in
/-- Induction kernel for BG Prop. 1.5(b). -/
private theorem aInvariant_piSubgroup_le_aInvariant_hall_aux :
    ∀ n : ℕ,
      ∀ (G A : Type*) [Group G] [Finite G] [IsSolvable G]
        [Group A] [Finite A],
        Nat.card G ≤ n → ∀ {φ : A →* MulAut G}
        (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
        {π : Set ℕ} {K : Subgroup G},
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K →
        OddOrder.Isaacs.Ch03.IsAInvariant φ K →
        ∃ H : Subgroup G,
          OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
            OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H := by
  intro n
  induction n with
  | zero =>
      intro G A _ _ _ _ _ hcard φ _hCop π K hK_pi hK_inv
      have hpos : 0 < Nat.card G := Nat.card_pos
      omega
  | succ n ih =>
      intro G A _ _ _ _ _ hcard φ hCop π K hK_pi hK_inv
      by_cases hsmall : Nat.card G ≤ n
      · exact ih G A hsmall hCop hK_pi hK_inv
      by_cases hG_pi : ∀ p ∈ (Nat.card G).primeFactors, p ∈ π
      · refine ⟨⊤, ?_, OddOrder.Isaacs.Ch03.IsAInvariant.top φ, le_top⟩
        exact (OddOrder.Isaacs.Ch03.IsHallSubgroup.top_iff (G := G) π).mpr hG_pi
      have hG_card_ne_one : Nat.card G ≠ 1 := by
        intro hcard_one
        exact hG_pi (by
          intro p hp
          rw [hcard_one, Nat.primeFactors_one] at hp
          simp at hp)
      have hG_card_gt_one : 1 < Nat.card G :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_card_ne_one⟩
      haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hG_card_gt_one
      obtain ⟨M, hM_normal, hM_inv, hM_ne_bot, hM_min⟩ :=
        exists_minimal_normal_aInvariant (G := G) (A := A) (φ := φ)
      haveI : M.Normal := hM_normal
      obtain ⟨p, hp_prime, hM_p⟩ :=
        exists_prime_isPGroup_of_minimal_normal_aInvariant hM_inv hM_ne_bot hM_min
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hquot_lt : Nat.card (G ⧸ M) < Nat.card G :=
        card_quotient_lt_card_of_ne_bot hM_ne_bot
      have hquot_le_n : Nat.card (G ⧸ M) ≤ n := by
        omega
      have hKbar_pi :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' M)) :=
        isPiGroup_map_mk' (N := M) hK_pi
      have hKbar_inv :
          OddOrder.Isaacs.Ch03.IsAInvariant
            (quotientMulAutHom hM_inv) (K.map (QuotientGroup.mk' M)) :=
        isAInvariant_map_mk' hM_inv hK_inv
      have hCop_quot : Nat.Coprime (Nat.card A) (Nat.card (G ⧸ M)) :=
        coprime_card_quotient_of_coprime (N := M) hCop
      obtain ⟨Hbar, hHbar_hall, hHbar_inv, hKbar_le⟩ :=
        ih (G ⧸ M) A hquot_le_n hCop_quot hKbar_pi hKbar_inv
      obtain ⟨H, hH_inv, hK_le_H, hH_index, hH_eq⟩ :=
        quotient_hall_preimage_frame hM_inv hHbar_hall hHbar_inv hKbar_le
      by_cases hH_top : H = ⊤
      · have hHbar_top : Hbar = ⊤ := by
          apply eq_top_iff.mpr
          intro y hy
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := M) y
          have hgH : g ∈ H := by
            rw [hH_top]
            trivial
          rw [hH_eq] at hgH
          exact hgH
        have hquot_pi : ∀ q ∈ (Nat.card (G ⧸ M)).primeFactors, q ∈ π := by
          have htop_hall :
              OddOrder.Isaacs.Ch03.IsHallSubgroup π (⊤ : Subgroup (G ⧸ M)) := by
            simpa [hHbar_top] using hHbar_hall
          exact (OddOrder.Isaacs.Ch03.IsHallSubgroup.top_iff (G := G ⧸ M) π).mp
            htop_hall
        exact top_preimage_branch_frame hCop hG_pi hM_inv hM_p hquot_pi hK_pi hK_inv
      · have hH_le_n : Nat.card H ≤ n := by
          have hH_lt : Nat.card H < Nat.card G :=
            subgroup_card_lt_card_of_ne_top hH_top
          omega
        have hCop_H : Nat.Coprime (Nat.card A) (Nat.card H) :=
          coprime_card_subgroup_of_coprime (H := H) hCop
        have hIH_H : ∀ {Ksub : Subgroup H},
            OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π Ksub →
              OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict Ksub →
              ∃ L : Subgroup H,
                OddOrder.Isaacs.Ch03.IsHallSubgroup π L ∧
                  OddOrder.Isaacs.Ch03.IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L := by
          intro Ksub hKsub_pi hKsub_inv
          exact ih H A hH_le_n hCop_H hKsub_pi hKsub_inv
        exact proper_overgroup_branch_frame hH_inv hH_index hK_pi hK_inv hK_le_H hIH_H

/-- **BG Prop 1.5(b)**: if a finite solvable group `G` is acted on by a finite operator
 group `A` with coprime order, every `A`-invariant `π`-subgroup is contained in an
`A`-invariant Hall `π`-subgroup. -/
theorem aInvariant_piSubgroup_le_aInvariant_hall
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set ℕ} {K : Subgroup G}
    (hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π K)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsHallSubgroup π H ∧
        OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H :=
  aInvariant_piSubgroup_le_aInvariant_hall_aux (Nat.card G) G A le_rfl hCop hK_pi hK_inv

/-- Complementary Hall subgroups have coprime orders. -/
private theorem hall_compl_card_coprime {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.Coprime (Nat.card K) (Nat.card H) := by
  have hHK : Nat.Coprime (Nat.card H) (Nat.card K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne'
      hH.1
      (fun p hp => by simpa using hK.1 p hp)
  exact hHK.symm

/-- The index of a `π'`-Hall subgroup and the index of a `π`-Hall subgroup are coprime. -/
private theorem hall_compl_index_coprime {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.Coprime K.index H.index := by
  refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite ?_ hH.2
  intro p hp
  by_contra hp_not
  exact hK.2 p hp hp_not

/-- If `K` is Hall `π'` and `H` is Hall `π`, then `|K| * |H| = |G|`. -/
private theorem hall_compl_card_mul {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Nat.card K * Nat.card H = Nat.card G := by
  have h_card_cop : Nat.Coprime (Nat.card K) (Nat.card H) :=
    hall_compl_card_coprime hK hH
  have h_index_cop : Nat.Coprime H.index K.index :=
    (hall_compl_index_coprime hK hH).symm
  have hK_dvd_Hindex : Nat.card K ∣ H.index := by
    have hdiv : Nat.card K ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index H]
      exact Subgroup.card_subgroup_dvd_card K
    rw [mul_comm] at hdiv
    exact h_card_cop.dvd_of_dvd_mul_right hdiv
  have hHindex_dvd_K : H.index ∣ Nat.card K := by
    have hdivG : H.index ∣ Nat.card G :=
      ⟨Nat.card H, by rw [mul_comm, Subgroup.card_mul_index H]⟩
    have hdiv : H.index ∣ Nat.card K * K.index := by
      rwa [← Subgroup.card_mul_index K] at hdivG
    exact h_index_cop.dvd_of_dvd_mul_right hdiv
  have hK_card_eq : Nat.card K = H.index :=
    Nat.dvd_antisymm hK_dvd_Hindex hHindex_dvd_K
  calc
    Nat.card K * Nat.card H = H.index * Nat.card H := by rw [hK_card_eq]
    _ = Nat.card H * H.index := by rw [mul_comm]
    _ = Nat.card G := Subgroup.card_mul_index H

/-- Complementary Hall subgroups multiply bijectively. This is the Lean form of BG's
`G = K H` line in Prop. 1.5(e).

De-privatised (2026-06-20) for use in BG Theorem 15.2 (`S15_MF`), where the `K`-invariant
`{q}ᶜ`-Hall complement `D` of the normal Sylow `q`-subgroup `Q` of `M_σ` is built via
`exists_aInvariant_hall` and shown to complement `Q` by this lemma. -/
theorem hall_compl_isComplement {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {K H : Subgroup G}
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) :
    Subgroup.IsComplement' K H :=
  Subgroup.isComplement'_of_coprime (hall_compl_card_mul hK hH)
    (hall_compl_card_coprime hK hH)

/-- **BG Prop 1.5(e)**: if `C_G(A)` contains a Hall `π'`-subgroup, then the action
commutator `[G,A]` lies in the `π`-core of `G`.

The containment proof follows BG L412-L414. Choose an `A`-invariant Hall `π`-subgroup `H`.
For `g = k*h` with `k ∈ K ≤ C_G(A)` and `h ∈ H`, each generator
`g⁻¹ * (φ a) g` of `[G,A]` reduces to `h⁻¹ * (φ a) h ∈ H`; hence `[G,A] ≤ H`.
Since `[G,A]` is normal, it is a normal `π`-subgroup and therefore lies in `O_π(G)`. -/
theorem actionCommutator_le_oPiCore_of_fixedPoints_contains_hallComplement
    {G A : Type*} [Group G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set ℕ} {K : Subgroup G}
    (hK_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup {p | p ∉ π} K)
    (hK_le_fixed : K ≤ Subgroup.fixedPointsOfMulAut φ) :
    OddOrder.Isaacs.Ch04.actionCommutator φ ≤ OddOrder.Isaacs.Ch03.oPiCore π G := by
  obtain ⟨H, hH_hall, hH_inv⟩ := exists_aInvariant_hall hCop π
  have hCompl : Subgroup.IsComplement' K H :=
    hall_compl_isComplement hK_hall hH_hall
  have hAC_le_H : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ H := by
    exact (OddOrder.Isaacs.Ch04.actionCommutator_le_iff_left φ H).mpr
      (fun a g => by
        obtain ⟨⟨k, h⟩, hg⟩ := hCompl.2 g
        have hk_fix : (φ a) (k : G) = k :=
          (Subgroup.mem_fixedPointsOfMulAut.mp (hK_le_fixed k.2)) a
        have hh_smul : (φ a) (h : G) ∈ H := hH_inv.smul_mem a h.2
        rw [← hg]
        change (((k : G) * (h : G))⁻¹ * (φ a) ((k : G) * (h : G))) ∈ H
        rw [map_mul, hk_fix]
        have hcalc :
            ((k : G) * (h : G))⁻¹ * ((k : G) * (φ a) (h : G)) =
              (h : G)⁻¹ * (φ a) (h : G) := by
          group
        rw [hcalc]
        exact H.mul_mem (H.inv_mem h.2) hh_smul)
  have hAC_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π
        (OddOrder.Isaacs.Ch04.actionCommutator φ) :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le hAC_le_H hH_hall.1
  exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hAC_pi


/-- **BG Prop 1.6(c)**: if `[G,A,A] = 1`, then `[G,A] = 1`.

This is the immediate consequence of Isaacs Lemma 4.29, represented in the semidirect-product
`Γ = G ⋊[φ] A` form used by the Ch.4 API. -/
theorem iterCommutator_inl_inr_one_eq_bot_of_two_eq_bot
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    (h_two : OddOrder.Isaacs.Ch04.iterCommutator
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range 2 = ⊥) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range 1 = ⊥ := by
  have h_eq := OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one
    (φ := φ) hCop hSolv
  rw [← h_eq, h_two]

/-- **BG Prop 1.6(d)**: if `G` is abelian, then
`G = C_G(A) × [G,A]`.

Lean packages the internal direct product as a complement: multiplication from
`C_G(A) × [G,A]` onto `G` is bijective. -/
theorem fixedPoints_isComplement_actionCommutator_of_abelian
    {G A : Type*} [CommGroup G] [Finite G] [IsSolvable G]
    [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.IsComplement' (Subgroup.fixedPointsOfMulAut φ)
      (OddOrder.Isaacs.Ch04.actionCommutator φ) := by
  have hsup : Subgroup.fixedPointsOfMulAut φ ⊔
      OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ :=
    OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := φ) hCop (Or.inr inferInstance)
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓
      OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    exact hinf
  · rw [Set.eq_univ_iff_forall]
    intro g
    have hg : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔
        OddOrder.Isaacs.Ch04.actionCommutator φ := by
      rw [hsup]
      trivial
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨c, hc, d, hd, hcd⟩ := hg
    exact ⟨c, hc, d, hd, hcd⟩

end AInvariantHall

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
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le).is_comm.comm
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

/-- **Element form of BG Theorem 1.8 (Burnside)**: a `p'`-order automorphism `f` of a finite
`p`-group `H` all of whose powers act trivially modulo `Φ(H)` is the identity.

The elementwise companion of `burnside_operator`: apply it to the cyclic operator group
`⟨f⟩ = Subgroup.zpowers f` (coprimality of `|⟨f⟩|` with `|H| = pⁿ` follows from the `p'`-order
of `f`).  Used by BG Theorem 3.6 (3.9) (`S03f_Prelim`) and Lemma 4.17 (`S04_PGroupsSmallRank`). -/
theorem mulAut_eq_one_of_coprime_orderOf_of_frattini {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] (hH : IsPGroup p H)
    (f : MulAut H) (hcop : Nat.Coprime (orderOf f) p)
    (htriv : ∀ z : ℤ, ∀ r : H, ∃ x ∈ _root_.frattini H, (f ^ z) r = r * x) :
    f = 1 := by
  classical
  set B : Subgroup (MulAut H) := Subgroup.zpowers f with hB
  set ψ : ↥B →* MulAut H := B.subtype with hψ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  have hcop' : Nat.Coprime (Nat.card ↥B) (Nat.card H) := by
    rw [hB, Nat.card_zpowers, hn]
    exact Nat.Coprime.pow_right n hcop
  have htriv' : ∀ b : ↥B, ∀ r : H, ∃ x ∈ _root_.frattini H, (ψ b) r = r * x := by
    rintro ⟨b, hb⟩ r
    rw [hB, Subgroup.mem_zpowers_iff] at hb
    obtain ⟨z, rfl⟩ := hb
    exact htriv z r
  have hconc := burnside_operator hH (φ := ψ) hcop' htriv'
  ext r
  rw [MulAut.one_apply]
  exact hconc ⟨f, Subgroup.mem_zpowers f⟩ r

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

open OddOrder.Isaacs.Ch03 in
/-- **BG Lemma 1.9 (多段一般形, coprime 核)**: 有限群 `K` に有限群 `A` が
`ψ : A →* MulAut K` で coprime (`(|A|,|K|)=1`) 作用し, `A` または `K` が可解とする.
`K` の正規降鎖 `s` (`Antitone`, `s 0 = ⊤`, `s n = ⊥`, 各 `s i ◁ K`, `ψ`-不変) を `A` が
**stabilize** (各 factor `s i / s (i+1)` 上自明: `∀ x ∈ s i, ∃ y ∈ s (i+1), ψ a x = x * y`)
するなら, `ψ` は自明 (`∀ a, ψ a = 1`).

BG Lem 1.9 の原 statement「`G` solvable π-群, `A` が normal series を stabilize ⇒
`A/C_A(G)` は π-群」は, π'-元 `a` に対し `⟨a⟩` を本補題に渡す (coprime 性 = π'-性) ことで
elementwise に従う (§5 Thm 5.5 がこの形で使用)。AppA (PSTAB) の chain-stabilizer 補題も
本補題経由 (旧 AppA private から §1 へ昇格, 2026-06-02)。

`coprime_actsTrivially_of_normal_and_quotient` (2-step) を `↥(s i)` 上へ
`IsAInvariant.restrict` で制限し, 鎖を `m`-bound 付き上向き帰納で下降して `s 0 = ⊤` に到達. -/
theorem coprime_stabilizes_chain_trivial
    {K : Type*} [Group K] [Finite K] {A : Type*} [Group A] [Finite A]
    (ψ : A →* MulAut K) (hcop : (Nat.card A).Coprime (Nat.card K))
    (hsolv : IsSolvable A ∨ IsSolvable K)
    (s : ℕ → Subgroup K) (hanti : Antitone s) (hs0 : s 0 = ⊤) {n : ℕ} (hsn : s n = ⊥)
    (hnorm : ∀ i, (s i).Normal)
    (hinv : ∀ i, IsAInvariant ψ (s i))
    (htriv : ∀ i, ∀ a : A, ∀ x ∈ s i, ∃ y ∈ s (i + 1), (ψ a) x = x * y) :
    ∀ a : A, ψ a = 1 := by
  -- One step down: trivial on `s (i+1)` ⇒ trivial on `s i` (via the coprime 2-step lemma).
  have stepdown : ∀ i, (∀ a : A, ∀ x, x ∈ s (i + 1) → (ψ a) x = x) →
      ∀ a : A, ∀ x, x ∈ s i → (ψ a) x = x := by
    intro i hIH
    haveI hN1 : (s (i + 1)).Normal := hnorm (i + 1)
    have hcopi : (Nat.card A).Coprime (Nat.card ↥(s i)) :=
      hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card (s i))
    have hsolvi : IsSolvable A ∨ IsSolvable ↥(s i) := by
      rcases hsolv with h | h
      · exact Or.inl h
      · haveI := h; exact Or.inr inferInstance
    have hInvN : IsAInvariant ((hinv i).restrict) ((s (i + 1)).subgroupOf (s i)) := by
      rw [isAInvariant_iff_smul_mem]
      intro a' g hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [IsAInvariant.restrict_apply_val]
      exact (hinv (i + 1)).smul_mem a' hg
    have htrivN : ∀ a' : A, ∀ g ∈ (s (i + 1)).subgroupOf (s i),
        ((hinv i).restrict a') g = g := by
      intro a' g hg
      rw [Subgroup.mem_subgroupOf] at hg
      exact Subtype.ext (by rw [IsAInvariant.restrict_apply_val]; exact hIH a' g.val hg)
    have htrivQ : ∀ a' : A, ∀ g : ↥(s i),
        ∃ y ∈ (s (i + 1)).subgroupOf (s i), ((hinv i).restrict a') g = g * y := by
      intro a' g
      obtain ⟨y, hy_mem, hy_eq⟩ := htriv i a' g.val g.property
      refine ⟨⟨y, hanti (Nat.le_succ i) hy_mem⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact hy_mem
      · exact Subtype.ext (by rw [IsAInvariant.restrict_apply_val, Subgroup.coe_mul]; exact hy_eq)
    have hconc := coprime_actsTrivially_of_normal_and_quotient
      (φ := (hinv i).restrict) hcopi hsolvi hInvN htrivN htrivQ
    intro a x hx
    have h2 := congrArg Subtype.val (hconc a ⟨x, hx⟩)
    rw [IsAInvariant.restrict_apply_val] at h2
    exact h2
  -- `s i = ⊥` for `i ≥ n`, and `stepdown` propagates triviality down to `s 0 = ⊤`.
  have key : ∀ m i, n ≤ i + m → ∀ a : A, ∀ x, x ∈ s i → (ψ a) x = x := by
    intro m
    induction m with
    | zero =>
      intro i hi a x hx
      have hxn : x ∈ s n := hanti (by simpa using hi) hx
      rw [hsn, Subgroup.mem_bot] at hxn
      subst hxn
      exact map_one (ψ a)
    | succ m ih =>
      intro i hi a x hx
      exact stepdown i (ih (i + 1) (by omega)) a x hx
  intro a
  refine MulEquiv.ext (fun x => ?_)
  show (ψ a) x = x
  exact key n 0 (by omega) a x (by rw [hs0]; exact Subgroup.mem_top x)

open OddOrder.Isaacs.Ch03 (IsAInvariant) in
/-- 演算子作用 `φ : A →* MulAut G` を `A`-不変部分群 `H` へ制限し `A →* MulAut ↥H` を得る.
Prop 1.10 等で `A` の作用を `N_G(C)` などの不変部分群上で扱うための橋. -/
def restrictAction {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : A →* MulAut ↥H where
  toFun a :=
    { toFun := fun g => ⟨φ a g, hH.smul_mem a g.2⟩
      invFun := fun g => ⟨(φ a)⁻¹ g, hH.inv_smul_mem a g.2⟩
      left_inv := fun g => Subtype.ext (MulAut.inv_apply_self G (φ a) g.1)
      right_inv := fun g => Subtype.ext (MulAut.apply_inv_self G (φ a) g.1)
      map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.1 y.1) }
  map_one' := MulEquiv.ext fun g => Subtype.ext <| by
    change (φ 1) g.1 = g.1; rw [map_one, MulAut.one_apply]
  map_mul' a b := MulEquiv.ext fun g => Subtype.ext <| by
    change (φ (a * b)) g.1 = (φ a) ((φ b) g.1); rw [map_mul, MulAut.mul_apply]

open OddOrder.Isaacs.Ch03 (IsAInvariant) in
@[simp]
theorem restrictAction_apply {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) (a : A) (g : ↥H) :
    (restrictAction hH a g : G) = φ a g := rfl

open OddOrder.Isaacs.Ch03 (IsAInvariant) in
/-- **BG Proposition 1.10** (mmd L445): `A` が冪零群 `G` 上の演算子群で `(|A|,|G|)=1`.
`C := C_G(A)` (`fixedPointsOfMulAut φ`) とおく. `C_G(C) ⊆ C` なら `A` は `G` 上自明に作用.

**証明** (BG): `x ∈ N_G(C)`, `a ∈ A`, `y ∈ C` に対し `xᵃx⁻¹ ∈ C_G(C) ⊆ C` を示すと `A` が
`N_G(C)/C` を中心化. `C` は `A`-fixed なので Lemma 1.9
(`coprime_actsTrivially_of_normal_and_quotient`) で `A` は `N_G(C)` 上自明 ⇒ `N_G(C) ⊆ C`
⇒ `C` self-normalizing ⇒ (冪零の normalizer condition) `C = ⊤` ⇒ `A` は `G` 上自明. -/
theorem coprime_nilpotent_acts_trivially_of_centralizer_self
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [Group.IsNilpotent G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set G)
        ≤ Subgroup.fixedPointsOfMulAut φ) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  set C := Subgroup.fixedPointsOfMulAut φ with hC
  -- `C` is `A`-invariant (fixed pointwise).
  have hC_inv : IsAInvariant φ C := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
    intro a'
    rw [hg a, hg a']
  -- `N := N_G(C)` is `A`-invariant, contains `C`.
  have hNC_inv : IsAInvariant φ (Subgroup.normalizer (C : Set G)) := hC_inv.normalizer
  have hC_le_NC : C ≤ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer
  haveI : (C.subgroupOf (Subgroup.normalizer (C : Set G))).Normal := Subgroup.normal_in_normalizer
  -- coprimality / solvability descend to `↥N`.
  have hcardNC : Nat.card ↥(Subgroup.normalizer (C : Set G)) ∣ Nat.card G :=
    (Subgroup.normalizer (C : Set G)).card_subgroup_dvd_card
  have hCopNC : Nat.Coprime (Nat.card A) (Nat.card ↥(Subgroup.normalizer (C : Set G))) :=
    hCop.coprime_dvd_right hcardNC
  haveI : IsSolvable G := inferInstance
  -- engine hypotheses (acting via `restrictAction hNC_inv` on `↥N`).
  have hNinv_eng : IsAInvariant (restrictAction hNC_inv)
      (C.subgroupOf (Subgroup.normalizer (C : Set G))) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    have hx' : (x : G) ∈ C := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf, restrictAction_apply]
    exact hC_inv.smul_mem a hx'
  have hTrivN_eng : ∀ a : A, ∀ x ∈ C.subgroupOf (Subgroup.normalizer (C : Set G)),
      (restrictAction hNC_inv a) x = x := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx
    apply Subtype.ext
    rw [restrictAction_apply]
    exact (Subgroup.mem_fixedPointsOfMulAut.mp hx) a
  have hQuot_eng : ∀ a : A, ∀ x : ↥(Subgroup.normalizer (C : Set G)),
      ∃ y ∈ C.subgroupOf (Subgroup.normalizer (C : Set G)),
        (restrictAction hNC_inv a) x = x * y := by
    intro a x
    set g : G := x.1 with hg
    have hgNC : g ∈ Subgroup.normalizer (C : Set G) := x.2
    -- (i) `t := φ a g * g⁻¹` centralizes `C`, hence `t ∈ C`.
    have htC : (φ a) g * g⁻¹ ∈ C := by
      apply hCC
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      have hyc : g⁻¹ * y * g ∈ C := by
        have h := Subgroup.mem_normalizer_iff.mp (inv_mem hgNC) y
        rw [inv_inv] at h
        exact h.mp hy
      have hfix : (φ a) (g⁻¹ * y * g) = g⁻¹ * y * g := by
        rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hyc; exact hyc a
      rw [map_mul, map_mul, map_inv] at hfix
      have hyfix : (φ a) y = y := by
        rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hy; exact hy a
      rw [hyfix] at hfix
      -- `hfix : (φ a g)⁻¹ * y * (φ a g) = g⁻¹ * y * g` ⇒ `Commute (φ a g * g⁻¹) y`.
      have key : ((φ a) g * g⁻¹) * y * ((φ a) g * g⁻¹)⁻¹ = y :=
        calc ((φ a) g * g⁻¹) * y * ((φ a) g * g⁻¹)⁻¹
            = (φ a) g * (g⁻¹ * y * g) * ((φ a) g)⁻¹ := by group
          _ = (φ a) g * (((φ a) g)⁻¹ * y * ((φ a) g)) * ((φ a) g)⁻¹ := by rw [← hfix]
          _ = y := by group
      exact (mul_inv_eq_iff_eq_mul.mp key).symm
    -- (ii) `g⁻¹ * φ a g ∈ C` (conjugate of `t` by `g⁻¹`, `C` normal in `N_G(C)`).
    have hyC : g⁻¹ * (φ a) g ∈ C := by
      have h := Subgroup.mem_normalizer_iff.mp (inv_mem hgNC) ((φ a) g * g⁻¹)
      rw [inv_inv] at h
      have h2 : g⁻¹ * ((φ a) g * g⁻¹) * g ∈ C := h.mp htC
      rwa [show g⁻¹ * ((φ a) g * g⁻¹) * g = g⁻¹ * (φ a) g by group] at h2
    refine ⟨⟨g⁻¹ * (φ a) g, hC_le_NC hyC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hyC
    · apply Subtype.ext
      rw [restrictAction_apply]
      simp only [Subgroup.coe_mul]
      rw [← hg]; group
  -- engine ⇒ `A` trivial on `N_G(C)`.
  have hTrivNC : ∀ a : A, ∀ x : ↥(Subgroup.normalizer (C : Set G)),
      (restrictAction hNC_inv a) x = x :=
    coprime_actsTrivially_of_normal_and_quotient hCopNC (Or.inr inferInstance)
      hNinv_eng hTrivN_eng hQuot_eng
  -- `N_G(C) ⊆ C`, so `C` is self-normalizing.
  have hNC_le_C : Subgroup.normalizer (C : Set G) ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    exact congrArg Subtype.val (hTrivNC a ⟨g, hg⟩)
  -- nilpotent ⇒ self-normalizing subgroup is `⊤`.
  have hNCeqC : Subgroup.normalizer (C : Set G) = C := le_antisymm hNC_le_C hC_le_NC
  have hC_top : C = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) C hNCeqC
  intro a g
  have hmem : g ∈ C := hC_top ▸ Subgroup.mem_top g
  rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hmem
  exact hmem a

/-! ## §1D: p-odd action (Thm 1.11, Cor 1.12, Thm 1.13 Thompson critical)

BG Theorem 1.13 (J. G. Thompson). 証明本体は Gorenstein "Finite Groups" Thm 5.3.11
(critical subgroup の存在) + 5.3.13 (`Ω₁(C)` の四性質) で,
`OddOrder.GroupTheory.CriticalSubgroup` に段階実装済 (`isCritical_exists` +
`IsCritical.omega1*`). 本節では `H = Ω₁(C)` を取り出して四性質を束ねる. -/

open OddOrder.GroupTheory in
/-- **BG Theorem 1.13** (J. G. Thompson) — `references/bg/local-analysis.mmd:461`.
**Gorenstein "Finite Groups" Theorem 5.3.13** (p. 186) の Lean 化.

`p` が奇素数で `G` が非自明な `p`-群ならば, `G` は次の四性質を持つ characteristic
subgroup `H` (= ある critical subgroup `C` の `Ω₁(C)`) を含む:

* (a) `[H, G] ⊆ Z(H)`;
* (b) `H` の nilpotence class は `≤ 2` (`commutator ↥H ≤ Z(↥H)`);
* (c) `H` の exponent は `p`;
* (d) `C_{Aut G}(H)` (= `H` を pointwise に固定する `Aut G` の部分群) は `p`-群.

証明: `isCritical_exists` で critical subgroup `C` を取り `H = Ω₁(C)`
(`omega1Map C p`) とする. (a)=`commutator_top_le_center_omega1Map` (BG L468 の
三段包含), (b)=`omega1Map_class_le_two` (`H ≤ C` から継承), (c)=`exponent_omega1Map`
(Gorenstein 5.3.9(i)), (d)=`isPGroup_autCentralizer_omega1Map` (Gorenstein 5.3.10
で `Ω₁(C)` 固定 ⇒ `C` 上自明, 5.3.11(iv) で `G` 上自明). characteristic は
`omega1Map_characteristic` (char-in-char). -/
theorem thompson_critical_omega {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) (hG : IsPGroup p G) :
    ∃ H : Subgroup G,
      H.Characteristic
      ∧ ⁅H, (⊤ : Subgroup G)⁆ ≤ (Subgroup.center ↥H).map H.subtype
      ∧ _root_.commutator ↥H ≤ Subgroup.center ↥H
      ∧ Monoid.exponent ↥H = p
      ∧ IsPGroup p (autCentralizer H) := by
  obtain ⟨C, hC⟩ := isCritical_exists hG
  refine ⟨omega1Map C p, hC.omega1Map_characteristic, ?_,
    hC.omega1Map_class_le_two, hC.exponent_omega1Map hp_odd hG,
    hC.isPGroup_autCentralizer_omega1Map hp_odd hG⟩
  -- (a) `[H, G] ⊆ Z(H)` from the symmetric `[G, H]` via `commutator_comm`.
  rw [Subgroup.commutator_comm]
  exact hC.commutator_top_le_center_omega1Map

open OddOrder.Isaacs.Ch03 (IsAInvariant) in
/-- **BG Corollary 1.12** (mmd L457): `p` odd, `G` a `p`-group, `E` an elementary abelian
subgroup, `A` a `p'`-group of operators on `G` (via `φ : A →* MulAut G`). If `A` fixes every
order-`p` element of `C_G(E)`, then `A` acts trivially on `G`.

**証明** (BG): `C := C_G(A)` (`fixedPointsOfMulAut φ`) とおく.
- `E ⊆ C`: `E` の各元 `e` は `E` を中心化し (`E` abelian) かつ `eᵖ = 1` (`E` elementary
  abelian) なので, `e ∈ C_G(E)` の order-`p` 元として仮定 `h_fix` で `A` に固定される,
  すなわち `e ∈ C`.
- `D := C_G(C)` は `A`-不変 (`IsAInvariant.centralizer`) で, `E ⊆ C` より `D ⊆ C_G(E)`
  (centralizer の反単調性). `D` は `G` の部分群として `p`-群 (`hG.to_subgroup`).
- `D` の order-`p` 元 `ḡ` は `(ḡ : G) ∈ D ⊆ C_G(E)` で `(ḡ)ᵖ = 1` ゆえ `h_fix` で `A` に固定;
  ゆえに `restrictAction` 経由の `↥D` 上作用は全 order-`p` 元を固定. BG Thm 1.11 = Isaacs
  Thm 4.36 (`isaacs_thm_4_36`) を `↥D` 上の制限作用に適用すると `A` は `↥D` 上自明に作用し,
  これは `D ⊆ C`, すなわち `C_G(C) ⊆ C` を与える.
- 最後に `G` は冪零 (`hG.isNilpotent`), `(|A|, |G|) = 1`, `C_G(C) ⊆ C` の三条件で BG
  Prop 1.10 (`coprime_nilpotent_acts_trivially_of_centralizer_self`) を適用し結論. -/
theorem corollary_1_12 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (φ : A →* MulAut G) {E : Subgroup G} (hE : E.IsElementaryAbelian p)
    (h_fix : ∀ g : G, g ∈ Subgroup.centralizer (E : Set G) → g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  set C := Subgroup.fixedPointsOfMulAut φ with hC
  -- `C` is `A`-invariant (fixed pointwise), as in Prop 1.10.
  have hC_inv : IsAInvariant φ C := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
    intro a'
    rw [hg a, hg a']
  -- Step 1: `E ≤ C`.
  have hE_le_C : E ≤ C := by
    intro e he
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    -- `e ∈ C_G(E)`: `e` commutes with every element of `E` (`E` abelian).
    have he_cent : e ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      have := hE.comm ⟨e, he⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this.symm
    -- `e ^ p = 1` (`E` elementary abelian).
    have he_pow : e ^ p = 1 := by
      have h := congrArg (fun x : ↥E => (x : G)) (hE.pow_eq_one ⟨e, he⟩)
      simpa using h
    exact h_fix e he_cent he_pow
  -- Step 2/3: `D := C_G(C)` is `A`-invariant and `D ≤ C_G(E)`.
  set D := Subgroup.centralizer (C : Set G) with hD
  have hD_inv : IsAInvariant φ D := hC_inv.centralizer
  have hD_le_cE : D ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE_le_C)
  -- `D` is a `p`-group (subgroup of the `p`-group `G`).
  have hD_pgroup : IsPGroup p ↥D := hG.to_subgroup D
  -- Step 4: every order-`p` element of `↥D` is fixed by the restricted action.
  have h_fixD : ∀ x : ↥D, x ^ p = 1 → ∀ a : A, (restrictAction hD_inv a) x = x := by
    intro x hpow a
    have hgD : (x : G) ∈ D := x.2
    have hg_cent : (x : G) ∈ Subgroup.centralizer (E : Set G) := hD_le_cE hgD
    have hg_pow : (x : G) ^ p = 1 := by
      have h := congrArg (fun y : ↥D => (y : G)) hpow
      simpa using h
    apply Subtype.ext
    rw [restrictAction_apply]
    exact h_fix (x : G) hg_cent hg_pow a
  -- Apply BG Thm 1.11 = Isaacs Thm 4.36 to the restricted action on `↥D`.
  have hAC : OddOrder.Isaacs.Ch04.actionCommutator (restrictAction hD_inv) = ⊥ :=
    OddOrder.Isaacs.Ch04.isaacs_thm_4_36 hp_odd (restrictAction hD_inv) hD_pgroup hA_p' h_fixD
  have hTrivD : ∀ a : A, ∀ x : ↥D, (restrictAction hD_inv a) x = x :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially (restrictAction hD_inv)).mp hAC
  -- `D ≤ C`, i.e. `C_G(C) ⊆ C`.
  have hCC : Subgroup.centralizer (C : Set G) ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    have := hTrivD a ⟨g, hg⟩
    have h2 := congrArg Subtype.val this
    rwa [restrictAction_apply] at h2
  -- Step 5: conclude via BG Prop 1.10.
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    rw [hn]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hA_p').symm).pow_right n
  exact coprime_nilpotent_acts_trivially_of_centralizer_self hCop hCC

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

/-- **BG Lemma 1.14 (centralizer-in-G form)**: `T` p-subgroup of `G`, `M ⊴ G` p'-subgroup.
Writing `f = QuotientGroup.mk' M`, the preimage of `C_{G/M}(TM/M)` equals `C_G(T)·M`:
`(C_{G/M}(T.map f)).comap f = C_G(T) ⊔ M`. Equivalently `C_G(T)` surjects onto `C_{G/M}(TM/M)`.

This is the centralizer half of BG Lemma 1.14, derived from the normalizer half
(`normalizer_sup_eq_normalizer_sup_of_pGroup_coprime`) plus `T ⊓ M = ⊥`
(BG p.5: `CM ⊆ C* ⊆ N* = NM`, `C* ⊓ N = C`, so `C* = (C* ⊓ N)·M = CM`). Used for the
`O_{p'}(G) = 1` reduction in Proposition 1.15(b). -/
theorem centralizer_comap_mk'_eq_centralizer_sup_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [M.Normal] (hM_p' : (Nat.card M).Coprime p) :
    (Subgroup.centralizer
        ((T.map (QuotientGroup.mk' M) : Subgroup (G ⧸ M)) : Set (G ⧸ M))).comap
        (QuotientGroup.mk' M)
      = Subgroup.centralizer (T : Set G) ⊔ M := by
  set f := QuotientGroup.mk' M with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective M
  have hker : f.ker = M := QuotientGroup.ker_mk' M
  have hdisj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  apply le_antisymm
  · -- hard direction: `C* ⊆ C_G(T) ⊔ M`.
    intro x hx
    rw [Subgroup.mem_comap] at hx
    -- `x ∈ N_G(T ⊔ M)` via the normalizer-of-quotient identity.
    have hxN : x ∈ Subgroup.normalizer (T ⊔ M : Subgroup G) := by
      have hxn : f x ∈ Subgroup.normalizer (T.map f : Subgroup (G ⧸ M)) :=
        Subgroup.centralizer_le_normalizer _ hx
      have e1 : (T.map f).comap f = (T ⊔ M : Subgroup G) := by
        rw [Subgroup.comap_map_eq, hker]
      have e2 := Subgroup.comap_normalizer_eq_of_surjective (T.map f) hsurj
      have hmem : x ∈ (Subgroup.normalizer (T.map f : Subgroup (G ⧸ M))).comap f := by
        rw [Subgroup.mem_comap]; exact hxn
      rw [e2, e1] at hmem
      exact hmem
    rw [normalizer_sup_eq_normalizer_sup_of_pGroup_coprime hT hM_p', sup_comm] at hxN
    obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
    -- `f m = 1`, hence `f n = f x`.
    have hfm : f m = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hm)
    have hfn : f n = f x := by rw [← hmn, map_mul, hfm, one_mul]
    -- `n` centralizes `T`.
    have hn_cent : n ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htT : t ∈ T := SetLike.mem_coe.mp ht
      -- `f n` commutes with `f t` (image of `T`).
      have hcomm : f n * f t = f t * f n := by
        have hft : (f t) ∈ (↑(T.map f) : Set (G ⧸ M)) :=
          SetLike.mem_coe.mpr (Subgroup.mem_map_of_mem f htT)
        rw [hfn]
        exact (Subgroup.mem_centralizer_iff.mp hx (f t) hft).symm
      -- `c := n*t*n⁻¹*t⁻¹ ∈ M` (vanishes mod `M`).
      have hcM : n * t * n⁻¹ * t⁻¹ ∈ M := by
        rw [← hker]
        refine MonoidHom.mem_ker.mpr ?_
        have : f n * f t * (f n)⁻¹ * (f t)⁻¹ = 1 := by rw [hcomm]; group
        simpa [map_mul, map_inv] using this
      -- `c ∈ T` since `n` normalizes `T`.
      have hcT : n * t * n⁻¹ * t⁻¹ ∈ T := by
        have hntn : n * t * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn t).mp htT
        exact T.mul_mem hntn (T.inv_mem htT)
      have hc1 : n * t * n⁻¹ * t⁻¹ = 1 :=
        Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hcT, hcM⟩)
      have h1 : n * t * n⁻¹ = t := mul_inv_eq_one.mp hc1
      calc t * n = (n * t * n⁻¹) * n := by rw [h1]
        _ = n * t := by group
    rw [sup_comm]
    exact Subgroup.mem_sup_of_normal_left.mpr ⟨m, hm, n, hn_cent, hmn⟩
  · -- easy direction: `C_G(T) ⊔ M ⊆ C*`.
    rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · intro c hc
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro h ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_centralizer_iff.mp hc t ht)
    · intro μ hμ
      rw [Subgroup.mem_comap]
      have hμ1 : f μ = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hμ)
      rw [hμ1]
      exact Subgroup.one_mem _

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

/-- **Isaacs Thm 3.21 / Hall-Higman 1.2.3 (general form)**: for a finite π-separable
group `G`, the centralizer of `O_{π',π}(G)` is contained in `O_{π',π}(G)`:
`C_G(O_{π',π}(G)) ≤ O_{π',π}(G)`.

There is **no** hypothesis that `O_{π'}(G) = 1`; this is the genuine general statement.
The literal numbered Isaacs Thm 3.21 carries the `O_{π'}(G) = 1` hypothesis and is exactly
the special case `OddOrder.Isaacs.Ch03.hall_higman_1_2_3`. This general form is obtained by
transporting that special case to `Ḡ = G/O_{π'}(G)` (where `O_{π'}(Ḡ) = 1` automatically) and
recognizing `O_π(Ḡ)` pulled back as `O_{π',π}(G)` — exactly Isaacs' own reduction in the proof
of Thm 3.22. This is the form BG §9 Thm 9.1 needs.

`IsSolvable` callers obtain `[IsPiSeparable π G]` for free via the instance
`OddOrder.Isaacs.Ch03.isPiSeparable_of_solvable`. -/
theorem centralizer_oPiPrimePiCore_le
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [OddOrder.Isaacs.Ch03.IsPiSeparable π G] :
    Subgroup.centralizer (OddOrder.Isaacs.Ch03.oPiPrimePiCore π G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiPrimePiCore π G := by
  -- `Ḡ = G ⧸ O_{π'}(G)`, written inline to keep all occurrences syntactically identical.
  -- `mk : G →* Ḡ` is the quotient map.
  let mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G)
  -- `Ḡ` is π-separable and `O_{π'}(Ḡ) = ⊥` (self-quotient identity at the complement set).
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable π
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G) := inferInstance
  have hbot : OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot {p | p ∉ π}
  -- Special-case Hall-Higman on `Ḡ`: `C_Ḡ(O_π(Ḡ)) ≤ O_π(Ḡ)`.
  have hHH := OddOrder.Isaacs.Ch03.hall_higman_1_2_3
    (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G) π hbot
  -- `O_{π',π}(G) = comap mk (O_π(Ḡ))`, with `mk` written to match the `let`-binding.
  have hcomap : OddOrder.Isaacs.Ch03.oPiPrimePiCore π G
      = Subgroup.comap mk
        (OddOrder.Isaacs.Ch03.oPiCore π (G ⧸ OddOrder.Isaacs.Ch03.oPiCore {p | p ∉ π} G)) := by
    rw [OddOrder.Isaacs.Ch03.oPiPrimePiCore]
  -- Push the centralizer through `mk` and conclude via the Galois connection.
  -- After `map_le_iff_le_comap` the goal is `map mk (centralizer ↑(comap mk Oπ)) ≤ Oπ`.
  rw [hcomap, ← Subgroup.map_le_iff_le_comap]
  refine le_trans (Subgroup.map_centralizer_le_centralizer_image _ mk) ?_
  -- `mk '' ↑(comap mk Oπ) = ↑Oπ` since `mk` is surjective.
  rw [← Subgroup.coe_map,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
  exact hHH

/-- **Prop 1.15(b) core** (`O_{p'}(G) = ⊥` case, per element): every `u ∈ M := O_{p'}(C_G(R))`
centralizes `T := O_p(G)`. Proof mirrors `BG.AppA.thmA5_part2`: `⟨u⟩` acts by conjugation on the
`p`-group `RT := R ⊔ T`, and `C_{RT}(C_{RT}(u)) ⊆ C_{RT}(R) ⊆ C_{RT}(u)` — the second inclusion
because `C_{RT}(R) ⊆ C_G(R)` centralizes `u` (`[c,u] ∈ RT ⊓ M = ⊥`, since `M ⊴ C_G(R)` and `u`
normalizes `RT`). Proposition 1.10 then makes `⟨u⟩` act trivially on `RT ⊇ T`. -/
private theorem mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R)
    {u : G} (huM : u ∈ OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
      (Subgroup.centralizer (R : Set G))) :
    u ∈ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) : Set G) := by
  classical
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hM
  set T : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hT
  set RT : Subgroup G := R ⊔ T with hRT
  -- `u ∈ C_G(R)` and `u` is a `p'`-element.
  have huC : u ∈ Subgroup.centralizer (R : Set G) :=
    OddOrder.GroupTheory.opiCoreInG_le _ _ huM
  have hMp' : Nat.Coprime (Nat.card ↥M) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := ({p} : Set ℕ)ᶜ)
      Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM, OddOrder.GroupTheory.card_opiCoreInG] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hu_cop : (orderOf u).Coprime p := by
    have hdvd : orderOf u ∣ Nat.card ↥M := by
      have h : orderOf (⟨u, huM⟩ : ↥M) ∣ Nat.card ↥M := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h
    exact Nat.Coprime.coprime_dvd_left hdvd hMp'
  -- `T` normal, `RT` a `p`-group; `RT ⊓ M = ⊥`.
  haveI hTnorm : T.Normal := by rw [hT]; exact OddOrder.Isaacs.Ch01.opCore.normal p G
  have hRT_pg : IsPGroup p ↥RT :=
    hR.to_sup_of_normal_right (OddOrder.Isaacs.Ch01.opCore_isPGroup p G)
  have hRTM_disj : RT ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hRT_pg hMp'
  -- `u` normalizes `RT` (centralizes `R`, normalizes `T ⊴ G`).
  have hu_norm_RT : u ∈ Subgroup.normalizer RT := by
    have huNR : u ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.centralizer_le_normalizer (R : Set G) huC
    rw [hRT]
    exact le_normalizer_sup_of_normal R T (Subgroup.mem_sup_left huNR)
  have hzu_le : Subgroup.zpowers u ≤ Subgroup.normalizer RT :=
    Subgroup.zpowers_le.mpr hu_norm_RT
  -- conjugation action of `⟨u⟩` on `RT`.
  set φ : ↥(Subgroup.zpowers u) →* MulAut ↥RT :=
    RT.normalizerMonoidHom.comp (Subgroup.inclusion hzu_le) with hφ
  have hφcoe : ∀ (a : ↥(Subgroup.zpowers u)) (g : ↥RT),
      ((φ a) g : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
    intro a g; rw [hφ]; rfl
  -- (i) `R.subgroupOf RT ≤ fixedPoints` (`R ⊆ C_{RT}(u)`).
  have hR_le_fix : R.subgroupOf RT ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hgu : Commute (g : G) u := Subgroup.mem_centralizer_iff.mp huC (g : G) hg
    have hcomm : Commute (a : G) (g : G) := by rw [← hk]; exact (hgu.symm).zpow_left k
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  -- (ii) `C_{RT}(R) ≤ fixedPoints` (`C_{RT}(R)` centralizes `u`, via `[c,u] ∈ RT ⊓ M = ⊥`).
  have hCRTR_le_fix : Subgroup.centralizer ((R.subgroupOf RT : Subgroup ↥RT) : Set ↥RT)
      ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    -- `c` centralizes `R`, so `c ∈ C_G(R)`.
    have hc_cent_R : (c : G) ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : (⟨r, Subgroup.mem_sup_left hr⟩ : ↥RT) ∈ (R.subgroupOf RT : Subgroup ↥RT) := by
        rw [Subgroup.mem_subgroupOf]; exact hr
      have hcr := Subgroup.mem_centralizer_iff.mp hc ⟨r, Subgroup.mem_sup_left hr⟩ hr'
      exact congrArg Subtype.val hcr
    -- `[c,u] ∈ M` (since `M ⊴ C_G(R)`).
    have hcomm_M : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ M := by
      have hcu : (c : G) * u * (c : G)⁻¹ ∈ M :=
        ((Subgroup.mem_normalizer_iff.mp
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _ hc_cent_R)) u).mp huM
      exact M.mul_mem hcu (M.inv_mem huM)
    -- `[c,u] ∈ RT` (`c ∈ RT`, `u` normalizes `RT`).
    have hcomm_RT : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ RT := by
      have hucu : u * (c : G)⁻¹ * u⁻¹ ∈ RT :=
        ((Subgroup.mem_normalizer_iff.mp hu_norm_RT) (c : G)⁻¹).mp (RT.inv_mem c.2)
      have hrw : (c : G) * u * (c : G)⁻¹ * u⁻¹ = (c : G) * (u * (c : G)⁻¹ * u⁻¹) := by group
      rw [hrw]; exact RT.mul_mem c.2 hucu
    -- so `[c,u] = 1`, i.e. `u` and `c` commute.
    have hcomm1 : (c : G) * u * (c : G)⁻¹ * u⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hRTM_disj ▸ Subgroup.mem_inf.mpr ⟨hcomm_RT, hcomm_M⟩)
    have hcu_eq : u * (c : G) = (c : G) * u := by
      have h1 : (c : G) * u * (c : G)⁻¹ = u := mul_inv_eq_one.mp hcomm1
      calc u * (c : G) = ((c : G) * u * (c : G)⁻¹) * (c : G) := by rw [h1]
        _ = (c : G) * u := by group
    have hcu : Commute u (c : G) := hcu_eq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hac : Commute (a : G) (c : G) := by rw [← hk]; exact hcu.zpow_left k
    rw [hac.eq, mul_assoc, mul_inv_cancel, mul_one]
  -- `C_{RT}(C_{RT}(u)) ⊆ C_{RT}(u)` for Prop 1.10.
  have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥RT)
      ≤ Subgroup.fixedPointsOfMulAut φ :=
    calc Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥RT)
        ≤ Subgroup.centralizer ((R.subgroupOf RT : Subgroup ↥RT) : Set ↥RT) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR_le_fix)
      _ ≤ Subgroup.fixedPointsOfMulAut φ := hCRTR_le_fix
  haveI : Group.IsNilpotent ↥RT := hRT_pg.isNilpotent
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥RT) := by
    obtain ⟨n, hn⟩ := hRT_pg.exists_card_eq
    rw [Nat.card_zpowers, hn]
    exact hu_cop.pow_right n
  have htrivφ := coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥(Subgroup.zpowers u)) (G := ↥RT) (φ := φ) hcop hCC
  -- `u` centralizes `T ≤ RT`.
  rw [Subgroup.mem_centralizer_iff]
  intro x hxT
  have hxRT : x ∈ RT := Subgroup.mem_sup_right hxT
  have h := htrivφ ⟨u, Subgroup.mem_zpowers u⟩ ⟨x, hxRT⟩
  have hco := congrArg Subtype.val h
  rw [hφcoe] at hco
  have hco' : u * x * u⁻¹ = x := hco
  have hux : u * x = x * u := by
    have hcg := congrArg (· * u) hco'; simpa [mul_assoc] using hcg
  exact hux.symm

/-- **BG Proposition 1.15(b), `O_{p'}(G) = ⊥` case** (D. Goldschmidt): if `G` is solvable with
trivial `p'`-core and `R` is a `p`-subgroup, then `O_{p'}(C_G(R)) = ⊥`. From the unconditional
`O_{p'}(C_G(R)) ⊆ C_G(O_p(G))` (`mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer`) and
`C_G(O_p(G)) ⊆ O_p(G)` (Prop 1.15(a)): `O_{p'}(C_G(R))` is both a `p`-subgroup (`≤ O_p(G)`) and a
`p'`-group, hence `⊥`. The general form (below) reduces to this case modulo `O_{p'}(G)`. -/
theorem oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R)
    (hbot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G = ⊥) :
    OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) = ⊥ := by
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hM
  set T : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hT
  -- `M ≤ C_G(T) ≤ T`.
  have hM_le_T : M ≤ T := by
    have hM_le_CT : M ≤ Subgroup.centralizer (T : Set G) := fun u hu =>
      mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer hR (hM ▸ hu)
    have hset : {q | q ∉ ({p} : Set ℕ)} = ({p} : Set ℕ)ᶜ := by ext q; simp
    have hHH := hall_higman_solvable_specialization (p := p) (G := G) (by rw [hset]; exact hbot)
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hT] at hHH
    exact hM_le_CT.trans hHH
  -- `card M` is coprime to `p` (`M` is a `p'`-group).
  have hMp' : Nat.Coprime (Nat.card ↥M) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := ({p} : Set ℕ)ᶜ)
      Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM, OddOrder.GroupTheory.card_opiCoreInG] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  -- `card M ∣ card T = p^n` and coprime to `p` ⟹ `card M = 1` ⟹ `M = ⊥`.
  obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).exists_card_eq
  have hdvd : Nat.card ↥M ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hM_le_T
  rw [hT, hn] at hdvd
  have hcard1 : Nat.card ↥M = 1 := by
    have hg := Nat.gcd_eq_left hdvd
    rw [← hg]; exact hMp'.pow_right n
  exact (Subgroup.card_eq_one).mp hcard1

/-- **BG Proposition 1.15(b) (D. Goldschmidt)**, general form: if `G` is a finite solvable group
and `R` is a `p`-subgroup, then `O_{p'}(C_G(R)) ≤ O_{p'}(G)`.

This reduces the general statement to the `O_{p'}(G) = ⊥` case
(`oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot`) modulo `M₀ := O_{p'}(G)`. Writing
`f = mk' M₀`, `Ḡ = G/M₀`, `R̄ = R.map f`, Lemma 1.14 (`centralizer_comap_mk'_…`) gives
`C_Ḡ(R̄) = C_G(R)·M₀/M₀ = (C_G(R)).map f`. Setting `K := M.map f` for `M := O_{p'}(C_G(R))`:
`K` lies in `C̄ := C_Ḡ(R̄)`, is normalized by `C̄` (since `M ⊴ C_G(R)`), and is a `p'`-group, so
`K.subgroupOf C̄ ≤ O_{p'}(↥C̄)`, i.e. `K ≤ O_{p'}(C_Ḡ(R̄))`. The special case at `Ḡ` (where
`O_{p'}(Ḡ) = ⊥` by `oPiCore_quotient_self_eq_bot`) forces `K = ⊥`, hence `M ≤ ker f = M₀`. -/
theorem oPiPrimeCore_centralizer_le_oPiPrimeCore
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R) :
    OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) ≤
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G := by
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hMdef
  set M₀ : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G with hM₀def
  -- goal is now `M ≤ M₀`.
  haveI hM₀norm : M₀.Normal := by rw [hM₀def]; infer_instance
  set f : G →* G ⧸ M₀ := QuotientGroup.mk' M₀ with hfdef
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective M₀
  have hker : f.ker = M₀ := QuotientGroup.ker_mk' M₀
  -- `M₀ = O_{p'}(G)` is a `p'`-group, so its order is coprime to `p`.
  have hM₀p' : Nat.Coprime (Nat.card ↥M₀) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM₀def] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hM₀map : M₀.map f = ⊥ := by rw [Subgroup.map_eq_bot_iff]; exact hker.ge
  -- `Cbar = C_Ḡ(R̄)`, the centralizer of the image of `R`.
  set Cbar : Subgroup (G ⧸ M₀) := Subgroup.centralizer ((R.map f) : Set (G ⧸ M₀)) with hCbardef
  -- brick 1 (Lemma 1.14): the preimage of `Cbar` is `C_G(R) ⊔ M₀`.
  have hbrick1 : Cbar.comap f = Subgroup.centralizer (R : Set G) ⊔ M₀ :=
    centralizer_comap_mk'_eq_centralizer_sup_of_pGroup_coprime hR hM₀p'
  -- hence `Cbar = (C_G(R)).map f` (apply `map f`, `M₀.map f = ⊥`).
  have hCbareq : Cbar = (Subgroup.centralizer (R : Set G)).map f := by
    have h := congrArg (Subgroup.map f) hbrick1
    rwa [Subgroup.map_comap_eq_self_of_surjective hsurj, Subgroup.map_sup, hM₀map,
      sup_bot_eq] at h
  set K : Subgroup (G ⧸ M₀) := M.map f with hKdef
  -- (A) `K ≤ Cbar`.
  have hM_le_C : M ≤ Subgroup.centralizer (R : Set G) :=
    OddOrder.GroupTheory.opiCoreInG_le _ _
  have hKC : K ≤ Cbar := by rw [hKdef, hCbareq]; exact Subgroup.map_mono hM_le_C
  -- (B) `Cbar` stabilizes `K` by conjugation (`M ⊴ C_G(R)`).
  have hK_conj_stable : ∀ g ∈ Cbar, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    rw [hCbareq] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [hKdef] at hx ⊢
    obtain ⟨m, hm, rfl⟩ := hx
    have hconj : y * m * y⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp
        (OddOrder.GroupTheory.le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ
          (Subgroup.centralizer (R : Set G)) hy) m).mp hm
    have heq : f y * f m * (f y)⁻¹ = f (y * m * y⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map_of_mem f hconj
  -- (C) `K.subgroupOf Cbar` is normal in `↥Cbar`.
  haveI hK_norm : (K.subgroupOf Cbar).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hK_conj_stable (g : G ⧸ M₀) g.2 (n : G ⧸ M₀) hn
  -- (D) `K` is a `p'`-group, so `K.subgroupOf Cbar ≤ O_{p'}(↥Cbar)`.
  have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)ᶜ M := by
    intro q hq
    rw [hMdef, OddOrder.GroupTheory.card_opiCoreInG] at hq
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)ᶜ K := by
    intro q hq
    have hdvd : Nat.card ↥K ∣ Nat.card ↥M := by rw [hKdef]; exact Subgroup.card_map_dvd _ _
    exact hM_pi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
  have hK_le_oPiCore : K.subgroupOf Cbar ≤ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar :=
    (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hKC hK_pi).le_oPiCore
  -- (E) `K ≤ O_{p'}(Cbar)` realized in `Ḡ`.
  have hK_le : K ≤ OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ Cbar := by
    intro x hx
    have hxCbar : x ∈ Cbar := hKC hx
    have hmem : (⟨x, hxCbar⟩ : ↥Cbar) ∈ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar :=
      hK_le_oPiCore (by rw [Subgroup.mem_subgroupOf]; exact hx)
    show x ∈ (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar).map Cbar.subtype
    exact Subgroup.mem_map.mpr ⟨⟨x, hxCbar⟩, hmem, rfl⟩
  -- (F) special case at `Ḡ`: `O_{p'}(Cbar) = ⊥` (because `O_{p'}(Ḡ) = ⊥`).
  have hbarbot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ (G ⧸ M₀) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)ᶜ
  have hCbarbot : OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ Cbar = ⊥ :=
    oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot (hR.map f) hbarbot
  -- conclude `K = ⊥`, hence `M ≤ ker f = M₀`.
  have hKbot : K = ⊥ := le_bot_iff.mp (hK_le.trans hCbarbot.le)
  have hMmap : M.map f = ⊥ := by rw [← hKdef]; exact hKbot
  rw [Subgroup.map_eq_bot_iff, hker] at hMmap
  exact hMmap

/-! ## §1F: Focal + Burnside + Maschke (Thm 1.17-1.20)

Focal/Burnside は Ch05 側に BG から引用する public entrypoint を置く.

- **BG Thm 1.17** (Focal Subgroup): `OddOrder.Isaacs.Ch05.focalSubgroupTheorem`.
- **BG Thm 1.18** (Burnside p-complement):
  `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer`.
- **BG Cor 1.19(b)** (Z-group ⇒ G' Hall): mathlib `IsZGroup.coprime_commutator_index`
  (`Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:280`).
- **BG Thm 1.20** (Maschke): mathlib `Mathlib/RepresentationTheory/Maschke.lean`. -/

/-! ## §1G: p-length one + p-group normal series (Lem 1.21, Lem 1.22)

- **Lem 1.21** (p-length one の 5 性質): `HasPLengthOne` として定義を固定.
- **Lem 1.22** (p-group normal series): 本ファイル下記.

### Lem 1.22 implementation -/

/-- The BG subgroup `O_{π',π,π'}(G)`.

It is defined as the preimage of `O_{π'}` in `G / O_{π',π}(G)`, where
`O_{π',π}` is the Phase 1 subgroup `OddOrder.Isaacs.Ch03.oPiPrimePiCore`. -/
noncomputable def oPiPrimePiPiPrimeCore (π : Set ℕ) (G : Type*) [Group G] :
    Subgroup G :=
  Subgroup.comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiPrimePiCore π G))
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ π}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiPrimePiCore π G))

instance oPiPrimePiPiPrimeCore.normal (π : Set ℕ) (G : Type*) [Group G] :
    (oPiPrimePiPiPrimeCore π G).Normal := by
  rw [oPiPrimePiPiPrimeCore]
  infer_instance

/-- BG `π`-length one: `G = O_{π',π,π'}(G)`. -/
def HasPiLengthOne (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  oPiPrimePiPiPrimeCore π G = ⊤

/-- BG `p`-length one: the singleton-prime specialization of `HasPiLengthOne`. -/
def HasPLengthOne (p : ℕ) (G : Type*) [Group G] : Prop :=
  HasPiLengthOne ({p} : Set ℕ) G

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
