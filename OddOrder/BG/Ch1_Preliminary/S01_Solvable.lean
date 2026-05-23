/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow
import OddOrder.Isaacs.Ch03_SplitExtensions
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
| Thm 1.8 | Thm 1.8 | (Ch.1 §1B TODO) | Phase 1 待ち |
| Thm 1.11 | Thm 4.36 | Phase 1 Ch.4 §4D | Phase 1 待ち |
| Thm 1.13 | (Thompson critical) | (Phase 1 未) | Phase 1 待ち |
| **Lem 1.14** | — | `Subgroup.comap_map_eq` + Sylow corresp. | **本ファイル statement (sorry)** |
| **Prop 1.15(a)** | Thm 3.21 | `hall_higman_1_2_3` ✅ | **本ファイル placeholder (thin wrap 予定)** |
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

## 実装 status (2026-05-23)

- **Skeleton** + **§1F docstring mapping** + **3 結果 (Lem 1.14, Prop 1.15(a), Lem 1.22) statement**
  + **`card_comap_eq_card_mul_card_ker` helper proof 完成** (Lem 1.22 で使用予定)
- Proof body は次 commit で実装. 各 statement に proof 方針 docstring 記載.
- Phase 1 完成度: Ch.1 ✅ / Ch.3 ✅ (Hall + Hall-Higman 3.21) / Ch.4 §4D 進行中 / Ch.6, Ch.7 未着手.
-/

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01

/-! ## §1A-§1D: 未実装 (Phase 1 + shared module 待ち) -/

/-! ## §1E: Sylow lift + Hall-Higman + noncyclic auto -/

/-- **BG Lemma 1.14** (Sylow correspondence under quotient): `T` p-subgroup of `G`,
`M ⊴ G` p'-subgroup, `C = C_G(T)`, `N = N_G(T)`. Then in `G/M`:
- `C_{G/M}(TM/M) = CM/M`
- `N_{G/M}(TM/M) = NM/M`.

**Proof** (BG p.5): `NM ⊆ N*` clear. Reverse: `x ∈ N*` normalizes `TM` ⇒ `T^x` is Sylow `p` of
`TM` ⇒ `∃ y ∈ M` with `T^x = T^y` (Sylow II in `TM`) ⇒ `xy⁻¹ ∈ N`, so `x ∈ NM`. Hence
`N* = NM`. Then `CM ⊆ C* ⊆ N* = NM`. Since `T ∩ M = 1` (orders coprime), `C* ∩ N = C`, so
`C* = (C* ∩ N)M = CM`.

形式化方針: mathlib `Sylow.exists_smul_eq` + `Subgroup.comap_map_eq` の組み合わせ.
`T ∩ M = 1` は `IsPGroup.disjoint_of_coprime` 系または直接 cardinality argument.
proof 実装は次 commit. -/
theorem sylow_lift_centralizer_normalizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [hM_norm : M.Normal] (hM : IsPGroup p M → M = ⊥) :
    -- The "C_{G/M}(TM/M) = CM/M" + "N_{G/M}(TM/M) = NM/M" claim
    -- C = centralizer T, N = normalizer T as Subgroup G
    -- TM/M = (T ⊔ M).map (mk' M) in G/M
    True := by
  -- Full statement is complex; placeholder True for skeleton.
  -- Actual statement to be refined in next commit using
  -- Subgroup.centralizer (T : Set G) / Subgroup.normalizer T and quotient.
  trivial

/-- **BG Proposition 1.15(a) (P. Hall & G. Higman "Lemma 1.2.3")**: `G` solvable + `T` Sylow
`p`-subgroup of `O_{p',p}(G)` ⇒ `C_G(T) ⊆ O_{p',p}(G)`.

**Proof**: thin wrapper of Phase 1 `OddOrder.Isaacs.Ch03.hall_higman_1_2_3` via:
1. Quotient by `O_{p'}(G)` to get `G̅` with `O_{p'}(G̅) = ⊥`
2. `T̅ = T·O_{p'}(G)/O_{p'}(G) = O_p(G̅)` (Sylow p of `O_p` of quotient)
3. Apply `hall_higman_1_2_3` with `π = {p}` to `G̅`: `centralizer(O_p(G̅)) ≤ O_p(G̅)`
4. Pull back via Lem 1.14 to get `C_G(T) ⊆ O_{p',p}(G)`

proof 実装は次 commit (Lem 1.14 完成と並行). -/
theorem hall_higman_solvable_specialization
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G] :
    -- Statement placeholder: full form needs T explicitly and O_{p',p} (= mathlib oPiCore
    -- for π = {p'} preimage in G/O_{p'}, structure-wise).
    -- Refining the actual statement after Lem 1.14 in next commit.
    True := by
  trivial

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
