/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.BG.Ch1_Preliminary.S04g_Thm418

/-!
# BG §4H: Corollary 4.19 — general form

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4, **Corollary 4.19** (printed p. 43, mmd
`references/bg/local-analysis.mmd` L1765-1780).  Tracked in issue 3015.

**Statement**: `p` prime, `G` finite solvable, `G* ⊴ G`, `r_p(G*) ≤ 2`, `|G|` odd.
Then `G'` centralizes every chief factor `U/V` of `G` such that `U/V` is a `p`-group
and `U ⊆ G*`.

## 証明 (BG)

`O_{p'}(G*) = 1` に帰着 (Thm 4.18 の証明同様)。`R = O_p(G*)` は Thm 4.18 で `G*` の
Sylow `p`, ゆえ `U ⊆ RV`。`C = C_G(U/V)`; Lemma 4.17 で `(G/C_G(R))'` は `p`-群 ⟹
`(G/C)'` `p`-群; `G/C` が `U/V` に faithful irreducible ⟹ `O_p(G/C) = 1 ⊇ (G/C)' =
G'C/C` ⟹ `G' ⊆ C`。この Lemma 4.17 + faithful-action ステップは reduced endpoint
`commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup` (S04g_Thm418) が
packaging 済み — 本ファイルは `O_{p'}(G*) ≠ 1` の一般形を、商 `Ḡ = G/O_{p'}(G*)` へ
chief factor を移送して reduced endpoint に帰着させる。

## 実装 (`O_{p'}(G*) = 1` reduction)

`W := O_{p'}(G*)` (characteristic in `G*` ⊴ `G`, ゆえ `W ⊴ G`, `p'`-群)。`Ḡ = G/W` で
`R̄ := O_{p',p}(G*)` の像 (これは `O_p(Ḡ*)`, `p`-群 rank ≤ 2)。`U/V` が `p`-群ゆえ
`U ⊓ W ≤ V` — これが `Ū/V̄` が `Ḡ` の chief factor で `U/V` と同型 (かつ `p`-群) である
ことと、逆写像 `commutator G ≤ C_G(U/V)` の橋になる。`U ≤ R̄ ⊔ V̄`-相当の `U ≤ T ⊔ V`
(`T = O_{p',p}(G*)`) は `G*/O_{p',p}(G*)` が `p'`-群 (Thm 4.18(e)) と `U/V` が `p`-群の
衝突から従う (`collapse`)。
-/

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped commutatorElement

section Cor419

variable {G : Type*} [Group G]

/-- **`U ⊓ (V ⊔ W) ≤ V`** の Dedekind 版: `V ≤ U`, `W ⊴ G`, `U ⊓ W ≤ V` なら
`U ⊓ (V ⊔ W) ≤ V`。`W` normal ゆえ `V ⊔ W` の元は `v * w` の形。 -/
private theorem inf_sup_le_of_inf_le {U V W : Subgroup G} [W.Normal]
    (hVU : V ≤ U) (hUW : U ⊓ W ≤ V) : U ⊓ (V ⊔ W) ≤ V := by
  rintro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxU, hxVW⟩ := hx
  obtain ⟨v, hv, w, hw, hx_eq⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := V) (t := W)).mp hxVW
  have hvU : v ∈ U := hVU hv
  have hwU : w ∈ U := by
    have h := U.mul_mem (U.inv_mem hvU) hxU
    rw [← hx_eq, inv_mul_cancel_left] at h
    exact h
  rw [← hx_eq]
  exact V.mul_mem hv (hUW (Subgroup.mem_inf.mpr ⟨hwU, hw⟩))

/-- **`p`-vs-`p'` collapse**: 有限群 `H` で `B ≤ A`, `C ⊴ H`。`[A : B]` が `p`-冪、
`[H : C]` が `p'`-数なら `A ≤ B ⊔ C`。 -/
private theorem collapse {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {A B C : Subgroup H} (_hBA : B ≤ A) [C.Normal]
    (hB_ppow : ∃ n : ℕ, (B.subgroupOf A).index = p ^ n)
    (hC_p' : ¬ p ∣ C.index) : A ≤ B ⊔ C := by
  classical
  set D : Subgroup H := B ⊔ (A ⊓ C) with hD
  have hBD : B.subgroupOf A ≤ D.subgroupOf A := Subgroup.comap_mono le_sup_left
  have hdvd_p : (D.subgroupOf A).index ∣ (B.subgroupOf A).index :=
    Subgroup.index_dvd_of_le hBD
  have hCD : C.subgroupOf A ≤ D.subgroupOf A := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Subgroup.comap_mono le_sup_right
  have hdvd_C : (D.subgroupOf A).index ∣ C.index :=
    dvd_trans (Subgroup.index_dvd_of_le hCD)
      (Subgroup.relIndex_dvd_index_of_normal (H := C) (K := A))
  have hnp : ¬ p ∣ (D.subgroupOf A).index := fun h => hC_p' (dvd_trans h hdvd_C)
  obtain ⟨n, hn⟩ := hB_ppow
  have hdvd_pn : (D.subgroupOf A).index ∣ p ^ n := hn ▸ hdvd_p
  have hidx1 : (D.subgroupOf A).index = 1 := by
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd_pn
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, pow_zero] at hm; exact hm
    · exact absurd (hm ▸ dvd_pow_self p hmpos.ne') hnp
  have hDtop : D.subgroupOf A = ⊤ := Subgroup.index_eq_one.mp hidx1
  exact le_trans (Subgroup.subgroupOf_eq_top.mp hDtop) (sup_le_sup_left inf_le_right B)

/-- **chief factor 移送** (`W ⊴ G`, `p'`-層で商): `U/V` が `G` の chief factor で
`U ⊓ W ≤ V` なら `Ū/V̄` (`Ū = U.map (mk' W)`, `V̄ = V.map (mk' W)`) は `G/W` の
chief factor。 -/
private theorem isChiefFactor_map_mk' {W U V : Subgroup G} [W.Normal]
    (hChief : IsChiefFactor U V) (hUW : U ⊓ W ≤ V) :
    IsChiefFactor (U.map (QuotientGroup.mk' W)) (V.map (QuotientGroup.mk' W)) := by
  haveI hU : U.Normal := hChief.normal_top
  haveI hVn : V.Normal := hChief.normal_bot
  haveI hUbn : (U.map (QuotientGroup.mk' W)).Normal :=
    hU.map _ (QuotientGroup.mk'_surjective W)
  haveI hVbn : (V.map (QuotientGroup.mk' W)).Normal :=
    hVn.map _ (QuotientGroup.mk'_surjective W)
  have hVU : V ≤ U := hChief.le
  refine ⟨hUbn, hVbn, ?_, ?_⟩
  · rw [lt_iff_le_and_ne]
    refine ⟨Subgroup.map_mono hChief.le, ?_⟩
    intro hEq
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' W)) hEq
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hcomap
    have hU_le : U ≤ V ⊔ W := by rw [hcomap]; exact le_sup_left
    have hU_le_V : U ≤ V := fun u hu =>
      inf_sup_le_of_inf_le hVU hUW (Subgroup.mem_inf.mpr ⟨hu, hU_le hu⟩)
    exact absurd (le_antisymm hU_le_V hVU) hChief.lt.ne'
  · intro N hN hVN hNU
    haveI hNn : N.Normal := hN
    haveI hN'norm : (N.comap (QuotientGroup.mk' W)).Normal := hN.comap _
    have hWN' : W ≤ N.comap (QuotientGroup.mk' W) := by
      intro x hx
      rw [Subgroup.mem_comap,
        show (QuotientGroup.mk' W) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact N.one_mem
    have hVN' : V ≤ N.comap (QuotientGroup.mk' W) := by
      intro v hv
      rw [Subgroup.mem_comap]
      exact hVN (Subgroup.mem_map_of_mem _ hv)
    have hN'U : N.comap (QuotientGroup.mk' W) ≤ U ⊔ W := by
      have hc := Subgroup.comap_mono (f := QuotientGroup.mk' W) hNU
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc
    have hN_eq : N = (N.comap (QuotientGroup.mk' W)).map (QuotientGroup.mk' W) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective W) N).symm
    haveI hInf_norm : ((N.comap (QuotientGroup.mk' W)) ⊓ U).Normal := inferInstance
    rcases hChief.eq_or_eq_of_normal (W := (N.comap (QuotientGroup.mk' W)) ⊓ U) hInf_norm
      (le_inf hVN' hChief.le) inf_le_right with hcase | hcase
    · left
      apply le_antisymm _ hVN
      have hN'_le_VW : N.comap (QuotientGroup.mk' W) ≤ V ⊔ W := by
        intro x hx
        obtain ⟨u, hu, w, hw, hx_eq⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := U) (t := W)).mp (hN'U hx)
        have hwN' : w ∈ N.comap (QuotientGroup.mk' W) := hWN' hw
        have huN' : u ∈ N.comap (QuotientGroup.mk' W) := by
          have h := (N.comap (QuotientGroup.mk' W)).mul_mem hx
            ((N.comap (QuotientGroup.mk' W)).inv_mem hwN')
          rw [← hx_eq, mul_inv_cancel_right] at h
          exact h
        have huV : u ∈ V := by
          have hmem : u ∈ (N.comap (QuotientGroup.mk' W)) ⊓ U := Subgroup.mem_inf.mpr ⟨huN', hu⟩
          rw [hcase] at hmem; exact hmem
        rw [← hx_eq]
        exact (Subgroup.mem_sup_of_normal_right (s := V) (t := W)).mpr ⟨u, huV, w, hw, rfl⟩
      rw [hN_eq]
      calc (N.comap (QuotientGroup.mk' W)).map (QuotientGroup.mk' W)
          ≤ (V ⊔ W).map (QuotientGroup.mk' W) := Subgroup.map_mono hN'_le_VW
        _ = V.map (QuotientGroup.mk' W) ⊔ W.map (QuotientGroup.mk' W) := Subgroup.map_sup _ _ _
        _ = V.map (QuotientGroup.mk' W) := by
              rw [QuotientGroup.map_mk'_self, sup_bot_eq]
    · right
      apply le_antisymm hNU
      have hUN' : U ≤ N.comap (QuotientGroup.mk' W) := by rw [← hcase]; exact inf_le_left
      rw [hN_eq]
      exact Subgroup.map_mono hUN'

/-- `O_{p',p}(H)` の `O_{p'}(H)`-商での像は `O_p(H/O_{p'}(H))` すなわち `p`-群。 -/
private theorem isPGroup_oPiPrimePiCore_map {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] :
    IsPGroup p ↥((Ch03.oPiPrimePiCore {p} H).map
      (QuotientGroup.mk' (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} H))) := by
  have hmap : (Ch03.oPiPrimePiCore {p} H).map
      (QuotientGroup.mk' (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} H)) =
      Ch03.oPiCore {p} (H ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} H) := by
    rw [Ch03.oPiPrimePiCore]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [hmap]
  exact isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup _)

/-- **`p`-群像の移送**: `U.map (mk' V)` が `p`-群なら、`W ⊴ G` の商で
`(U.map (mk' W)).map (mk' (V.map (mk' W)))` も `p`-群。 -/
private theorem isPGroup_map_mk'_map_mk' {p : ℕ} {W U V : Subgroup G} [W.Normal] [V.Normal]
    (hUbar : IsPGroup p ↥(U.map (QuotientGroup.mk' V))) :
    IsPGroup p ↥((U.map (QuotientGroup.mk' W)).map
      (QuotientGroup.mk' (V.map (QuotientGroup.mk' W)))) := by
  haveI hVbn : (V.map (QuotientGroup.mk' W)).Normal :=
    (inferInstance : V.Normal).map _ (QuotientGroup.mk'_surjective W)
  have hcond : V ≤ (V.map (QuotientGroup.mk' W)).comap (QuotientGroup.mk' W) :=
    Subgroup.le_comap_map _ _
  set ψ : G ⧸ V →* (G ⧸ W) ⧸ (V.map (QuotientGroup.mk' W)) :=
    QuotientGroup.map V (V.map (QuotientGroup.mk' W)) (QuotientGroup.mk' W) hcond with hψ
  have hcomp : ψ.comp (QuotientGroup.mk' V) =
      (QuotientGroup.mk' (V.map (QuotientGroup.mk' W))).comp (QuotientGroup.mk' W) := by
    ext g
    simp [hψ]
  have hmap : (U.map (QuotientGroup.mk' V)).map ψ =
      (U.map (QuotientGroup.mk' W)).map (QuotientGroup.mk' (V.map (QuotientGroup.mk' W))) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rw [← hmap]
  exact hUbar.map ψ

/-- **BG Corollary 4.19 (一般形)**: `p` prime, `G` 有限 solvable, `G* ⊴ G`,
`r_p(G*) ≤ 2`, `|G|` odd。すると `G'` は、`U ⊆ G*` かつ `U/V` が `p`-群である全ての
`G` の chief factor `U/V` を中心化する。

`O_{p'}(G*) = 1` reduction を商 `Ḡ = G/O_{p'}(G*)` への chief factor 移送で実装し、
reduced endpoint `commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup`
(normal `p`-subgroup rank ≤ 2, `U ⊆ R ⊔ V` 版) に帰着させる。 -/
theorem commutator_le_chiefFactorCentralizer_of_rank_le_two_of_le_normal
    [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {Gstar U V : Subgroup G} [Gstar.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hChief : IsChiefFactor U V) (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hrank : pRank ↥Gstar p ≤ 2) (hU_le : U ≤ Gstar) :
    _root_.commutator G ≤ chiefFactorCentralizer U V := by
  classical
  haveI hU_normal : U.Normal := hChief.normal_top
  have hVU : V ≤ U := hChief.le
  have hV_le : V ≤ Gstar := hVU.trans hU_le
  -- `W = O_{p'}(G*)`, `T = O_{p',p}(G*)` pushed to `G` (literal cores in `↥Gstar`)
  haveI hWsub_char : (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} ↥Gstar).Characteristic :=
    Ch03.oPiCore.characteristic _ _
  haveI hTsub_char : (Ch03.oPiPrimePiCore {p} ↥Gstar).Characteristic := by
    rw [Ch03.oPiPrimePiCore]
    exact Subgroup.Characteristic.comap_quotient_mk (Ch03.oPiCore.characteristic _ _)
  set W : Subgroup G := (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} ↥Gstar).map Gstar.subtype
    with hW
  set T : Subgroup G := (Ch03.oPiPrimePiCore {p} ↥Gstar).map Gstar.subtype with hT
  haveI hW_normal : W.Normal := by rw [hW]; exact OddOrder.GroupTheory.normal_map_subtype_of_characteristic hWsub_char
  haveI hT_normal : T.Normal := by rw [hT]; exact OddOrder.GroupTheory.normal_map_subtype_of_characteristic hTsub_char
  have hW_le_T : W ≤ T := by
    rw [hW, hT]; exact Subgroup.map_mono (Ch03.oPiCore_compl_le_oPiPrimePiCore _ _)
  have hT_le : T ≤ Gstar := by rw [hT]; exact Subgroup.map_subtype_le _
  have hW_p' : ¬ p ∣ Nat.card ↥W := by
    rw [hW, Subgroup.card_map_of_injective Gstar.subtype_injective]
    exact not_dvd_card_oPiCore (by simp)
  -- KEY: `U ⊓ W ≤ V`
  have hUW : U ⊓ W ≤ V := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hUbar_pg
    have hcard_dvd_p : Nat.card ↥((U ⊓ W).map (QuotientGroup.mk' V)) ∣ p ^ a :=
      ha ▸ Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)
    have hcard_dvd_UW : Nat.card ↥((U ⊓ W).map (QuotientGroup.mk' V)) ∣ Nat.card ↥(U ⊓ W) :=
      Subgroup.card_map_dvd (U ⊓ W) (QuotientGroup.mk' V)
    have hUW_dvd_W : Nat.card ↥(U ⊓ W) ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_right
    have hnp : ¬ p ∣ Nat.card ↥((U ⊓ W).map (QuotientGroup.mk' V)) := fun h =>
      hW_p' (dvd_trans (dvd_trans h hcard_dvd_UW) hUW_dvd_W)
    have hcard1 : Nat.card ↥((U ⊓ W).map (QuotientGroup.mk' V)) = 1 := by
      obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hcard_dvd_p
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0, pow_zero] at hm; exact hm
      · exact absurd (hm ▸ dvd_pow_self p hmpos.ne') hnp
    have hbot : (U ⊓ W).map (QuotientGroup.mk' V) = ⊥ := Subgroup.card_eq_one.mp hcard1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  -- structure of `G*` (Thm 4.18(e))
  have hodd_Gstar : Odd (Nat.card ↥Gstar) := by
    rcases Nat.even_or_odd (Nat.card ↥Gstar) with he | ho
    · exact absurd (dvd_trans he.two_dvd (Subgroup.card_subgroup_dvd_card Gstar))
        (by rw [Nat.odd_iff] at hodd; omega)
    · exact ho
  have hp_mem_Gstar : p ∣ Nat.card ↥Gstar := by
    have hUbar_ne : U.map (QuotientGroup.mk' V) ≠ ⊥ :=
      hChief.isMinimalNormal_map_quotient.2.1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hUbar_pg
    have hgt : 1 < Nat.card ↥(U.map (QuotientGroup.mk' V)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hUbar_ne
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero] at hn; rw [hn] at hgt; exact absurd hgt (lt_irrefl 1)
      · exact hpos
    have hp_dvd_Ubar : p ∣ Nat.card ↥(U.map (QuotientGroup.mk' V)) := by
      rw [hn]; exact dvd_pow_self p hn_pos.ne'
    have heq : Nat.card ↥(U.map (QuotientGroup.mk' V)) = V.relIndex U := by
      rw [← Subgroup.relIndex_ker U (QuotientGroup.mk' V), QuotientGroup.ker_mk']
    have hp_dvd_U : p ∣ Nat.card ↥U :=
      dvd_trans (heq ▸ hp_dvd_Ubar) (Subgroup.relIndex_dvd_card V U)
    have hU_dvd_Gstar : Nat.card ↥U ∣ Nat.card ↥Gstar := by
      rw [show Nat.card ↥U = Nat.card ↥(U.subgroupOf Gstar) from
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv).symm]
      exact Subgroup.card_subgroup_dvd_card (U.subgroupOf Gstar)
    exact dvd_trans hp_dvd_U hU_dvd_Gstar
  have hstruct := solvable_structure_of_pRank_le_two (G := ↥Gstar) hodd_Gstar hp_mem_Gstar hrank
  have hpl : hasPLengthOne p ↥Gstar := hstruct.2.2.2.2.2
  have hTsub_index_p' : ¬ p ∣ (Ch03.oPiPrimePiCore {p} ↥Gstar).index := by
    rw [Subgroup.index_eq_card]
    exact (hasPLengthOne_iff p ↥Gstar).mp hpl
  -- `U ≤ T ⊔ V` via collapse
  have hU_le_TV : U ≤ T ⊔ V := by
    have hcollapse : U.subgroupOf Gstar ≤
        V.subgroupOf Gstar ⊔ Ch03.oPiPrimePiCore {p} ↥Gstar := by
      refine collapse (A := U.subgroupOf Gstar) (B := V.subgroupOf Gstar)
        (C := Ch03.oPiPrimePiCore {p} ↥Gstar)
        (Subgroup.subgroupOf_mono Gstar hVU) ?_ hTsub_index_p'
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hUbar_pg
      refine ⟨n, ?_⟩
      have h2 : (V.subgroupOf Gstar).relIndex (U.subgroupOf Gstar) = V.relIndex U :=
        Subgroup.relIndex_subgroupOf hU_le
      have h3 : V.relIndex U = Nat.card ↥(U.map (QuotientGroup.mk' V)) := by
        rw [← Subgroup.relIndex_ker U (QuotientGroup.mk' V), QuotientGroup.ker_mk']
      change ((V.subgroupOf Gstar).subgroupOf (U.subgroupOf Gstar)).index = p ^ n
      rw [show ((V.subgroupOf Gstar).subgroupOf (U.subgroupOf Gstar)).index
            = (V.subgroupOf Gstar).relIndex (U.subgroupOf Gstar) from rfl, h2, h3, hn]
    have hmapped := Subgroup.map_mono (f := Gstar.subtype) hcollapse
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hU_le, Subgroup.map_sup,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV_le, ← hT] at hmapped
    rw [sup_comm] at hmapped
    exact hmapped
  -- assemble in `Ḡ = G/W`
  haveI hVbar_normal : (V.map (QuotientGroup.mk' W)).Normal :=
    (inferInstance : V.Normal).map _ (QuotientGroup.mk'_surjective W)
  haveI hRbar_normal : (T.map (QuotientGroup.mk' W)).Normal :=
    (inferInstance : T.Normal).map _ (QuotientGroup.mk'_surjective W)
  haveI hUbarmap_normal :
      ((U.map (QuotientGroup.mk' W)).map
        (QuotientGroup.mk' (V.map (QuotientGroup.mk' W)))).Normal :=
    ((inferInstance : U.Normal).map _ (QuotientGroup.mk'_surjective W)).map _
      (QuotientGroup.mk'_surjective _)
  have hChiefBar : IsChiefFactor (U.map (QuotientGroup.mk' W)) (V.map (QuotientGroup.mk' W)) :=
    isChiefFactor_map_mk' hChief hUW
  have hUbarBar_pg :
      IsPGroup p ↥((U.map (QuotientGroup.mk' W)).map
        (QuotientGroup.mk' (V.map (QuotientGroup.mk' W)))) :=
    isPGroup_map_mk'_map_mk' hUbar_pg
  -- `R̄ = T.map (mk' W)` is a p-group of rank ≤ 2
  have hRbar_pg : IsPGroup p ↥(T.map (QuotientGroup.mk' W)) := by
    have hcard : Nat.card ↥(T.map (QuotientGroup.mk' W)) =
        Nat.card ↥((Ch03.oPiPrimePiCore {p} ↥Gstar).map
          (QuotientGroup.mk' (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} ↥Gstar))) := by
      rw [← Subgroup.relIndex_ker T (QuotientGroup.mk' W),
        ← Subgroup.relIndex_ker (Ch03.oPiPrimePiCore {p} ↥Gstar)
          (QuotientGroup.mk' (Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} ↥Gstar)),
        QuotientGroup.ker_mk', QuotientGroup.ker_mk', hW, hT,
        Subgroup.relIndex_map_map_of_injective _ _ Gstar.subtype_injective]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (isPGroup_oPiPrimePiCore_map (H := ↥Gstar) (p := p))
    exact IsPGroup.of_card (n := m) (hcard.trans hm)
  have hRbar_rank : pRank ↥(T.map (QuotientGroup.mk' W)) p ≤ 2 := by
    have hker_eq : ((QuotientGroup.mk' W).comp T.subtype).ker = W.subgroupOf T := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hrange_eq : ((QuotientGroup.mk' W).comp T.subtype).range
        = T.map (QuotientGroup.mk' W) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have e : (↥T ⧸ ((QuotientGroup.mk' W).comp T.subtype).ker) ≃*
        ↥((QuotientGroup.mk' W).comp T.subtype).range :=
      QuotientGroup.quotientKerEquivRange _
    have e' : (↥T ⧸ ((QuotientGroup.mk' W).comp T.subtype).ker) ≃*
        ↥(T.map (QuotientGroup.mk' W)) := hrange_eq ▸ e
    have hp'ker : ¬ p ∣ Nat.card ↥(((QuotientGroup.mk' W).comp T.subtype).ker) := by
      rw [hker_eq, show Nat.card ↥(W.subgroupOf T) = Nat.card ↥W from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_T).toEquiv]
      exact hW_p'
    calc pRank ↥(T.map (QuotientGroup.mk' W)) p
        ≤ pRank (↥T ⧸ ((QuotientGroup.mk' W).comp T.subtype).ker) p :=
          pRank_le_of_injective (f := e'.symm.toMonoidHom) e'.symm.injective
      _ ≤ pRank ↥T p := pRank_quotient_le_of_coprime hp'ker
      _ ≤ pRank ↥Gstar p := pRank_le_of_injective (Subgroup.inclusion_injective hT_le)
      _ ≤ 2 := hrank
  have hUbar_le : U.map (QuotientGroup.mk' W) ≤
      (T.map (QuotientGroup.mk' W)) ⊔ (V.map (QuotientGroup.mk' W)) := by
    rw [← Subgroup.map_sup]
    refine Subgroup.map_mono (le_trans hU_le_TV ?_)
    rw [sup_comm]
  have hoddQ : Odd (Nat.card (G ⧸ W)) := by
    have hdvd : Nat.card (G ⧸ W) ∣ Nat.card G := by
      have := Subgroup.index_dvd_card W
      simpa [Subgroup.index] using this
    rcases Nat.even_or_odd (Nat.card (G ⧸ W)) with he | ho
    · exact absurd (dvd_trans he.two_dvd hdvd) (by rw [Nat.odd_iff] at hodd; omega)
    · exact ho
  have hcentQ : _root_.commutator (G ⧸ W) ≤
      chiefFactorCentralizer (U.map (QuotientGroup.mk' W)) (V.map (QuotientGroup.mk' W)) :=
    commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup
      (G := G ⧸ W) hoddQ hp_odd hChiefBar hUbarBar_pg hRbar_pg hRbar_rank hUbar_le
  -- back-transfer to `G`
  rw [chiefFactorCentralizer.le_iff_commutator_le] at hcentQ ⊢
  have hcommQ : _root_.commutator (G ⧸ W) = (_root_.commutator G).map (QuotientGroup.mk' W) := by
    rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective W)]
  rw [hcommQ, ← Subgroup.map_commutator] at hcentQ
  have h1 : ⁅U, _root_.commutator G⁆ ≤ V ⊔ W := by
    have hc := Subgroup.comap_mono (f := QuotientGroup.mk' W) hcentQ
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc
    exact le_trans le_sup_left hc
  have h2 : ⁅U, _root_.commutator G⁆ ≤ U := Subgroup.commutator_le_left U _
  intro x hx
  exact inf_sup_le_of_inf_le hVU hUW (Subgroup.mem_inf.mpr ⟨h2 hx, h1 hx⟩)

end Cor419

end OddOrder.BG.Ch1.S04
