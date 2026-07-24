/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.ChiefFactor
import OddOrder.GroupTheory.FittingSelfCentralizing
import OddOrder.GroupTheory.FrattiniPGroup
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.AInvariantPiSubgroups
import Mathlib.Order.Minimal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BG §1A — Solvable group basics (Lem 1.1, Prop 1.2-1.4)

Bender–Glauberman §1, the opening solvable-group facts: Lemma 1.1 and
Propositions 1.2-1.4 (Fitting subgroup self-centralizing in solvable groups, coprime
action commutators).

Split from `OddOrder.BG.Ch1_Preliminary.S01_FrattiniBurnside` (issue 0149, the
longFile-1500 campaign); `S01_FrattiniBurnside` imports this leaf, so downstream
imports are unchanged.
-/

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01
open Pointwise

/-! ## §1A: Solvable group basics (Lem 1.1, Prop 1.2-1.4) -/

/-- **BG Lemma 1.1**: 有限群 `G` の **solvable** minimal normal `M` は
elementary abelian で `F(G)` の中心に入る.

book 強度 (2026-07-22 に `[IsSolvable G]` から一般化 — BG は `M` の可解性しか仮定しない;
`G` 可解のときは mathlib の部分群 instance が `[IsSolvable ↥M]` を自動供給するので
既存 call site は無変更).

CLAUDE.md no-wrapper policy 例外: 異なる Ch.3 結果 + nilpotent_normal_le_fitting の合成
+ Ch.4 の `le_centralizer_of_isMinimalNormal`. -/
theorem isMinimalNormal_le_fitting_and_isElementaryAbelian
    {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} [IsSolvable ↥M] (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
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
      exact OddOrder.GroupTheory.centralizer_fitting_le_fitting)
  have htriv :
      ∀ a : A, ∀ h ∈ OddOrder.Isaacs.Ch04.actionCommutator φ, (φ a) h = h := by
    intro a h hh
    exact Subgroup.mem_fixedPointsOfMulAut.mp (hF_le_fixed (hAC_le_F hh)) a
  exact OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    hCop (Or.inr inferInstance) htriv


end OddOrder.BG.Ch1.S01
