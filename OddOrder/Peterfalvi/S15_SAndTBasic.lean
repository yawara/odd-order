/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndTDefs

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndTBasic` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-- **`T`-side dual of `coprime_card_U_card_P_of_disjoint`** (Pf (13.2.a), V-side): for the type-II
member `T` with a `TypeIIData` witness `tdata` and `Q ⊓ V = ⊥`, the complement order `|V|` is
coprime to `|Q| = |T_F|`.  The `V`-side analogue used by the V-side of (13.17)/(14.10). -/
theorem coprime_card_V_card_Q_of_disjoint [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T) (hdisj : hyp.Q ⊓ hyp.V = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) := by
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hQnVn_inf : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊓
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
    rwa [hdisj, Subgroup.mem_bot] at hxQV
  have hQnVn_sup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hQnVn_inf)
    have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
      (hyp.V.subgroupOf (derivedInG hyp.T))
    rw [hQnVn_sup, Subgroup.coe_top] at hmul
    exact hmul.symm
  have hidx : (hyp.Q.subgroupOf (derivedInG hyp.T)).index = Nat.card ↥hyp.V := by
    rw [hVcompl.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]
  have hQ_mnh : hyp.Q = maxNilpotentNormalHall (derivedInG hyp.T) :=
    hQH.trans tdata.derived_fitting_eq.symm
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG hyp.T)
  rw [← hQ_mnh] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv, hidx] at hcop_idx
  exact hcop_idx.symm

/- `reconciled_typePData_T` (T-side type-`P` reconciliation) relocated to
`S15_SAndT_Setup` for the (13.9)/(13.10) counting layer (same namespace; citations unchanged). -/

/- `Q ⊓ V = ⊥` is now the honest `Hypothesis.Q_inf_V_eq_bot` field (threaded from the §16 constructor
via `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)); the former
`Q_inf_V_eq_bot_of_reconciled` — which derived it circularly from the sorried `reconciled_typePData_T`
— is retired.  V-side helpers use `hyp.Q_inf_V_eq_bot` directly. -/

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

/-- **`T`-side Fitting-TI source** (Pf (13.16), dual of the `S`-side type-uniform TI result):
`F(T)^#` is a TI-subset of `G` (with normalizer `T`).

On the `W₂`-side, `normalizer_W2_le_S` reduces `N_G(W₂) ≤ S` using the type-uniform
`S13.fittingIsTI_of_isTypeNonI`.  The `W₁`-side dual applies BG Theorem 15.7(a) to `T`: the
(14.9) conclusion `IsTypeII T`, together with the BG type dictionary
`proposition_type_classification` (`IsTypeII M ↔ IsTypeP2 M`), makes `T` **type-`P₂`**, so
`fittingIsTI_of_isTypeP2` applies directly.  (The `q < p` κ-Hall ordering pins the *matched-pair*
labelling `S`/`T`, not the type: both members of a type-`P₂` pair are type-`P₂` — the earlier belief
that `T` is type-`P₁` and needed the `M_F ≠ M_σ` route was mistaken.) -/
theorem fittingIsTI_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    OddOrder.BG.Ch4.S15.FittingIsTI hyp.T := by
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T :=
    ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.T_maximal).2.1).mp hTTypeII
  exact OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.T_maximal hP2

/-- **Peterfalvi (13.16), TI reduction for the `W₁`-side**: `N_G(W₁) ≤ T`.

The `T`-side dual of `normalizer_W2_le_S`.  `W₁ ≤ Q = T_F ≤ F(T)` (`W1_le_Q` +
`maxNilpotentNormalHall_le_fittingInG`), and `F(T)^#` is a TI-subset whose normalizer is `T`
(`fittingIsTI_T` + `normalizer_fittingInAmbient_eq_self`).  Any `g` normalizing `W₁` sends a
nonidentity `a ∈ W₁ ⊆ F(T)^#` to `g a g⁻¹ ∈ W₁ ⊆ F(T)^#`, so the TI condition places
`g ∈ N_G(F(T)) = T`.  This is the first (TI) half of the (13.16) `W₁`-confinement; the residual
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂` is the Maschke/Wielandt core (the dual of `normalizer_W2_within_S`). -/
theorem normalizer_W1_le_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.T := by
  have hTI := fittingIsTI_T hG hyp hTTypeII
  have hNorm := OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.T_maximal
  -- `W₁ ≤ Q ≤ F(T)`.
  have hW1F : hyp.W1 ≤ OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T := by
    refine (W1_le_Q hG hyp).trans ?_
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_fittingInG hyp.T
  -- a nonidentity element `a ∈ W₁` (`|W₁| = q ≥ 3`).
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro hbot
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  haveI : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥hyp.W1)
  set a : G := (x : G) with ha
  have haW1 : a ∈ hyp.W1 := x.2
  have hane : a ≠ 1 := fun h => hx1 (OneMemClass.coe_eq_one.mp (ha ▸ h))
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hgaW1 : g * a * g⁻¹ ∈ hyp.W1 := (hg a).mp haW1
  have hgane : g * a * g⁻¹ ≠ 1 := by
    intro h
    have key : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h] at key; simp only [mul_one, inv_mul_cancel] at key
    exact hane key
  have ha_sharp : a ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.T := by
    change a ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
    exact ⟨hW1F haW1, hane⟩
  have hga_sharp : g * a * g⁻¹ ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.T := by
    change g * a * g⁻¹ ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
    exact ⟨hW1F hgaW1, hgane⟩
  have hgN : g ∈ Subgroup.normalizer
      (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) :=
    hTI g ⟨a, ha_sharp, hga_sharp⟩
  rwa [hNorm] at hgN

/-- **Peterfalvi (13.16), Frobenius fixed-point-freeness of `W₂` on `V`**: `C_V(W₂) = ⊥` — no
nonidentity element of the complement `V` centralizes `W₂`.

The `T`-side dual of `centralizer_W1_inf_U_eq_bot`.  On the `S`-side the `U ⋊ W₁` Frobenius structure
comes from `basic_structure`; here the `V ⋊ W₂` Frobenius structure is read off the reconciled type-`P`
decomposition of `T` (`reconciled_typePData_T` + `typeP_uW1_frobenius`), with `V ≠ ⊥` supplied by the
(14.9) `T_typeII` core (`tdata.common`).  A nonidentity `x ∈ V` centralizing a nonidentity `w ∈ W₂`
would give `w x w⁻¹ = x`, contradicting the Frobenius condition (`IsFrobeniusGroup.conj_frobenius`).
This is the `C_D(W₂) ≤ C_V(W₂) = ⊥` input to the (13.16) `W₁`-side core. -/
theorem centralizer_W2_inf_V_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.centralizer (hyp.W2 : Set G) = ⊥ := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  -- a nonidentity `w ∈ W₂` (`|W₂| = p` prime).
  have hW2ne : hyp.W2 ≠ ⊥ := by
    intro hbot
    have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
    exact hyp.p_prime.one_lt.ne' hp1
  haveI : Nontrivial ↥hyp.W2 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
  obtain ⟨w0, hw0⟩ := exists_ne (1 : ↥hyp.W2)
  set w : G := (w0 : G) with hw
  have hwW2 : w ∈ hyp.W2 := w0.2
  have hwne : w ≠ 1 := fun h => hw0 (OneMemClass.coe_eq_one.mp (hw ▸ h))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxC⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxVW2 : x ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_left hxV
  have hwVW2 : w ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_right hwW2
  have hxN : (⟨x, hxVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.V.subgroupOf (hyp.V ⊔ hyp.W2) := by
    rw [Subgroup.mem_subgroupOf]; exact hxV
  have hwA : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2) := by
    rw [Subgroup.mem_subgroupOf]; exact hwW2
  have hxN1 : (⟨x, hxVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 :=
    fun h => hx1 (by simpa using congrArg (Subgroup.subtype _) h)
  have hwA1 : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 :=
    fun h => hwne (by simpa using congrArg (Subgroup.subtype _) h)
  have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hxC) w hwW2
  exact hfrob.conj_frobenius _ hwA hwA1 _ hxN hxN1 (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hcomm]; group)

/-- **Peterfalvi (13.16), trivial `W₂`-action on `K/C_K(W₁)` (`W₁`-side)**: for `g ∈ N_G(W₁)` and
`w ∈ W₂`, the "commutator representative" `g⁻¹ (w g w⁻¹)` centralizes `W₁`.

The `T`-side dual of `conj_W1_mem_centralizer_W2`, pure group theory: `w ∈ W₂` centralizes `W₁`
(`W₁ × W₂` abelian), and `g` normalizes `W₁`, so `w g w⁻¹` and `g` induce the same conjugation on
every `y ∈ W₁`, whence `g⁻¹ (w g w⁻¹)` fixes `y`.  Feeds the coprime fixed-point lifting of the
`W₁`-side crux `N_V(W₁) ≤ C_G(W₁)`. -/
theorem conj_W2_mem_centralizer_W1 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {g : G} (hg : g ∈ Subgroup.normalizer (hyp.W1 : Set G))
    {w : G} (hw : w ∈ hyp.W2) :
    g⁻¹ * (w * g * w⁻¹) ∈ Subgroup.centralizer (hyp.W1 : Set G) := by
  -- `w` centralizes `W₁`.
  have hwC : ∀ z ∈ hyp.W1, w * z = z * w := fun z hz => (hyp.W1_commutes_W2 z hz w hw).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyW1 : y ∈ hyp.W1 := hy
  -- `g y g⁻¹ ∈ W₁`.
  have hy1 : g * y * g⁻¹ ∈ hyp.W1 := (Subgroup.mem_normalizer_iff.mp hg y).mp hyW1
  -- `w⁻¹ y w = y` and `w (g y g⁻¹) w⁻¹ = g y g⁻¹`.
  have h1 : w⁻¹ * y * w = y := by
    rw [mul_assoc, ← hwC y hyW1, inv_mul_cancel_left]
  have h2 : w * (g * y * g⁻¹) * w⁻¹ = g * y * g⁻¹ := by
    rw [hwC _ hy1, mul_assoc, mul_inv_cancel, mul_one]
  -- `w g w⁻¹` and `g` induce the same conjugation on `y`.
  have hsame : (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹ = g * y * g⁻¹ := by
    calc (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹
        = w * g * (w⁻¹ * y * w) * g⁻¹ * w⁻¹ := by group
      _ = w * g * y * g⁻¹ * w⁻¹ := by rw [h1]
      _ = w * (g * y * g⁻¹) * w⁻¹ := by group
      _ = g * y * g⁻¹ := h2
  -- hence `n' := g⁻¹ (w g w⁻¹)` fixes `y`.
  have hn' : (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹ = y := by
    calc (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹
        = g⁻¹ * ((w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hsame]
      _ = y := by group
  exact (mul_inv_eq_iff_eq_mul.mp hn').symm

/-- **`T`-side analogue of the carried `S_U_commutative` fact** (Pf (13.2.a), V-side): the complement
`V` of the type-II member `T` is commutative.  Here `IsTypeII T` is a hypothesis
(the (14.9) `T_typeII` conclusion, supplied by the caller).  Sources the `T`-side type-`P` structure
from the off-spine `reconciled_typePData_T` (not the withdrawn `Tdata` carrier). -/
theorem isMulCommutative_V [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) : IsMulCommutative ↥hyp.V := by
  obtain ⟨tdata⟩ := hTTypeII
  -- `Q ⊓ V = ⊥` is now the honest `Hypothesis` field `Q_inf_V_eq_bot` (threaded from the §16
  -- constructor's `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)), replacing the
  -- former circular route through the sorried `reconciled_typePData_T`.
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hdisj, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hV'compl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.T)) := by
    rw [hQH]; exact tdata.typeP.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv, hVcompl.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]
    exact (coprime_card_V_card_Q_of_disjoint hyp tdata hdisj).symm
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.Q := _hG.solvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hVcompl hV'compl
  have h2 : IsMulCommutative ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe tdata.typeP.U_le).symm tdata.U_commutative
  rw [← hn] at h2
  have h4 : IsMulCommutative ↥(hyp.V.subgroupOf (derivedInG hyp.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).symm h2
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hV_le) h4

/-- **Peterfalvi (13.16), the crux `N_V(W₁) ≤ C_G(W₁)`** (`W₁`-side dual of
`normalizer_U_inf_W2_le_centralizer_W2`): every element of `N_V(W₁) := V ⊓ N_G(W₁)` centralizes `W₁`.

The conjugation action of `W₂` on the abelian `V` is coprime (`(|W₂|, |V|) = 1` from the `V ⋊ W₂`
Frobenius structure) with fixed points `C_V(W₂) = ⊥` (`centralizer_W2_inf_V_eq_bot`).  For `g ∈ N_V(W₁)`,
`W₂` fixes the coset `g · C_V(W₁)` (`conj_W2_mem_centralizer_W1`), so the coprime fixed-point lifting
(`Isaacs.Ch04.coprime_fixedPoints_quotient`) produces a `W₂`-fixed representative `c ∈ C_V(W₂) = ⊥`;
hence `g ≡ 1 (mod C_V(W₁))`, i.e. `g ∈ C_G(W₁)`.  Gated on the (14.9) `T_typeII` structure (via the
`V ⋊ W₂` Frobenius and the abelianness of `V`, both from the reconciled type-`P` data of `T`). -/
theorem normalizer_V_inf_W1_le_centralizer_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  haveI hVcomm : IsMulCommutative ↥hyp.V := isMulCommutative_V hG hyp ⟨tdata⟩
  -- conjugation action `φ : ↥W₂ → MulAut ↥V`.
  letI actV : MulDistribMulAction ↥hyp.W2 ↥hyp.V :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (hyp.V : Set G))) ↥hyp.V
      (Subgroup.inclusion hyp.W2_normalizes_V)
  set φ : ↥hyp.W2 →* MulAut ↥hyp.V := MulDistribMulAction.toMulAut ↥hyp.W2 ↥hyp.V with hφ
  have hφ_coe : ∀ (a : ↥hyp.W2) (x : ↥hyp.V),
      (hyp.V.subtype ((φ a) x)) = (↑a) * (hyp.V.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
  -- `N := C_V(W₁)`, normal in the abelian `↥V`.
  set N : Subgroup ↥hyp.V :=
    (hyp.V ⊓ Subgroup.centralizer (hyp.W1 : Set G)).subgroupOf hyp.V with hN_def
  haveI hNnorm : N.Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  -- coprimality `(|W₂|, |V|) = 1`.
  have hCop : Nat.Coprime (Nat.card ↥hyp.W2) (Nat.card ↥hyp.V) := by
    have hk := hfrob.coprime_card_kernel_complement
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      Nat.coprime_comm] at hk
  -- `W₂ ≤ C_G(W₁)`, so `N` is `W₂`-invariant.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hyp.W1_commutes_W2 z hz x hx
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hN_def, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.mp hx
    have hval : (hyp.V.subtype ((φ a) x)) = (↑a) * (hyp.V.subtype x) * (↑a)⁻¹ := hφ_coe a x
    refine Subgroup.mem_inf.mpr ⟨((φ a) x).2, ?_⟩
    rw [show ((φ a) x : G) = (hyp.V.subtype ((φ a) x)) from rfl, hval]
    exact (Subgroup.centralizer (hyp.W1 : Set G)).mul_mem
      (Subgroup.mul_mem _ (hW2_le_C a.2) hxC) (Subgroup.inv_mem _ (hW2_le_C a.2))
  -- main: `g ∈ V ⊓ N_G(W₁)` ⟹ `g ∈ C_G(W₁)`.
  intro g hg
  obtain ⟨hgV, hgNW1⟩ := Subgroup.mem_inf.mp hg
  set gg : ↥hyp.V := ⟨g, hgV⟩ with hgg
  -- `W₂` fixes the coset `gg · N`.
  have hg_fix : ∀ a : ↥hyp.W2, ∃ n ∈ N, (φ a) gg = gg * n := by
    intro a
    refine ⟨gg⁻¹ * (φ a) gg, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [hN_def, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨(gg⁻¹ * (φ a) gg).2, ?_⟩
    have hval : ((gg⁻¹ * (φ a) gg : ↥hyp.V) : G) = g⁻¹ * ((a : G) * g * (a : G)⁻¹) := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv,
        show ((φ a) gg : G) = (hyp.V.subtype ((φ a) gg)) from rfl, hφ_coe a gg]
      rfl
    rw [hval]
    exact conj_W2_mem_centralizer_W1 hG hyp hgNW1 a.2
  obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ) hCop
      (Or.inr (isSolvable_of_comm (fun a b => mul_comm' a b))) hN_inv hg_fix
  -- `c` is `W₂`-fixed ⟹ `(c:G) ∈ C_V(W₂) = ⊥` ⟹ `c = 1`.
  have hc1 : c = 1 := by
    have hcmem : (c : G) ∈ hyp.V ⊓ Subgroup.centralizer (hyp.W2 : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfix := hc_fix ⟨w, hw⟩
      have hco : (hyp.V.subtype c) = (w : G) * (hyp.V.subtype c) * (w : G)⁻¹ := by
        have e1 := hφ_coe ⟨w, hw⟩ c
        rw [hfix] at e1
        exact e1
      exact mul_inv_eq_iff_eq_mul.mp hco.symm
    rw [centralizer_W2_inf_V_eq_bot hG hyp ⟨tdata⟩, Subgroup.mem_bot] at hcmem
    exact Subtype.ext hcmem
  -- `gg = m⁻¹ ∈ N` ⟹ `g ∈ C_G(W₁)`.
  rw [hc1, eq_comm, mul_eq_one_iff_eq_inv] at hc_eq
  have hggN : gg ∈ N := by rw [hc_eq]; exact N.inv_mem hm
  rw [hN_def, Subgroup.mem_subgroupOf] at hggN
  exact (Subgroup.mem_inf.mp hggN).2

/-- **Peterfalvi (13.16), the `W₁`-side core assembly** (`V ⊓ N_G(W₁) = ⊥`, `T`-side dual of
`normalizer_U_inf_W2_eq_bot_of_data`).

Given the coprime-action datum `hcop : Coprime |Q| |V ⋊ W₂|`, the type-`P₂`-dual structure facts
`hQ_elemAb : Q` elementary abelian (14.2.a, `T`-side) and `hDbot : V ⊓ C_G(Q) = ⊥` (13.12 `d = 1`,
`T`-side), the assembly closes the `W₁`-side core from the proven crux `K ≤ C_G(W₁)`
(`normalizer_V_inf_W1_le_centralizer_W1`) exactly as on the `W₂`-side:

* the coprime `K`-action on the abelian `Q` decomposes `Q = (C_G(K) ⊓ Q) ⊕ ⁅Q, K⁆`
  (`fitting_coprime_abelian_decomp`, Gorenstein Thm 2.3);
* `W₂` acts fixed-point-freely on `⁅Q, K⁆`: a `W₂`-fixed `n ∈ ⁅Q, K⁆ ⊆ Q` lies in
  `T' ⊓ C_G(x) = tpd.W2 = W₁` (`TypePData.centralizer_W1` + the reconciliation `tpd.W2 = W₁`)
  `⊆ C_G(K) ⊓ Q`, so `n = 1`;
* the full `V ⋊ W₂` Frobenius (`typeP_uW1_frobenius`; `V` abelian ⟹ `V ≤ N_G(⁅Q,K⁆)`) centralizes
  `⁅Q, K⁆` by Wielandt (`frobenius_kernel_centralizes_of_complement_fpf`);
* so `⁅Q, K⁆ = ⊥`, i.e. `K ≤ C_G(Q)`, giving `K ≤ V ⊓ C_G(Q) = ⊥`.

The two structural inputs `hQ_elemAb`/`hDbot` are the `T`-side duals of `basic_structure`'s
`P_elementaryAbelian` and `U_inf_centralizer_P_eq_bot` (both (14.9)-`T_typeII`-gated); the rest is
proven group theory. -/
theorem normalizer_V_inf_W1_eq_bot_of_data [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)))
    (hQ_elemAb : IsElementaryAbelian hyp.q ↥hyp.Q)
    (hDbot : hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW1] at h
  haveI hVcomm : IsMulCommutative ↥hyp.V := isMulCommutative_V hG hyp ⟨tdata⟩
  set K := hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) with hK_def
  have hK_le_V : K ≤ hyp.V := inf_le_left
  -- crux: `K ≤ C_G(W₁)`.
  have hKC : K ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    normalizer_V_inf_W1_le_centralizer_W1 hG hyp ⟨tdata⟩
  -- `Q` abelian.
  haveI hQcomm : IsMulCommutative ↥hyp.Q := IsMulCommutative.of_comm hQ_elemAb.comm
  -- divisibilities `|K| ∣ |V| ∣ |V⋊W₂|`, from the coprime-action datum `hcop`.
  have hVdvdVW2 : Nat.card ↥hyp.V ∣ Nat.card ↥(hyp.V ⊔ hyp.W2) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hKdvdV : Nat.card ↥K ∣ Nat.card ↥hyp.V := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_V).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopQK : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥K) :=
    hcop.coprime_dvd_right (hKdvdV.trans hVdvdVW2)
  -- normalizer facts: `T ≤ N(Q)`, `V ≤ T`, `W₂ ≤ T`, `W₂ ≤ N(W₁)`.
  have hMFleM : maxNilpotentNormalHall hyp.T ≤ hyp.T :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T)
  have hM'le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hV_le_T : hyp.V ≤ hyp.T :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.T_deriv_eq_QV.symm)) hM'le
  have hW2_le_T : hyp.W2 ≤ hyp.T := htpdW1 ▸ tpd.W1_le
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    exact hyp.W1_commutes_W2 z hz x hx
  have hW2_le_N : hyp.W2 ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hW2_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hK_norm_Q : K ≤ Subgroup.normalizer (hyp.Q : Set G) := (hK_le_V.trans hV_le_T).trans hT_norm_Q
  -- `V ≤ N(K)` (`V` abelian, `K ≤ V`).
  haveI hKnormalV : (K.subgroupOf hyp.V).Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  have hV_norm_K : hyp.V ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hK_le_V
  -- `W₂ ≤ N(K)` (`W₂ ≤ N(V)` and `W₂ ≤ N(N(W₁))`).
  have hW2_norm_K : hyp.W2 ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]; intro n
    have hwV := Subgroup.mem_normalizer_iff.mp (hyp.W2_normalizes_V hw) n
    have hwN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hW2_le_N hw)) n
    rw [hK_def, Subgroup.mem_inf, Subgroup.mem_inf, hwV, hwN]
  -- Gorenstein 2.3 decomposition `Q = (C(K) ⊓ Q) ⊕ ⁅Q, K⁆`.
  obtain ⟨hdec_inf, hdec_sup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp hK_norm_Q hcopQK
  have hQK_le_Q : (⁅hyp.Q, K⁆ : Subgroup G) ≤ hyp.Q := le_sup_right.trans (le_of_eq hdec_sup)
  -- `W₁ ≤ C(K) ⊓ Q`.
  have hW1_le_Q' : hyp.W1 ≤ hyp.Q := W1_le_Q hG hyp
  have hW1_le_CK : hyp.W1 ≤ Subgroup.centralizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hk)) y hy).symm
  -- Wielandt: `V ≤ C(⁅Q,K⁆)`.
  have hVEnorm : hyp.V ⊔ hyp.W2 ≤ Subgroup.normalizer ((⁅hyp.Q, K⁆ : Subgroup G) : Set G) := by
    rw [sup_le_iff]
    refine ⟨fun v hv => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator ((hV_le_T.trans hT_norm_Q) hv)
      (hV_norm_K hv), fun w hw => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator
      ((hW2_le_T.trans hT_norm_Q) hw) (hW2_norm_K hw)⟩
  haveI hQKsolv : IsSolvable ↥(⁅hyp.Q, K⁆ : Subgroup G) :=
    isSolvable_of_comm (fun a b => Subtype.ext (by
      have h := hQ_elemAb.comm (⟨(a : G), hQK_le_Q a.2⟩ : ↥hyp.Q) (⟨(b : G), hQK_le_Q b.2⟩ : ↥hyp.Q)
      have h2 := congrArg (Subgroup.subtype hyp.Q) h
      simpa using h2))
  have hQKdvdQ : Nat.card ↥(⁅hyp.Q, K⁆ : Subgroup G) ∣ Nat.card ↥hyp.Q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK_le_Q).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopQKfrob : Nat.Coprime (Nat.card ↥(⁅hyp.Q, K⁆ : Subgroup G))
      (Nat.card ↥(hyp.V ⊔ hyp.W2)) := hcop.coprime_dvd_left hQKdvdQ
  have hVcent : hyp.V ≤ Subgroup.centralizer ((⁅hyp.Q, K⁆ : Subgroup G) : Set G) :=
    frobenius_kernel_centralizes_of_complement_fpf hVEnorm hVW2frob hQKsolv hcopQKfrob
      (by
        intro n hnQK hnfix
        -- `n ∈ ⁅Q,K⁆ ⊆ Q` fixed by all of `W₂` ⟹ `n ∈ tpd.W2 = W₁ ⊆ C(K) ⊓ Q` ⟹ `n = 1`.
        have hnQ : n ∈ hyp.Q := hQK_le_Q hnQK
        have hW2ne : tpd.W1 ≠ ⊥ := tpd.W1_nontrivial
        haveI : Nontrivial ↥tpd.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
        obtain ⟨x0, hx0⟩ := exists_ne (1 : ↥tpd.W1)
        have hxW2 : (x0 : G) ∈ hyp.W2 := htpdW1 ▸ x0.2
        have hxne : (x0 : G) ≠ 1 := fun h => hx0 (OneMemClass.coe_eq_one.mp h)
        have hnCx : (x0 : G) * n * (x0 : G)⁻¹ = n := hnfix _ hxW2
        have hnCent : n ∈ Subgroup.centralizer ({(x0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; intro z hz
          rw [Set.mem_singleton_iff] at hz; subst hz
          exact (mul_inv_eq_iff_eq_mul.mp hnCx)
        have hnM' : n ∈ derivedInG hyp.T := by
          have hQM' : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
          exact hQM' hnQ
        have hreg := tpd.centralizer_W1 (x0 : G) x0.2 hxne
        have hnW1 : n ∈ hyp.W1 := by
          rw [← htpdW2, ← hreg]; exact Subgroup.mem_inf.mpr ⟨hnM', hnCent⟩
        have hnInf : n ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.Q) ⊓ (⁅hyp.Q, K⁆ : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hW1_le_CK hnW1, hnQ⟩, hnQK⟩
        rw [hdec_inf, Subgroup.mem_bot] at hnInf
        exact hnInf)
  -- `⁅Q,K⁆ ≤ C(K) ⊓ Q`, hence `⁅Q,K⁆ = ⊥`.
  have hQK_le_CK : (⁅hyp.Q, K⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hVcent (hK_le_V hk)) x hx).symm
  have hQK_bot : (⁅hyp.Q, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.Q) ⊓ (⁅hyp.Q, K⁆ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hQK_le_CK hx, hQK_le_Q hx⟩, hx⟩
    rwa [hdec_inf] at this
  -- `⁅Q,K⁆ = ⊥ ⟹ K ≤ C(Q) ⟹ K ≤ V ⊓ C(Q) = ⊥`.
  have hK_le_CQ : K ≤ Subgroup.centralizer (hyp.Q : Set G) := by
    have hQcentK : hyp.Q ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := hyp.Q) (H₂ := K)).mp hQK_bot
    intro k hk
    rw [Subgroup.mem_centralizer_iff]; intro q hq
    exact ((Subgroup.mem_centralizer_iff.mp (hQcentK hq)) k hk).symm
  have : K ≤ hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) := le_inf hK_le_V hK_le_CQ
  rw [hDbot] at this
  exact le_bot_iff.mp this

/-- **Peterfalvi (13.16), the `W₁`-side coprime-action datum**: `Coprime |Q| |V ⋊ W₂|` — the
complement `V ⋊ W₂` acts coprimely on the Fitting kernel `Q = T_F`.  The `T`-side dual of
`coprime_card_P_card_UW1`.

`Q = T_F` is the normal nilpotent Hall subgroup of `T` (`maxNilpotentNormalHall`, so
`Coprime |Q| [T:Q]`), and `V ⋊ W₂` complements `Q` in `T`: from the honest `Hypothesis` fields
`W2_isComplement_T_deriv` (`M' ⋊ W₂ = T`) and `Q_inf_V_eq_bot`/`T_deriv_eq_QV` (`Q ⋊ V = M'`) one
reads off `Q ⊓ (V ⊔ W₂) = ⊥` and `Q ⊔ (V ⊔ W₂) = T`, so `[T:Q] = |V ⊔ W₂|`.  **Fully honest /
ungated** — both complements come from the §16 constructor (`typeP_derivedInG_isComplement_kappaHall`
/ `exists_kappaHall_invariant_complement_to_MF`, via `T_nonI`, not (14.9)); no dependence on the
sorried `reconciled_typePData_T`. -/
theorem coprime_card_Q_card_VW2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by
  -- Fully honest (ungated): built from the `Hypothesis` fields `Q_inf_V_eq_bot` (`Q ⊓ V = ⊥`) and
  -- `W2_isComplement_T_deriv` (`T = T' ⋊ W₂`), both threaded from the §16 constructor's
  -- `exists_kappaHall_invariant_complement_to_MF` / `typeP_derivedInG_isComplement_kappaHall`
  -- (ungated by (14.9)).  No longer routed through the sorried `reconciled_typePData_T`.
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_M' : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le_M' : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hQ_le_T : hyp.Q ≤ hyp.T := hQ_le_M'.trans hM'_le_T
  have hW2_le_T : hyp.W2 ≤ hyp.T := by
    have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  have hVW2_le_T : hyp.V ⊔ hyp.W2 ≤ hyp.T := sup_le (hV_le_M'.trans hM'_le_T) hW2_le_T
  -- `Q ⊓ V = ⊥` (`Q_inf_V_eq_bot`).
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  -- `M' ⊓ W₂ = ⊥` from the complement `T = T' ⋊ W₂` (`W2_isComplement_T_deriv`).
  have hM'W2 : derivedInG hyp.T ⊓ hyp.W2 = ⊥ := by
    have hd := disjoint_iff.mp hyp.W2_isComplement_T_deriv.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW2⟩
    have hxT : x ∈ hyp.T := hM'_le_T hxM'
    have hmem : (⟨x, hxT⟩ : ↥hyp.T) ∈
        ((derivedInG hyp.T).subgroupOf hyp.T) ⊓ (hyp.W2.subgroupOf hyp.T) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr hxW2⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- `Q ⊔ (V ⊔ W₂) = T` from `T = T' ⋊ W₂` and `T' = Q ⊔ V`.
  have hTsup : hyp.Q ⊔ (hyp.V ⊔ hyp.W2) = hyp.T := by
    have htop := hyp.W2_isComplement_T_deriv.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.T.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_T,
      Subgroup.map_subgroupOf_eq_of_le hW2_le_T, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.T_deriv_eq_QV] at hmap
    rw [← sup_assoc]; exact hmap
  -- `Q ⊓ (V ⊔ W₂) = ⊥`.
  have hQVW2_disj : hyp.Q ⊓ (hyp.V ⊔ hyp.W2) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxQ, hxVW2⟩ := Subgroup.mem_inf.mp hx
    have hxVW2' : (x : G) ∈ (↑(hyp.V ⊔ hyp.W2) : Set G) := hxVW2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.V hyp.W2 hyp.W2_normalizes_V] at hxVW2'
    obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_mul.mp hxVW2'
    have hwM' : w ∈ derivedInG hyp.T := by
      have : w = v⁻¹ * x := by rw [← hvw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV_le_M' (SetLike.mem_coe.mp hv)))
        (hQ_le_M' hxQ)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.T ⊓ hyp.W2 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W2, Subgroup.mem_bot] at this
    have hxv : x = v := by rw [← hvw, hw1, mul_one]
    have hxQV : x ∈ hyp.Q ⊓ hyp.V := Subgroup.mem_inf.mpr ⟨hxQ, hxv ▸ SetLike.mem_coe.mp hv⟩
    rwa [hdisj, Subgroup.mem_bot] at hxQV
  -- `V ⋊ W₂` complements `Q` in `↥T`; hence `[T:Q] = |V ⋊ W₂|`.
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_T).mpr hT_norm_Q
  have hcompl : Subgroup.IsComplement' ((hyp.V ⊔ hyp.W2).subgroupOf hyp.T)
      (hyp.Q.subgroupOf hyp.T) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      have hyQV : (y : G) ∈ hyp.Q ⊓ (hyp.V ⊔ hyp.W2) := ⟨hy.2, hy.1⟩
      rw [hQVW2_disj, Subgroup.mem_bot] at hyQV
      rw [Subgroup.mem_bot]; exact Subtype.ext hyQV
    · have hsup : ((hyp.V ⊔ hyp.W2).subgroupOf hyp.T) ⊔ (hyp.Q.subgroupOf hyp.T) = ⊤ := by
        rw [sup_comm, ← Subgroup.subgroupOf_sup hQ_le_T hVW2_le_T, hTsup, Subgroup.subgroupOf_self]
      rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]
  have hindex : (hyp.Q.subgroupOf hyp.T).index = Nat.card ↥(hyp.V ⊔ hyp.W2) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW2_le_T).toEquiv
  -- `Q` is Hall in `T`: `Coprime |Q| [T:Q]`.
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
  rw [← hyp.Q_eq_TF] at hHall
  have hcopIdx : Nat.Coprime (Nat.card ↥hyp.Q) (hyp.Q.subgroupOf hyp.T).index := by
    have hcard_eq : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv
    exact hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
  rw [hindex] at hcopIdx
  exact hcopIdx

/-- **Peterfalvi (14.2.a), `T`-side dual of `BasicStructureGated.P_elementaryAbelian`**: the Fitting
kernel `Q = T_F` is elementary abelian of exponent `q`.

On the `S`-side this is the `§16`-carrier fact `P_elementaryAbelian` (from the type-`P₂` structure of
`S`); `T` is likewise type-`P₂` (`IsTypeII T ↔ IsTypeP2 T`, `proposition_type_classification`), so the
same σ-structure fact holds — `T_σ = T_F` is the elementary-abelian `q`-group of rank `p` on which the
prime-order `κ`-factor `W₂` acts.  Proven as the exact dual of the `S`-side `P_elementaryAbelian`
(`S15_SAndT_Setup`, now sorry-free): the (14.9) type-II `T` gives a `TypesIIIIIIVSetup T` from the
reconciled `TypePData T` (`reconciled_typePData_T`) whose chief kernel `N = ⊥` (since `|Q| = q^p`,
`card_Q_eq`), so `Q` itself is the chief factor and carries `quotient_elementaryAbelian` at
`chief.p = q`.  Gated on the (14.9) `T_typeII` (through `card_Q_eq` / `reconciled_typePData_T`);
supplies the `hQ_elemAb` input of `normalizer_V_inf_W1_eq_bot_of_data`. -/
theorem Q_elementaryAbelian_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    IsElementaryAbelian hyp.q ↥hyp.Q := by
  classical
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  let setupT : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T :=
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, tdata.common.2.2⟩
      type_alt := Or.inl hTTypeII }
  obtain ⟨chief, _⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG setupT
  haveI := chief.N_normal
  have hHeq : (setupT.H : Subgroup G) = hyp.Q := by
    change tpd.H = hyp.Q; rw [tpd.H_eq, hyp.Q_eq_TF]
  have hqdim : setupT.q = hyp.p := by
    change Nat.card ↥tpd.W1 = hyp.p; rw [htpdW1, ← hyp.p_eq_card_W2]
  have hcardH : Nat.card ↥setupT.H = hyp.q ^ hyp.p := by
    -- Wielandt (9.3) order relation `|H| = |W₂|^|W₁|` for the type-II `T` (as in `card_Q_eq`,
    -- inlined since `card_Q_eq` is downstream of this lemma).
    have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG setupT).1 hTTypeII
    have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
    have hW2card : Nat.card ↥tpd.W2 = hyp.q := by rw [htpdW2, ← hyp.q_eq_card_W1]
    rw [hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
    exact hord2
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hqdim] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  -- `q^p = chief.p^p · |N|` forces `chief.p = q` and `|N| = 1`.
  have hdvd : chief.p ∣ hyp.q ^ hyp.p := by
    refine dvd_trans (dvd_pow_self chief.p hyp.p_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.q :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.q_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN : chief.N = ⊥ := by
    have hN1 : Nat.card ↥chief.N = 1 := by
      have := hsplit.symm
      nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.q_prime.pos hyp.p]
    exact Subgroup.card_eq_one.mp hN1
  have hEA : IsElementaryAbelian hyp.q ↥setupT.H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

/-- **Peterfalvi (13.16), explicit-`D = ⊥` Maschke/Wielandt core for the `W₁`-side**:
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.

The `T`-side dual of `normalizer_W2_within_S`.  The `T`-internal residual of the (13.16)
`W₁`-confinement (after the TI reduction `N_G(W₁) ≤ T` of `normalizer_W1_le_T`).  Reduced by the
**Dedekind modular law** to the core `N_V(W₁) = ⊥`
(`normalizer_V_inf_W1_eq_bot_of_data`): writing
`T = (Q ⊔ V) ⊔ W₂` (`T_deriv_eq_QV` + the reconciled complement `M' ⋊ W₂ = T`), and using
`Q, W₂ ≤ C_G(W₁) ≤ N_G(W₁)` (`Q` elementary abelian, `W = W₁ × W₂` abelian), modularity peels off
`W₂` and `Q`. -/
theorem normalizer_W1_within_T_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) ⊓ hyp.T ≤ hyp.Q ⊔ hyp.W2 := by
  obtain ⟨tpd, _, htpdW1, _⟩ := reconciled_typePData_T hG hyp
  have hK : hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ :=
    normalizer_V_inf_W1_eq_bot_of_data hG hyp hTTypeII (coprime_card_Q_card_VW2 hG hyp)
      (Q_elementaryAbelian_T hG hyp hTTypeII) (by rw [← hyp.D_eq]; exact hDbot)
  -- `W₂ ≤ C_G(W₁)`: `W = W₁ × W₂` is abelian.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hyp.W1_commutes_W2 y (SetLike.mem_coe.mp hy) x hx
  -- `Q ≤ C_G(W₁)`: `W₁ ≤ Q` and `Q` elementary abelian give `Q` centralizes `W₁`.
  have hQ_le_C : hyp.Q ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    have hQ_elemAb := Q_elementaryAbelian_T hG hyp hTTypeII
    have hW1Q := W1_le_Q hG hyp
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : y ∈ hyp.Q := hW1Q (SetLike.mem_coe.mp hy)
    have h := hQ_elemAb.comm (⟨y, hyQ⟩ : ↥hyp.Q) (⟨g, hg⟩ : ↥hyp.Q)
    have h2 := congrArg (Subgroup.subtype hyp.Q) h
    simpa using h2
  have hQ_le_N : hyp.Q ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hQ_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hW2_le_N : hyp.W2 ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hW2_le_C.trans (Subgroup.centralizer_le_normalizer _)
  -- `Q ⊴ T` and `M' := derivedInG T ⊴ T`, so `T ≤ N_G(Q)` and `T ≤ N_G(M')`.
  have hMFleM : maxNilpotentNormalHall hyp.T ≤ hyp.T :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T)
  have hM'le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hM'_normal : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by
    rw [show (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective]]
    infer_instance
  have hT_norm_M' : hyp.T ≤ Subgroup.normalizer ((derivedInG hyp.T : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'le).mp hM'_normal
  have hV_le_T : hyp.V ≤ hyp.T :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.T_deriv_eq_QV.symm)) hM'le
  have hW2_le_T : hyp.W2 ≤ hyp.T := htpdW1 ▸ tpd.W1_le
  -- `T = derivedInG T ⊔ W₂` (the reconciled complement `M' ⋊ W₂ = T`).
  have hTsup : derivedInG hyp.T ⊔ hyp.W2 = hyp.T := by
    have htop := tpd.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.T.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'le,
      Subgroup.map_subgroupOf_eq_of_le tpd.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [htpdW1] at hmap
    exact hmap
  -- **Sub-goal A** (Dedekind): `M' ⊓ N_G(W₁) = Q`.
  have hHV : ((derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G)) ⊓ hyp.V = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_right hyp.V inf_le_right) ?_)
    rw [inf_comm]; exact hK.le
  have hQ_le_M' : hyp.Q ≤ derivedInG hyp.T :=
    le_trans le_sup_left (le_of_eq hyp.T_deriv_eq_QV.symm)
  have hMN : (derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G) = hyp.Q := by
    have happ := OddOrder.BG.Ch3.S12.eq_sup_inf_of_le_normalizer (hV_le_T.trans hT_norm_Q)
      (le_inf hQ_le_M' hQ_le_N) (inf_le_left.trans (le_of_eq hyp.T_deriv_eq_QV))
    rw [happ, hHV, sup_bot_eq]
  -- **Sub-goal B** (element-wise): `g ∈ N_G(W₁) ⊓ T`; write `g = w·m` (`w ∈ W₂`, `m ∈ M'`).
  intro g hg
  obtain ⟨hgN, hgT⟩ := Subgroup.mem_inf.mp hg
  have hmem : (g : G) ∈ ((hyp.W2 : Set G) * (derivedInG hyp.T : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right hyp.W2 (derivedInG hyp.T)
      (hW2_le_T.trans hT_norm_M'), SetLike.mem_coe, sup_comm, hTsup]
    exact hgT
  obtain ⟨w, hw, m, hm, hwm⟩ := Set.mem_mul.mp hmem
  have hmN : m ∈ Subgroup.normalizer (hyp.W1 : Set G) := by
    have hm_eq : m = w⁻¹ * g := by rw [← hwm]; group
    rw [hm_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW2_le_N (SetLike.mem_coe.mp hw))) hgN
  have hmQ : m ∈ hyp.Q := by
    have hmem2 : m ∈ (derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G) :=
      Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hm, hmN⟩
    rwa [hMN] at hmem2
  rw [← hwm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (SetLike.mem_coe.mp hw))
    (Subgroup.mem_sup_left hmQ)

/-- **Peterfalvi (13.16), structural core for the `W₁`-side** (conjunct 3 of
`normalizer_W1_structure_of_D_eq_bot`):
the Frobenius/Wielandt containment `N_G(W₁) ≤ Q ⊔ W₂`.  Assembles the TI reduction `N_G(W₁) ≤ T`
(`normalizer_W1_le_T`, proven) and the Maschke/Wielandt core `N_G(W₁) ⊓ T ≤ Q ⊔ W₂`
(`normalizer_W1_within_T_of_D_eq_bot`): every `g ∈ N_G(W₁)` lies in `T`, hence in
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.
`T`-side dual of `normalizer_W2_structure`; gated on (14.9) `T_typeII` via the `W₁`-side core. -/
theorem normalizer_W1_le_QW2_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 := by
  intro g hg
  have hgT : g ∈ hyp.T := normalizer_W1_le_T hG hyp hTTypeII hg
  exact normalizer_W1_within_T_of_D_eq_bot hG hyp hTTypeII hDbot
    (Subgroup.mem_inf.mpr ⟨hg, hgT⟩)

/-- **Peterfalvi (13.16), structural core** (Coq `FTtypeP_norm_cent_compl`, `PFsection13.v:1519`), the
three atomic facts carrying the content of (13.16), **assembled** for the (14.9) type-II member `T`:

* `W₁ ≤ Q` (`W1_le_Q`, proven) — the `T`-side dual of `W₂ ≤ P`, placing the cyclic `q`-factor `W₁`
  inside the `T`-Fitting kernel `Q = T_F`;
* `Q` abelian — from `Q_elementaryAbelian_T` (the one deep §14 σ-residual, dual of the `S`-side
  `P_elementaryAbelian`, itself sorried);
* `N_G(W₁) ≤ Q ⊔ W₂` (`normalizer_W1_le_QW2_of_D_eq_bot`, proven) — the TI reduction
  `normalizer_W1_le_T` + the Maschke/Wielandt core `normalizer_W1_within_T_of_D_eq_bot`.

`IsTypeII T` is threaded from `exists_LHypothesis` (§16, via (14.9) `T_typeII`); conjuncts 1 and 3 are
sorry-free, so the residual is exactly conjunct 2. -/
theorem normalizer_W1_structure_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    hyp.W1 ≤ hyp.Q ∧ IsMulCommutative ↥hyp.Q ∧
      Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 :=
  ⟨W1_le_Q hG hyp,
    IsMulCommutative.of_comm (Q_elementaryAbelian_T hG hyp hTTypeII).comm,
    normalizer_W1_le_QW2_of_D_eq_bot hG hyp hTTypeII hDbot⟩

/-- **Peterfalvi (13.16)**: `N_G(W₁) = C_G(W₁) = Q ⊔ W₂`.

Proved from the structural core `normalizer_W1_structure_of_D_eq_bot` by the antisymmetric chain
`Q ⊔ W₂ ≤ C_G(W₁) ≤ N_G(W₁) ≤ Q ⊔ W₂`, which collapses all three subgroups:

* `W₂ ≤ C_G(W₁)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `Q ≤ C_G(W₁)` because `W₁ ≤ Q` and `Q` is abelian (both from the core);
* `C_G(W₁) ≤ N_G(W₁)` always (`centralizer_le_normalizer`);
* `N_G(W₁) ≤ Q ⊔ W₂` is the Frobenius/Wielandt containment (the core).

Consumed by the explicit-`D = ⊥` (13.17.c) Huppert step. -/
theorem normalizer_W1_of_D_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) = Subgroup.centralizer (hyp.W1 : Set G) ∧
      Subgroup.centralizer (hyp.W1 : Set G) = hyp.Q ⊔ hyp.W2 := by
  obtain ⟨hW1_le_Q, hQ_comm, hN_le⟩ :=
    normalizer_W1_structure_of_D_eq_bot hG hyp hTTypeII hDbot
  -- `W₂ ≤ C_G(W₁)`: `W = W₁ × W₂` is abelian, so `W₂` centralizes `W₁`.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyp.W1_commutes_W2 x (SetLike.mem_coe.mp hx) y hy
  -- `Q ≤ C_G(W₁)`: `W₁ ≤ Q` and `Q` abelian give `Q ≤ C_G(Q) ≤ C_G(W₁)`.
  have hQ_le_C : hyp.Q ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQ_comm).trans
      (Subgroup.centralizer_le (SetLike.coe_mono hW1_le_Q))
  have hQW2_le_C : hyp.Q ⊔ hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    sup_le hQ_le_C hW2_le_C
  have hC_le_N : Subgroup.centralizer (hyp.W1 : Set G) ≤
      Subgroup.normalizer (hyp.W1 : Set G) := Subgroup.centralizer_le_normalizer _
  exact ⟨le_antisymm (hN_le.trans hQW2_le_C) hC_le_N,
    le_antisymm (hC_le_N.trans hN_le) hQW2_le_C⟩

/-- **`T`-side dual of `not_normalizer_U_le_S`** (Pf (13.17), V-side): if `V` is a `T`-conjugate of
the `TypeIIData` witness's complement `tdata.typeP.U`, then `N_G(V) ⊄ T`.  Transfers the type-II
property `tdata.normalizer_not_le` along the conjugation `V = (typeP.U)^x`, `x ∈ T`. -/
theorem not_normalizer_V_le_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T)
    (hconj : ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U) :
    ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T := by
  obtain ⟨x, hxT, hVconj⟩ := hconj
  intro hNVT
  refine tdata.normalizer_not_le ?_
  have hTfix : MulAut.conj x • hyp.T = hyp.T :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxT)
  have hnorm_eq : Subgroup.normalizer (hyp.V : Set G)
      = MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G) := by
    rw [hVconj]
    exact (OddOrder.BG.Ch3.S12.normalizer_conj_smul x tdata.typeP.U).symm
  rw [hnorm_eq] at hNVT
  have hle : MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G)
      ≤ MulAut.conj x • hyp.T := by rw [hTfix]; exact hNVT
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle

/-- **`T`-side dual of `exists_conj_typeP_U_of_coprime`** (Pf (13.17), V-side): for the type-II
member `T`, if `|V|` is coprime to `|Q| = |T_F|`, then `V` is a `T`-conjugate of the `TypeIIData`
witness's complement `tdata.typeP.U` (both complement `Q` in `T' = [T,T]`, Schur–Zassenhaus). -/
theorem exists_conj_typeP_V_of_coprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q)) :
    ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U := by
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have htU_le : tdata.typeP.U ≤ derivedInG hyp.T := tdata.typeP.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  haveI hTsolv : IsSolvable ↥hyp.T := hG.solvable_of_mem_maximalSubgroups hyp.T_maximal
  haveI hM'solv : IsSolvable ↥(derivedInG hyp.T) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hM'_le_T)
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hM'_le_NQ : derivedInG hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) :=
    hM'_le_T.trans hT_le_NQ
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr hM'_le_NQ
  have hKcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.T)) := by
    rw [hQH]; exact tdata.typeP.derived_complement
  have hcop' : Nat.Coprime (Nat.card ↥(hyp.V.subgroupOf (derivedInG hyp.T)))
      (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv]
    exact hcop
  have hQV_eq : hyp.Q ⊔ hyp.V = derivedInG hyp.T := hyp.T_deriv_eq_QV.symm
  have hQnVn_sup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hQV_eq, Subgroup.subgroupOf_self]
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · exact Subgroup.disjoint_of_coprime_natCard hcop'.symm
    · have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hQnVn_sup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hcardV : Nat.card ↥hyp.V = Nat.card ↥tdata.typeP.U := by
    have hVcong : Nat.card ↥(hyp.V.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv
    have hKcong : Nat.card ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.T)) =
        Nat.card ↥tdata.typeP.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe htU_le).toEquiv
    have hQpos : 0 < Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) := Nat.card_pos
    have key := Nat.eq_of_mul_eq_mul_left hQpos
      (hVcompl.card_mul.trans hKcompl.card_mul.symm)
    rw [← hVcong, ← hKcong]; exact key
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    (M := hyp.Q.subgroupOf (derivedInG hyp.T))
    (K := tdata.typeP.U.subgroupOf (derivedInG hyp.T))
    (U := hyp.V.subgroupOf (derivedInG hyp.T))
    inferInstance hKcompl hcop'
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (x : G) • K = K.map (MulAut.conj (x : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hintertwine : (derivedInG hyp.T).subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp (derivedInG hyp.T).subtype := by
    ext ⟨y, hy⟩; rfl
  have hRHS : (((tdata.typeP.U.subgroupOf (derivedInG hyp.T)).map
        (MulAut.conj x).toMonoidHom).map (derivedInG hyp.T).subtype)
      = MulAut.conj (x : G) • tdata.typeP.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le htU_le, hsmul_map]
  have hle : hyp.V ≤ MulAut.conj (x : G) • tdata.typeP.U := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hV_le, ← hRHS]
    exact Subgroup.map_mono hx
  have hconj_card : Nat.card ↥(MulAut.conj (x : G) • tdata.typeP.U) =
      Nat.card ↥tdata.typeP.U := by
    rw [hsmul_map]; exact Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective
  refine ⟨(x : G), hM'_le_T x.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hconj_card, hcardV]

/-- **Structural core of Peterfalvi (13.17.a)** — the `L`-conjugate-to-`S` exclusion.  If `U` is a
`π`-Hall subgroup of the solvable subgroup `V`, `L` is conjugate to `V` (`L^g = V`, i.e.
`conj g • L = V`), and `N_G(U) ⊆ L`, then `N_G(U) ⊆ V`.

*Proof (Pf p.81):* `U ⊆ N_G(U) ⊆ L`, so `U^g = conj g • U ⊆ conj g • L = V` is another
`π`-Hall subgroup of `V` (same order as `U`).  Since `V` is solvable, Hall conjugacy
(`exists_conj_eq_of_isHall_subgroupOf`, Isaacs Thm 3.21) gives `w ∈ V` with `(U^g)^w = U`, i.e.
`wg ∈ N_G(U)`.  Then `N_G(U) = N_G(U)^{wg} ⊆ L^{wg} = (L^g)^w = V^w = V`.  Specialised to
`V = S` of type II (with `hNUS = IsTypeII.normalizer_not_le` transferred to `U`) this rules out
the `L ~ S` branch of (8.8.b4).  Generic and reusable; the only `S`-specific input is "`U` is a
Hall subgroup of `S`". -/
theorem normalizer_le_of_isHall_subgroupOf_of_conj [Finite G] {V U L : Subgroup G}
    (hVsolv : IsSolvable ↥V) (hUV : U ≤ V) {π : Set ℕ}
    (hUhall : Ch03.IsHallSubgroup π (U.subgroupOf V))
    {g : G} (hconj : MulAut.conj g • L = V)
    (hNUL : Subgroup.normalizer (U : Set G) ≤ L) :
    Subgroup.normalizer (U : Set G) ≤ V := by
  -- `U ⊆ L`, hence `U^g = conj g • U ⊆ conj g • L = V`.
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNUL
  have hUgV : (MulAut.conj g • U : Subgroup G) ≤ V := by
    rw [← hconj]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hUL
  -- `U^g` is a `π`-Hall subgroup of `V`: same card and (hence) same index in `V` as `U`.
  have hcardUg : Nat.card ↥(MulAut.conj g • U : Subgroup G) = Nat.card ↥U := by
    rw [OddOrder.BG.Ch3.S12.mulAut_smul_eq_map]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardEq : Nat.card ↥((MulAut.conj g • U).subgroupOf V)
      = Nat.card ↥(U.subgroupOf V) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUgV).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, hcardUg]
  have hidxEq : ((MulAut.conj g • U).subgroupOf V).index = (U.subgroupOf V).index := by
    have h1 := Subgroup.card_mul_index ((MulAut.conj g • U).subgroupOf V)
    have h2 := Subgroup.card_mul_index (U.subgroupOf V)
    rw [hcardEq] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hUghall : Ch03.IsHallSubgroup π ((MulAut.conj g • U).subgroupOf V) :=
    ⟨fun p hp => hUhall.1 p (hcardEq ▸ hp), fun p hp => hUhall.2 p (hidxEq ▸ hp)⟩
  -- Hall conjugacy in the solvable `V`: some `w ∈ V` conjugates `U^g` back to `U`.
  obtain ⟨w, hwV, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hVsolv hUgV hUV hUghall hUhall
  -- `wg` normalises `U`, and conjugates `L` onto `V`.
  have hwgU : MulAut.conj (w * g) • U = U := by rw [map_mul, mul_smul, hw]
  have hLconj : MulAut.conj (w * g) • L = V := by
    rw [map_mul, mul_smul, hconj]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwV)
  -- `N_G(U) = N_G(U)^{wg} ⊆ L^{wg} = V`.
  calc Subgroup.normalizer (U : Set G)
      = MulAut.conj (w * g) • Subgroup.normalizer (U : Set G) := by
        rw [OddOrder.BG.Ch3.S12.normalizer_conj_smul, hwgU]
    _ ≤ MulAut.conj (w * g) • L := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNUL
    _ = V := hLconj

/-- A subgroup `H ≤ V` whose order is coprime to its index `[V : H]` is a Hall subgroup of `V`
for `π = π(|H|)` (its own set of prime divisors).  The Hall conditions are immediate:
`π(|H|) ⊆ π` by definition, and no prime of `[V : H]` divides `|H|`, by coprimality. -/
theorem isHall_subgroupOf_primeFactors_of_coprime_index [Finite G] {V H : Subgroup G}
    (hHV : H ≤ V) (hcop : Nat.Coprime (Nat.card ↥H) ((H.subgroupOf V).index)) :
    Ch03.IsHallSubgroup {p | p ∈ (Nat.card ↥H).primeFactors} (H.subgroupOf V) := by
  have hcard : Nat.card ↥(H.subgroupOf V) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  refine ⟨fun p hp => by rw [hcard] at hp; exact hp, fun p hp hpπ => ?_⟩
  rw [Nat.mem_primeFactors] at hp
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hpπ).2.1 hp.2.1
  exact absurd (Nat.dvd_one.mp hp1) hp.1.ne_one

end OddOrder.Peterfalvi.S15
