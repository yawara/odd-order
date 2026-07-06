/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.SetLike.Fintype
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Chief factors

`OddOrder.GroupTheory` shared module for chief factors `U/V` of a finite group.

BG §1 Prop. 1.2 uses intersections of centralizers `C_{G*}(U/V)` over all chief
factors.  mathlib v4.29.1 has an abstract `Order.JordanHolder.CompositionSeries`,
but it does not provide the group-level chief-factor centralizer API needed here.

## Main definitions

* `IsChiefFactor U V`: `V < U`, both normal in `G`, and there is no normal subgroup
  strictly between `V` and `U`.
* `chiefFactorCentralizer U V`: the ambient centralizer `C_G(U/V)`, defined as the
  preimage of the centralizer of the image of `U` in `G ⧸ V`.
* `maxProperNormalOrBot K`: a maximal proper `G`-normal subgroup of `K`, or `⊥`
  if no such subgroup exists.  Used to extract chief factors below `K`.
* `chiefSeriesInside K n`: the chief series of `G` inside `K`, obtained by
  iterating `maxProperNormalOrBot` starting from `K`.

The centralizer in a normal subgroup `G*` is obtained as
`G* ⊓ chiefFactorCentralizer U V`.
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A chief factor `U/V` of `G`.

The order of arguments follows the mathematical notation `U/V`: the top subgroup
comes first, then the bottom subgroup. -/
structure IsChiefFactor (U V : Subgroup G) : Prop where
  normal_top : U.Normal
  normal_bot : V.Normal
  lt : V < U
  eq_bot_or_eq_top_of_normal :
    ∀ W : Subgroup G, W.Normal → V ≤ W → W ≤ U → W = V ∨ W = U

namespace IsChiefFactor

variable {U V W : Subgroup G}

/-- In a chief factor `U/V`, the bottom subgroup is contained in the top subgroup. -/
theorem le (h : IsChiefFactor U V) : V ≤ U :=
  h.lt.le

/-- Any normal subgroup between the two terms of a chief factor is one endpoint. -/
theorem eq_or_eq_of_normal (h : IsChiefFactor U V)
    (hW_normal : W.Normal) (hVW : V ≤ W) (hWU : W ≤ U) :
    W = V ∨ W = U :=
  h.eq_bot_or_eq_top_of_normal W hW_normal hVW hWU

end IsChiefFactor

/-- The ambient centralizer `C_G(U/V)` of a factor `U/V`.

This is the preimage in `G` of the centralizer of the image of `U` in `G ⧸ V`.
For a subgroup `G* ≤ G`, BG's `C_{G*}(U/V)` is
`G* ⊓ chiefFactorCentralizer U V`. -/
def chiefFactorCentralizer (U V : Subgroup G) [V.Normal] : Subgroup G :=
  (Subgroup.centralizer
    ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V))).comap
      (QuotientGroup.mk' V)

namespace chiefFactorCentralizer

variable {U V H : Subgroup G} [V.Normal]

/-- If `U` is normal, then the ambient centralizer of `U/V` is normal. -/
instance normal [U.Normal] : (chiefFactorCentralizer U V).Normal := by
  change ((Subgroup.centralizer
    (U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V))).comap
      (QuotientGroup.mk' V)).Normal
  infer_instance

/-- Membership in `C_G(U/V)` is membership of the quotient image in the quotient centralizer. -/
theorem mem_iff {g : G} :
    g ∈ chiefFactorCentralizer U V ↔
      (QuotientGroup.mk' V) g ∈
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
  Iff.rfl

/-- A subgroup lies in `C_G(U/V)` iff its quotient image lies in the quotient centralizer. -/
theorem le_iff_map_le_centralizer :
    H ≤ chiefFactorCentralizer U V ↔
      H.map (QuotientGroup.mk' V) ≤
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) := by
  constructor
  · intro hH
    rintro _ ⟨h, hh, rfl⟩
    exact hH hh
  · intro hH g hg
    exact hH ⟨g, hg, rfl⟩

/-- If the quotient image of `H` centralizes `U/V`, then `H ≤ C_G(U/V)`. -/
theorem le_of_map_le_centralizer
    (hH : H.map (QuotientGroup.mk' V) ≤
      Subgroup.centralizer
        ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V))) :
    H ≤ chiefFactorCentralizer U V :=
  le_iff_map_le_centralizer.mpr hH

/-- If `H ≤ C_G(U/V)`, then `[U, H] ≤ V`. -/
theorem commutator_le_of_le (hH : H ≤ chiefFactorCentralizer U V) :
    ⁅U, H⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro u hu h hh
  have hqh_cent :
      (QuotientGroup.mk' V) h ∈
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
    mem_iff.mp (hH hh)
  have hmul :
      (QuotientGroup.mk' V) u * (QuotientGroup.mk' V) h =
        (QuotientGroup.mk' V) h * (QuotientGroup.mk' V) u :=
    Subgroup.mem_centralizer_iff.mp hqh_cent
      ((QuotientGroup.mk' V) u) ⟨u, hu, rfl⟩
  apply (QuotientGroup.eq_one_iff ⁅u, h⁆).mp
  change (QuotientGroup.mk' V) ⁅u, h⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hmul

/-- If `[U, H] ≤ V`, then `H ≤ C_G(U/V)`. -/
theorem le_of_commutator_le (hcomm : ⁅U, H⁆ ≤ V) :
    H ≤ chiefFactorCentralizer U V := by
  rw [le_iff_map_le_centralizer]
  intro qh hqh
  rw [Subgroup.mem_centralizer_iff]
  intro qu hqu
  obtain ⟨h, hh, rfl⟩ := hqh
  obtain ⟨u, hu, rfl⟩ := hqu
  have hcomm_el : ⁅u, h⁆ ∈ V :=
    Subgroup.commutator_le.mp hcomm u hu h hh
  have hq_comm : ⁅(QuotientGroup.mk' V) u, (QuotientGroup.mk' V) h⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅u, h⁆).mpr hcomm_el
  exact commutatorElement_eq_one_iff_mul_comm.mp hq_comm

/-- A subgroup centralizes `U/V` iff its commutator with `U` lies in `V`. -/
theorem le_iff_commutator_le :
    H ≤ chiefFactorCentralizer U V ↔ ⁅U, H⁆ ≤ V :=
  ⟨commutator_le_of_le, le_of_commutator_le⟩

end chiefFactorCentralizer

/-- The conjugation action of `G` on a chief-factor quotient `U/V`, written on the
model `↥U ⧸ V.subgroupOf U`. -/
@[reducible]
noncomputable def chiefFactorConjAction (U V : Subgroup G) [U.Normal] [V.Normal] :
    MulDistribMulAction G (↥U ⧸ V.subgroupOf U) :=
  letI : MulDistribMulAction (ConjAct G) (↥U ⧸ V.subgroupOf U) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction
      (V.subgroupOf U) (by
        intro a m hm
        rw [Subgroup.mem_subgroupOf] at hm ⊢
        change ConjAct.ofConjAct a * (↑m : G) * (ConjAct.ofConjAct a)⁻¹ ∈ V
        exact (‹V.Normal›).conj_mem _ hm _)
  MulDistribMulAction.compHom _ (ConjAct.toConjAct (G := G)).toMonoidHom

/-- The chief-factor conjugation action sends the class of `x` to the class of its
conjugate. -/
theorem chiefFactorConjAction_smul_mk {U V : Subgroup G} [U.Normal] [V.Normal]
    (g : G) (x : U) :
    letI := chiefFactorConjAction U V
    (g • (QuotientGroup.mk x : U ⧸ V.subgroupOf U)) =
      QuotientGroup.mk (ConjAct.toConjAct g • x) :=
  rfl

/-- An element acts trivially on the chief-factor conjugation action iff it lies in
the ambient centralizer `C_G(U/V)`. -/
theorem chiefFactorConjAction_smul_eq_self_iff_mem {U V : Subgroup G}
    [U.Normal] [V.Normal] (g : G) :
    letI := chiefFactorConjAction U V
    (∀ v : U ⧸ V.subgroupOf U, g • v = v) ↔ g ∈ chiefFactorCentralizer U V := by
  letI := chiefFactorConjAction U V
  have hcoe : ∀ x : U, (↑(ConjAct.toConjAct g • x) : G) = g * ↑x * g⁻¹ := fun _ => rfl
  have hL : (∀ v : U ⧸ V.subgroupOf U, g • v = v)
      ↔ ∀ x : U, (g * (↑x)⁻¹ * g⁻¹ * ↑x : G) ∈ V := by
    constructor
    · intro h x
      have hv := h (QuotientGroup.mk x)
      rw [chiefFactorConjAction_smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv, hcoe] at hv
      have heq : ((g * ↑x * g⁻¹)⁻¹ * ↑x : G) = g * (↑x)⁻¹ * g⁻¹ * ↑x := by group
      rwa [heq] at hv
    · intro h v
      induction v using QuotientGroup.induction_on with
      | _ x =>
        rw [chiefFactorConjAction_smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
          Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
        have heq : ((g * ↑x * g⁻¹)⁻¹ * ↑x : G) = g * (↑x)⁻¹ * g⁻¹ * ↑x := by group
        rw [heq]
        exact h x
  have hR : g ∈ chiefFactorCentralizer U V
      ↔ ∀ x : U, (g * ↑x * g⁻¹ * (↑x)⁻¹ : G) ∈ V := by
    rw [chiefFactorCentralizer.mem_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x
      have hcomm := h ((QuotientGroup.mk' V) (↑x : G)) ⟨↑x, x.2, rfl⟩
      have hgoal : (QuotientGroup.mk' V) (g * ↑x * g⁻¹ * (↑x)⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcomm]
        group
      exact (QuotientGroup.eq_one_iff _).mp hgoal
    · intro h q hq
      obtain ⟨x, hx, rfl⟩ := hq
      have hy : (QuotientGroup.mk' V) (g * ↑x * g⁻¹ * (↑x)⁻¹) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (h ⟨x, hx⟩)
      simp only [map_mul, map_inv] at hy
      rw [mul_inv_eq_one] at hy
      rw [mul_inv_eq_iff_eq_mul] at hy
      exact hy.symm
  rw [hL, hR]
  constructor
  · intro h x
    have := h x⁻¹
    simpa using this
  · intro h x
    have := h x⁻¹
    simpa using this

/-! ## Chief series inside a normal subgroup

For BG §1 Prop. 1.2 reverse direction we need to walk through the chief factors
of `G` that lie inside a normal subgroup `K`.  The construction iterates the
choice of a maximal proper `G`-normal subgroup. -/

section ChiefSeriesInside

variable [Finite G]

/-- A maximal `G`-normal subgroup strictly below `K`, chosen by classical
selection from the finite set of `G`-normal subgroups `<K`.  Returns `⊥` when
no proper `G`-normal subgroup of `K` exists (e.g. `K = ⊥`). -/
noncomputable def maxProperNormalOrBot (K : Subgroup G) : Subgroup G := by
  classical
  by_cases h : ∃ L : Subgroup G, L.Normal ∧ L < K
  · exact ((Set.toFinite {L : Subgroup G | L.Normal ∧ L < K}).exists_maximal h).choose
  · exact ⊥

private theorem maxProperNormalOrBot_choose_spec
    {K : Subgroup G} (h : ∃ L : Subgroup G, L.Normal ∧ L < K) :
    let L := ((Set.toFinite {L : Subgroup G | L.Normal ∧ L < K}).exists_maximal h).choose
    L.Normal ∧ L < K ∧
      ∀ W : Subgroup G, W.Normal → W < K → L ≤ W → W ≤ L := by
  classical
  intro L
  have hspec :=
    ((Set.toFinite {L : Subgroup G | L.Normal ∧ L < K}).exists_maximal h).choose_spec
  refine ⟨hspec.1.1, hspec.1.2, ?_⟩
  intro W hW_normal hW_lt hLW
  have hW_mem : W ∈ {L : Subgroup G | L.Normal ∧ L < K} := ⟨hW_normal, hW_lt⟩
  exact hspec.2 hW_mem hLW

theorem maxProperNormalOrBot_normal (K : Subgroup G) :
    (maxProperNormalOrBot K).Normal := by
  classical
  unfold maxProperNormalOrBot
  by_cases h : ∃ L : Subgroup G, L.Normal ∧ L < K
  · rw [dif_pos h]
    exact (maxProperNormalOrBot_choose_spec h).1
  · rw [dif_neg h]
    exact inferInstance

instance maxProperNormalOrBot_instNormal (K : Subgroup G) :
    (maxProperNormalOrBot K).Normal := maxProperNormalOrBot_normal K

theorem maxProperNormalOrBot_le (K : Subgroup G) :
    maxProperNormalOrBot K ≤ K := by
  classical
  unfold maxProperNormalOrBot
  by_cases h : ∃ L : Subgroup G, L.Normal ∧ L < K
  · rw [dif_pos h]
    exact (maxProperNormalOrBot_choose_spec h).2.1.le
  · rw [dif_neg h]
    exact bot_le

theorem maxProperNormalOrBot_lt_of_ne_bot {K : Subgroup G} (hK : K ≠ ⊥) :
    maxProperNormalOrBot K < K := by
  classical
  have h_exists : ∃ L : Subgroup G, L.Normal ∧ L < K :=
    ⟨⊥, inferInstance, bot_lt_iff_ne_bot.mpr hK⟩
  unfold maxProperNormalOrBot
  rw [dif_pos h_exists]
  exact (maxProperNormalOrBot_choose_spec h_exists).2.1

theorem isChiefFactor_maxProperNormalOrBot
    {K : Subgroup G} [hK_normal : K.Normal] (hK : K ≠ ⊥) :
    IsChiefFactor K (maxProperNormalOrBot K) := by
  classical
  have h_exists : ∃ L : Subgroup G, L.Normal ∧ L < K :=
    ⟨⊥, inferInstance, bot_lt_iff_ne_bot.mpr hK⟩
  have hV_normal : (maxProperNormalOrBot K).Normal := maxProperNormalOrBot_normal K
  have hV_lt : maxProperNormalOrBot K < K := maxProperNormalOrBot_lt_of_ne_bot hK
  refine ⟨hK_normal, hV_normal, hV_lt, ?_⟩
  intro W hW_normal hVW hWK
  rcases lt_or_eq_of_le hWK with h_WK_lt | h_WK_eq
  · -- W < K, so W is in the set, by maximality of V (= maxProperNormalOrBot K), W ≤ V
    left
    have hV_max : ∀ W' : Subgroup G, W'.Normal → W' < K →
        maxProperNormalOrBot K ≤ W' → W' ≤ maxProperNormalOrBot K := by
      unfold maxProperNormalOrBot
      rw [dif_pos h_exists]
      exact (maxProperNormalOrBot_choose_spec h_exists).2.2
    exact le_antisymm (hV_max W hW_normal h_WK_lt hVW) hVW
  · right
    exact h_WK_eq

/-- The chief series of `G` inside `K`: iterates `maxProperNormalOrBot` from `K`. -/
noncomputable def chiefSeriesInside (K : Subgroup G) : ℕ → Subgroup G
  | 0 => K
  | n + 1 => maxProperNormalOrBot (chiefSeriesInside K n)

@[simp]
theorem chiefSeriesInside_zero (K : Subgroup G) : chiefSeriesInside K 0 = K := rfl

theorem chiefSeriesInside_succ (K : Subgroup G) (n : ℕ) :
    chiefSeriesInside K (n + 1) = maxProperNormalOrBot (chiefSeriesInside K n) := rfl

instance chiefSeriesInside_instNormal (K : Subgroup G) [K.Normal] (n : ℕ) :
    (chiefSeriesInside K n).Normal := by
  induction n with
  | zero => exact ‹K.Normal›
  | succ n _ => rw [chiefSeriesInside_succ]; exact maxProperNormalOrBot_normal _

theorem chiefSeriesInside_le (K : Subgroup G) [K.Normal] (n : ℕ) :
    chiefSeriesInside K n ≤ K := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [chiefSeriesInside_succ]
    exact (maxProperNormalOrBot_le _).trans ih

theorem chiefSeriesInside_antitone (K : Subgroup G) [K.Normal] :
    Antitone (chiefSeriesInside K) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  rw [chiefSeriesInside_succ]
  exact maxProperNormalOrBot_le _

theorem chiefSeriesInside_lt_of_ne_bot {K : Subgroup G} [K.Normal] {n : ℕ}
    (hne : chiefSeriesInside K n ≠ ⊥) :
    chiefSeriesInside K (n + 1) < chiefSeriesInside K n := by
  rw [chiefSeriesInside_succ]
  exact maxProperNormalOrBot_lt_of_ne_bot hne

theorem isChiefFactor_chiefSeriesInside {K : Subgroup G} [K.Normal] {n : ℕ}
    (hne : chiefSeriesInside K n ≠ ⊥) :
    IsChiefFactor (chiefSeriesInside K n) (chiefSeriesInside K (n + 1)) := by
  rw [chiefSeriesInside_succ]
  exact isChiefFactor_maxProperNormalOrBot hne

/-- The chief series inside `K` eventually reaches `⊥`. -/
theorem chiefSeriesInside_exists_eq_bot (K : Subgroup G) [K.Normal] :
    ∃ N : ℕ, chiefSeriesInside K N = ⊥ := by
  by_contra h
  push_neg at h
  have h_strict_anti : StrictAnti (chiefSeriesInside K) :=
    strictAnti_nat_of_succ_lt (fun n => chiefSeriesInside_lt_of_ne_bot (h n))
  -- `Finite (Subgroup G)` comes from `Finite G` via `SetLike` (Mathlib.Data.SetLike.Fintype).
  have h_inj : Function.Injective (chiefSeriesInside K) := h_strict_anti.injective
  have : Finite ℕ := Finite.of_injective _ h_inj
  exact (Infinite.not_finite (α := ℕ)) this

end ChiefSeriesInside

/-! ## Chief factors of solvable groups

A chief factor of a solvable group is elementary abelian, so its commutator
vanishes in the bottom subgroup. -/

section SolvableChiefFactor

/-- Convert a `G`-chief factor `U/V` to a minimal normal subgroup of `G/V`. -/
theorem IsChiefFactor.isMinimalNormal_map_quotient
    {U V : Subgroup G} (hChief : IsChiefFactor U V) :
    haveI : V.Normal := hChief.normal_bot
    OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) := by
  haveI hV_normal : V.Normal := hChief.normal_bot
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

/-- In a finite solvable group, a chief factor `U/V` is elementary abelian, in
particular `[U, U] ≤ V`. -/
theorem IsChiefFactor.commutator_le_of_isSolvable
    [Finite G] [IsSolvable G] {U V : Subgroup G} (hChief : IsChiefFactor U V) :
    ⁅U, U⁆ ≤ V := by
  haveI hV_normal : V.Normal := hChief.normal_bot
  haveI hU_normal : U.Normal := hChief.normal_top
  -- `U.map (mk' V)` is a minimal normal subgroup of `G/V`, hence elementary
  -- abelian (chief factor of a finite solvable group).
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  obtain ⟨p, hp_prime, hElem⟩ :=
    OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hMin
  -- `U/V` abelian ⇒ `[u, u'] ∈ V` for `u, u' ∈ U`.
  rw [Subgroup.commutator_le]
  intro u hu u' hu'
  have hu_q : (QuotientGroup.mk' V) u ∈ U.map (QuotientGroup.mk' V) := ⟨u, hu, rfl⟩
  have hu'_q : (QuotientGroup.mk' V) u' ∈ U.map (QuotientGroup.mk' V) := ⟨u', hu', rfl⟩
  -- `U/V` elementary abelian ⇒ commutativity at the subtype level.
  have hSubComm := hElem.comm
    (⟨(QuotientGroup.mk' V) u, hu_q⟩ : ↥(U.map (QuotientGroup.mk' V)))
    (⟨(QuotientGroup.mk' V) u', hu'_q⟩ : ↥(U.map (QuotientGroup.mk' V)))
  have hComm : Commute ((QuotientGroup.mk' V) u) ((QuotientGroup.mk' V) u') :=
    congr_arg Subtype.val hSubComm
  apply (QuotientGroup.eq_one_iff ⁅u, u'⁆).mp
  change (QuotientGroup.mk' V) ⁅u, u'⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hComm

end SolvableChiefFactor

/-! ## Nilpotency from chief-factor centralization

If `K ⊴ G` and the commutator `⁅K, V_i⁆` is contained in the next chief-series term
`V_{i+1}` for every step of the chief series of `G` inside `K`, then `↥K` is nilpotent.
This is the engine behind BG §1 Prop. 1.2 reverse direction. -/

section NilpotencyFromCentralization

variable [Finite G]

/-- The chief series of `G` inside `K`, viewed in `↥K`. -/
private noncomputable def chiefSeriesSubgroupOf (K : Subgroup G) (n : ℕ) : Subgroup ↥K :=
  (chiefSeriesInside K n).subgroupOf K

private theorem chiefSeriesSubgroupOf_zero (K : Subgroup G) [K.Normal] :
    chiefSeriesSubgroupOf K 0 = ⊤ := by
  unfold chiefSeriesSubgroupOf
  rw [chiefSeriesInside_zero]
  ext x
  simp [Subgroup.mem_subgroupOf]

private theorem chiefSeriesSubgroupOf_eq_bot_of_chiefSeriesInside_eq_bot
    {K : Subgroup G} {N : ℕ} (h : chiefSeriesInside K N = ⊥) :
    chiefSeriesSubgroupOf K N = ⊥ := by
  unfold chiefSeriesSubgroupOf
  rw [h]
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_bot]

/-- **Nilpotency engine** for BG §1 Prop. 1.2 reverse direction: if `⁅K, V_i⁆ ≤ V_{i+1}`
for every step of `chiefSeriesInside K`, then `↥K` is nilpotent. -/
theorem isNilpotent_of_chief_factor_centralization
    {K : Subgroup G} [K.Normal]
    (h_cent : ∀ i : ℕ, ⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i + 1)) :
    Group.IsNilpotent ↥K := by
  obtain ⟨N, hN_bot⟩ := chiefSeriesInside_exists_eq_bot K
  rw [nilpotent_iff_finite_descending_central_series]
  refine ⟨N, chiefSeriesSubgroupOf K, ⟨?_, ?_⟩, ?_⟩
  · exact chiefSeriesSubgroupOf_zero K
  · intro x n hx g
    have hx_val : (x : G) ∈ chiefSeriesInside K n := hx
    have hg_val : (g : G) ∈ K := g.2
    have h_subset : ⁅chiefSeriesInside K n, K⁆ ≤ chiefSeriesInside K (n + 1) := by
      rw [Subgroup.commutator_comm]
      exact h_cent n
    have h_elem : ⁅(x : G), (g : G)⁆ ∈ chiefSeriesInside K (n + 1) :=
      h_subset (Subgroup.commutator_mem_commutator hx_val hg_val)
    show ((x * g * x⁻¹ * g⁻¹ : ↥K) : G) ∈ chiefSeriesInside K (n + 1)
    have h_eq : ((x * g * x⁻¹ * g⁻¹ : ↥K) : G) = ⁅(x : G), (g : G)⁆ := by
      simp [commutatorElement_def]
    rw [h_eq]
    exact h_elem
  · exact chiefSeriesSubgroupOf_eq_bot_of_chiefSeriesInside_eq_bot hN_bot

end NilpotencyFromCentralization

end OddOrder.GroupTheory
