/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup

/-!
# Peterfalvi Section 15: The Subgroups S and T — normalizers and type-I interaction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 15, pp. 82--86.

This file is the structural second half of Peterfalvi §15, covering blocks
(13.16)--(13.19): the determination of `N_G(W₁) = C_G(W₁) = Q W₂` (13.16), the
Frobenius structure of the type-I maximal subgroup over `N_G(U)` (13.17), and the
β-character / type-I orthogonality dichotomy (13.18)--(13.19).

The setup and the character-theoretic / numerical first half ((13.1)--(13.15) —
the `S,T` hypothesis, basic structure, character degrees, norm estimates, and the
numerical determination of `c` and `u`) live in
`OddOrder.Peterfalvi.S15_SAndT_Setup`, which this file imports and extends.  The
split keeps each file under the merge-monitor size threshold; downstream importers
of `OddOrder.Peterfalvi.S15_SAndT` transitively obtain the full §15 API.
-/

namespace OddOrder.Peterfalvi.S15
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (13.16)--(13.19): normalizers and type-I interaction -/

/-- **Group-theoretic core of the `∃ y ∈ Q, W₂^y ≤ E` step of Peterfalvi (13.17.c).**

Let `Q ⊔ W₂` be a semidirect product `Q ⋊ W₂` with `Q` a (solvable) normal Hall subgroup
(`W₂ ≤ N(Q)`, `Q ⊓ W₂ = ⊥`, `|W₂| = p` prime, `p ∤ |Q|`).  Then any subgroup `E ≤ Q ⊔ W₂`
whose order is divisible by `p` contains a `Q`-conjugate of `W₂`.

*Proof:* an order-`p` subgroup `P ≤ E` (Cauchy) is coprime to the normal complemented `Q`, so by
Schur–Zassenhaus complement conjugacy (`exists_conj_le_of_isComplement'_of_coprime`, applied inside
`↥(Q ⊔ W₂)`) it lies in a conjugate `W₂^g` of the complement `W₂`; cardinalities force `P = W₂^g`.
Decomposing `g = q w` (`q ∈ Q`, `w ∈ W₂`) gives `W₂^g = W₂^q`, so `W₂^q = P ≤ E` with `q ∈ Q`. -/
theorem exists_mem_conj_W2_le_of_dvd_card [Finite G]
    {Q W2 E : Subgroup G} (hWnorm : W2 ≤ Subgroup.normalizer (Q : Set G))
    (hQsolv : IsSolvable ↥Q) (hdisj : Q ⊓ W2 = ⊥)
    {p : ℕ} (hp : p.Prime) (hW2 : Nat.card ↥W2 = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hE : E ≤ Q ⊔ W2) (hpE : p ∣ Nat.card ↥E) :
    ∃ y ∈ Q, (MulAut.conj y • W2 : Subgroup G) ≤ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := Q ⊔ W2 with hKdef
  -- `Q` and `W₂`, transported into `↥K`, with `Q` normal and complementing `W₂`.
  have hQK : Q ≤ K := le_sup_left
  have hW2K : W2 ≤ K := le_sup_right
  haveI hQ'normal : (Q.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [hKdef]; exact sup_le Subgroup.le_normalizer hWnorm)
  have hsup_top : (Q.subgroupOf K) ⊔ (W2.subgroupOf K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQK hW2K, ← hKdef, Subgroup.subgroupOf_self]
  have hcompl : (Q.subgroupOf K).IsComplement' (W2.subgroupOf K) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      have hyQW : (y : G) ∈ Q ⊓ W2 := ⟨hy.1, hy.2⟩
      rw [hdisj, Subgroup.mem_bot] at hyQW
      rw [Subgroup.mem_bot]; exact Subtype.ext hyQW
    · rw [← Subgroup.normal_mul, hsup_top, Subgroup.coe_top]
  -- An order-`p` subgroup `P ≤ E` (Cauchy).
  haveI : Fintype ↥E := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥E) p (by
    rwa [Nat.card_eq_fintype_card] at hpE)
  set z : G := (x : G) with hzdef
  have hzE : z ∈ E := x.2
  have hzord : orderOf z = p := by
    have h : orderOf z = orderOf x := orderOf_injective E.subtype Subtype.coe_injective x
    rw [h]; exact hx
  set P : Subgroup G := Subgroup.zpowers z with hPdef
  have hPcard : Nat.card ↥P = p := by rw [hPdef, Nat.card_zpowers, hzord]
  have hPE : P ≤ E := (Subgroup.zpowers_le).mpr hzE
  have hPK : P ≤ K := hPE.trans hE
  -- `P` (inside `↥K`) is coprime to `Q`, so it lies in a conjugate of `W₂`.
  have hcop : Nat.Coprime (Nat.card ↥(P.subgroupOf K)) (Nat.card ↥(Q.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hPcard]
    exact (hp.coprime_iff_not_dvd).mpr hpQ
  haveI : IsSolvable ↥Q := hQsolv
  haveI hQ'solv : IsSolvable ↥(Q.subgroupOf K) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQK).symm.surjective
  obtain ⟨ξ, hξ⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime hQ'solv hcompl hcop
  -- Decompose `ξ = q' * w'` in `↥K` (`Q'` normal complement).
  have hξprod : (ξ : ↥K) ∈ (↑(Q.subgroupOf K) : Set ↥K) * (↑(W2.subgroupOf K) : Set ↥K) := by
    rw [← Subgroup.normal_mul, hsup_top, Subgroup.coe_top]; exact Set.mem_univ ξ
  obtain ⟨q', hq', w', hw', hqw⟩ := Set.mem_mul.mp hξprod
  refine ⟨(q' : G), (Subgroup.mem_subgroupOf.mp hq'), ?_⟩
  -- `W₂^(↑q') = W₂^ξ ⊇ P`, and cardinalities give equality.
  have hconj_le : P ≤ MulAut.conj (q' : G) • W2 := by
    intro a ha
    -- `a ∈ P`, so `⟨a,_⟩ ∈ P.subgroupOf K ≤ (W₂.subgroupOf K).map (conj ξ)`.
    have haK : a ∈ K := hPK ha
    have ha' : (⟨a, haK⟩ : ↥K) ∈ (W2.subgroupOf K).map (MulAut.conj ξ).toMonoidHom :=
      hξ (by rw [Subgroup.mem_subgroupOf]; exact ha)
    rw [Subgroup.mem_map] at ha'
    obtain ⟨v, hv, hva⟩ := ha'
    -- `v ∈ W₂'`, `conj ξ v = ⟨a,_⟩`; project to `G`: `ξ v ξ⁻¹ = a`.
    rw [Subgroup.mem_subgroupOf] at hv
    have hvW2 : (v : G) ∈ W2 := hv
    have hval : (ξ : G) * (v : G) * (ξ : G)⁻¹ = a := by
      have h := congrArg (Subgroup.subtype K) hva
      simpa [MulAut.conj_apply] using h
    -- `ξ = q' w'`.
    have hξqw : (ξ : G) = (q' : G) * (w' : G) := by
      have h := congrArg (Subgroup.subtype K) hqw
      simpa using h.symm
    have hw'W2 : (w' : G) ∈ W2 := hw'
    have hconj_w : (w' : G) * (v : G) * (w' : G)⁻¹ ∈ W2 :=
      W2.mul_mem (W2.mul_mem hw'W2 hvW2) (W2.inv_mem hw'W2)
    -- `a = q' (w' v w'⁻¹) q'⁻¹ ∈ W₂.map (conj q')`.
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      ← hval, hξqw]
    have hsimp : (q' : G)⁻¹ * ((q' : G) * (w' : G) * (v : G) * ((q' : G) * (w' : G))⁻¹) * (q' : G)
        = (w' : G) * (v : G) * (w' : G)⁻¹ := by group
    rw [hsimp]; exact hconj_w
  -- `P = W₂^(↑q')` by cardinality, and `P ≤ E`.
  have hmap : (MulAut.conj (q' : G) • W2 : Subgroup G)
      = W2.map (MulAut.conj (q' : G)).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]; rfl
  have hcard_eq : Nat.card ↥(MulAut.conj (q' : G) • W2 : Subgroup G) = p := by
    rw [hmap, Nat.card_congr (Subgroup.equivMapOfInjective W2
      (MulAut.conj (q' : G)).toMonoidHom (MulAut.conj (q' : G)).injective).toEquiv.symm, hW2]
  have hPeq : P = MulAut.conj (q' : G) • W2 :=
    Subgroup.eq_of_le_of_card_ge hconj_le (by rw [hcard_eq, hPcard])
  rw [← hPeq]; exact hPE
/-- **Peterfalvi (13.16), structural core** (Coq `FTtypeP_norm_cent_compl`, `PFsection13.v:1519`).
The three atomic facts that carry the genuine content of (13.16):

* `W₁ ≤ Q` — the `T`-side dual of `W₂ ≤ P` (`W2_le_P` in `S16_NonExistenceG`), placing the cyclic
  `q`-factor `W₁` inside the `T`-Fitting kernel `Q = T_F`;
* `Q` abelian — the `T`-side dual of `P` elementary abelian (`P_elementaryAbelian`);
* `N_G(W₁) ≤ Q ⊔ W₂` — the Frobenius/Wielandt fixed-point argument: `P = S_F` (elementary abelian)
  is decomposed by Maschke, and the coprime `U ⋊ W₁`-action is forced trivial on each direct factor
  by the Wielandt fixed-point theorem (`OddOrder.GroupTheory.WielandtFixedPoint`), confining the
  normalizer of the `q`-factor to `Q ⊔ W₂`.

The machinery required for the last containment is all present in the repository — the cyclic-TI
`W`-setup (`S05_TICyclic.TICyclicHypothesis`) and `OddOrder/GroupTheory/{WielandtFixedPoint,
CoprimeAction,CoprimeFrobeniusKernel,TISubset}`; the two `T`-side structural duals are gated on the
`T`-side `basic_structure` (issue 3001).  This isolates the residual assembly. -/
theorem normalizer_W1_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ hyp.Q ∧ IsMulCommutative ↥hyp.Q ∧
      Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 := sorry

/-- **Peterfalvi (13.16)**: `N_G(W₁) = C_G(W₁) = Q ⊔ W₂`.

Proved from the structural core `normalizer_W1_structure` by the antisymmetric chain
`Q ⊔ W₂ ≤ C_G(W₁) ≤ N_G(W₁) ≤ Q ⊔ W₂`, which collapses all three subgroups:

* `W₂ ≤ C_G(W₁)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `Q ≤ C_G(W₁)` because `W₁ ≤ Q` and `Q` is abelian (both from the core);
* `C_G(W₁) ≤ N_G(W₁)` always (`centralizer_le_normalizer`);
* `N_G(W₁) ≤ Q ⊔ W₂` is the Frobenius/Wielandt containment (the core).

Consumed by (13.17.c) at `normalizer_W1` uses below (the `W₁W₂^y`-alternative of the Frobenius
complement). -/
theorem normalizer_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W1 : Set G) = Subgroup.centralizer (hyp.W1 : Set G) ∧
      Subgroup.centralizer (hyp.W1 : Set G) = hyp.Q ⊔ hyp.W2 := by
  obtain ⟨hW1_le_Q, hQ_comm, hN_le⟩ := normalizer_W1_structure hG hyp
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

/-- **A `p`-subgroup lies in a normal subgroup of coprime-to-`p` index.**  If `W ≤ S`,
`P.subgroupOf S ⊴ S`, `[S : P]` is coprime to `|P|`, and `p ∣ |P|`, then every element of `W` of
order dividing `p` lies in `P`: its image in `S/P` has order dividing both `p` and `[S : P]`, hence
`1`.  Generic group theory (used to place the prime-order factors `W₁`, `W₂` inside the Fitting
kernels `Q`, `P`). -/
theorem pgroup_le_of_normal_coprime_index [Finite G]
    {S P W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime (Nat.card ↥P) (P.subgroupOf S).index)
    (hpP : p ∣ Nat.card ↥P) (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  haveI := hPnorm
  have hp_not_index : ¬ p ∣ (P.subgroupOf S).index := by
    intro hdvd
    have : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpP hdvd
    exact Nat.Prime.not_dvd_one hp this
  have hcop2 : Nat.Coprime p (P.subgroupOf S).index :=
    (hp.coprime_iff_not_dvd).mpr hp_not_index
  intro w hw
  have hwS : w ∈ S := hWS hw
  have horder : orderOf w ∣ p := hWp w hw
  have hmk : QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩ = 1 := by
    rw [← orderOf_eq_one_iff]
    have hd1 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣ p := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [show orderOf (⟨w, hwS⟩ : ↥S) = orderOf w from
        (orderOf_injective S.subtype Subtype.coe_injective ⟨w, hwS⟩).symm]
      exact horder
    have hd2 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣
        (P.subgroupOf S).index := orderOf_dvd_natCard _
    exact Nat.dvd_one.mp (hcop2 ▸ Nat.dvd_gcd hd1 hd2)
  have hmem : (⟨w, hwS⟩ : ↥S) ∈ P.subgroupOf S := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hmk
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T ≤ S`), while `P = S_F` is the normal Hall `p`-subgroup of `S` of order `p^q`
(`basic_structure`); hence `W₂ ≤ P` — the `F_p ⊆ F` identification of (14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W2 ≤ hyp.P := by
  obtain ⟨_, _, _, hP_card, _, _⟩ := basic_structure _hG hyp
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  refine pgroup_le_of_normal_coprime_index (S := hyp.S) hyp.p_prime ?_ ?_ ?_ ?_ ?_
  · have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  · rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S
  · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have hcard_eq : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
    exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
  · rw [hP_card]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
      (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
    rw [heq, ← hyp.p_eq_card_W2] at h1
    exact h1

/-- **Peterfalvi (13.16), TI reduction for the `W₂`-side**: `N_G(W₂) ≤ S`.

`W₂ ≤ P = S_F ≤ F(S)` (`W2_le_P` + `maxNilpotentNormalHall_le_fittingInG`), and `F(S)^#` is a
TI-subset whose normalizer is `S` (BG Theorem 15.7(a), `fittingIsTI_of_isTypeP2` from the type-`P₂`
carrier `S_typeP2`; `normalizer_fittingInAmbient_eq_self`).  Any `g` normalizing `W₂` sends a
nonidentity `a ∈ W₂ ⊆ F(S)^#` to `g a g⁻¹ ∈ W₂ ⊆ F(S)^#`, so the TI condition places
`g ∈ N_G(F(S)) = S`.  This is the first (TI) half of the (13.16) `W₂`-confinement; the residual
`N_G(W₂) ⊓ S ≤ P ⊔ W₁` is the Maschke/Wielandt core (`normalizer_W2_within_S`). -/
theorem normalizer_W2_le_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.S := by
  have hTI := OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have hNorm := OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  -- `W₂ ≤ P ≤ F(S)`.
  have hW2F : hyp.W2 ≤ OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S := by
    refine (W2_le_P hG hyp).trans ?_
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_fittingInG hyp.S
  -- a nonidentity element `a ∈ W₂` (`|W₂| = p ≥ 3`).
  have hW2ne : hyp.W2 ≠ ⊥ := by
    intro hbot
    have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
    exact hyp.p_prime.one_lt.ne' hp1
  haveI : Nontrivial ↥hyp.W2 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥hyp.W2)
  set a : G := (x : G) with ha
  have haW2 : a ∈ hyp.W2 := x.2
  have hane : a ≠ 1 := fun h => hx1 (OneMemClass.coe_eq_one.mp (ha ▸ h))
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hgaW2 : g * a * g⁻¹ ∈ hyp.W2 := (hg a).mp haW2
  have hgane : g * a * g⁻¹ ≠ 1 := by
    intro h
    have key : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h] at key; simp only [mul_one, inv_mul_cancel] at key
    exact hane key
  have ha_sharp : a ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    show a ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    exact ⟨hW2F haW2, hane⟩
  have hga_sharp : g * a * g⁻¹ ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    show g * a * g⁻¹ ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    exact ⟨hW2F hgaW2, hgane⟩
  have hgN : g ∈ Subgroup.normalizer
      (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) :=
    hTI g ⟨a, ha_sharp, hga_sharp⟩
  rwa [hNorm] at hgN

/-- **Peterfalvi (13.12) `c = 1`, as `C = ⊥`**: the centralizer datum `C = U ⊓ C_G(P)` is trivial.
Since `c := |C| = 1` (`c_eq_one`), `C` is the trivial subgroup.  This is the regularity *finish* of
the (13.16) `W₂`-confinement Maschke/Wielandt core: the residual kernel `N_U(W₂)` centralizes
`P = S_F` (Maschke + Wielandt), hence lies in `U ⊓ C_G(P) = C = 1`. -/
theorem C_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.C = ⊥ := by
  have hcard : Nat.card ↥hyp.C = 1 := by rw [← hyp.c_eq_card_C, c_eq_one hG hyp]
  exact Subgroup.card_eq_one.mp hcard

/-- **Peterfalvi (13.12) `c = 1`, usable form**: `U ⊓ C_G(P) = ⊥` — no nonidentity element of the
complement `U` centralizes the Fitting kernel `P = S_F` (`U` acts faithfully on `P`).  Immediate from
`C_eq_bot` and `C = U ⊓ C_G(P)` (`C_eq`).  The Maschke/Wielandt core of (13.16) concludes
`N_U(W₂) ≤ U ⊓ C_G(P) = ⊥`. -/
theorem U_inf_centralizer_P_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.centralizer (hyp.P : Set G) = ⊥ := by
  rw [← hyp.C_eq]; exact C_eq_bot hG hyp

/-- **Peterfalvi (13.16), Maschke/Wielandt core for the `W₂`-side**: `N_G(W₂) ⊓ S ≤ P ⊔ W₁`.

The `S`-internal residual of the (13.16) `W₂`-confinement (after the TI reduction `N_G(W₂) ≤ S` of
`normalizer_W2_le_S`).  `P = S_F` (elementary abelian) is decomposed by Maschke, and the coprime
`U ⋊ W₁`-action on each direct factor is forced trivial by the Wielandt fixed-point theorem
(`OddOrder.GroupTheory.WielandtFixedPoint`), so `N_U(W₂) = 1` and the normalizer has no `U`-part:
`N_S(W₂) ≤ P W₁`.  The machinery is present (`WielandtFixedPoint`, `CoprimeAction`); this is the
isolated Maschke/Wielandt assembly (Coq `FTtypeP_norm_cent_compl`, the inner `N_S` computation). -/
theorem normalizer_W2_within_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ⊓ hyp.S ≤ hyp.P ⊔ hyp.W1 := sorry

/-- **Peterfalvi (13.16), structural core for the `W₂`-side**: the Frobenius/Wielandt containment
`N_G(W₂) ≤ P ⊔ W₁`.  Assembled from the TI reduction `N_G(W₂) ≤ S` (`normalizer_W2_le_S`, proven)
and the Maschke/Wielandt core `N_G(W₂) ⊓ S ≤ P ⊔ W₁` (`normalizer_W2_within_S`, the isolated
residual): every `g ∈ N_G(W₂)` lies in `S`, hence in `N_G(W₂) ⊓ S ≤ P ⊔ W₁`. -/
theorem normalizer_W2_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 := by
  intro g hg
  have hgS : g ∈ hyp.S := normalizer_W2_le_S hG hyp hg
  exact normalizer_W2_within_S hG hyp (Subgroup.mem_inf.mpr ⟨hg, hgS⟩)

/-- **Peterfalvi (13.16), `W₂`-side**: `N_G(W₂) = C_G(W₂) = P ⊔ W₁` (the `S↔T`, `W₁↔W₂`, `P↔Q`
dual of `normalizer_W1`; the form stated directly in Coq `FTtypeP_norm_cent_compl`).

Proved from `normalizer_W2_structure` by the antisymmetric chain
`P ⊔ W₁ ≤ C_G(W₂) ≤ N_G(W₂) ≤ P ⊔ W₁`:

* `W₁ ≤ C_G(W₂)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `P ≤ C_G(W₂)` because `W₂ ≤ P` (`W2_le_P`) and `P` is elementary abelian (`basic_structure`);
* `C_G(W₂) ≤ N_G(W₂)` always (`centralizer_le_normalizer`);
* `N_G(W₂) ≤ P ⊔ W₁` is the Frobenius/Wielandt containment (`normalizer_W2_structure`).

Supplies the `W₂`-side of the (13.17.c) Huppert step (`E ≤ P W₁`). -/
theorem normalizer_W2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) = Subgroup.centralizer (hyp.W2 : Set G) ∧
      Subgroup.centralizer (hyp.W2 : Set G) = hyp.P ⊔ hyp.W1 := by
  have hN_le : Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 :=
    normalizer_W2_structure hG hyp
  -- `W₁ ≤ C_G(W₂)`: `W = W₁ × W₂` is abelian.
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hyp.W1_commutes_W2 x hx y (SetLike.mem_coe.mp hy)).symm
  -- `P ≤ C_G(W₂)`: `W₂ ≤ P` and `P` elementary abelian give `P` centralizes `W₂`.
  have hP_le_C : hyp.P ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    obtain ⟨_, _, hP_elemAb, _, _, _⟩ := basic_structure hG hyp
    have hW2P := W2_le_P hG hyp
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y ∈ hyp.P := hW2P (SetLike.mem_coe.mp hy)
    have h := hP_elemAb.comm (⟨y, hyP⟩ : ↥hyp.P) (⟨g, hg⟩ : ↥hyp.P)
    have h2 := congrArg (Subgroup.subtype hyp.P) h
    simpa using h2
  have hPW1_le_C : hyp.P ⊔ hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
    sup_le hP_le_C hW1_le_C
  have hC_le_N : Subgroup.centralizer (hyp.W2 : Set G) ≤
      Subgroup.normalizer (hyp.W2 : Set G) := Subgroup.centralizer_le_normalizer _
  exact ⟨le_antisymm (hN_le.trans hPW1_le_C) hC_le_N,
    le_antisymm (hC_le_N.trans hN_le) hPW1_le_C⟩

/-- Carrier for Peterfalvi (13.17), the type-I maximal subgroup over
`N_G(U)`. -/
structure TypeIOverNormalizerData (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  H_eq_LF : H = maxNilpotentNormalHall L
  normalizer_U_le_L : Subgroup.normalizer (hyp.U : Set G) ≤ L
  frobenius : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L
  U_le_H : hyp.U ≤ H
  /-- **Peterfalvi (13.17.c)/(14.5)**: the Frobenius complement has order `p q` (the `W₁W₂^y`
  alternative; the `W₁` alternative of (13.17.c) is ruled out by (14.5)). -/
  complement_card_eq_pq : Nat.card ↥frobenius.complement = hyp.p * hyp.q
  /-- **Peterfalvi (13.17.c)/(14.5)**: a conjugate `W₂^y` (`y ∈ Q`) lies in the Frobenius
  complement `W₁W₂^y` of `L`. -/
  exists_y_W2_conj_le_complement :
    ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
      frobenius.complement.map L.subtype

/-- **Coherence bridge for Pf (13.17), L~S rule-out**: for `S` of type II, the configuration
complement `U` (coprime to `P = S_F`) has `N_G(U) ⊄ S`.

`U` and the type-data complement `typeP.U` are both `P`-complements in `M' = derivedInG S`
(`P ◁ M'`, solvable), hence conjugate by some `x ∈ M' ≤ S` (Schur–Zassenhaus,
`exists_conj_le_of_isComplement'_of_coprime`).  Transferring the type-II property
`IsTypeII.normalizer_not_le` (`¬ N_G(typeP.U) ≤ S`) along `conj x` (`normalizer_conj_smul`;
`conj x` fixes the subgroup `S` as `x ∈ S`) gives `N_G(U) ⊄ S`.

The `Coprime |U| |P|` hypothesis is the (13.2) faithfulness datum (`U` is the `(κ∪σ)'`-complement,
`p ∈ σ`); it is supplied by the enriched §16 Hypothesis (Phase 0(b),
`notes/peterfalvi/s13_17_structural_program.md`).  The Schur–Zassenhaus conjugacy step itself is
isolated as `exists_conj_typeP_U_of_coprime` below. -/
theorem not_normalizer_U_le_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.S)
    (hconj : ∃ x : G, x ∈ hyp.S ∧ hyp.U = MulAut.conj x • tdata.typeP.U) :
    ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S := by
  obtain ⟨x, hxS, hUconj⟩ := hconj
  intro hNUS
  refine tdata.normalizer_not_le ?_
  have hSfix : MulAut.conj x • hyp.S = hyp.S :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxS)
  have hnorm_eq : Subgroup.normalizer (hyp.U : Set G)
      = MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G) := by
    rw [hUconj]
    exact (OddOrder.BG.Ch3.S12.normalizer_conj_smul x tdata.typeP.U).symm
  rw [hnorm_eq] at hNUS
  have hle : MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G)
      ≤ MulAut.conj x • hyp.S := by rw [hSfix]; exact hNUS
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle

/-- **Schur–Zassenhaus conjugacy for the (13.17) coherence bridge**: when the configuration
complement `U` is coprime to `P = S_F`, it is conjugate (by an element of `S`) to the type-data
complement `typeP.U`.

Both `U` and `typeP.U` complement the normal Hall subgroup `P` in `M' = derivedInG S`: `P ◁ M'`
(since `M' ≤ S ≤ N_G(P)`) is solvable, `M' = P ⊔ typeP.U` is the `derived_complement` field, and
`M' = P ⊔ U` is `S_deriv_eq_PU`.  Coprimality `Nat.Coprime |U| |P|` forces `P ⊓ U = ⊥`, so `U` is a
genuine `P`-complement of the same order as `typeP.U`; Schur–Zassenhaus
(`exists_conj_le_of_isComplement'_of_coprime`, applied inside `↥M'`) then conjugates `typeP.U` onto
`U`.  This discharges the `hconj` hypothesis of `not_normalizer_U_le_S`; the coprimality is the
(13.2) faithfulness datum supplied by the enriched §16 Hypothesis (Phase 0(b)). -/
theorem exists_conj_typeP_U_of_coprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.S)
    (hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P)) :
    ∃ x : G, x ∈ hyp.S ∧ hyp.U = MulAut.conj x • tdata.typeP.U := by
  -- `P = typeP.H` and the containments in `M' = derivedInG S`.
  have hPH : hyp.P = tdata.typeP.H := by rw [hyp.P_eq_SF, tdata.typeP.H_eq]
  have hP_le : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have htU_le : tdata.typeP.U ≤ derivedInG hyp.S := tdata.typeP.U_le
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  -- Solvability of `↥M'` (fix ii: transport along the injective inclusion `↥M' ↪ ↥S`).
  haveI hSsolv : IsSolvable ↥hyp.S := hG.solvable_of_mem_maximalSubgroups hyp.S_maximal
  haveI hM'solv : IsSolvable ↥(derivedInG hyp.S) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hM'_le_S)
  -- `P ◁ M'` (fix iv: `normal_subgroupOf_iff_le_normalizer`, set-form normalizer).
  have hS_le_NP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hM'_le_NP : derivedInG hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) :=
    hM'_le_S.trans hS_le_NP
  haveI hPn_normal : (hyp.P.subgroupOf (derivedInG hyp.S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr hM'_le_NP
  -- `typeP.U` complements `P` in `M'` (the `derived_complement` field, rewritten via `P = typeP.H`).
  have hKcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.S)) := by
    rw [hPH]; exact tdata.typeP.derived_complement
  -- Coprimality transported into `↥M'`.
  have hcop' : Nat.Coprime (Nat.card ↥(hyp.U.subgroupOf (derivedInG hyp.S)))
      (Nat.card ↥(hyp.P.subgroupOf (derivedInG hyp.S))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv]
    exact hcop
  -- `U` also complements `P` in `M'` (join from `S_deriv_eq_PU`, disjoint from coprimality).
  have hPU_eq : hyp.P ⊔ hyp.U = derivedInG hyp.S := hyp.S_deriv_eq_PU.symm
  have hPnUn_sup : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊔
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP_le hU_le, hPU_eq, Subgroup.subgroupOf_self]
  have hUcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (hyp.U.subgroupOf (derivedInG hyp.S)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · exact disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop'.symm)
    · have hmul := Subgroup.normal_mul (hyp.P.subgroupOf (derivedInG hyp.S))
        (hyp.U.subgroupOf (derivedInG hyp.S))
      rw [hPnUn_sup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `|U| = |typeP.U|` (both complement `P` in `M'`, so both have index `[M' : P]`).
  have hcardU : Nat.card ↥hyp.U = Nat.card ↥tdata.typeP.U := by
    have hUcong : Nat.card ↥(hyp.U.subgroupOf (derivedInG hyp.S)) = Nat.card ↥hyp.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv
    have hKcong : Nat.card ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.S)) =
        Nat.card ↥tdata.typeP.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe htU_le).toEquiv
    have hPpos : 0 < Nat.card ↥(hyp.P.subgroupOf (derivedInG hyp.S)) := Nat.card_pos
    have key := Nat.eq_of_mul_eq_mul_left hPpos
      (hUcompl.card_mul.trans hKcompl.card_mul.symm)
    rw [← hUcong, ← hKcong]; exact key
  -- Schur–Zassenhaus inside `↥M'`: `U.subgroupOf M' ≤ (typeP.U.subgroupOf M')ᶜᵒⁿʲ` by some `x ∈ M'`.
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    (M := hyp.P.subgroupOf (derivedInG hyp.S))
    (K := tdata.typeP.U.subgroupOf (derivedInG hyp.S))
    (U := hyp.U.subgroupOf (derivedInG hyp.S))
    inferInstance hKcompl hcop'
  -- Map the conjugacy back to `G` (fix v: intertwine `M'.subtype` with `conj`).
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (x : G) • K = K.map (MulAut.conj (x : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hintertwine : (derivedInG hyp.S).subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp (derivedInG hyp.S).subtype := by
    ext ⟨y, hy⟩; rfl
  have hRHS : (((tdata.typeP.U.subgroupOf (derivedInG hyp.S)).map
        (MulAut.conj x).toMonoidHom).map (derivedInG hyp.S).subtype)
      = MulAut.conj (x : G) • tdata.typeP.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le htU_le, hsmul_map]
  have hle : hyp.U ≤ MulAut.conj (x : G) • tdata.typeP.U := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hU_le, ← hRHS]
    exact Subgroup.map_mono hx
  have hconj_card : Nat.card ↥(MulAut.conj (x : G) • tdata.typeP.U) =
      Nat.card ↥tdata.typeP.U := by
    rw [hsmul_map]; exact Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective
  -- Upgrade containment to equality via the matching orders.
  refine ⟨(x : G), hM'_le_S x.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hconj_card, hcardU]

/-- **Peterfalvi (14.11)**, base-derived: `|W₁| + |W₂| = p + q`.  Immediate from the (13.1) prime
data `q = |W₁|`, `p = |W₂|`.  Supplies the `card_W1_add_W2_eq` field of `MHypothesis` (currently
isolated to the §16 carrier), de-gating it to an elementary consequence of the base `Hypothesis`. -/
theorem card_W1_add_W2 (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.W1 + Nat.card ↥hyp.W2 = hyp.p + hyp.q := by
  rw [← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]; omega

/-- **Peterfalvi (14.11)**, base-derived: `|W| = p q`.  `W = W₁ ⊔ W₂` (`W_eq_join`) is the internal
direct product of the elementwise-commuting (`W1_commutes_W2`), trivially-intersecting
(`W1_inf_W2_eq_bot`) cyclic factors `W₁` (order `q`) and `W₂` (order `p`), so
`|W| = |W₁| · |W₂| = q p = p q` via the disjoint-normalizer product formula.  Supplies the `card_W_eq`
field of `MHypothesis`, de-gating it from a §13-14 σ-prerequisite to a base consequence. -/
theorem card_W_eq_pq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.W = hyp.p * hyp.q := by
  -- `W₁` normalizes `W₂`: each `x ∈ W₁` centralizes `W₂`, hence fixes it under conjugation.
  have hconj : ∀ x ∈ hyp.W1, ∀ a ∈ hyp.W2, x * a * x⁻¹ ∈ hyp.W2 := by
    intro x hx a ha
    have hc : Commute x a := hyp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (hyp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [hyp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm hyp.W1_inf_W2_eq_bot,
    ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
  exact mul_comm hyp.q hyp.p

/-- **Peterfalvi (14.11.3)**, base-derived: the exceptional set `W − (W₁ ∪ W₂)` is nonempty.
`|W| = p q` (`card_W_eq_pq`) strictly exceeds `|W₁ ∪ W₂| ≤ |W₁| + |W₂| = q + p` since `(p−1)(q−1) > 0`
for the odd primes `p, q ≥ 3`, so `W` cannot be covered by `W₁ ∪ W₂`.  Supplies the `W_set_nonempty`
field of `MHypothesis`. -/
theorem W_sdiff_nonempty [Finite G] (hyp : Hypothesis (G := G)) :
    ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))).Nonempty := by
  rw [Set.diff_nonempty]
  intro hsub
  have hWc : (hyp.W : Set G).ncard = hyp.p * hyp.q := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact card_W_eq_pq hyp
  have hW1c : (hyp.W1 : Set G).ncard = hyp.q := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact hyp.q_eq_card_W1.symm
  have hW2c : (hyp.W2 : Set G).ncard = hyp.p := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact hyp.p_eq_card_W2.symm
  have hle : (hyp.W : Set G).ncard ≤ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hunion : ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)).ncard ≤
      (hyp.W1 : Set G).ncard + (hyp.W2 : Set G).ncard := Set.ncard_union_le _ _
  rw [hWc] at hle
  rw [hW1c, hW2c] at hunion
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hkey : hyp.p * hyp.q ≤ hyp.q + hyp.p := le_trans hle hunion
  have h3q : 3 * hyp.q ≤ hyp.p * hyp.q := mul_le_mul_right' hp3 hyp.q
  have h3p : hyp.p * 3 ≤ hyp.p * hyp.q := mul_le_mul_left' hq3 hyp.p
  omega

/-- **Coprimality of the configuration complement from disjointness** (the Hall mechanism of
Phase 0): for `S` of type II, if the complement `U` meets the Fitting kernel `P = S_F` trivially
(`P ⊓ U = ⊥`), then `|U|` is coprime to `|P|`.

This is the *derivable* half of the (13.2) faithfulness datum.  `P = S_F = maxNilpotentNormalHall M'`
(`TypeIIData.derived_fitting_eq`) is a **relative Hall** subgroup of `M' = derivedInG S`
(`maxNilpotentNormalHall_isHall`: `(M_F).subgroupOf M'` is Hall in `↥M'`), so `|P|` is coprime to its
index `[M' : P]`.  Disjointness plus `M' = P ⊔ U` (`S_deriv_eq_PU`) makes `U` a genuine `P`-complement
with `|U| = [M' : P]`, whence `Coprime |U| |P|`.  The remaining input `P ⊓ U = ⊥` is the carrier
faithfulness datum (`hyp.U` is currently under-constrained; supplied by the enriched §16 Hypothesis,
Phase 0(b)).  Composes with `exists_conj_typeP_U_of_coprime` to discharge the L~S rule-out. -/
theorem coprime_card_U_card_P_of_disjoint [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.S) (hdisj : hyp.P ⊓ hyp.U = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) := by
  have hPH : hyp.P = tdata.typeP.H := by rw [hyp.P_eq_SF, tdata.typeP.H_eq]
  have hP_le : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hS_le_NP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPn_normal : (hyp.P.subgroupOf (derivedInG hyp.S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr (hM'_le_S.trans hS_le_NP)
  -- `U` complements `P` in `M'` (disjoint from `hdisj`, join from `S_deriv_eq_PU`).
  have hPnUn_inf : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊓
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxP, hxU⟩ => ?_, fun h => by simp [h]⟩
    have hxPU : x ∈ (hyp.P ⊓ hyp.U : Subgroup G) := ⟨hxP, hxU⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  have hPnUn_sup : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊔
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP_le hU_le, hyp.S_deriv_eq_PU.symm, Subgroup.subgroupOf_self]
  have hUcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (hyp.U.subgroupOf (derivedInG hyp.S)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hPnUn_inf)
    have hmul := Subgroup.normal_mul (hyp.P.subgroupOf (derivedInG hyp.S))
      (hyp.U.subgroupOf (derivedInG hyp.S))
    rw [hPnUn_sup, Subgroup.coe_top] at hmul
    exact hmul.symm
  have hidx : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
    rw [hUcompl.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv]
  -- `P` is a relative Hall subgroup of `M'`, so `|P|` is coprime to `[M' : P] = |U|`.
  have hP_mnh : hyp.P = maxNilpotentNormalHall (derivedInG hyp.S) :=
    hPH.trans tdata.derived_fitting_eq.symm
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG hyp.S)
  rw [← hP_mnh] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv, hidx] at hcop_idx
  exact hcop_idx.symm

/-- **Peterfalvi (13.2.a), `U` abelian (non-gated carrier form)**: the complement `U` of the
type-`P₂` member `S` is commutative — independent of the §16-gated `basic_structure_gated`.

`S` is type II (`isTypeII_of_isTypeP2`), so it has a `TypeIIData` witness `tdata` whose complement
`tdata.typeP.U` is commutative (`TypeIIData.U_commutative`).  Both that witness's `U` and the
carrier's `U = Sdata.U` are complements of `M_F = S_F = P` in `M' = [S,S]`, hence `M'`-conjugate
(Schur–Zassenhaus, `|P|` coprime to `|U|`, `IsComplement'.exists_conj_of_coprime`); conjugation is
an isomorphism, so commutativity transfers to `hyp.U`.  This de-opacifies the `U_commutative` field
of `basic_structure_gated`: downstream consumers can cite this directly instead of the §16-gated
`BasicStructureData.U_commutative`. -/
theorem isMulCommutative_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsMulCommutative ↥hyp.U := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 _hG hyp.S_maximal hyp.S_typeP2
  obtain ⟨tdata⟩ := hSII
  -- `P ⊓ U = ⊥` from the carrier's derived complement (the `hdisj` input to coprimality).
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have key : hyp.Sdata.H ⊓ hyp.Sdata.U = ⊥ := by
      have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxU⟩
      have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le hxH
      have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
          (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓
            (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
        ⟨Subgroup.mem_subgroupOf.mpr hxH, Subgroup.mem_subgroupOf.mpr hxU⟩
      rw [hd, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      simpa using Subtype.ext_iff.mp hmem
    rw [hyp.P_eq_SF, ← hyp.Sdata.H_eq, ← hyp.Sdata_U_eq]
    exact key
  -- the `M' = [S,S]` setup (mirrors `coprime_card_U_card_P_of_disjoint`).
  have hPH : hyp.P = tdata.typeP.H := by rw [hyp.P_eq_SF, tdata.typeP.H_eq]
  have hP_le : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hS_le_NP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPn_normal : (hyp.P.subgroupOf (derivedInG hyp.S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr (hM'_le_S.trans hS_le_NP)
  -- `U` complements `P` in `M'`.
  have hUcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (hyp.U.subgroupOf (derivedInG hyp.S)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxP, hxU⟩ => ?_, fun h => by simp [h]⟩
      have hxPU : x ∈ (hyp.P ⊓ hyp.U : Subgroup G) := ⟨hxP, hxU⟩
      rwa [hdisj, Subgroup.mem_bot] at hxPU
    · have hsup : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊔
          (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hP_le hU_le, hyp.S_deriv_eq_PU.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.P.subgroupOf (derivedInG hyp.S))
        (hyp.U.subgroupOf (derivedInG hyp.S))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `tdata.typeP.U` complements `P` in `M'` (after `H = P`).
  have hU'compl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.S)) := by
    rw [hPH]; exact tdata.typeP.derived_complement
  -- coprimality and solvability for Schur–Zassenhaus conjugacy of the two complements.
  have hcop : Nat.Coprime (Nat.card ↥(hyp.P.subgroupOf (derivedInG hyp.S)))
      ((hyp.P.subgroupOf (derivedInG hyp.S)).index) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv, hUcompl.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv]
    exact (coprime_card_U_card_P_of_disjoint hyp tdata hdisj).symm
  have hP_lt_top : hyp.P < ⊤ :=
    lt_of_le_of_lt hP_le_S (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.S_maximal).1)
  haveI hPsolv : IsSolvable ↥hyp.P := _hG.solvable_of_lt_top hyp.P hP_lt_top
  have hsolv : IsSolvable ↥(hyp.P.subgroupOf (derivedInG hyp.S)) ∨
      IsSolvable (↥(derivedInG hyp.S) ⧸ hyp.P.subgroupOf (derivedInG hyp.S)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hP_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hP_le).injective)
  -- the two complements are `M'`-conjugate by an element of `P`.
  obtain ⟨n, _hnP, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hU'compl
  -- transfer commutativity along the chain of isomorphisms.
  have h2 : IsMulCommutative ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.S)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe tdata.typeP.U_le).symm tdata.U_commutative
  rw [← hn] at h2
  have h4 : IsMulCommutative ↥(hyp.U.subgroupOf (derivedInG hyp.S)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).symm h2
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hU_le) h4

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

/-- **T-side type-`P` structure reconciled to the abstract `V`/`W₂`** (the honest replacement for the
withdrawn `Tdata` spine carrier; HUB tick² 2026-06-30).  `T` is type non-I (`T_nonI`), hence type-`P`,
and the §16-chosen complement `V` (κ-Hall-invariant) / cyclic factor `W₂` form a type-`P`
decomposition of `T`: there is a `TypePData T` with `.U = V` and `.W1 = W₂`.

This is the genuine §13 reconciliation — **TRUE** (unlike `IsTypeP2 T`, which is strictly stronger
than the (14.9) `T_typeII` conclusion `TypeIIData T` and generally false, so the earlier `Tdata`
spine supply was a dead-end).  It lives **off the FT spine**: the `V`-side helpers cite this obligation,
keeping `section16TypePStructure_of_isMinimalSimpleOdd` sorry-free.  Gated on §13; declared sorried. -/
theorem reconciled_typePData_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : TypePData hyp.T, data.U = hyp.V ∧ data.W1 = hyp.W2 := sorry

/-- `Q ⊓ V = ⊥` from a reconciled `TypePData T` (`tpd.U = V`): `V` complements `Q = T_F` in
`M' = [T,T]`.  Used by the V-side helpers in place of the withdrawn `Tdata` carrier. -/
theorem Q_inf_V_eq_bot_of_reconciled [Finite G] (hyp : Hypothesis (G := G))
    {tpd : TypePData hyp.T} (htpdV : tpd.U = hyp.V) : hyp.Q ⊓ hyp.V = ⊥ := by
  have key : tpd.H ⊓ tpd.U = ⊥ := by
    have hd := disjoint_iff.mp tpd.derived_complement.disjoint
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxU⟩
    have hxD : x ∈ derivedInG hyp.T := tpd.H_le hxH
    have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.T)) ∈
        (tpd.H.subgroupOf (derivedInG hyp.T)) ⊓ (tpd.U.subgroupOf (derivedInG hyp.T)) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxH, Subgroup.mem_subgroupOf.mpr hxU⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using Subtype.ext_iff.mp hmem
  rw [hyp.Q_eq_TF, ← tpd.H_eq, ← htpdV]
  exact key

/-- **`T`-side dual of `isMulCommutative_U`** (Pf (13.2.a), V-side): the complement `V` of the
type-II member `T` is commutative.  Mirror of `isMulCommutative_U`; `IsTypeII T` is a hypothesis
(the (14.9) `T_typeII` conclusion, supplied by the caller).  Sources the `T`-side type-`P` structure
from the off-spine `reconciled_typePData_T` (not the withdrawn `Tdata` carrier). -/
theorem isMulCommutative_V [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) : IsMulCommutative ↥hyp.V := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, _⟩ := reconciled_typePData_T _hG hyp
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := Q_inf_V_eq_bot_of_reconciled hyp htpdV
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
    · exact disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop'.symm)
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

/-! ### (13.17) gate 3/4 structural inputs (issue 2013)

The two structural facts that the type-II rule-out of (13.17.a/b) reads off the `§13`/`§14`
machinery but that the bare `Hypothesis` does not pin.  Both are declared here as faithful
sorried producers (the gate-2 pattern of `coprime_card_U_card_P_of_disjoint`): their proofs are
gated on the genuine §13 counting (`card_Q_eq`, B1) and on BG Theorem E
(`card_LF_coprime_pq`, B2), but their *statements* let the structural cores of the `L ~ T` and
type-`I` branches of `exists_typeI_maximal_overNormalizer_U` be discharged sorry-free.  See
issue 2013 / `notes/peterfalvi/s13_17_structural_program.md`. -/

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`).
The `Hypothesis` is `S`/`T`-asymmetric (`one_typeII`, `Q_eq_TF`), so this order is *not* obtained
by a formal swap of `basic_structure`; it is the genuine §13 structural datum.  Combined with the
automorphism-equivariance of `M_F` (`maxNilpotentNormalHall_pointwise_smul`), it gives
`|L_F| = q^p` for every `L` conjugate to `T`, which is what the `L ~ T` exclusion of (13.17.a)
uses.  Proof gated on the §13 machinery (`:= sorry`, the isolated residual of gate 3). -/
theorem card_Q_eq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hTTypeII : IsTypeNonI hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := sorry

/-- **Peterfalvi (13.17.a) T-conjugate Fitting structure**: for a maximal subgroup `L` conjugate
to `T` (`conj g • L = T`), the Fitting kernel `L_F` is a `q`-group of order `q^p` that contains
the cyclic factor `W₁` and meets the complement `U` trivially.

* `|L_F| = q^p` is the transfer of `card_Q_eq` (B1) along `maxNilpotentNormalHall_pointwise_smul`;
* `W₁ ≤ L_F` holds because `W₁ ⊆ N_G(U) ⊆ L` is a `q`-subgroup of `L` and `L_F` is the
  normal `q`-Hall subgroup (Pf p.81 "as `W₁ ⊆ N_G(U) ⊆ L`, `W₁ ⊆ H`");
* `L_F ⊓ U = 1` because `L_F` is a `q`-group while `|U| = u` is prime to `q` (Pf (13.2.a)).

These are exactly the three facts the `L ~ T` branch of (13.17.a) consumes before deriving
`[U, W₁] ⊆ L_F ⊓ U = 1` against the `U W₁` Frobenius structure.  The `card`-equality part is
the isolated §13 residual (`card_Q_eq`); `W₁ ≤ L_F` and `L_F ⊓ U = ⊥` are the §13.2-level
structural data, bundled here so the gate-3 core is sorry-free.  Proof `:= sorry` (isolated). -/
theorem tConjugate_fitting_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeNonI hyp.T)
    {L : Subgroup G} {g : G} (_hconj : MulAut.conj g • L = hyp.T) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p ∧
      hyp.W1 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := sorry

/-- **Peterfalvi (8.17.a) coprimality (B2)**: for a type-`I` maximal subgroup `L` that is *not*
conjugate to `S` or to `T`, the Fitting kernel order `|L_F|` is prime to `p q`.

*Derivation (Pf p.82 "(8.17.a)"):* `bgTheoremE_cover_data` (Peterfalvi (8.17), `:= sorry`,
BG Theorem E) exhibits representatives `M_i` of the conjugacy classes of maximal subgroups with
`π((M_i)_s)` pairwise disjoint (`BGTheoremECoverData.primeFactors_disjoint`).  For type `I`,
`(M_i)_s = M_F` (`mainSubgroup … .I = maxNilpotentNormalHall`); since `p ∈ π(S_s)` and
`q ∈ π(T_s)` while `L` is non-conjugate to either, `π(L_F)` is disjoint from `{p, q}`, i.e.
`Coprime |L_F| (p q)`.  Both the derivation *and* its `bgTheoremE_cover_data` cite are
§10/BG-gated;
declared here `:= sorry` as the isolated residual of gate 4 (the BG Theorem E content lives in
`bgTheoremE_cover_data`, owner = F).  This is exactly the input the type-`I` branch of (13.17.b)
reads off before deducing `W₁ ∩ L_F = 1` and running the (9.1) fixed-point-free argument. -/
theorem card_LF_coprime_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hLnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S)
    (_hLnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T) :
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q) := sorry

/-- **Frobenius-kernel self-centralizing (the gate-4 final step)**: in a finite Frobenius group `L`
with kernel `N`, any abelian subgroup `U` meeting `N` nontrivially lies in `N`.  Picking
`1 ≠ x ∈ U ⊓ N`, every `u ∈ U` commutes with `x` (`U` abelian), so `u ∈ C_L(x) ≤ N`
(`IsFrobeniusGroup.centralizer_kernel_le`: the centralizer of a nontrivial kernel element lies in
the kernel).  This is exactly the `U ⊆ C_L(U ∩ L_F) ⊆ L_F` deduction of Peterfalvi (13.17.b) once
`U ∩ L_F ≠ 1` is known.  General group theory; reusable, hoistable to `Ch06`. -/
theorem le_kernel_of_isMulCommutative_of_inf_ne_bot {L : Type*} [Group L] [Finite L]
    {N A U : Subgroup L} (h : Ch06.IsFrobeniusGroup L N A)
    (hUab : IsMulCommutative ↥U) (hinf : U ⊓ N ≠ ⊥) : U ≤ N := by
  obtain ⟨x, hxmem, hxne⟩ := (U ⊓ N).bot_or_exists_ne_one.resolve_left hinf
  have hxU : x ∈ U := (Subgroup.mem_inf.mp hxmem).1
  have hxN : x ∈ N := (Subgroup.mem_inf.mp hxmem).2
  have hcent := h.centralizer_kernel_le x hxN hxne
  intro u hu
  refine hcent (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact congrArg Subtype.val (hUab.is_comm.comm ⟨u, hu⟩ ⟨x, hxU⟩)

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

/-- **Peterfalvi (13.17.b), the (9.1) fixed-point-free residual (gate-4 pieces 4–6)**: once the
(8.17.a) coprimality `|L_F| ⟂ p q` is in hand for the type-`I` `L` over `N_G(U)`, the complement
`U` lies in the Fitting kernel `L_F`.  As `|W₁| = q ∤ |L_F|`, `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`,
the Frobenius group `U W₁ ⊆ L` (from (13.2.a)) would act fixed-point-freely on `L_F`
(`U, W₁ ≤ L ≤ N_G(L_F)`, a coprime action), so Wielandt's formula (9.1)
`wielandt_fixedPoint_frobenius` would force `|L_F| = 1`, against type-`I` `L_F ≠ 1`
(`TypeFData.H_nontrivial`); hence `U ∩ L_F ≠ 1` and `U ⊆ C_L(U ∩ L_F) ⊆ L_F`
(`le_kernel_of_isMulCommutative_of_inf_ne_bot`).  The isolated deep residual of gate 4: the
`CoprimeFrobeniusAction (U W₁) (L_F)` construction plus the (still sorried) Wielandt formula.
`:= sorry`; see issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`. -/
theorem typeI_U_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- The (12.7) Frobenius structure of the type-`I` `L`, with kernel `L_F = maxNilpotentNormalHall L`.
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  obtain ⟨bdata, _⟩ := basic_structure hG hyp
  have hsolv : IsSolvable ↥(maxNilpotentNormalHall L) := by
    haveI := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  -- piece 3: `W₁ ⊓ L_F = ⊥`, since `q = |W₁|` divides `p q` and `|L_F| ⟂ p q`.
  have hcopLFq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hW1LF : hyp.W1 ⊓ maxNilpotentNormalHall L = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [← hyp.q_eq_card_W1]; exact hcopLFq.symm)
  -- piece 5: `U ⊓ L_F ≠ ⊥` (else the Frobenius `U W₁` acts fixed-point-freely on `L_F`).
  have hUmeets : hyp.U ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopU : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hUleL hfrobLF hbot
    have hcopW1 : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW1leL hfrobLF hW1LF
    have hcardUW1 : Nat.card ↥(hyp.U ⊔ hyp.W1) = Nat.card ↥hyp.U * Nat.card ↥hyp.W1 := by
      rw [← bdata.UW1_frobenius.isComplement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopUW1 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥(hyp.U ⊔ hyp.W1)) := by
      rw [hcardUW1]; exact Nat.Coprime.mul_right hcopU.symm hcopW1.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hUleL hW1leL) ⟨frob.complement, hfrobLF⟩ bdata.UW1_frobenius hbot hW1LF hsolv hcopUW1
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  -- piece 6: `U ⊆ C_L(U ∩ L_F) ⊆ L_F` since `U` is abelian and `L_F` is the Frobenius kernel.
  have hUab : IsMulCommutative ↥(hyp.U.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hUleL).symm (isMulCommutative_U hG hyp)
  have hinf : (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.U ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hUmeets
    have hle : hyp.U ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hUab hinf
  calc hyp.U = (hyp.U.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hUleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **Peterfalvi (13.17.b) `U ⊆ L_F` for the type-`I` `L`**: when `S` is type II and `L` is a
type-`I` maximal subgroup over `N_G(U)`, the complement `U` lies in the Fitting kernel `L_F`.

*Proof (Pf p.82, the gate-4 structural core):* `L` is non-conjugate to `S` and `T` (it is type `I`
while `S`, `T` are non-I and type is conjugacy-invariant — `not_conj_of_isTypeI_of_isTypeNonI`, the
**discharged gate-4 piece 1**), so (8.17.a) = `card_LF_coprime_pq` (B2) gives `|L_F|` prime to
`p q`, in particular to `q = |W₁|`.  The remaining (9.1) fixed-point-free argument
(`W₁ ∩ L_F = 1`; `U ∩ L_F ≠ 1` by Wielandt; `U ⊆ C_L(U ∩ L_F) ⊆ L_F`) is
`typeI_U_le_fitting_of_coprime` (the isolated deep residual of gate 4).

Assembled `sorry`-free from the piece-1 non-conjugacy, the (8.17.a) coprimality producer
`card_LF_coprime_pq` (owner = F, BG Theorem E), and `typeI_U_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_U_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- (piece 1) `L` is non-conjugate to `S`, `T` (type is conjugacy-invariant; `S`, `T` are non-I).
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.T_maximal hyp.T_nonI
  -- (piece 2) the (8.17.a) coprimality, then (pieces 4–6) the isolated FPF residual.
  exact typeI_U_le_fitting_of_coprime _hG hyp _hSTypeII _hLmax _hLI _hNUL
    (card_LF_coprime_pq _hG hyp _hLmax _hLI hnS hnT)

/-- **`T`-side dual of `typeI_U_le_fitting_of_coprime`** (Pf (13.17.b), V-side): for `T` type II and
a type-`I` maximal `L` over `N_G(V)` with `|L_F| ⟂ pq`, the complement `V ⊆ L_F`.  Mirror of the
`U`-side; the `V W₂` Frobenius is built from the reconciled `TypePData T`
(`typeP_uW1_frobenius`) rather than `basic_structure` (which is `S`-side only). -/
theorem typeI_V_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2⟩ := reconciled_typePData_T hG hyp
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
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
    rwa [htpdV, htpdW2] at h
  have hsolv : IsSolvable ↥(maxNilpotentNormalHall L) := by
    haveI := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  have hcopLFp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hW2LF : hyp.W2 ⊓ maxNilpotentNormalHall L = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [← hyp.p_eq_card_W2]; exact hcopLFp.symm)
  have hVmeets : hyp.V ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopV : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hVleL hfrobLF hbot
    have hcopW2 : Nat.Coprime (Nat.card ↥hyp.W2) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW2leL hfrobLF hW2LF
    have hcardVW2 : Nat.card ↥(hyp.V ⊔ hyp.W2) = Nat.card ↥hyp.V * Nat.card ↥hyp.W2 := by
      rw [← hVW2frob.isComplement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopVW2 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L))
        (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by
      rw [hcardVW2]; exact Nat.Coprime.mul_right hcopV.symm hcopW2.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hVleL hW2leL) ⟨frob.complement, hfrobLF⟩ hVW2frob hbot hW2LF hsolv hcopVW2
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  have hVab : IsMulCommutative ↥(hyp.V.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hVleL).symm (isMulCommutative_V hG hyp ⟨tdata⟩)
  have hinf : (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.V ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hVmeets
    have hle : hyp.V ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hVab hinf
  calc hyp.V = (hyp.V.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hVleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **`T`-side dual of `typeI_overNormalizer_U_le_fitting`** (Pf (13.17.b), V-side): for `T` type II
and a type-`I` maximal `L` over `N_G(V)`, `V ⊆ L_F`.  Mirror; cites the (8.17.a) coprimality
`card_LF_coprime_pq` (gated, BG Thm E) and the V-side FPF residual `typeI_V_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_V_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  exact typeI_V_le_fitting_of_coprime _hG hyp hTTypeII hLmax hLI hNVL
    (card_LF_coprime_pq _hG hyp hLmax hLI hnS hnT)

/-- **Peterfalvi (13.17.a/b)**: a maximal subgroup `L` over `N_G(U)` (for `S` of type II) is of
type I with `U ⊆ L_F`.  *Proof (Pf pp.81-82):* take any maximal `L ⊇ N_G(U)` (proper since
`U ≠ 1` and `G` is simple).  `L` is not conjugate to `S` (else `N_G(U) ⊆ S`, against
`IsTypeII.normalizer_not_le`) nor to `T` (else `|L_F| = q^p` forces `[U,W₁] ⊆ L_F ∩ U = 1`,
against `U W₁` Frobenius from (13.2.a)), so by (8.8.b4) `L` is type I.  Then `U ⊆ L_F`: (8.17.a)
gives `|L_F|` prime to `q`, so `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`, `U W₁` would act
fixed-point-freely on `L_F`, forcing `L_F = 1` by (9.1).  The genuine §13 structural obligation
feeding (13.17); see issue 2009.

*Skeleton status (Phase 2):* the assembly is proven — `U ≠ ⊥` (from `fitting_lt_derived`), `N_G(U) ≠ ⊤`
(simplicity), the maximal `L ⊇ N_G(U)`, and the (8.8.b4) trichotomy dispatch, with the type-II
property `N_G(U) ⊄ S` wired in through `not_normalizer_U_le_S ∘ exists_conj_typeP_U_of_coprime ∘
coprime_card_U_card_P_of_disjoint`.  Four documented gates remain: `hdisj` (Phase 0(b) carrier
faithfulness, F-ask `P ⊓ U = ⊥`); the L~S Hall-conjugacy derivation of `N_G(U) ⊆ S`; the L~T
`|L_F| = q^p` exclusion; and `U ⊆ L_F` ((8.17.a)+(9.1)). -/
theorem exists_typeI_maximal_overNormalizer_U [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.U : Set G) ≤ L ∧ hyp.U ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hSTypeII
  -- The configuration complement meets the Fitting kernel trivially.  Now discharged from the
  -- §16 carrier `hyp.Sdata` (the type-`P` data of `S`, reconciled `Sdata.U = U`, `Sdata.H = P`):
  -- `U` complements `M_F = P` in `M' = [S,S]` (`Sdata.derived_complement`), so `P ⊓ U = ⊥`.
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have key : hyp.Sdata.H ⊓ hyp.Sdata.U = ⊥ := by
      have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxU⟩
      have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le hxH
      have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
          (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓
            (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
        ⟨Subgroup.mem_subgroupOf.mpr hxH, Subgroup.mem_subgroupOf.mpr hxU⟩
      rw [hd, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      simpa using Subtype.ext_iff.mp hmem
    rw [hyp.P_eq_SF, ← hyp.Sdata.H_eq, ← hyp.Sdata_U_eq]
    exact key
  have hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) :=
    coprime_card_U_card_P_of_disjoint hyp tdata hdisj
  -- (Phase 1) the type-II property transferred to `hyp.U`: `N_G(U) ⊄ S`.
  have hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S :=
    not_normalizer_U_le_S _hG hyp tdata (exists_conj_typeP_U_of_coprime _hG hyp tdata hcop)
  -- `U ≠ ⊥` (issue 7008): `U` is `S`-conjugate to `tdata.typeP.U`, which is `≠ ⊥` for type II
  -- (the `TypePNontrivialCore` first conjunct `common.1`); conjugation preserves nontriviality.
  have hUne : hyp.U ≠ ⊥ := by
    obtain ⟨x, _, hUconj⟩ := exists_conj_typeP_U_of_coprime _hG hyp tdata hcop
    rw [hUconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  -- `U ≤ S`, hence `U ≠ ⊤`; then by simplicity `N_G(U) ≠ ⊤`.
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hUleS : hyp.U ≤ hyp.S := (le_sup_right.trans hyp.S_deriv_eq_PU.ge).trans hM'_le_S
  have hUneTop : hyp.U ≠ ⊤ := fun hUtop =>
    (mem_maximalSubgroups.mp hyp.S_maximal).1 (top_le_iff.mp (hUtop ▸ hUleS))
  have hNUtop : Subgroup.normalizer (hyp.U : Set G) ≠ ⊤ := by
    intro hNtop
    haveI hUnormal : (hyp.U).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.U hUnormal with h | h
    · exact hUne h
    · exact hUneTop h
  -- a maximal subgroup `L ⊇ N_G(U)`.
  obtain ⟨L, hNUL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNUtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- (8.8.b4) trichotomy: `L` is type I, or conjugate to `S`, or conjugate to `T`.
  rcases hyp.theorem88_caseB L hLmem with hLI | _hLconjS | _hLconjT
  · -- `L` is type I; conclude with `U ⊆ L_F` (Pf (13.17.b)).  The (8.17.a)+(9.1)
    -- FPF structural core — `q ∤ |L_F|` (`card_LF_coprime_pq`), so `W₁ ∩ L_F = 1`;
    -- if `U ∩ L_F = 1` then `U W₁` acts FPF on `L_F`, forcing `L_F = 1` by
    -- `wielandt_fixedPoint_frobenius`, against type-`I` `L_F ≠ 1`; hence `U ∩ L_F ≠ 1` and
    -- `U ⊆ C_L(U ∩ L_F) ⊆ L_F` — is `typeI_overNormalizer_U_le_fitting`.
    exact ⟨L, hLmem, hLI, hNUL,
      typeI_overNormalizer_U_le_fitting _hG hyp ⟨tdata⟩ hLmem hLI hNUL⟩
  · -- `L` conjugate to `S` is excluded (`_hLconjS`): Pf (13.17.a) derives `N_G(U) ⊆ S` from the
    -- Hall conjugacy of `U` in the solvable `S`, contradicting `hNUS`.  The structural argument is
    -- `normalizer_le_of_isHall_subgroupOf_of_conj`; its only `S`-specific input is "`U` is a Hall
    -- subgroup of `S`".  That coprimality `|U| ⟂ [S:U]` is the residual (13.2) Hall-faithfulness
    -- datum: `[S:U] = [S:M']·|P|`, `|U| ⟂ |P|` is `hcop`, and `|U| ⟂ [S:M']` holds because
    -- `[S:M'] = |W₁|` is the order of the cyclic κ(S)-Hall complement of `M'` (Pf's `W₁`),
    -- coprime to `|M'| ⊇ |U|`.  The `W₁ = κ(S)`-Hall identification is the carrier-level fact
    -- supplied at the §16 `Section16MaximalPair` (lane-f) but not pinned by the bare `Hypothesis`;
    -- see issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`.
    obtain ⟨g, hg⟩ := _hLconjS
    -- `[S : U] = |P| · |W₁|` from the carrier complements (`U` complements `P` in `M'`,
    -- `W₁` complements `M'` in `S`); coprimality is `|U| ⟂ |P|` (`hcop`) and `|U| ⟂ |W₁|` (the
    -- Frobenius group `U ⋊ W₁` of (13.2.a), `coprime_card_kernel_complement`).
    have hUhall_cop : Nat.Coprime (Nat.card ↥hyp.U) ((hyp.U.subgroupOf hyp.S).index) := by
      obtain ⟨bdata, _⟩ := basic_structure _hG hyp
      have frobcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.W1) := by
        have h := bdata.UW1_frobenius.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ hyp.U ⊔ hyp.W1)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W1 ≤ hyp.U ⊔ hyp.W1)).toEquiv] at h
      have hPleM' : hyp.P ≤ derivedInG hyp.S := le_sup_left.trans hyp.S_deriv_eq_PU.ge
      have hidxM' : ((derivedInG hyp.S).subgroupOf hyp.S).index = Nat.card ↥hyp.W1 := by
        rw [← hyp.Sdata_W1_eq, ← hyp.Sdata.card_W1_eq_derived_index]
      have hidxP : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
        rw [hyp.P_eq_SF, ← hyp.Sdata.card_U_eq_index, hyp.Sdata_U_eq]
      have hScard : Nat.card ↥hyp.S
          = Nat.card ↥hyp.W1 * (Nat.card ↥hyp.U * Nat.card ↥hyp.P) := by
        have e1 := ((derivedInG hyp.S).subgroupOf hyp.S).index_mul_card
        have e2 := (hyp.P.subgroupOf (derivedInG hyp.S)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_S).toEquiv] at e1
        rw [hidxP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxU := (hyp.U.subgroupOf hyp.S).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleS).toEquiv] at hidxU
      have hidxUeq : (hyp.U.subgroupOf hyp.S).index = Nat.card ↥hyp.P * Nat.card ↥hyp.W1 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.U))
        rw [hidxU, hScard]; ring
      rw [hidxUeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.solvable_of_mem_maximalSubgroups hyp.S_maximal) hUleS
        (isHall_subgroupOf_primeFactors_of_coprime_index hUleS hUhall_cop) hg hNUL) hNUS
  · -- `L` conjugate to `T` is excluded (`_hLconjT`): `|L_F| = q^p` forces `W₁ ⊆ L_F` and
    -- `[U,W₁] ⊆ L_F ∩ U = 1`, contradicting the `U W₁` Frobenius structure (13.2.a).
    exfalso
    obtain ⟨g, hg⟩ := _hLconjT
    -- (B1, `tConjugate_fitting_data`) the T-side Fitting structure of `L_F`:
    -- `|L_F| = q^p`, `W₁ ≤ L_F`, and `L_F ⊓ U = 1`.
    obtain ⟨_hLFcard, hW1le, hLFU⟩ := tConjugate_fitting_data _hG hyp hyp.T_nonI hg
    -- `U ⊆ L`, hence `U` normalizes `L_F = maxNilpotentNormalHall L`.
    have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
    have hU_norm_LF : hyp.U ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hUleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    -- `⁅U, W₁⁆ ≤ U` since `W₁` normalizes `U` (`W1_normalizes_U`).
    have hUW1_le_U : ⁅hyp.U, hyp.W1⁆ ≤ hyp.U :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W1_normalizes_U
    -- `⁅U, W₁⁆ ≤ ⁅U, L_F⁆ ≤ L_F` since `W₁ ≤ L_F` and `U` normalizes `L_F`.
    have hUW1_le_LF : ⁅hyp.U, hyp.W1⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.U) hW1le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hU_norm_LF
    -- `⁅U, W₁⁆ ≤ L_F ⊓ U = 1`, so `U` and `W₁` commute elementwise.
    have hUW1_bot : ⁅hyp.U, hyp.W1⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hUW1_le_LF hUW1_le_U).trans hLFU.le)
    have hUcent : hyp.U ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUW1_bot
    -- `W₁ ≠ ⊥` (order `q ≥ 2`) and `U ≠ ⊥`: extract nontrivial witnesses contradicting Frobenius.
    have hW1ne : hyp.W1 ≠ ⊥ := by
      intro hbot
      have : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
      exact hyp.q_prime.one_lt.ne' this
    obtain ⟨w, hwW1, hwne⟩ := (hyp.W1.bot_or_exists_ne_one).resolve_left hW1ne
    obtain ⟨n, hnU, hnne⟩ := (hyp.U.bot_or_exists_ne_one).resolve_left hUne
    -- `w * n * w⁻¹ = n` from the commuting (centralizer) relation.
    have hcomm : w * n * w⁻¹ = n := by
      have := hUcent hnU w hwW1
      -- `this : w * n = n * w`; rearrange to `w * n * w⁻¹ = n`.
      rw [mul_inv_eq_iff_eq_mul, this]
    -- Move to the Frobenius group `↥(U ⊔ W₁)` and contradict `conj_frobenius`.
    obtain ⟨bdata, _⟩ := basic_structure _hG hyp
    have hwUW1 : w ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_right hwW1
    have hnUW1 : n ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_left hnU
    have hwmem : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) := hwW1
    have hnmem : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) := hnU
    have hwne' : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) * ⟨n, hnUW1⟩ * ⟨w, hwUW1⟩⁻¹ = ⟨n, hnUW1⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact bdata.UW1_frobenius.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq

/-- **`S`-side dual of `tConjugate_fitting_data`** (Pf (13.17.a), V-side L~S exclusion input): for a
maximal `L` conjugate to `S`, the Fitting kernel `L_F` is a `p`-group of order `p^q` containing `W₂`
and meeting `V` trivially.  The `card`-equality part is the isolated §13 residual (`card_P_eq`, dual
of the sorried `card_Q_eq`); declared sorried, the V-side analogue of `tConjugate_fitting_data`. -/
theorem sConjugate_fitting_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hSTypeII : IsTypeNonI hyp.S)
    {L : Subgroup G} {g : G} (_hconj : MulAut.conj g • L = hyp.S) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q ∧
      hyp.W2 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := sorry

/-- **`T`-side dual of `exists_typeI_maximal_overNormalizer_U`** (Pf (13.17.a/b), V-side): for `T`
type II, a maximal subgroup `L` over `N_G(V)` is type I with `V ⊆ L_F`.  Mirror of the `U`-side with
the two exclusion branches swapped: `L ~ T` is ruled out by the Hall conjugacy `N_G(V) ⊄ T`
(`not_normalizer_V_le_T`), and `L ~ S` by the `|L_F| = p^q` order contradiction
(`sConjugate_fitting_data`) against the `V W₂` Frobenius (from the reconciled `TypePData T`). -/
theorem exists_typeI_maximal_overNormalizer_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.V : Set G) ≤ L ∧ hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2⟩ := reconciled_typePData_T _hG hyp
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := Q_inf_V_eq_bot_of_reconciled hyp htpdV
  have hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) :=
    coprime_card_V_card_Q_of_disjoint hyp tdata hdisj
  have hNVT : ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T :=
    not_normalizer_V_le_T _hG hyp tdata (exists_conj_typeP_V_of_coprime _hG hyp tdata hcop)
  have hVne : hyp.V ≠ ⊥ := by
    obtain ⟨x, _, hVconj⟩ := exists_conj_typeP_V_of_coprime _hG hyp tdata hcop
    rw [hVconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hVleT : hyp.V ≤ hyp.T := (le_sup_right.trans hyp.T_deriv_eq_QV.ge).trans hM'_le_T
  have hVneTop : hyp.V ≠ ⊤ := fun hVtop =>
    (mem_maximalSubgroups.mp hyp.T_maximal).1 (top_le_iff.mp (hVtop ▸ hVleT))
  have hNVtop : Subgroup.normalizer (hyp.V : Set G) ≠ ⊤ := by
    intro hNtop
    haveI hVnormal : (hyp.V).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.V hVnormal with h | h
    · exact hVne h
    · exact hVneTop h
  obtain ⟨L, hNVL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNVtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- `V W₂` Frobenius from the reconciled `TypePData T` (used by both exclusion branches).
  have htpdVne : tpd.U ≠ ⊥ := by rw [htpdV]; exact hVne
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  rcases hyp.theorem88_caseB L hLmem with hLI | hLconjS | hLconjT
  · exact ⟨L, hLmem, hLI, hNVL,
      typeI_overNormalizer_V_le_fitting _hG hyp ⟨tdata⟩ hLmem hLI hNVL⟩
  · -- `L ~ S` excluded (order contradiction, mirror of the S-side `L ~ T`).
    exfalso
    obtain ⟨g, hg⟩ := hLconjS
    obtain ⟨_hLFcard, hW2le, hLFV⟩ := sConjugate_fitting_data _hG hyp hyp.S_nonI hg
    have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
    have hV_norm_LF : hyp.V ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hVleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    have hVW2_le_V : ⁅hyp.V, hyp.W2⁆ ≤ hyp.V :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W2_normalizes_V
    have hVW2_le_LF : ⁅hyp.V, hyp.W2⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.V) hW2le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hV_norm_LF
    have hVW2_bot : ⁅hyp.V, hyp.W2⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hVW2_le_LF hVW2_le_V).trans hLFV.le)
    have hVcent : hyp.V ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVW2_bot
    have hW2ne : hyp.W2 ≠ ⊥ := by
      intro hbot
      have : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
      exact hyp.p_prime.one_lt.ne' this
    obtain ⟨w, hwW2, hwne⟩ := (hyp.W2.bot_or_exists_ne_one).resolve_left hW2ne
    obtain ⟨n, hnV, hnne⟩ := (hyp.V.bot_or_exists_ne_one).resolve_left hVne
    have hcomm : w * n * w⁻¹ = n := by
      have := hVcent hnV w hwW2
      rw [mul_inv_eq_iff_eq_mul, this]
    have hwVW2 : w ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_right hwW2
    have hnVW2 : n ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_left hnV
    have hwmem : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2) := hwW2
    have hnmem : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.V.subgroupOf (hyp.V ⊔ hyp.W2) := hnV
    have hwne' : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) * ⟨n, hnVW2⟩ * ⟨w, hwVW2⟩⁻¹ = ⟨n, hnVW2⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact hVW2frob.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq
  · -- `L ~ T` excluded (Hall conjugacy, mirror of the S-side `L ~ S`): `N_G(V) ⊆ T` vs `hNVT`.
    obtain ⟨g, hg⟩ := hLconjT
    have hVhall_cop : Nat.Coprime (Nat.card ↥hyp.V) ((hyp.V.subgroupOf hyp.T).index) := by
      have frobcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.W2) := by
        have h := hVW2frob.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv] at h
      have hQleM' : hyp.Q ≤ derivedInG hyp.T := le_sup_left.trans hyp.T_deriv_eq_QV.ge
      have hidxM' : ((derivedInG hyp.T).subgroupOf hyp.T).index = Nat.card ↥hyp.W2 := by
        rw [← htpdW2, ← tpd.card_W1_eq_derived_index]
      have hidxQ : (hyp.Q.subgroupOf (derivedInG hyp.T)).index = Nat.card ↥hyp.V := by
        rw [hyp.Q_eq_TF, ← tpd.card_U_eq_index, htpdV]
      have hTcard : Nat.card ↥hyp.T
          = Nat.card ↥hyp.W2 * (Nat.card ↥hyp.V * Nat.card ↥hyp.Q) := by
        have e1 := ((derivedInG hyp.T).subgroupOf hyp.T).index_mul_card
        have e2 := (hyp.Q.subgroupOf (derivedInG hyp.T)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_T).toEquiv] at e1
        rw [hidxQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxV := (hyp.V.subgroupOf hyp.T).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleT).toEquiv] at hidxV
      have hidxVeq : (hyp.V.subgroupOf hyp.T).index = Nat.card ↥hyp.Q * Nat.card ↥hyp.W2 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.V))
        rw [hidxV, hTcard]; ring
      rw [hidxVeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.solvable_of_mem_maximalSubgroups hyp.T_maximal) hVleT
        (isHall_subgroupOf_primeFactors_of_coprime_index hVleT hVhall_cop) hg hNVL) hNVT

/-- **Peterfalvi (13.17.c), Huppert step.**  If `W₁` lies in a Frobenius complement `E` of the
type-I subgroup `L`, then `E ⊆ Q W₂`.

*Proof (Pf p.82):* `E` is a Frobenius complement of **odd** order (`E ≤ L ≤ G`, `|G|` odd), so by
Huppert ([H] Kapitel V Satz 8.18 b), `normal_of_card_prime_of_isFrobeniusGroup_of_odd`) its
prime-order subgroup `W₁` (`|W₁| = q`) is normal in `E`.  Hence `E ⊆ N_G(W₁) = C_G(W₁) = Q W₂`
by (13.16) (`normalizer_W1`).  This is the step of (13.17.c) consuming the new Frobenius-complement
structure theory; the remaining order analysis (`|E| ∈ {q, p q}`, cyclic Sylows by [BG] 3.9, and
the `(14.5)` exclusion of `E = W₁`) builds on this containment. -/
theorem complement_le_QW2 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.Q ⊔ hyp.W2 := by
  set E := frob.complement with hEdef
  -- `W₁ ≤ L`, and `W₁` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW1L : hyp.W1 ≤ L := hW1E.trans hEleL
  have hW1L_le_E : hyp.W1.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW1E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₁` viewed inside `E`, of prime order `q`.
  set R : Subgroup ↥E := (hyp.W1.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.q := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
    exact hyp.q_eq_card_W1.symm
  -- `E` has odd order (it divides `|G|`).
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₁` is normal in `E`, so `E` normalizes `W₁` in `↥L`.
  haveI hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.q_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW1L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₁)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW1L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      -- the conjugate lies in `W₁ ≤ L`, so `w ∈ L`, and we apply `heN` backwards.
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW1L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₁) = C_G(W₁) = Q W₂`.
  have h1316 := normalizer_W1 _hG hyp
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W1 : Set G) := h1316.1
    _ = hyp.Q ⊔ hyp.W2 := h1316.2

/-- §13 structural data for the semidirect product `Q ⋊ W₂` (`Q = T_F`) consumed by the
`∃ y` step of (13.17.c).  `W₂` normalizes `Q` (as `W₂ ≤ T` and `Q ◁ T`), meets it trivially, and
`p ∤ |Q| = q^p` (since `p ≠ q`).

*Proof.*  `W₂ ≤ W = S ⊓ T ≤ T` and `Q = T_F ◁ T` (`maxNilpotentNormalHall_le_normalizer`) give the
normalization.  The distinctness `p ≠ q` is forced because otherwise `W₁` and `W₂` would be equal
order-`q` subgroups of the cyclic `W` (`eq_of_card_eq_prime_of_isCyclic`), contradicting
`W₁ ⊓ W₂ = 1`; then `p ∤ q^p`, and the coprimality `|Q| ⟂ |W₂| = p` gives `Q ⊓ W₂ = 1`.  The only
gated input is `|Q| = q^p` (`card_Q_eq`, the isolated §13 counting residual B1). -/
theorem Q_W2_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) ∧ hyp.Q ⊓ hyp.W2 = ⊥ ∧
      ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
  -- `W₂ ≤ W = S ⊓ T ≤ T`.
  have hW2T : hyp.W2 ≤ hyp.T :=
    (le_sup_right.trans hyp.W_eq_join.ge).trans (hyp.W_eq_inter.le.trans inf_le_right)
  -- Conjunct 1: `W₂ ≤ N_G(Q)`, as `Q = T_F ◁ T` and `W₂ ≤ T`.
  have hWnorm : hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact hW2T.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  -- `p ≠ q`: else `W₁` and `W₂` are equal order-`q` subgroups of the cyclic `W`.
  have hpq : hyp.p ≠ hyp.q := by
    intro heq
    haveI : IsCyclic ↥hyp.W := hyp.W_cyclic
    have hW1W : hyp.W1 ≤ hyp.W := le_sup_left.trans hyp.W_eq_join.ge
    have hW2W : hyp.W2 ≤ hyp.W := le_sup_right.trans hyp.W_eq_join.ge
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv]; exact hyp.q_eq_card_W1.symm
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← heq]
      exact hyp.p_eq_card_W2.symm
    have hsubeq : hyp.W1.subgroupOf hyp.W = hyp.W2.subgroupOf hyp.W :=
      Ch06.eq_of_card_eq_prime_of_isCyclic hyp.q_prime hW1card hW2card
    have hWeq : hyp.W1 = hyp.W2 := by
      have hmap := congrArg (Subgroup.map hyp.W.subtype) hsubeq
      rwa [Subgroup.map_subgroupOf_eq_of_le hW1W, Subgroup.map_subgroupOf_eq_of_le hW2W] at hmap
    have hbot : hyp.W1 = ⊥ := by
      have h := hyp.W1_inf_W2_eq_bot; rwa [← hWeq, inf_idem] at h
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  -- Conjunct 3: `p ∤ |Q| = q^p`, since `p ∤ q` (distinct primes).
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    rw [card_Q_eq _hG hyp hyp.T_nonI]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hyp.p_prime hyp.q_prime).mp
      (hyp.p_prime.dvd_of_dvd_pow hdvd))
  -- Conjunct 2: `Q ⊓ W₂ = ⊥`, from coprimality `|Q| ⟂ p = |W₂|`.
  refine ⟨hWnorm, ?_, hpQ⟩
  apply Subgroup.inf_eq_bot_of_coprime
  rw [← hyp.p_eq_card_W2]
  exact (hyp.p_prime.coprime_iff_not_dvd.mpr hpQ).symm

/-- **Peterfalvi (13.17.c) §13 intersection structure.**  The `W₁`-containing Frobenius complement
`E` of the type-I `L` meets `Q = T_F` exactly in `W₁` (Pf p.82 "`E ∩ Q = W₁`"), and is not
contained in `Q` (the `E = W₁` alternative is excluded by Peterfalvi (13.19.c1)/(13.2.a)).  This is
the genuine deep §13 structural datum behind the order `|E| = p q`; it is not reducible to the
existing §13 residuals (`TypeIFrobeniusData` carries no complement-order field).  `:= sorry`,
isolated — the order argument `complement_card_eq_pq` below is sorry-free modulo this. -/
theorem complement_inf_Q_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.Q = hyp.W1 ∧
      ¬ frob.complement.map L.subtype ≤ hyp.Q := sorry

/-- **Peterfalvi (13.17.c) order argument.**  The `W₁`-containing Frobenius complement `E` of `L`
has order `p q`.

*Proof (Pf p.82).*  `E ⊆ Q W₂` (`complement_le_QW2`), and `Q ⋊ W₂` has `Q ◁ Q W₂` with
`[Q W₂ : Q] = |W₂| = p` (`Q_W2_structure`).  The relative index `[E : E ∩ Q]` divides `[Q W₂ : Q] = p`
(normal-subgroup relative index, `relIndex_dvd_index_of_normal` inside `↥(Q W₂)`) and is `≠ 1` since
`E ⊄ Q`, hence `= p`; with `E ∩ Q = W₁` of order `q`, `|E| = |E ∩ Q| · [E : E ∩ Q] = q p`.  The two
§13 facts `E ∩ Q = W₁` and `E ⊄ Q` are isolated in `complement_inf_Q_structure`; everything else is
sorry-free group theory. -/
theorem complement_card_eq_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- §13 residual: `E ∩ Q = W₁` and `E ⊄ Q`.
  obtain ⟨hInf, hnle⟩ := complement_inf_Q_structure _hG hyp frob hW1E
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hEH : Em ≤ Hg := complement_le_QW2 _hG hyp frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp
  have hQleH : hyp.Q ≤ Hg := le_sup_left
  -- `|E ∩ Q| = |W₁| = q`.
  have hInfCard : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q := by rw [hInf]; exact hyp.q_eq_card_W1.symm
  -- `Q ◁ Q W₂` (as `Q W₂ ≤ N_G(Q)`).
  haveI hQnorm : (hyp.Q.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  -- `|Q W₂| = |Q| · p`.
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.Q * hyp.p := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W2 ⊓ hyp.Q = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.p_eq_card_W2]
    exact mul_comm _ _
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  -- `[Q W₂ : Q] = p`.
  have hindexH : (hyp.Q.subgroupOf Hg).index = hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hQpos hmul
  -- `[E : E ∩ Q] = Q.relIndex E` divides `[Q W₂ : Q] = p`, and is `≠ 1` (`E ⊄ Q`), hence `= p`.
  have hdvd : hyp.Q.relIndex Em ∣ hyp.p := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.Q.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.Q.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.Q.relIndex Em = hyp.p :=
    (hyp.p_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  -- `|E| = |E ∩ Q| · [E : E ∩ Q] = q · p`.
  have hEmcard : Nat.card ↥Em = hyp.q * hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Em)
    rw [show (hyp.Q.subgroupOf Em).index = hyp.p from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  -- transfer `|E.map| = |E|`.
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]
  exact mul_comm _ _

/-- **Peterfalvi (13.17.c)/(14.5)**: the `W₁`-containing Frobenius complement of the type-I
subgroup `L` over `N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).

Assembled from the order argument (`complement_card_eq_pq`, gated on `E ∩ Q = W₁`) and the
group-theoretic `∃ y` extraction (`exists_mem_conj_W2_le_of_dvd_card`, Schur–Zassenhaus), the
latter fed `E ⊆ Q W₂` by the Huppert step (`complement_le_QW2`).  The `W₁ ⊆ E` hypothesis records
Peterfalvi's choice "let `E` be a complement to `H` in `L` such that `W₁ ⊂ E`". -/
theorem typeI_overNormalizer_complement [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq _hG hyp frob hW1E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp
  have hEQW2 := complement_le_QW2 _hG hyp frob hW1E
  -- `Q` is solvable: `Q = T_F ≤ T < ⊤`.
  haveI hQsolv : IsSolvable ↥hyp.Q := by
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hTlt : hyp.T < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1
    exact _hG.solvable_of_lt_top hyp.Q (lt_of_le_of_lt hQT hTlt)
  -- `p ∣ |E.map| = |E| = p q`.
  have hpE : hyp.p ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_right hyp.p hyp.q
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hQsolv hdisj hyp.p_prime
    hyp.p_eq_card_W2.symm hpQ hEQW2 hpE

/-- `W₁` (order `q`) is coprime to the type-I Frobenius kernel `L_F` (`q ∤ |L_F|`).  This is
Peterfalvi's "`W₁ ∩ H = 1`", from (8.17.a).

*Proof.*  `L` is type I while `S` and `T` are type non-I maximal subgroups, so `L` is conjugate to
neither (`not_conj_of_isTypeI_of_isTypeNonI`).  Hence (8.17.a) `card_LF_coprime_pq` gives
`|L_F| ⟂ p q`, in particular `|L_F| ⟂ q`, i.e. `q ∤ |L_F|`; the kernel `H = frob.typeI.typeF.H`
equals `L_F = maxNilpotentNormalHall L` (`TypeFData.H_eq`, so the "kernel_eq_MF" identification is
*not* opaque) and `|H.subgroupOf L| = |H|`.  The only gated input is `card_LF_coprime_pq` (B2,
BG Theorem E, owner F). -/
theorem q_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.q ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  -- `L` is type I, while `S`, `T` are type non-I maximal: `L` is conjugate to neither.
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  -- (8.17.a): `|L_F| ⟂ p q`, hence `q ∤ |L_F|`.
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hnotdvd : ¬ hyp.q ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.q_prime.coprime_iff_not_dvd.mp hcopq.symm
  -- `H = L_F = maxNilpotentNormalHall L`, and `|H.subgroupOf L| = |H|`.
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- (13.17.a/b)-strengthening of (12.7): the type-I Frobenius decomposition of `L` can be taken
with the complement containing `W₁` — Peterfalvi's "let `E` be a complement to `H` in `L` such
that `W₁ ⊂ E`".  Since `W₁ ≤ N_G(U) ≤ L` is coprime to the kernel (`q ∤ |L_F|`,
`q_not_dvd_kernel`), Schur–Zassenhaus complement conjugacy
(`exists_conj_le_of_isComplement'_of_coprime`) places `W₁` in a conjugate `E₀^x` of any complement
`E₀`, which is again a Frobenius complement (`IsFrobeniusGroup.conjComplement`).  The only `sorry`
is the coprimality, gated on the opaque `kernel_eq_MF` carrier. -/
theorem exists_typeIFrobeniusData_W1_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W1 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hLmax hLtypeI
  have hW1L : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  haveI : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  -- `L` (maximal) is solvable, hence so is the kernel.
  haveI hLsolv : IsSolvable ↥L :=
    _hG.solvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  haveI : IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  -- coprimality `|W₁| = q` to `|L_F|`.
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf L) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
      exact hyp.q_eq_card_W1.symm
    rw [hW1card]
    exact (hyp.q_prime.coprime_iff_not_dvd).mpr (q_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  -- `W₁` lies in a conjugate `E₀^x` of the complement.
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  -- `W₁ = (W₁.subgroupOf L).map L.subtype ≤ (E₀^x).map L.subtype`.
  have : hyp.W1 = (hyp.W1.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW1L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **Peterfalvi (13.17)**: if `S` is type II, a maximal subgroup over `N_G(U)` is type-I
Frobenius, contains `U` in its kernel, and has the stated complement alternatives (order `p q`,
containing a conjugate `W₂^y`).  Assembled from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), a `W₁`-containing Frobenius decomposition
(`exists_typeIFrobeniusData_W1_le`), and the complement structure (13.17.c,
`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ :=
    typeI_overNormalizer_complement _hG hyp hSTypeII hLmax hNUL hUH frob hW1E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

/-- **`T`-side dual of `q_not_dvd_kernel`** (V-side): `p = |W₂|` is coprime to the type-I Frobenius
kernel `L_F` (`p ∤ |L_F|`).  Mirror; same gated input `card_LF_coprime_pq` (`|L_F| ⟂ pq`). -/
theorem p_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hnotdvd : ¬ hyp.p ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.p_prime.coprime_iff_not_dvd.mp hcopp.symm
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- **`T`-side dual of `exists_typeIFrobeniusData_W1_le`** (V-side): the type-I Frobenius
decomposition of `L` can be taken with the complement containing `W₂` (`|W₂| = p` coprime to the
kernel by `p_not_dvd_kernel`, Schur–Zassenhaus complement conjugacy). -/
theorem exists_typeIFrobeniusData_W2_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W2 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hLmax hLtypeI
  have hW2L : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  haveI : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  haveI hLsolv : IsSolvable ↥L :=
    _hG.solvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  haveI : IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W2.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf L) = hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
      exact hyp.p_eq_card_W2.symm
    rw [hW2card]
    exact (hyp.p_prime.coprime_iff_not_dvd).mpr (p_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  have : hyp.W2 = (hyp.W2.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW2L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **`S`-side dual of `complement_inf_Q_structure`** (V-side, gated): for the `W₂`-containing
Frobenius complement `E`, `E ⊓ P = W₂` and `E ⊄ P`.  Mirror of the gated `complement_inf_Q_structure`
(the §13 residual `E ∩ P = W₂`); declared sorried per the hub cite-gated directive. -/
theorem complement_inf_P_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.P = hyp.W2 ∧
      ¬ frob.complement.map L.subtype ≤ hyp.P := sorry

/-- **`S`-side dual of `complement_le_QW2`** (V-side Huppert step): the `W₂`-containing Frobenius
complement `E` satisfies `E ≤ P W₁`.  Mirror of `complement_le_QW2` with `W₁/Q ↔ W₂/P`: `W₂` (of
prime order `p`) is normal in the Frobenius complement `E` (Huppert V.8.18b,
`normal_of_card_prime_of_isFrobeniusGroup_of_odd`), so `E ≤ N_G(W₂)`, and (13.16) `normalizer_W2`
gives `N_G(W₂) = P ⊔ W₁`.  (The Frobenius/Wielandt content of (13.16) is isolated in
`normalizer_W2_structure`.) -/
theorem complement_le_PW1 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.P ⊔ hyp.W1 := by
  set E := frob.complement with hEdef
  -- `W₂ ≤ L`, and `W₂` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW2L : hyp.W2 ≤ L := hW2E.trans hEleL
  have hW2L_le_E : hyp.W2.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW2E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₂` viewed inside `E`, of prime order `p`.
  set R : Subgroup ↥E := (hyp.W2.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.p := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
    exact hyp.p_eq_card_W2.symm
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₂` is normal in `E`, so `E` normalizes `W₂` in `↥L`.
  haveI hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.p_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW2L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₂)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW2L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW2L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₂) = C_G(W₂) = P W₁`.
  have h1316 := normalizer_W2 _hG hyp
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W2 : Set G) := h1316.1
    _ = hyp.P ⊔ hyp.W1 := h1316.2

/-- **`S`-side dual of `Q_W2_structure`** (V-side, gated): `W₁ ≤ N_G(P)`, `P ⊓ W₁ = ⊥`, and
`q ∤ |P|`.  Mirror of the gated `Q_W2_structure`; declared sorried per the hub cite-gated directive
(the `q ∤ |P|` and `P ⊓ W₁ = ⊥` parts bottom out on `|P| = p^q`, the §13 σ-structure). -/
theorem P_W1_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) ∧ hyp.P ⊓ hyp.W1 = ⊥ ∧
      ¬ hyp.q ∣ Nat.card ↥hyp.P := sorry

/-- **`T`-side dual of `complement_card_eq_pq`** (Pf (13.17.c)/(14.5), V-side): the `W₂`-containing
Frobenius complement of the type-I subgroup `L` over `N_G(V)` has order `p q`.  Mirror with the
`P`/`W₁` ↔ `Q`/`W₂` roles swapped; consumes the V-side complement-structure obligations. -/
theorem complement_card_eq_pq_V [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.P ⊔ hyp.W1 with hHg
  obtain ⟨hInf, hnle⟩ := complement_inf_P_structure _hG hyp frob hW2E
  have hEH : Em ≤ Hg := complement_le_PW1 _hG hyp frob hW2E
  obtain ⟨hWnorm, hdisj, _⟩ := P_W1_structure _hG hyp
  have hPleH : hyp.P ≤ Hg := le_sup_left
  have hInfCard : Nat.card ↥(Em ⊓ hyp.P) = hyp.p := by rw [hInf]; exact hyp.p_eq_card_W2.symm
  haveI hPnorm : (hyp.P.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.P * hyp.q := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W1 ⊓ hyp.P = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.q_eq_card_W1]
    exact mul_comm _ _
  have hPpos : 0 < Nat.card ↥hyp.P := Nat.card_pos
  have hindexH : (hyp.P.subgroupOf Hg).index = hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hPpos hmul
  have hdvd : hyp.P.relIndex Em ∣ hyp.q := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.P.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.P.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.P.relIndex Em = hyp.q :=
    (hyp.q_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  have hEmcard : Nat.card ↥Em = hyp.p * hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Em)
    rw [show (hyp.P.subgroupOf Em).index = hyp.q from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.P ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]

/-- **`T`-side dual of `TypeIOverNormalizerData`** (V-side): the type-I-over-`N_G(V)` structure of a
maximal `L` for `T` type II — its Frobenius decomposition with `V` in the kernel `L_F` and a
`W₁`-conjugate in the complement (order `p q`). -/
structure TypeIOverNormalizerDataV (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  H_eq_LF : H = maxNilpotentNormalHall L
  normalizer_V_le_L : Subgroup.normalizer (hyp.V : Set G) ≤ L
  frobenius : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L
  V_le_H : hyp.V ≤ H
  /-- **Peterfalvi (13.17.c)/(14.5)**: the Frobenius complement has order `p q` (the `W₂W₁^y`
  alternative). -/
  complement_card_eq_pq : Nat.card ↥frobenius.complement = hyp.p * hyp.q
  /-- **Peterfalvi (13.17.c)/(14.5)**: a conjugate `W₁^y` (`y ∈ P`) lies in the Frobenius
  complement of `L`. -/
  exists_y_W1_conj_le_complement :
    ∃ y ∈ hyp.P, (MulAut.conj y • hyp.W1 : Subgroup G) ≤
      frobenius.complement.map L.subtype

/-- **`T`-side dual of `typeI_overNormalizer_complement`** (Pf (13.17.c), V-side): the
`W₂`-containing Frobenius complement of `L` over `N_G(V)` has order `p q` and contains a conjugate
`W₁^y` (`y ∈ P`).  Mirror; the `∃ y` extraction reuses the generic `exists_mem_conj_W2_le_of_dvd_card`
with `(Q, W2, E) := (P, W1, E)`. -/
theorem typeI_overNormalizer_complement_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (_hTTypeII : IsTypeII hyp.T) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (_hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L)
    (_hVH : hyp.V ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.P, (MulAut.conj y • hyp.W1 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq_V _hG hyp frob hW2E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpP⟩ := P_W1_structure _hG hyp
  have hEPW1 := complement_le_PW1 _hG hyp frob hW2E
  haveI hPsolv : IsSolvable ↥hyp.P := by
    have hPS : hyp.P ≤ hyp.S := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    have hSlt : hyp.S < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.S_maximal).1
    exact _hG.solvable_of_lt_top hyp.P (lt_of_le_of_lt hPS hSlt)
  have hqE : hyp.q ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_left hyp.q hyp.p
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hPsolv hdisj hyp.q_prime
    hyp.q_eq_card_W1.symm hpP hEPW1 hqE

/-- **`T`-side dual of `typeII_overNormalizer_frobenius`** (Pf (13.17), V-side): for `T` type II, a
maximal subgroup over `N_G(V)` is type-I Frobenius, contains `V` in its kernel, and has a complement
of order `p q` with a conjugate `W₁^y`.  Assembled from `exists_typeI_maximal_overNormalizer_V`,
`exists_typeIFrobeniusData_W2_le`, and `typeI_overNormalizer_complement_V`. -/
theorem typeII_overNormalizer_frobenius_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    ∃ data : TypeIOverNormalizerDataV hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.V ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNVL, hVH⟩ :=
    exists_typeI_maximal_overNormalizer_V _hG hyp hTTypeII
  obtain ⟨frob, hker, hW2E⟩ := exists_typeIFrobeniusData_W2_le _hG hyp hLmax hLtypeI hNVL
  obtain ⟨hcard, hy⟩ :=
    typeI_overNormalizer_complement_V _hG hyp hTTypeII hLmax hNVL hVH frob hW2E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNVL, frob, hVH, hcard, hy⟩, hker, hVH⟩

/-- **Frobenius index bridge** (Pf (14.11), structural): for a type-I maximal `M` with
`TypeIFrobeniusData`, the index `|M : M_F|` of the Fitting kernel equals the order of the Frobenius
complement.  Immediate from the complement structure `M = M_F ⋊ complement` (`IsComplement'`) and the
kernel identity `typeF.H = M_F`.  Supplies the `e = |M : K| = p q` half of `MHypothesis`
(`e_eq_index` + `complement_card_eq_pq`): combined with the V-side `complement_card_eq_pq` (`= p q`),
the Fitting-kernel index of the type-I maximal over `N_G(V)` is `p q`. -/
theorem typeIFrobenius_kernel_index_eq_complement {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S14.TypeIFrobeniusData M) :
    ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card data.complement := by
  rw [← data.typeI.typeF.H_eq]
  exact data.frobenius.isComplement.symm.index_eq_card

/-- **Peterfalvi (14.10), structural foundation**: for `T` of type II, there is a type-I maximal
subgroup `M` over `N_G(V)` carrying a §14 `S14.Hypothesis`, with Fitting-kernel index
`|M : M_F| = p q`.  Assembled from the V-side producer `typeII_overNormalizer_frobenius_V` (`M`,
maximality, `N_G(V) ≤ M`, the Frobenius complement of order `p q`), `S14.exists_typeI_hypothesis`
(the (12.1) `Hypothesis` from `IsTypeI M`), and the index bridge
`typeIFrobenius_kernel_index_eq_complement` (`|M : M_F| = |complement| = p q`).  This is the
sorry-free structural half of `exists_MHypothesis` — it supplies `MHypothesis`'s
`M`/`K = M_F`/`typeIHyp`/`e_eq_index`/`complement_card_eq_pq` fields; the §7/§8/§13 character carrier
(`h78`, `betaM`, the σ counts) is isolated separately.  Gated on `T_typeII` (14.9) for `IsTypeII T`,
cited at the §16 consumer. -/
theorem exists_M_structural [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    ∃ (M : Subgroup G) (_typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.V : Set G) ≤ M ∧
          ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p * hyp.q := by
  obtain ⟨vdata, _hker, _hVH⟩ := typeII_overNormalizer_frobenius_V hG hyp hTII
  have hMtypeI : IsTypeI vdata.L := ⟨vdata.frobenius.typeI⟩
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG vdata.L_maximal hMtypeI
  refine ⟨vdata.L, typeIHyp, vdata.L_maximal, vdata.normalizer_V_le_L, ?_⟩
  rw [typeIFrobenius_kernel_index_eq_complement vdata.frobenius]
  exact vdata.complement_card_eq_pq

/-- Carrier for the virtual character `beta_j` and `Gamma_j` in (13.18). -/
structure BetaData (hyp : Hypothesis (G := G)) where
  j : Fin hyp.p
  j_ne_zero : (j : ℕ) ≠ 0
  beta : ClassFunction ↥hyp.S ℂ
  Gamma : ClassFunction G ℂ
  support_formula : Prop
  norm_formula : Prop
  Gamma_independent : Prop
  Gamma_orthogonal_one : Prop
  Gamma_real : Prop
  Y_norm_bound : Prop

/-- **Peterfalvi (13.18)**: the virtual character `beta_j` has controlled
support, norm, and orthogonal remainder. -/
theorem beta_support_norm_and_remainder [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : BetaData hyp,
      data.support_formula ∧ data.norm_formula ∧ data.Gamma_independent ∧
        data.Gamma_orthogonal_one ∧ data.Gamma_real ∧ data.Y_norm_bound := by
  sorry

/-- The parity conclusion in Peterfalvi (13.19.c2): the character inner
product is an odd integer, recorded inside `ℂ`. -/
def OddIntegerInner (χ ψ : ClassFunction G ℂ) : Prop :=
  ∃ n : ℤ, Odd n ∧
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)], ClassFunction.inner χ ψ = (n : ℂ)

/-- Carrier for the type-I comparison in Peterfalvi (13.19). -/
structure TypeIOrthogonalityData (hyp : Hypothesis (G := G)) (L : Subgroup G) where
  typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L
  e : ℕ
  e_eq_index : Prop
  Lset : Set (ClassFunction ↥L ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  disjoint_support : Prop
  Ltau_orthogonal_eta : Prop
  betaL_eta_independent : Prop
  caseC1 : Prop
  caseC2 : Prop
  caseC2_eta0j_odd :
    caseC2 →
      ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
  caseC1_bound :
    caseC1 →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
  caseC1_dual : Prop
  caseC2_dual : Prop
  caseC2_dual_etai0_odd :
    caseC2_dual →
      ∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
  caseC1_dual_bound :
    caseC1_dual →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))

namespace TypeIOrthogonalityData

/-- **Peterfalvi (13.19.c)**, consumer form: any strict gap beyond the
case-(c1) bound forces the parity alternative (c2). -/
theorem caseC2_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1 ∨ data.caseC2)
    (hgap :
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2 := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c)** after swapping `S` and `T`: any strict gap beyond
`(v - 1) / p` excludes the dual case-(c1) bound and forces the dual parity
alternative (c2), the source of the `eta_i0` congruences. -/
theorem caseC2_dual_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1_dual ∨ data.caseC2_dual)
    (hgap :
      ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2_dual := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_dual_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c2)**: once both S- and T-side parity alternatives
hold, the two zero-axis families of `eta` have odd integer inner product with
`beta_L`. -/
theorem eta_axes_odd_of_caseC2_pair {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L) (hcases : data.caseC2 ∧ data.caseC2_dual) :
    (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) := by
  exact ⟨data.caseC2_eta0j_odd hcases.1, data.caseC2_dual_etai0_odd hcases.2⟩

end TypeIOrthogonalityData

/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has Dade images
orthogonal to the `eta_ij`; on each zero axis, one of the two final parity
cases holds. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  sorry

end OddOrder.Peterfalvi.S15
