/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.Peterfalvi.S15_HonestTypeP2A0
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.GroupTheory.RepresentationTheory.InflationInduction
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient

/-!
# S15_SAndTDefs

Prefix-split from `OddOrder.Peterfalvi.S15_SAndTBasic` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# S15_SAndTBasic

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issue 0103 第 2 パス).
-/

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

/- `pgroup_le_of_normal_coprime_index` and `W2_le_P` were relocated upstream to
`S15_SAndT_Setup.lean` (issue 2033: the (1.10) congruence proof of `eta10_alphaCF_one_ne_zero`
needs `W2 <= P` at `Setup` level).  Downstream references are unchanged (same namespace). -/

/-- **Peterfalvi (13.16), TI reduction for the `W₂`-side**: `N_G(W₂) ≤ S`.

`W₂ ≤ P = S_F ≤ F(S)` (`W2_le_P` + `maxNilpotentNormalHall_le_fittingInG`), and `F(S)^#` is a
TI-subset whose normalizer is `S` (BG Theorem 15.7(a), in the type-uniform form
`S13.fittingIsTI_of_isTypeNonI`; the normalizer identity
`normalizer_fittingInAmbient_eq_self`).  Any `g` normalizing `W₂` sends a
nonidentity `a ∈ W₂ ⊆ F(S)^#` to `g a g⁻¹ ∈ W₂ ⊆ F(S)^#`, so the TI condition places
`g ∈ N_G(F(S)) = S`.  This is the first (TI) half of the (13.16) `W₂`-confinement; the residual
`N_G(W₂) ⊓ S ≤ P ⊔ W₁` is the Maschke/Wielandt core (`normalizer_W2_within_S`). -/
theorem normalizer_W2_le_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.S := by
  have hTI := OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI
    hG hyp.S_maximal hyp.S_nonI
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

/-- **Peterfalvi (13.12) `c = 1`, usable form**: `U ⊓ C_G(P) = ⊥` — no nonidentity element of the
complement `U` centralizes the Fitting kernel `P = S_F` (`U` acts faithfully on `P`).  Immediate from
`C_eq_bot` and `C = U ⊓ C_G(P)` (`C_eq`).  The Maschke/Wielandt core of (13.16) concludes
`N_U(W₂) ≤ U ⊓ C_G(P) = ⊥`. -/
theorem U_inf_centralizer_P_eq_bot_of_c_eq_one [Finite G]
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    hyp.U ⊓ Subgroup.centralizer (hyp.P : Set G) = ⊥ := by
  rw [← hyp.C_eq]
  exact hyp.C_eq_bot_of_c_eq_one hc1

/-- **Peterfalvi (13.16), Frobenius fixed-point-freeness of `W₁` on `U`**: `C_U(W₁) = ⊥` — no
nonidentity element of the complement `U` centralizes `W₁`.

Immediate from the `U ⋊ W₁` Frobenius structure (`BasicStructureData.UW1_frobenius`,
`IsFrobeniusGroup.conj_frobenius`): a nonidentity `x ∈ U` centralizing a nonidentity `w ∈ W₁` would
give `w x w⁻¹ = x`, contradicting the Frobenius condition (the complement acts fixed-point-freely on
the kernel).  This is the `C_K(W₁) ≤ C_U(W₁) = ⊥` input to the (13.16) core
`normalizer_U_inf_W2_eq_bot` (the coprime fixed-point lifting of the crux `K ≤ C_G(W₂)`). -/
theorem centralizer_W1_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.centralizer (hyp.W1 : Set G) = ⊥ := by
  obtain ⟨data, _⟩ := basic_structure hG hyp
  have hfrob := data.UW1_frobenius
  -- a nonidentity `w ∈ W₁` (`|W₁| = q` prime).
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro hbot
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  haveI : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨w0, hw0⟩ := exists_ne (1 : ↥hyp.W1)
  set w : G := (w0 : G) with hw
  have hwW1 : w ∈ hyp.W1 := w0.2
  have hwne : w ≠ 1 := fun h => hw0 (OneMemClass.coe_eq_one.mp (hw ▸ h))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxU, hxC⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  -- lift `w, x` to `↥(U ⊔ W₁)` and apply `conj_frobenius`.
  have hxUW1 : x ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_left hxU
  have hwUW1 : w ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_right hwW1
  have hxN : (⟨x, hxUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) := by
    rw [Subgroup.mem_subgroupOf]; exact hxU
  have hwA : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) := by
    rw [Subgroup.mem_subgroupOf]; exact hwW1
  have hxN1 : (⟨x, hxUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 :=
    fun h => hx1 (by simpa using congrArg (Subgroup.subtype _) h)
  have hwA1 : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 :=
    fun h => hwne (by simpa using congrArg (Subgroup.subtype _) h)
  have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hxC) w hwW1
  exact hfrob.conj_frobenius _ hwA hwA1 _ hxN hxN1 (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hcomm]; group)

/-- **Peterfalvi (13.16), the coprime-action datum**: `Coprime |P| |U ⋊ W₁|` — the complement
`U ⋊ W₁` acts coprimely on the Fitting kernel `P = S_F`.

`P = S_F` is the normal nilpotent Hall subgroup of `S` (`maxNilpotentNormalHall`, so
`Coprime |P| [S:P]`), and `U ⋊ W₁` complements `P` in `S`: from the `Sdata` complements
`M' ⋊ W₁ = S` (`M_complement`) and `P ⋊ U = M'` (`derived_complement`) one reads off
`P ⊓ (U ⊔ W₁) = ⊥` and `P ⊔ (U ⊔ W₁) = S`, so `[S:P] = |U ⊔ W₁|`.  This is the coprimality
datum consumed by the (13.16) core `normalizer_U_inf_W2_eq_bot` (ungated: `Sdata` supplies it). -/
theorem coprime_card_P_card_UW1 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥(hyp.U ⊔ hyp.W1)) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  -- `P ⊓ U = ⊥` (`derived_complement`).
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxH, hxU⟩
    have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF])
    have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
        (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓ (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
      ⟨Subgroup.mem_subgroupOf.mpr (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF]),
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_U_eq ▸ hxU)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- `M' ⊓ W₁ = ⊥` (`M_complement`).
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- `P ⊔ (U ⊔ W₁) = S`.
  have hSsup : hyp.P ⊔ (hyp.U ⊔ hyp.W1) = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_S,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq, hyp.S_deriv_eq_PU] at hmap
    rw [← sup_assoc]; exact hmap
  -- `P ⊓ (U ⊔ W₁) = ⊥` (write `y ∈ U ⊔ W₁ = U · W₁`, push into `M' ⊓ W₁` and `P ⊓ U`).
  have hPUW1_disj : hyp.P ⊓ (hyp.U ⊔ hyp.W1) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxUW1⟩ := Subgroup.mem_inf.mp hx
    have hxUW1' : (x : G) ∈ (↑(hyp.U ⊔ hyp.W1) : Set G) := hxUW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.U hyp.W1 hyp.W1_normalizes_U] at hxUW1'
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp hxUW1'
    have hwM' : w ∈ derivedInG hyp.S := by
      have : w = u⁻¹ * x := by rw [← huw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M' (SetLike.mem_coe.mp hu)))
        (hP_le_M' hxP)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W1, Subgroup.mem_bot] at this
    have hxu : x = u := by rw [← huw, hw1, mul_one]
    have hxPU : x ∈ hyp.P ⊓ hyp.U := Subgroup.mem_inf.mpr ⟨hxP, hxu ▸ SetLike.mem_coe.mp hu⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  -- `U ⋊ W₁` complements `P` in `↥S`; hence `[S:P] = |U ⋊ W₁|`.
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hcompl : Subgroup.IsComplement' ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S)
      (hyp.P.subgroupOf hyp.S) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      have hyPU : (y : G) ∈ hyp.P ⊓ (hyp.U ⊔ hyp.W1) := ⟨hy.2, hy.1⟩
      rw [hPUW1_disj, Subgroup.mem_bot] at hyPU
      rw [Subgroup.mem_bot]; exact Subtype.ext hyPU
    · have hsup : ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊔ (hyp.P.subgroupOf hyp.S) = ⊤ := by
        rw [sup_comm, ← Subgroup.subgroupOf_sup hP_le_S hUW1_le_S, hSsup, Subgroup.subgroupOf_self]
      rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]
  have hindex : (hyp.P.subgroupOf hyp.S).index = Nat.card ↥(hyp.U ⊔ hyp.W1) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv
  -- `P` is Hall in `S`: `Coprime |P| [S:P]`.
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
  rw [← hyp.P_eq_SF] at hHall
  have hcopIdx : Nat.Coprime (Nat.card ↥hyp.P) (hyp.P.subgroupOf hyp.S).index := by
    have hcard_eq : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
    exact hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
  rw [hindex] at hcopIdx
  exact hcopIdx

/-- **Peterfalvi (13.16), `W₁`-triviality on `K/C_K(W₂)`**: for `g ∈ N_G(W₂)` and `w ∈ W₁`, the
"twisted commutator" `g⁻¹ (w g w⁻¹) ∈ C_G(W₂)` — conjugating `g` by `w ∈ W₁ ≤ C_G(W₂)` changes it
only by an element centralizing `W₂`.

Since `w` centralizes `W₂` (`W = W₁ × W₂` abelian) and `g` normalizes `W₂`, the elements `w g w⁻¹`
and `g` induce the **same** conjugation on `W₂` (`w` fixes `g y g⁻¹ ∈ W₂`), so
`g⁻¹ (w g w⁻¹)` centralizes `W₂`.  This is the "`W₁` acts trivially on `K/C_K(W₂)`" input to the
coprime fixed-point lifting (`coprime_fixedPoints_quotient`) of the crux `K ≤ C_G(W₂)` in
`normalizer_U_inf_W2_eq_bot`. -/
theorem conj_W1_mem_centralizer_W2 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {g : G} (hg : g ∈ Subgroup.normalizer (hyp.W2 : Set G))
    {w : G} (hw : w ∈ hyp.W1) :
    g⁻¹ * (w * g * w⁻¹) ∈ Subgroup.centralizer (hyp.W2 : Set G) := by
  -- `w` centralizes `W₂`.
  have hwC : ∀ z ∈ hyp.W2, w * z = z * w := fun z hz => hyp.W1_commutes_W2 w hw z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyW2 : y ∈ hyp.W2 := hy
  -- `g y g⁻¹ ∈ W₂`.
  have hy1 : g * y * g⁻¹ ∈ hyp.W2 := (Subgroup.mem_normalizer_iff.mp hg y).mp hyW2
  -- `w⁻¹ y w = y` and `w (g y g⁻¹) w⁻¹ = g y g⁻¹`.
  have h1 : w⁻¹ * y * w = y := by
    rw [mul_assoc, ← hwC y hyW2, inv_mul_cancel_left]
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

/-- **Peterfalvi (13.16), the crux `K ≤ C_G(W₂)`**: every element of `K := U ⊓ N_G(W₂)` centralizes
`W₂`.

The conjugation action of `W₁` on the abelian `U` is coprime (`(|W₁|, |U|) = 1` from the `U ⋊ W₁`
Frobenius structure) with fixed points `C_U(W₁) = ⊥` (`centralizer_W1_inf_U_eq_bot`).  For `g ∈ K`,
`W₁` fixes the coset `g · C_U(W₂)` (`conj_W1_mem_centralizer_W2`: `g⁻¹ (w g w⁻¹) ∈ C_G(W₂)`), so the
coprime fixed-point lifting `Isaacs.Ch04.coprime_fixedPoints_quotient` (Cor 3.28) produces a
`W₁`-fixed representative `c ∈ C_U(W₁) = ⊥`; hence `g ≡ 1 (mod C_U(W₂))`, i.e. `g ∈ C_G(W₂)`. -/
theorem normalizer_U_inf_W2_le_centralizer_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
  obtain ⟨data, _⟩ := basic_structure hG hyp
  have hfrob := data.UW1_frobenius
  haveI hUcomm := data.U_commutative
  -- conjugation action `φ : ↥W₁ → MulAut ↥U`.
  letI actU : MulDistribMulAction ↥hyp.W1 ↥hyp.U :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (hyp.U : Set G))) ↥hyp.U
      (Subgroup.inclusion hyp.W1_normalizes_U)
  set φ : ↥hyp.W1 →* MulAut ↥hyp.U := MulDistribMulAction.toMulAut ↥hyp.W1 ↥hyp.U with hφ
  have hφ_coe : ∀ (a : ↥hyp.W1) (x : ↥hyp.U),
      (hyp.U.subtype ((φ a) x)) = (↑a) * (hyp.U.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
  -- `N := C_U(W₂)`, normal in the abelian `↥U`.
  set N : Subgroup ↥hyp.U :=
    (hyp.U ⊓ Subgroup.centralizer (hyp.W2 : Set G)).subgroupOf hyp.U with hN_def
  haveI hNnorm : N.Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  -- coprimality `(|W₁|, |U|) = 1`.
  have hCop : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥hyp.U) := by
    have hk := hfrob.coprime_card_kernel_complement
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      Nat.coprime_comm] at hk
  -- `W₁ ≤ C_G(W₂)`, so `N` is `W₁`-invariant.
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hyp.W1_commutes_W2 x hx z hz).symm
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hN_def, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.mp hx
    have hval : (hyp.U.subtype ((φ a) x)) = (↑a) * (hyp.U.subtype x) * (↑a)⁻¹ := hφ_coe a x
    refine Subgroup.mem_inf.mpr ⟨((φ a) x).2, ?_⟩
    rw [show ((φ a) x : G) = (hyp.U.subtype ((φ a) x)) from rfl, hval]
    exact (Subgroup.centralizer (hyp.W2 : Set G)).mul_mem
      (Subgroup.mul_mem _ (hW1_le_C a.2) hxC) (Subgroup.inv_mem _ (hW1_le_C a.2))
  -- main: `g ∈ U ⊓ N_G(W₂)` ⟹ `g ∈ C_G(W₂)`.
  intro g hg
  obtain ⟨hgU, hgNW2⟩ := Subgroup.mem_inf.mp hg
  set gg : ↥hyp.U := ⟨g, hgU⟩ with hgg
  -- `W₁` fixes the coset `gg · N`.
  have hg_fix : ∀ a : ↥hyp.W1, ∃ n ∈ N, (φ a) gg = gg * n := by
    intro a
    refine ⟨gg⁻¹ * (φ a) gg, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [hN_def, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨(gg⁻¹ * (φ a) gg).2, ?_⟩
    have hval : ((gg⁻¹ * (φ a) gg : ↥hyp.U) : G) = g⁻¹ * ((a : G) * g * (a : G)⁻¹) := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv,
        show ((φ a) gg : G) = (hyp.U.subtype ((φ a) gg)) from rfl, hφ_coe a gg]
      rfl
    rw [hval]
    exact conj_W1_mem_centralizer_W2 hG hyp hgNW2 a.2
  obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ) hCop
      (Or.inr (isSolvable_of_comm (fun a b => mul_comm' a b))) hN_inv hg_fix
  -- `c` is `W₁`-fixed ⟹ `(c:G) ∈ C_U(W₁) = ⊥` ⟹ `c = 1`.
  have hc1 : c = 1 := by
    have hcmem : (c : G) ∈ hyp.U ⊓ Subgroup.centralizer (hyp.W1 : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfix := hc_fix ⟨w, hw⟩
      have hco : (hyp.U.subtype c) = (w : G) * (hyp.U.subtype c) * (w : G)⁻¹ := by
        have e1 := hφ_coe ⟨w, hw⟩ c
        rw [hfix] at e1
        exact e1
      exact mul_inv_eq_iff_eq_mul.mp hco.symm
    rw [centralizer_W1_inf_U_eq_bot hG hyp, Subgroup.mem_bot] at hcmem
    exact Subtype.ext hcmem
  -- `gg = m⁻¹ ∈ N` ⟹ `g ∈ C_G(W₂)`.
  rw [hc1, eq_comm, mul_eq_one_iff_eq_inv] at hc_eq
  have hggN : gg ∈ N := by rw [hc_eq]; exact N.inv_mem hm
  rw [hN_def, Subgroup.mem_subgroupOf] at hggN
  exact (Subgroup.mem_inf.mp hggN).2

/-- **Peterfalvi (13.16), the core assembly** (`U ⊓ N_G(W₂) = ⊥`, modulo the two §16-carrier data).

Given the (13.2) faithfulness data `hdisj : P ⊓ U = ⊥` (yielding `Coprime |U| |P|`) and the type-`P`
reconciliation `hrec : Sdata.W2 = W2`, the assembly closes the core from the proven crux
`K ≤ C_G(W₂)` (`normalizer_U_inf_W2_le_centralizer_W2`):

* the coprime `K`-action on the abelian `P` decomposes `P = (C_G(K) ⊓ P) ⊕ ⁅P, K⁆`
  (`Isaacs.Ch05.fitting_coprime_abelian_decomp`, Gorenstein Thm 2.3);
* `W₁` acts fixed-point-freely on `⁅P, K⁆`: any `W₁`-fixed `n ∈ ⁅P, K⁆ ⊆ P` lies in
  `M' ⊓ C_G(x) = Sdata.W2 = W₂` (`TypePData.centralizer_W1` + `hrec`) `⊆ C_G(K) ⊓ P` (crux), so
  `n ∈ (C_G(K) ⊓ P) ⊓ ⁅P, K⁆ = ⊥`;
* the full `U ⋊ W₁` Frobenius (`UW1_frobenius`; `U` abelian ⟹ `U ≤ N_G(⁅P,K⁆)`) then centralizes
  `⁅P, K⁆` by Wielandt (`frobenius_kernel_centralizes_of_complement_fpf`);
* so `⁅P, K⁆ ≤ C_G(U) ∩ P ≤ C_G(K) ⊓ P`, whence `⁅P, K⁆ = ⊥`, i.e. `K ≤ C_G(P)`, giving
  `K ≤ U ⊓ C_G(P) = ⊥` (`U_inf_centralizer_P_eq_bot`). -/
theorem normalizer_U_inf_W2_eq_bot_of_data_and_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (hcop : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥(hyp.U ⊔ hyp.W1)))
    (hrec : hyp.Sdata.W2 = hyp.W2) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ := by
  obtain ⟨data, _, hP_elemAb, _, _, _⟩ := basic_structure hG hyp
  haveI hUcomm := data.U_commutative
  set K := hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) with hK_def
  have hK_le_U : K ≤ hyp.U := inf_le_left
  -- crux: `K ≤ C_G(W₂)`.
  have hKC : K ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
    normalizer_U_inf_W2_le_centralizer_W2 hG hyp
  -- `P` abelian.
  haveI hPcomm : IsMulCommutative ↥hyp.P := IsMulCommutative.of_comm hP_elemAb.comm
  -- divisibilities `|K| ∣ |U| ∣ |U⋊W₁|`, from the coprime-action datum `hcop`.
  have hUdvdUW1 : Nat.card ↥hyp.U ∣ Nat.card ↥(hyp.U ⊔ hyp.W1) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hKdvdU : Nat.card ↥K ∣ Nat.card ↥hyp.U := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_U).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopPK : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥K) :=
    hcop.coprime_dvd_right (hKdvdU.trans hUdvdUW1)
  -- normalizer facts: `S ≤ N(P)`, `U ≤ S`, `W₁ ≤ S`, `W₁ ≤ N(W₂)`.
  have hMFleM : maxNilpotentNormalHall hyp.S ≤ hyp.S :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S)
  have hM'le : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hU_le_S : hyp.U ≤ hyp.S :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.S_deriv_eq_PU.symm)) hM'le
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    exact (hyp.W1_commutes_W2 x hx z hz).symm
  have hW1_le_N : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) :=
    hW1_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hK_norm_P : K ≤ Subgroup.normalizer (hyp.P : Set G) := (hK_le_U.trans hU_le_S).trans hS_norm_P
  -- `U ≤ N(K)` (`U` abelian, `K ≤ U`).
  haveI hKnormalU : (K.subgroupOf hyp.U).Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  have hU_norm_K : hyp.U ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hK_le_U
  -- `W₁ ≤ N(K)` (`W₁ ≤ N(U)` and `W₁ ≤ N(N(W₂))`).
  have hW1_norm_K : hyp.W1 ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]; intro n
    have hwU := Subgroup.mem_normalizer_iff.mp (hyp.W1_normalizes_U hw) n
    have hwN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hW1_le_N hw)) n
    rw [hK_def, Subgroup.mem_inf, Subgroup.mem_inf, hwU, hwN]
  -- Gorenstein 2.3 decomposition `P = (C(K) ⊓ P) ⊕ ⁅P, K⁆`.
  obtain ⟨hdec_inf, hdec_sup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp hK_norm_P hcopPK
  have hPK_le_P : (⁅hyp.P, K⁆ : Subgroup G) ≤ hyp.P := le_sup_right.trans (le_of_eq hdec_sup)
  -- `W₂ ≤ C(K) ⊓ P`.
  have hW2_le_P : hyp.W2 ≤ hyp.P := W2_le_P hG hyp
  have hW2_le_CK : hyp.W2 ≤ Subgroup.centralizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hk)) y hy).symm
  -- Wielandt: `U ≤ C(⁅P,K⁆)`.
  have hUEnorm : hyp.U ⊔ hyp.W1 ≤ Subgroup.normalizer ((⁅hyp.P, K⁆ : Subgroup G) : Set G) := by
    rw [sup_le_iff]
    refine ⟨fun u hu => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator ((hU_le_S.trans hS_norm_P) hu)
      (hU_norm_K hu), fun w hw => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator
      ((hW1_le_S.trans hS_norm_P) hw) (hW1_norm_K hw)⟩
  haveI hPKsolv : IsSolvable ↥(⁅hyp.P, K⁆ : Subgroup G) :=
    isSolvable_of_comm (fun a b => Subtype.ext (by
      have h := hP_elemAb.comm (⟨(a : G), hPK_le_P a.2⟩ : ↥hyp.P) (⟨(b : G), hPK_le_P b.2⟩ : ↥hyp.P)
      have h2 := congrArg (Subgroup.subtype hyp.P) h
      simpa using h2))
  -- `Coprime |⁅P,K⁆| |U⋊W₁|`: `⁅P,K⁆ ≤ P` and `hcop`.
  have hPKdvdP : Nat.card ↥(⁅hyp.P, K⁆ : Subgroup G) ∣ Nat.card ↥hyp.P := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK_le_P).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopPKfrob : Nat.Coprime (Nat.card ↥(⁅hyp.P, K⁆ : Subgroup G))
      (Nat.card ↥(hyp.U ⊔ hyp.W1)) := hcop.coprime_dvd_left hPKdvdP
  have hUcent : hyp.U ≤ Subgroup.centralizer ((⁅hyp.P, K⁆ : Subgroup G) : Set G) :=
    frobenius_kernel_centralizes_of_complement_fpf hUEnorm data.UW1_frobenius hPKsolv hcopPKfrob
      (by
        intro n hnPK hnfix
        -- `n ∈ ⁅P,K⁆ ⊆ P` fixed by all of `W₁` ⟹ `n ∈ Sdata.W2 = W₂ ⊆ C(K) ⊓ P` ⟹ `n = 1`.
        have hnP : n ∈ hyp.P := hPK_le_P hnPK
        -- a nonidentity `x ∈ W₁ = Sdata.W1`.
        have hW1ne : hyp.Sdata.W1 ≠ ⊥ := hyp.Sdata.W1_nontrivial
        haveI : Nontrivial ↥hyp.Sdata.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
        obtain ⟨x0, hx0⟩ := exists_ne (1 : ↥hyp.Sdata.W1)
        have hxW1 : (x0 : G) ∈ hyp.W1 := hyp.Sdata_W1_eq ▸ x0.2
        have hxne : (x0 : G) ≠ 1 := fun h => hx0 (OneMemClass.coe_eq_one.mp h)
        have hnCx : (x0 : G) * n * (x0 : G)⁻¹ = n := hnfix _ hxW1
        have hnCent : n ∈ Subgroup.centralizer ({(x0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; intro z hz
          rw [Set.mem_singleton_iff] at hz; subst hz
          exact (mul_inv_eq_iff_eq_mul.mp hnCx)
        have hnM' : n ∈ derivedInG hyp.S := by
          have hPM' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
          exact hPM' hnP
        have hreg := hyp.Sdata.centralizer_W1 (x0 : G) x0.2 hxne
        have hnW2 : n ∈ hyp.W2 := by
          rw [← hrec, ← hreg]; exact Subgroup.mem_inf.mpr ⟨hnM', hnCent⟩
        have hnInf : n ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.P) ⊓ (⁅hyp.P, K⁆ : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hW2_le_CK hnW2, hnP⟩, hnPK⟩
        rw [hdec_inf, Subgroup.mem_bot] at hnInf
        exact hnInf)
  -- `⁅P,K⁆ ≤ C(K) ⊓ P`, hence `⁅P,K⁆ = ⊥`.
  have hPK_le_CK : (⁅hyp.P, K⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    -- `k ∈ K ≤ U ≤ C(⁅P,K⁆)`, so `k` centralizes `x ∈ ⁅P,K⁆`.
    exact (Subgroup.mem_centralizer_iff.mp (hUcent (hK_le_U hk)) x hx).symm
  have hPK_bot : (⁅hyp.P, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.P) ⊓ (⁅hyp.P, K⁆ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hPK_le_CK hx, hPK_le_P hx⟩, hx⟩
    rwa [hdec_inf] at this
  -- `⁅P,K⁆ = ⊥ ⟹ K ≤ C(P) ⟹ K ≤ U ⊓ C(P) = ⊥`.
  have hK_le_CP : K ≤ Subgroup.centralizer (hyp.P : Set G) := by
    have hPcentK : hyp.P ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := hyp.P) (H₂ := K)).mp hPK_bot
    intro k hk
    rw [Subgroup.mem_centralizer_iff]; intro p hp
    exact ((Subgroup.mem_centralizer_iff.mp (hPcentK hp)) k hk).symm
  have : K ≤ hyp.U ⊓ Subgroup.centralizer (hyp.P : Set G) := le_inf hK_le_U hK_le_CP
  rw [U_inf_centralizer_P_eq_bot_of_c_eq_one hyp hc1] at this
  exact le_bot_iff.mp this

/-- **Peterfalvi (13.16), the Maschke/Wielandt core proper**: `N_U(W₂) = 1`, i.e.
`U ⊓ N_G(W₂) = ⊥` — no nonidentity element of the complement `U` normalizes `W₂`.

This is the single group-theoretic fact carrying the genuine content of the `W₂`-side of (13.16)
(Coq `FTtypeP_norm_cent_compl`, the `K := 'N_U(W₂)` computation).  Writing `K := U ⊓ N_G(W₂)`, the
proof plan below has been **verified to need no new infrastructure** — every cited lemma is present
in the repo (see `notes/peterfalvi/s15_s_and_t.md`, the (13.16) core plan block).

**Crux (ungated, about the abstract `W₂`): `K ≤ C_G(W₂)` — PROVEN as
`normalizer_U_inf_W2_le_centralizer_W2`.**  `W₁` acts on the abelian `U` by conjugation, coprimely
(`|W₁| = q` coprime to `|U|` from `BasicStructureData.UW1_frobenius`), with fixed points
`C_U(W₁) = ⊥` (`centralizer_W1_inf_U_eq_bot`).  `W₁` acts **trivially** on `K/C_K(W₂)`
(`conj_W1_mem_centralizer_W2`), so the coprime fixed-point lifting
`Isaacs.Ch04.coprime_fixedPoints_quotient` (Cor 3.28) forces `K = C_K(W₂) ≤ C_G(W₂)`.

**Assembly (given `K ≤ C_G(W₂)`).**  Two simplifications over the Coq route:
* use the **full** `U ⋊ W₁` Frobenius (not `K ⋊ W₁`), so no `Frobenius_subl` is needed — `U`
  abelian ⟹ `U ≤ N_G(⁅P,K⁆)`, and the Wielandt fixed-point theorem
  (`frobenius_kernel_centralizes_of_complement_fpf`, `N := ⁅P,K⁆`) yields `U ≤ C_G(⁅P,K⁆)`;
* use **Gorenstein Thm 2.3** `P = C_P(K) × ⁅P,K⁆` (`fixedPoints_inf_actionCommutator_eq_bot_of_abelian`
  for the coprime `K`-action on the abelian `P`) instead of a Maschke complement to `W₂`.

  The `W₁`-fixed-point-freeness on `⁅P,K⁆` is `C_{⁅P,K⁆}(W₁) = ⁅P,K⁆ ⊓ C_P(W₁) = ⁅P,K⁆ ⊓ W₂ ⊆
  ⁅P,K⁆ ⊓ C_P(K) = ⊥` — using `W₂ ≤ C_P(K)` (from the crux) and the **regularity** `C_P(W₁) = W₂`
  (`TypePData.centralizer_W1`, the one **`Sdata.W2 = W₂` reconciliation gate**, §16-carrier content
  threaded through the enriched §16 `Hypothesis`, issue 3001-adjacent).  Then `⁅P,K⁆ ≤ C_P(U) ≤
  C_P(K)`, so `⁅P,K⁆ ⊆ C_P(K) ⊓ ⁅P,K⁆ = ⊥`, giving `K ≤ C_G(P)`, hence
  `K ≤ U ⊓ C_G(P) = ⊥` (`U_inf_centralizer_P_eq_bot`, the `c = 1` finish).

`normalizer_W2_within_S` (the Dedekind reduction) already discharges (13.16) from this fact. -/
theorem normalizer_U_inf_W2_eq_bot_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ :=
  -- The coprime-action datum is discharged by `coprime_card_P_card_UW1` (ungated); the type-`P`
  -- reconciliation is the `Hypothesis` field `Sdata_W2_eq` (§16-carrier, supplied by the enriched
  -- §16 construction via `typePData_of_kappaHall_hallComplement_W2`).
  normalizer_U_inf_W2_eq_bot_of_data_and_c_eq_one hG hyp hc1
    (coprime_card_P_card_UW1 hG hyp) hyp.Sdata_W2_eq

/-- **Peterfalvi (13.16), Maschke/Wielandt core for the `W₂`-side**: `N_G(W₂) ⊓ S ≤ P ⊔ W₁`.

The `S`-internal residual of the (13.16) `W₂`-confinement (after the TI reduction `N_G(W₂) ≤ S` of
`normalizer_W2_le_S`).  Reduced by the **Dedekind modular law** to the core `N_U(W₂) = ⊥`
(`normalizer_U_inf_W2_eq_bot`): writing `S = (P ⊔ U) ⊔ W₁` (`S_deriv_eq_PU` + the `Sdata` complement
`M' ⋊ W₁ = S`), and using `P, W₁ ≤ C_G(W₂) ≤ N_G(W₂)` (`P` elementary abelian, `W = W₁ × W₂`
abelian), modularity peels off `W₁` and `P`:
`N_G(W₂) ⊓ S = W₁ ⊔ (P ⊔ (U ⊓ N_G(W₂))) = P ⊔ W₁ ⊔ N_U(W₂) = P ⊔ W₁` since `N_U(W₂) = ⊥`. -/
theorem normalizer_W2_within_S_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) ⊓ hyp.S ≤ hyp.P ⊔ hyp.W1 := by
  have hK : hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ :=
    normalizer_U_inf_W2_eq_bot_of_c_eq_one hG hyp hc1
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
  have hP_le_N : hyp.P ≤ Subgroup.normalizer (hyp.W2 : Set G) :=
    hP_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hW1_le_N : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) :=
    hW1_le_C.trans (Subgroup.centralizer_le_normalizer _)
  -- `P ⊴ S` and `M' := derivedInG S ⊴ S`, so `S ≤ N_G(P)` and `S ≤ N_G(M')`.
  have hMFleM : maxNilpotentNormalHall hyp.S ≤ hyp.S :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S)
  have hM'le : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hM'_normal : ((derivedInG hyp.S).subgroupOf hyp.S).Normal := by
    rw [show (derivedInG hyp.S).subgroupOf hyp.S = commutator ↥hyp.S by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective hyp.S.subtype_injective]]
    infer_instance
  have hS_norm_M' : hyp.S ≤ Subgroup.normalizer ((derivedInG hyp.S : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'le).mp hM'_normal
  have hU_le_S : hyp.U ≤ hyp.S :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.S_deriv_eq_PU.symm)) hM'le
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  -- `S = derivedInG S ⊔ W₁` (the `Sdata` complement `M' ⋊ W₁ = S`).
  have hSsup : derivedInG hyp.S ⊔ hyp.W1 = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'le,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq] at hmap
    exact hmap
  -- **Sub-goal A** (Dedekind): `M' ⊓ N_G(W₂) = P`, since `M' = P ⊔ U`, `U ≤ N_G(P)`, and
  -- `(M' ⊓ N_G(W₂)) ⊓ U = U ⊓ N_G(W₂) = ⊥`.
  have hHU : ((derivedInG hyp.S) ⊓ Subgroup.normalizer (hyp.W2 : Set G)) ⊓ hyp.U = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_right hyp.U inf_le_right) ?_)
    rw [inf_comm]; exact hK.le
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S :=
    le_trans le_sup_left (le_of_eq hyp.S_deriv_eq_PU.symm)
  have hMN : (derivedInG hyp.S) ⊓ Subgroup.normalizer (hyp.W2 : Set G) = hyp.P := by
    have happ := OddOrder.BG.Ch3.S12.eq_sup_inf_of_le_normalizer (hU_le_S.trans hS_norm_P)
      (le_inf hP_le_M' hP_le_N) (inf_le_left.trans (le_of_eq hyp.S_deriv_eq_PU))
    rw [happ, hHU, sup_bot_eq]
  -- **Sub-goal B** (element-wise): `g ∈ N_G(W₂) ⊓ S`; write `g = w·m` (`w ∈ W₁`, `m ∈ M'`) via
  -- `S = W₁ · M'`.  Then `m = w⁻¹ g ∈ N_G(W₂)`, so `m ∈ M' ⊓ N_G(W₂) = P`, hence `g ∈ P ⊔ W₁`.
  intro g hg
  obtain ⟨hgN, hgS⟩ := Subgroup.mem_inf.mp hg
  have hmem : (g : G) ∈ ((hyp.W1 : Set G) * (derivedInG hyp.S : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right hyp.W1 (derivedInG hyp.S)
      (hW1_le_S.trans hS_norm_M'), SetLike.mem_coe, sup_comm, hSsup]
    exact hgS
  obtain ⟨w, hw, m, hm, hwm⟩ := Set.mem_mul.mp hmem
  have hmN : m ∈ Subgroup.normalizer (hyp.W2 : Set G) := by
    have hm_eq : m = w⁻¹ * g := by rw [← hwm]; group
    rw [hm_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW1_le_N (SetLike.mem_coe.mp hw))) hgN
  have hmP : m ∈ hyp.P := by
    have hmem2 : m ∈ (derivedInG hyp.S) ⊓ Subgroup.normalizer (hyp.W2 : Set G) :=
      Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hm, hmN⟩
    rwa [hMN] at hmem2
  rw [← hwm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (SetLike.mem_coe.mp hw))
    (Subgroup.mem_sup_left hmP)

/-- **Peterfalvi (13.16), structural core for the `W₂`-side**: the Frobenius/Wielandt containment
`N_G(W₂) ≤ P ⊔ W₁`.  Assembled from the TI reduction `N_G(W₂) ≤ S` (`normalizer_W2_le_S`, proven)
and the Maschke/Wielandt core `N_G(W₂) ⊓ S ≤ P ⊔ W₁` (`normalizer_W2_within_S`, the isolated
residual): every `g ∈ N_G(W₂)` lies in `S`, hence in `N_G(W₂) ⊓ S ≤ P ⊔ W₁`. -/
theorem normalizer_W2_structure_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 := by
  intro g hg
  have hgS : g ∈ hyp.S := normalizer_W2_le_S hG hyp hg
  exact normalizer_W2_within_S_of_c_eq_one hG hyp hc1 (Subgroup.mem_inf.mpr ⟨hg, hgS⟩)

/-- **Peterfalvi (13.16), `W₂`-side**: `N_G(W₂) = C_G(W₂) = P ⊔ W₁` (the `S↔T`, `W₁↔W₂`, `P↔Q`
dual of `normalizer_W1_of_D_eq_bot`; the form stated directly in Coq
`FTtypeP_norm_cent_compl`).

Proved from `normalizer_W2_structure` by the antisymmetric chain
`P ⊔ W₁ ≤ C_G(W₂) ≤ N_G(W₂) ≤ P ⊔ W₁`:

* `W₁ ≤ C_G(W₂)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `P ≤ C_G(W₂)` because `W₂ ≤ P` (`W2_le_P`) and `P` is elementary abelian (`basic_structure`);
* `C_G(W₂) ≤ N_G(W₂)` always (`centralizer_le_normalizer`);
* `N_G(W₂) ≤ P ⊔ W₁` is the Frobenius/Wielandt containment (`normalizer_W2_structure`).

Supplies the `W₂`-side of the (13.17.c) Huppert step (`E ≤ P W₁`). -/
theorem normalizer_W2_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) = Subgroup.centralizer (hyp.W2 : Set G) ∧
      Subgroup.centralizer (hyp.W2 : Set G) = hyp.P ⊔ hyp.W1 := by
  have hN_le : Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 :=
    normalizer_W2_structure_of_c_eq_one hG hyp hc1
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
  have h3p : hyp.p * 3 ≤ hyp.p * hyp.q := mul_le_mul_right hq3 hyp.p
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

end OddOrder.Peterfalvi.S15
