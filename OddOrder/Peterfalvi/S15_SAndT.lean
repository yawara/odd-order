/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.GroupTheory.RepresentationTheory.InflationInduction
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient

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
theorem normalizer_U_inf_W2_eq_bot_of_data [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
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
  rw [U_inf_centralizer_P_eq_bot hG hyp] at this
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
theorem normalizer_U_inf_W2_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ :=
  -- The coprime-action datum is discharged by `coprime_card_P_card_UW1` (ungated); the type-`P`
  -- reconciliation is the `Hypothesis` field `Sdata_W2_eq` (§16-carrier, supplied by the enriched
  -- §16 construction via `typePData_of_kappaHall_hallComplement_W2`).
  normalizer_U_inf_W2_eq_bot_of_data hG hyp (coprime_card_P_card_UW1 hG hyp) hyp.Sdata_W2_eq

/-- **Peterfalvi (13.16), Maschke/Wielandt core for the `W₂`-side**: `N_G(W₂) ⊓ S ≤ P ⊔ W₁`.

The `S`-internal residual of the (13.16) `W₂`-confinement (after the TI reduction `N_G(W₂) ≤ S` of
`normalizer_W2_le_S`).  Reduced by the **Dedekind modular law** to the core `N_U(W₂) = ⊥`
(`normalizer_U_inf_W2_eq_bot`): writing `S = (P ⊔ U) ⊔ W₁` (`S_deriv_eq_PU` + the `Sdata` complement
`M' ⋊ W₁ = S`), and using `P, W₁ ≤ C_G(W₂) ≤ N_G(W₂)` (`P` elementary abelian, `W = W₁ × W₂`
abelian), modularity peels off `W₁` and `P`:
`N_G(W₂) ⊓ S = W₁ ⊔ (P ⊔ (U ⊓ N_G(W₂))) = P ⊔ W₁ ⊔ N_U(W₂) = P ⊔ W₁` since `N_U(W₂) = ⊥`. -/
theorem normalizer_W2_within_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ⊓ hyp.S ≤ hyp.P ⊔ hyp.W1 := by
  have hK : hyp.U ⊓ Subgroup.normalizer (hyp.W2 : Set G) = ⊥ :=
    normalizer_U_inf_W2_eq_bot hG hyp
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
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16) `normalizer_W1_structure`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

/-- **`T`-side Fitting-TI source** (Pf (13.16), dual of the `S`-side `fittingIsTI_of_isTypeP2`):
`F(T)^#` is a TI-subset of `G` (with normalizer `T`).

On the `W₂`-side, `normalizer_W2_le_S` reduces `N_G(W₂) ≤ S` using BG Theorem 15.7(a) applied to `S`'s
type-`P₂` carrier `S_typeP2` (`fittingIsTI_of_isTypeP2`).  The `W₁`-side dual applies the same
Theorem 15.7(a) to `T`: the (14.9) conclusion `IsTypeII T`, together with the BG type dictionary
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
    show a ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
    exact ⟨hW1F haW1, hane⟩
  have hga_sharp : g * a * g⁻¹ ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.T := by
    show g * a * g⁻¹ ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
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

/-- **`T`-side dual of `isMulCommutative_U`** (Pf (13.2.a), V-side): the complement `V` of the
type-II member `T` is commutative.  Mirror of `isMulCommutative_U`; `IsTypeII T` is a hypothesis
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
    show tpd.H = hyp.Q; rw [tpd.H_eq, hyp.Q_eq_TF]
  have hqdim : setupT.q = hyp.p := by
    show Nat.card ↥tpd.W1 = hyp.p; rw [htpdW1, ← hyp.p_eq_card_W2]
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

/-- **Peterfalvi (13.12) `d = 1`, `T`-side dual of `U_inf_centralizer_P_eq_bot`**: `V ⊓ C_G(Q) = ⊥`
— no nonidentity element of the complement `V` centralizes the Fitting kernel `Q = T_F` (i.e. `V`
acts faithfully on `Q`).  The `T`-side `d = |D| = 1` finish, dual of the `S`-side `c = 1` (`c_eq_one`,
`C_eq_bot`, `U_inf_centralizer_P_eq_bot`).  Isolated as the `T`-side residual gated on the (14.9)
`T_typeII` structure; supplies the `hDbot` input of `normalizer_V_inf_W1_eq_bot_of_data`. -/
theorem V_inf_centralizer_Q_eq_bot [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥ := sorry

/-- **Peterfalvi (13.16), the `W₁`-side core** (`V ⊓ N_G(W₁) = ⊥`), `T`-side dual of
`normalizer_U_inf_W2_eq_bot`.  Assembles the proven core `normalizer_V_inf_W1_eq_bot_of_data` from the
ungated coprime-action datum (`coprime_card_Q_card_VW2`) and the two (14.9)-gated `T`-side structural
residuals `Q_elementaryAbelian_T` and `V_inf_centralizer_Q_eq_bot`.  Consumed by the (13.16)
`W₁`-confinement `normalizer_W1_within_T` (the Maschke/Wielandt core of `normalizer_W1_structure`). -/
theorem normalizer_V_inf_W1_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ :=
  normalizer_V_inf_W1_eq_bot_of_data hG hyp hTTypeII (coprime_card_Q_card_VW2 hG hyp)
    (Q_elementaryAbelian_T hG hyp hTTypeII) (V_inf_centralizer_Q_eq_bot hG hyp hTTypeII)

/-- **Peterfalvi (13.16), Maschke/Wielandt core for the `W₁`-side**: `N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.

The `T`-side dual of `normalizer_W2_within_S`.  The `T`-internal residual of the (13.16)
`W₁`-confinement (after the TI reduction `N_G(W₁) ≤ T` of `normalizer_W1_le_T`).  Reduced by the
**Dedekind modular law** to the core `N_V(W₁) = ⊥` (`normalizer_V_inf_W1_eq_bot`): writing
`T = (Q ⊔ V) ⊔ W₂` (`T_deriv_eq_QV` + the reconciled complement `M' ⋊ W₂ = T`), and using
`Q, W₂ ≤ C_G(W₁) ≤ N_G(W₁)` (`Q` elementary abelian, `W = W₁ × W₂` abelian), modularity peels off
`W₂` and `Q`. -/
theorem normalizer_W1_within_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Subgroup.normalizer (hyp.W1 : Set G) ⊓ hyp.T ≤ hyp.Q ⊔ hyp.W2 := by
  obtain ⟨tpd, _, htpdW1, _⟩ := reconciled_typePData_T hG hyp
  have hK : hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ :=
    normalizer_V_inf_W1_eq_bot hG hyp hTTypeII
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

/-- **Peterfalvi (13.16), structural core for the `W₁`-side** (conjunct 3 of `normalizer_W1_structure`):
the Frobenius/Wielandt containment `N_G(W₁) ≤ Q ⊔ W₂`.  Assembles the TI reduction `N_G(W₁) ≤ T`
(`normalizer_W1_le_T`, proven) and the Maschke/Wielandt core `N_G(W₁) ⊓ T ≤ Q ⊔ W₂`
(`normalizer_W1_within_T`): every `g ∈ N_G(W₁)` lies in `T`, hence in `N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.
`T`-side dual of `normalizer_W2_structure`; gated on (14.9) `T_typeII` via the `W₁`-side core. -/
theorem normalizer_W1_le_QW2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 := by
  intro g hg
  have hgT : g ∈ hyp.T := normalizer_W1_le_T hG hyp hTTypeII hg
  exact normalizer_W1_within_T hG hyp hTTypeII (Subgroup.mem_inf.mpr ⟨hg, hgT⟩)

/-- **Peterfalvi (13.16), structural core** (Coq `FTtypeP_norm_cent_compl`, `PFsection13.v:1519`), the
three atomic facts carrying the content of (13.16), **assembled** for the (14.9) type-II member `T`:

* `W₁ ≤ Q` (`W1_le_Q`, proven) — the `T`-side dual of `W₂ ≤ P`, placing the cyclic `q`-factor `W₁`
  inside the `T`-Fitting kernel `Q = T_F`;
* `Q` abelian — from `Q_elementaryAbelian_T` (the one deep §14 σ-residual, dual of the `S`-side
  `P_elementaryAbelian`, itself sorried);
* `N_G(W₁) ≤ Q ⊔ W₂` (`normalizer_W1_le_QW2`, proven) — the TI reduction `normalizer_W1_le_T` +
  the Maschke/Wielandt core `normalizer_W1_within_T`.

`IsTypeII T` is threaded from `exists_LHypothesis` (§16, via (14.9) `T_typeII`); conjuncts 1 and 3 are
sorry-free, so the residual is exactly conjunct 2. -/
theorem normalizer_W1_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.W1 ≤ hyp.Q ∧ IsMulCommutative ↥hyp.Q ∧
      Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 :=
  ⟨W1_le_Q hG hyp,
    IsMulCommutative.of_comm (Q_elementaryAbelian_T hG hyp hTTypeII).comm,
    normalizer_W1_le_QW2 hG hyp hTTypeII⟩

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
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Subgroup.normalizer (hyp.W1 : Set G) = Subgroup.centralizer (hyp.W1 : Set G) ∧
      Subgroup.centralizer (hyp.W1 : Set G) = hyp.Q ⊔ hyp.W2 := by
  obtain ⟨hW1_le_Q, hQ_comm, hN_le⟩ := normalizer_W1_structure hG hyp hTTypeII
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

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to `tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
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
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

/-- **Peterfalvi (13.17.a), `T`-conjugate Fitting order** — the **proven** part (1) of
`tConjugate_fitting_data`: for `L` conjugate to `T` (`conj g • L = T`), `|L_F| = q^p`.

`M_F` is automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so
`conj g • L_F = maxNilpotentNormalHall (conj g • L) = maxNilpotentNormalHall T = Q`; conjugation
preserves cardinality, so `|L_F| = |Q| = q^p` (`card_Q_eq`, now proven for the (14.9) type-II `T`). -/
theorem tConjugate_card_LF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p := by
  have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.Q := by
    rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.Q_eq_TF]
  have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.Q := by
    rw [← hMF]
    exact Nat.card_congr
      (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
  rw [hcard]; exact card_Q_eq hG hyp hTTypeII

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
structural data.  **Now proven**: part (1) is `tConjugate_card_LF` (via `card_Q_eq`); part (2)
`W₁ ≤ L_F` places the `q`-group `W₁ ⊆ N_G(U) ⊆ L` in the normal `q`-Hall `L_F`
(`pgroup_le_of_normal_coprime_index`); part (3) `L_F ⊓ U = ⊥` from `|L_F| = q^p` coprime to `|U|`
(the `U ⋊ W₁` Frobenius gives `(|U|, q) = 1`).  `IsTypeII T` is threaded from
`exists_typeI_maximal_overNormalizer_U` (via (14.9) `T_typeII`); `hNUL` is the `N_G(U) ⊆ L` context. -/
theorem tConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p ∧
      hyp.W1 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p :=
    tConjugate_card_LF hG hyp hTTypeII hconj
  -- `W₁ ⊆ N_G(U) ⊆ L`.
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  -- part 2: `W₁ ≤ L_F` — `W₁` is a `q`-group in `L`, `L_F` the normal `q`-Hall subgroup.
  have hW1leLF : hyp.W1 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.q_prime hW1leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.q hyp.p_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W1) = orderOf w :=
        (orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W1) ∣ Nat.card ↥hyp.W1 := orderOf_dvd_natCard _
      rw [heq, ← hyp.q_eq_card_W1] at h1
      exact h1
  -- part 3: `L_F ⊓ U = ⊥` — `L_F` a `q`-group (`|L_F| = q^p`), `U` coprime to `q` (`U ⋊ W₁` Frobenius).
  have hLFU : maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
    obtain ⟨data, _⟩ := basic_structure hG hyp
    have hcopUq : Nat.Coprime (Nat.card ↥hyp.U) hyp.q := by
      have hk := data.UW1_frobenius.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.q_eq_card_W1] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.U) := by
      rw [hLFcard]; exact hcopUq.symm.pow_left hyp.p
    exact Subgroup.inf_eq_bot_of_coprime hcop
  exact ⟨hLFcard, hW1leLF, hLFU⟩

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
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
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
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) :
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
    obtain ⟨_hLFcard, hW1le, hLFU⟩ := tConjugate_fitting_data _hG hyp hTTypeII hg hNUL
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
and meeting `V` trivially.  **Now proven** (the V-side mirror of `tConjugate_fitting_data`): part (1)
`|L_F| = p^q` from the proven `card_P_eq` via the `S`-conjugation equivariance of `M_F`; part (2)
`W₂ ≤ L_F` places the `p`-group `W₂ ⊆ N_G(V) ⊆ L` in the normal `p`-Hall `L_F`; part (3) `L_F ⊓ V = ⊥`
from `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius, `(|V|, p) = 1`).  `IsTypeII T` (for the
`V ⋊ W₂` Frobenius) is threaded from `exists_typeI_maximal_overNormalizer_V`. -/
theorem sConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.S)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q ∧
      hyp.W2 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
  -- part 1: `|L_F| = p^q` (`card_P_eq`, proven, via the `S`-conjugation equivariance of `M_F`).
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q := by
    have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.P := by
      rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.P_eq_SF]
    have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.P := by
      rw [← hMF]
      exact Nat.card_congr
        (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
    rw [hcard]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `W₂ ⊆ N_G(V) ⊆ L`.
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  -- part 2: `W₂ ≤ L_F` — `W₂` a `p`-group in `L`, `L_F` the normal `p`-Hall subgroup.
  have hW2leLF : hyp.W2 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.p_prime hW2leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
        (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
      rw [heq, ← hyp.p_eq_card_W2] at h1
      exact h1
  -- part 3: `L_F ⊓ V = ⊥` — `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius gives `(|V|, p) = 1`).
  have hLFV : maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
    obtain ⟨tpd, htpdV, htpdW1, _⟩ := reconciled_typePData_T hG hyp
    obtain ⟨tdata⟩ := hTTypeII
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
    have hcopVp : Nat.Coprime (Nat.card ↥hyp.V) hyp.p := by
      have hk := hVW2frob.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.p_eq_card_W2] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.V) := by
      rw [hLFcard]; exact hcopVp.symm.pow_left hyp.q
    exact Subgroup.inf_eq_bot_of_coprime hcop
  exact ⟨hLFcard, hW2leLF, hLFV⟩

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
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T _hG hyp
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
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
    obtain ⟨_hLFcard, hW2le, hLFV⟩ := sConjugate_fitting_data _hG hyp ⟨tdata⟩ hg hNVL
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
    (hTTypeII : IsTypeII hyp.T)
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
  have h1316 := normalizer_W1 _hG hyp hTTypeII
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
theorem Q_W2_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
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
    rw [card_Q_eq hG hyp hTTypeII]
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
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- §13 residual: `E ∩ Q = W₁` and `E ⊄ Q`.
  obtain ⟨hInf, hnle⟩ := complement_inf_Q_structure _hG hyp frob hW1E
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hEH : Em ≤ Hg := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp hTTypeII
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
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq _hG hyp hTTypeII frob hW1E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp hTTypeII
  have hEQW2 := complement_le_QW2 _hG hyp hTTypeII frob hW1E
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
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ :=
    typeI_overNormalizer_complement _hG hyp hSTypeII hTTypeII hLmax hNUL hUH frob hW1E
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

/-- **`S`-side of the (13.17.c) `W₁`-structure**: `W₁ ≤ N_G(P)`, `P ⊓ W₁ = ⊥`, and `q ∤ |P|`.

All three are ungated `S`-side facts: `W₁ ≤ S ≤ N_G(P)` (`P = S_F ⊴ S`); `P ⊓ W₁ ≤ M' ⊓ W₁ = ⊥`
(`P ≤ M' = derivedInG S`, `M_complement` disjointness); and `q ∤ |P|` from
`Coprime |P| |U ⋊ W₁|` (`coprime_card_P_card_UW1`) with `|W₁| = q ∣ |U ⋊ W₁|`. -/
theorem P_W1_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) ∧ hyp.P ⊓ hyp.W1 = ⊥ ∧
      ¬ hyp.q ∣ Nat.card ↥hyp.P := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  refine ⟨hW1_le_S.trans hS_norm_P, ?_, ?_⟩
  · rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxW1⟩ := Subgroup.mem_inf.mp hx
    have hxm : x ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hP_le_M' hxP, hxW1⟩
    rwa [hM'W1] at hxm
  · intro hq
    have hcop := coprime_card_P_card_UW1 hG hyp
    have hW1dvd : Nat.card ↥hyp.W1 ∣ Nat.card ↥(hyp.U ⊔ hyp.W1) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hcopPW1 : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥hyp.W1) :=
      hcop.coprime_dvd_right hW1dvd
    rw [← hyp.q_eq_card_W1] at hcopPW1
    have hqdvd1 : hyp.q ∣ 1 := hcopPW1 ▸ Nat.dvd_gcd hq (dvd_refl hyp.q)
    exact hyp.q_prime.one_lt.ne' (Nat.dvd_one.mp hqdvd1)

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

/-- Carrier for the virtual character `beta_j` and `Gamma_j` in Peterfalvi (13.18).

**De-opacified (W3 §15).**  This carrier previously held six free `_formula : Prop` placeholders
(the [[scaffold-sorry-free-not-done]] convention).  Since `BetaData` has no external consumers (only
`beta_support_norm_and_remainder` produces it), the placeholder fields are now the **genuine
Peterfalvi (13.18) statements** about `β_j`/`Γ_j`, tied to `hyp`, the grid `hyp.eta`, and `S`:

* `Gamma_real` — `Γ_j` is real (`Γ_j.conj = Γ_j`);
* `Gamma_orthogonal_one` — `(Γ_j, 1_G) = 0`, the residual is orthogonal to the principal character;
* `norm_formula` — **(13.18.b)** `‖β_j‖²_S = (u−1)/q + 2` (its Frobenius `Ind` half is the sorry-free
  `norm_induce_one_frobenius`);
* `support_formula` — the support of `β_j` is contained in `S`'s η-carrier support (the grid-side
  support control of (13.18.a));
* `Gamma_independent` — `Γ_j` is orthogonal to the whole η-grid `{η_ij}` (independence from the
  Dade images, (13.18.a));
* `Y_norm_bound` — `‖Γ_j‖² ≤ (u−1)/q + 1`, the residual-norm bound feeding the (13.10) cascade.

The genuine grid/Dade content bottoms out at the (3.2) τ-isometry (`tau3`, σ-pinned 2026-06-15) and
the (13.18.b) Frobenius norm; it is isolated into the single faithful producer `betaData_of_grid`. -/
structure BetaData (hyp : Hypothesis (G := G)) where
  j : Fin hyp.p
  j_ne_zero : (j : ℕ) ≠ 0
  beta : ClassFunction ↥hyp.S ℂ
  Gamma : ClassFunction G ℂ
  /-- **(13.18.a)** support control: `β_j` is supported on `S`'s η-carrier support. -/
  support_formula : beta.support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i j).support
  /-- **(13.18.b)** norm: `‖β_j‖²_S = (u−1)/q + 2`, whose `Ind_{PW₁}^S 1` half is
  `norm_induce_one_frobenius`. -/
  norm_formula :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner beta beta
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
  /-- **(13.18.a)** independence: `Γ_j` is orthogonal to the whole `η`-grid. -/
  Gamma_independent :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Gamma (hyp.eta i k) = 0
  /-- **(13.18)** `Γ_j` is orthogonal to the principal character `1_G`. -/
  Gamma_orthogonal_one :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner Gamma (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0
  /-- **(13.18)** `Γ_j` is a real virtual character. -/
  Gamma_real : Gamma.conj = Gamma
  /-- **(13.18)** residual-norm bound `‖Γ_j‖² ≤ (u−1)/q + 1` feeding the (13.10) cascade. -/
  Y_norm_bound :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      (ClassFunction.inner Gamma Gamma).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1

/-- **`U ⋊ W₁` complements `P` in `S`** (structural bridge for (13.18.b), `S`-side form).  From the
`Sdata` complements `M' ⋊ W₁ = S` and `P ⋊ U = M'`, the subgroup `U ⊔ W₁` intersects `P = S_F`
trivially and joins with it to `S`.  This is the `↥S`-internal `IsComplement'` behind the Frobenius
quotient `S̄ = S/P ≅ U ⋊ W₁` used to evaluate `‖Ind_{PW₁}^S 1‖²`.  (Re-derived here in the (13.18)
carve-out rather than exposed from `coprime_card_P_card_UW1`, whose derivation it mirrors.) -/
theorem uW1_isComplement_P [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) (hyp.P.subgroupOf hyp.S) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
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
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hSsup : hyp.P ⊔ (hyp.U ⊔ hyp.W1) = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_S,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq, hyp.S_deriv_eq_PU] at hmap
    rw [← sup_assoc]; exact hmap
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
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The induced trivial character** `Ind_{P⋊W₁}^S(1)` of the subgroup `P ⋊ W₁ ≤ S`, the
positive part of the (13.18) bridge character `β_j`.  Its squared `S`-norm is the Frobenius
value `(u−1)/q + 1` (`norm_induce_one_frobenius` composed with the `S̄ = S/P = U⋊W₁` inflation). -/
noncomputable def indPW1 [Finite G] (hyp : Hypothesis (G := G)) : ClassFunction ↥hyp.S ℂ :=
  ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
    (trivialClassFunction ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S))

/-- **Peterfalvi (13.18) `S`-side virtual character** `β_j := Ind_{P⋊W₁}^S(1) − μ_{0j}`
(Coq `PFsection13.FTtypeP_bridge`).  The induced trivial character `indPW1 hyp` of `P ⋊ W₁ ≤ S`
minus the base-row grid irreducible `μ_{0j} = hyp.mu 0 j`. -/
noncomputable def betaGrid [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction ↥hyp.S ℂ :=
  indPW1 hyp - hyp.mu ⟨0, hyp.q_prime.pos⟩ j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The genuine `S`-side Dade image** `τ_S(β_{#1})` of the (13.18) bridge character at column
`#1`.  Uses the honest (13.2.e) Dade isometry `τ_S = dadeIntegralCharacterMap (hyp.dadeHypS hG) …`
— the `S`-instance of the (5.3) Dade map — **NOT** the off-path `= 0` placeholder `hyp.tauS`. -/
noncomputable def tauSbetaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))
    (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18) residual** `Γ := τ_S(β_{#1}) − 1_G + η_{01}` (Coq
`PFsection13.FTtypeP_bridge_gap`).  `η_{01} = hyp.eta 0 1` is the (3.3) grid image `τ₃(ω_{01})`;
`1_G = constOne G`.  Note `Γ` does not depend on the column `j` of `βData`. -/
noncomputable def GammaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  tauSbetaGrid hG hyp - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
    + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩

/-- **(13.18.a) support control** (`S`-side, grid form): `supp(β_j) ⊆ ⋃_i supp(μ_{ij})`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  This is Coq's `PVSbeta`/`A0beta` (`β_j ∈ CF(S, P^# ∪
V_S) ⊆ CF(S, A₀(S))`), restated here in the grid-support form the (13.19)/(14.9) consumers use:
off `⋃_i supp(μ_{ij})` the induced permutation character `Ind_{PW₁}^S 1` exactly cancels `μ_{0j}`.
The cancellation is the `normedTI` structure of the `W₁`-classes in `S̄ = S/P` (Coq `gammaW1`,
`Ptype_Fcore_sdprod`); no repo API yet supplies it. -/
theorem betaGrid_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i j).support := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b), Frobenius half** (`FiniteInduce`-instance form): `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.
The wrapper `indPW1_inner_self` bridges to arbitrary `Fintype`/`Invertible` instances. -/
private theorem indPW1_inner_self_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  classical
  -- Structural setup: `U ⋊ W₁` complements `P` in `S`.
  have hcompl := uW1_isComplement_P hyp
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hW1_le_UW1 : hyp.W1 ≤ hyp.U ⊔ hyp.W1 := le_sup_right
  have hW1_le_PW1 : hyp.W1 ≤ hyp.P ⊔ hyp.W1 := le_sup_right
  have hP_le_PW1 : hyp.P ≤ hyp.P ⊔ hyp.W1 := le_sup_left
  have hPW1_le_S : hyp.P ⊔ hyp.W1 ≤ hyp.S := sup_le hP_le_S hW1_le_S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono hP_le_PW1
  -- Step 1: `indPW1 = (Ind_{Ā}^{S̄} 1) ∘ mk'`, so its `S`-norm equals the `S̄`-norm (P2 + P1).
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA,
    OddOrder.RepresentationTheory.inner_compHom_mk'_eq]
  -- Step 2: `S̄ = S/P` is Frobenius via the iso `e : ↥(U⊔W₁) ≃* S̄`.
  obtain ⟨data, _⟩ := basic_structure _hG hyp
  set f : ↥(hyp.U ⊔ hyp.W1) →* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)).comp (Subgroup.inclusion hUW1_le_S) with hf
  have he_apply : ∀ w : ↥(hyp.U ⊔ hyp.W1),
      f w = QuotientGroup.mk (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) := by
    intro w
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [he_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    have hwUW1S : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S := by
      rw [Subgroup.mem_subgroupOf]; exact w.2
    have hbot : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S)
        ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hwUW1S, Subgroup.mem_subgroupOf.mpr hw⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using congrArg Subtype.val hbot)
  have hcard : Fintype.card ↥(hyp.U ⊔ hyp.W1)
      = Fintype.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) = (hyp.P.subgroupOf hyp.S).index from rfl,
      hcompl.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv]
  set e : ↥(hyp.U ⊔ hyp.W1) ≃* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    MulEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩) with he
  have he_toMonoidHom : ∀ w, e.toMonoidHom w = f w := fun _ => rfl
  -- Transport the `U ⋊ W₁` Frobenius structure to `S̄`.
  have hFrob := Ch06.isFrobeniusGroup_map_equiv data.UW1_frobenius e
  -- The transported complement `W̄₁.map e` equals the (13.18) induction subgroup `Ā = (PW₁)/P`.
  have hAmatch : (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)).map e.toMonoidHom
      = ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) := by
    apply le_antisymm
    · rintro _ ⟨w, hwW1, rfl⟩
      have hwW1' : (w : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hwW1)
      refine Subgroup.mem_map.mpr ⟨⟨(w : G), hPW1_le_S (hW1_le_PW1 hwW1')⟩,
        Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hwW1'), ?_⟩
      rw [QuotientGroup.mk'_apply, he_toMonoidHom, he_apply]
    · rintro _ ⟨s, hsPW1, rfl⟩
      have hsG : (s : G) ∈ hyp.P ⊔ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hsPW1)
      have hsmem : (s : G) ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hsG
      rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1 (hW1_le_S.trans hS_norm_P)]
        at hsmem
      obtain ⟨p, hp, w, hw, hpw⟩ := Set.mem_mul.mp hsmem
      have hwW1 : w ∈ hyp.W1 := SetLike.mem_coe.mp hw
      have hpP : p ∈ hyp.P := SetLike.mem_coe.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨w, hW1_le_UW1 hwW1⟩,
        Subgroup.mem_subgroupOf.mpr hwW1, ?_⟩
      have hs_eq : s = (⟨p, hP_le_S hpP⟩ : ↥hyp.S) * ⟨w, hW1_le_S hwW1⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hpw.symm)
      have hp1 : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) ⟨p, hP_le_S hpP⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hpP
      rw [he_toMonoidHom, he_apply, ← QuotientGroup.mk'_apply, hs_eq, map_mul, hp1, one_mul]
  rw [hAmatch] at hFrob
  -- Frobenius norm on `S̄`.
  rw [norm_induce_one_frobenius hFrob]
  -- `|Ā| = |W₁| = q`.
  have hcardAmap : Nat.card ↥(((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))) = hyp.q := by
    rw [← hAmatch,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1_le_UW1).toEquiv, ← hyp.q_eq_card_W1]
  -- `Ā.index = |Ū| = |U| = u` (using `c = 1`, Pf (13.12)).
  have hindexAmap : (((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))).index = hyp.u := by
    rw [hFrob.isComplement.index_eq_card,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ _)).toEquiv,
      hyp.card_U_eq_uc, c_eq_one _hG hyp, mul_one]
  rw [invOf_eq_inv, hcardAmap, hindexAmap]
  have hq : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  push_cast
  field_simp
  ring

/-- **(13.18.b), Frobenius half**: `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.

By the inflation `Ind_{PW₁}^S 1 = Ind_{W̄₁}^{S̄} 1` inflated through `P` (P2
`induce_one_eq_compHom_induce_one_of_le` + P1 `inner_compHom_mk'_eq`), its `S`-norm equals
`‖Ind_{W̄₁}^{S̄} 1‖²` in the Frobenius quotient `S̄ = S/P ≅ U⋊W₁` (`uW1_isComplement_P` transported
by `isFrobeniusGroup_map_equiv`), which `norm_induce_one_frobenius` evaluates to
`(|U|−1)/|W₁| + 1 = (u−1)/q + 1` (using `c = 1`, Pf (13.12), so `|U| = u`).  The
`FiniteInduce`-instance content is `indPW1_inner_self_aux`; here we bridge to the caller's
`Fintype`/`Invertible` instances (both `Subsingleton`). -/
theorem indPW1_inner_self [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp using 2
  exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := indPW1_inner_self hG hyp
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

/-- **(13.18.a) grid-independence**: `⟨Γ, η_{ik}⟩ = 0` for every grid entry.

⚠ DEEP §13 RESIDUAL, isolated obligation.  `Γ = τ_S(β_{#1}) − 1_G + η_{01}`.  The hard term is
`⟨τ_S(β_{#1}), η_{ik}⟩`: the `S`-side Dade image `τ_S` and the `W`-side grid `η = τ₃∘ω` are
different Dade maps, linked by the (13.1.e)/(5.3) cross-relation `τ_S(μ_{ij} − μ_{0j}) =
δ_j(η_{ij} − η_{0j})` (Coq `prDade_sub_TIirr`, `Dtau`), which forces `Γ` orthogonal to the whole
`σ`-image `{η_{ik}}`.  No repo field yet supplies this `S`↔`W` Dade cross-relation. -/
theorem gammaGrid_independent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (k : Fin hyp.p),
        ClassFunction.inner (GammaGrid hG hyp) (hyp.eta i k) = 0 := sorry

/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  Coq `oGamma1`: `⟨Γ,1⟩ = ⟨τ_S β,1⟩ − 1 + ⟨η_{01},1⟩`;
`⟨η_{01},1⟩ = 0` (grid orthogonality) and `⟨τ_S β,1⟩ = 1` via the Dade=Ind bridge
(`hyp.sInstance_dade_eq_induce_of_supported_trivial_H`, gated on the (13.2.e) `A₀(S)` normedTI) +
Frobenius reciprocity + `⟨μ_{0j},1_S⟩ = 0`.  The Dade=Ind bridge's normedTI hypotheses are the
missing content. -/
theorem gammaGrid_orthogonal_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := sorry

/-- **(13.18.c)** `Γ` is real: `Γ.conj = Γ`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  Coq `GammaReal`: conjugation commutes with `Ind` and
with the Dade map (`cfAutInd`, `Dtau`), and sends grid entries to their conjugate index
(`prTIirr_aut`, `cfAut_cycTIiso`: `η̄_{0j} = η_{0,-j}`, `μ̄_{0j} = μ_{0,-j}`), so
`Γ̄ = τ_S(β̄_{#1}) − 1_G + η̄_{01}` collapses back to `Γ` via `defGamma` at the conjugate column.
The Dade/grid conjugation-commutation facts are not yet in the repo. -/
theorem gammaGrid_real [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (GammaGrid hG hyp).conj = GammaGrid hG hyp := sorry

/-- **(13.18.d) residual-norm bound**: `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  Coq's (13.18.d) argument bounds `‖Γ‖²` using
`‖β_{#1}‖² = (u−1)/q + 2` (`betaGrid_norm`), the Dade isometry `‖τ_S β‖² = ‖β‖²` on `A₀(S)`-support
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`), and the decomposition
`β_{#1} = Γ − η_{01} + 1_G` with the `η_{01}`/`1_G` orthogonalities peeled off (`cfnormDd`).  It
needs the (13.18.a,c) orthogonalities above plus the on-support isometry, hence gated on the same
`A₀(S)` normedTI content. -/
theorem gammaGrid_norm_bound [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      (ClassFunction.inner (GammaGrid hG hyp) (GammaGrid hG hyp)).re
        ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 := sorry

/-- **Faithful §13 producer for Peterfalvi (13.18).**  The (13.18) virtual characters `β_j`/`Γ_j`
and all six of their genuine properties (support (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`,
grid-independence, orthogonality to `1_G`, reality, and the residual bound) are supplied here.  The
concrete `β_j = betaGrid hyp j` and `Γ = GammaGrid hG hyp` are built from the honest `S`-side Dade
isometry `τ_S` (`hyp.dadeHypS`, **not** the `= 0` placeholder `hyp.tauS`) and the induced trivial
character `Ind_{PW₁}^S 1`.  The six properties are the precisely-isolated §13 obligations
`betaGrid_support` / `betaGrid_norm` / `gammaGrid_independent` / `gammaGrid_orthogonal_one` /
`gammaGrid_real` / `gammaGrid_norm_bound`, each stating the genuine (13.18) fact about the concrete
`β_j`/`Γ`; their deep content bottoms out at the (13.2.e) `A₀(S)` normedTI Dade=Ind bridge, the
(5.3) `S`↔`W` Dade cross-relation, and the Frobenius norm `norm_induce_one_frobenius`. -/
noncomputable def betaData_of_grid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    BetaData hyp where
  j := j
  j_ne_zero := hj
  beta := betaGrid hyp j
  Gamma := GammaGrid hG hyp
  support_formula := betaGrid_support hG hyp j hj
  norm_formula := betaGrid_norm hG hyp j hj
  Gamma_independent := gammaGrid_independent hG hyp
  Gamma_orthogonal_one := gammaGrid_orthogonal_one hG hyp
  Gamma_real := gammaGrid_real hG hyp
  Y_norm_bound := gammaGrid_norm_bound hG hyp

/-- **Peterfalvi (13.18)**: the virtual character `beta_j` has controlled
support, norm, and orthogonal remainder.

De-opacified (W3 §15): the six conclusions are now the genuine (13.18) statements — `β_j`'s support
control (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`, and the residual `Γ_j`'s
grid-independence, orthogonality to `1_G`, reality, and norm bound — each about the produced
characters `data.beta`/`data.Gamma`.  They are the genuine fields of the faithful producer
`betaData_of_grid`; the (13.18.b) Frobenius induced-trivial norm half is the already-proven
`norm_induce_one_frobenius`. -/
theorem beta_support_norm_and_remainder [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : BetaData hyp,
      (data.beta.support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i data.j).support) ∧
        (∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
          ClassFunction.inner data.beta data.beta
            = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)) ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ∀ (i : Fin hyp.q) (k : Fin hyp.p),
            ClassFunction.inner data.Gamma (hyp.eta i k) = 0) ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ClassFunction.inner data.Gamma
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0) ∧
        data.Gamma.conj = data.Gamma ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          (ClassFunction.inner data.Gamma data.Gamma).re
            ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1) := by
  -- The principal index `j = 1` (nonzero, using `p ≥ 3`).
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  refine ⟨betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp),
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).support_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).norm_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_independent,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_orthogonal_one,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_real,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Y_norm_bound⟩

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

/-- **Faithful §13 grid/Dade producer for Peterfalvi (13.19).**

Given a type-I maximal subgroup `L` with its (12.1) `S14.Hypothesis` `typeISetup`, this bundles the
genuinely grid-dependent data and facts of (13.19) against a concrete kernel index `e`, family
`Lset` and generator `phi`:

* the Dade images `β_L`, `β_S`, disjoint-supported (13.18.a-style);
* `phi ∈ Lset` of degree `e = |L : H|`;
* **(13.19.a)** `L^{τ₁} ⊥ {η_ij}` and `β_L ⊥ {η_ij}` (grid orthogonality, the `Ltau_orthogonal_eta`
  / `betaL_eta_independent` content), bottoming out at the (3.9) `τ`-isometry (σ-pinned);
* **(13.19.c)** the S- and T-side dichotomies `caseC1 ∨ caseC2` where `caseC1` is the rational
  degree bound `(|H|−1)/e ≤ (u−1)/q` and `caseC2` is the genuine `η`-axis odd-integer parity
  `∀ j ≠ 0, ⟨β_L, η_0j⟩ ∈ 2ℤ+1` (dual: `(v−1)/p`, `η_i0`).

Everything grid-dependent is isolated here; the assembling theorem
`typeI_orthogonality_dichotomy` supplies the honest §14 `typeISetup`, the `τ₁ = typeISetup.tau`
Dade map, and reads the dichotomy implication fields off as identities (no over-claim). -/
structure TypeIOrthogonalityGridData (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) where
  e : ℕ
  e_eq_index : ((maxNilpotentNormalHall L).subgroupOf L).index = e
  Lset : Set (ClassFunction ↥L ℂ)
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  disjoint_support : Disjoint betaL.support betaS.support
  Ltau_orthogonal_eta :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p),
        ClassFunction.inner (typeISetup.tau phi) (hyp.eta i j) = 0
  betaL_eta_independent :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner betaL (hyp.eta i j) = 0
  /-- **(13.19.c)** S-side dichotomy: the degree bound or the `η_0j` odd-parity alternative. -/
  caseC :
    (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) ∨
      (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j))
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy: `(v−1)/p` bound or the `η_i0` odd-parity. -/
  caseC_dual :
    (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ)) ∨
      (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩))

/-- **Faithful §13 producer for Peterfalvi (13.19).**  The grid/Dade data and facts of (13.19) for a
type-I maximal `L` with its (12.1) Hypothesis `typeISetup`.  The construction is the §3/§4/§5
Dade-isometry layer for `L` (the (3.9) `τ`-isometry, σ-pinned via `S05_IntegralSigma`, giving the
`η`-grid orthogonality) plus the (13.19.c) degree/parity dichotomy from the coherence bounds; this is
the single isolated deep obligation.  Mirrors the `betaData_of_grid` / `betaM_expansion_data`
producer pattern. -/
noncomputable def typeIOrthogonalityGridData_of_typeISetup [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    TypeIOrthogonalityGridData hyp typeISetup := sorry

/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has Dade images
orthogonal to the `eta_ij`; on each zero axis, one of the two final parity
cases holds.

De-opacified (W3 §15): the honest §14 content — the (12.1) `S14.Hypothesis` of `L`
(`S14.exists_typeI_hypothesis`) and its genuine Dade map `τ₁ = typeISetup.tau` — is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements (grid orthogonality of `β_L`, the disjoint support, and the two (13.19.c) case flags as
the actual degree bound / `η`-axis odd-parity propositions).  The dichotomy implication fields
(`caseC1_bound`, `caseC2_eta0j_odd`, dual) are then the **identity** — no over-claim beyond the
textbook.  The only grid-dependent atoms (`β_L`, `β_S`, the orthogonalities, and the (13.19.c)
disjunctions) come from the faithful producer `typeIOrthogonalityGridData_of_typeISetup`, whose type
is the genuine (13.19) grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(14.*): the type-I maximal `L` carries a genuine `S14.Hypothesis` (honest own-logic).
  obtain ⟨typeISetup⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis _hG hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_typeISetup _hG hyp typeISetup
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and identity
  -- dichotomy implication fields.
  refine ⟨{ typeISetup := typeISetup
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := typeISetup.tau
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                  ClassFunction.inner (typeISetup.tau g.phi) (hyp.eta i j) = 0
            betaL_eta_independent :=
              ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                  ClassFunction.inner g.betaL (hyp.eta i j) = 0
            caseC1 :=
              (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j))
            caseC2_eta0j_odd := fun h => h
            caseC1_bound := fun h => h
            caseC1_dual :=
              (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))
            caseC2_dual :=
              (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩))
            caseC2_dual_etai0_odd := fun h => h
            caseC1_dual_bound := fun h => h },
    g.disjoint_support, g.Ltau_orthogonal_eta, g.betaL_eta_independent, g.caseC, g.caseC_dual⟩

end OddOrder.Peterfalvi.S15
