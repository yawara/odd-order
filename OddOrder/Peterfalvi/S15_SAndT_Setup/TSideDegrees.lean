/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup.CountingLayer
import OddOrder.Peterfalvi.S15_SAndT_Setup.HypothesisSwap

/-! # T-side degree arithmetic for Peterfalvi (13.3.c) (pp. 76-77)

The `T`-side mirrors of the `S`-side (13.3) degree/counting layer, toward the `δ'`-half of
(13.3.c) (`δ'_i = 1`): the order `|K| = |Q|·d` and the index `[T : K] = v·p` (mirrors of
`card_H_eq` / `H_index_eq_uq`, on top of the existing `card_T_eq_deriv_mul_p` /
`card_deriv_T_eq` — note the Fitting order `|Q|` *cancels*, so none of these needs the
(14.9)-gated `|Q| = q^p`); the Frobenius congruence
`v ≡ 1 (mod p)` (mirror of `u_modEq_one`, Peterfalvi's "As `(V/D)W₂` is a Frobenius group,
`v ≡ 1 (mod p)`", via the reconciled type-`P` datum of `T`); the `ν`-row degree constancy
(mirror of `mu_apply_one_column_const`); and the assembled sign theorem
`deltaPrime_eq_one_of_ne_zero_T` (mirror of `delta_eq_one_of_ne_zero`), parametric in the
ν-grid supply `pins : NuGridSupplyData`.

The single non-mirrored obligation is the (13.3.a)-at-`T` per-entry degree
`nu_apply_one_eq_v` (`ν_{ij}(1) = v` for `i ≠ 0`) — see its docstring for the precise gate
(the §9-on-`T` chief-kernel triviality needs `|Q| = q^p`, which at the abstract §13 level is
(13.2.a)-at-`T` content unavailable without the (14.9) `IsTypeII T`).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- `K = QD ≤ T`: `Q = T_F ≤ T` and `D = V ∩ C_G(Q) ≤ V ≤ T' ≤ T`.  Mirror of `H_le_S`. -/
theorem Hypothesis.K_le_T [Finite G] (hyp : Hypothesis (G := G)) : hyp.K ≤ hyp.T := by
  have hVT : hyp.V ≤ hyp.T := by
    have h1 : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  exact sup_le hQT (le_trans (hyp.D_eq ▸ inf_le_left) hVT)

/-- **`|K| = |Q|·d`** (Peterfalvi (13.2), `T`-side): `K = QD` with `Q ⊓ D = ⊥` (`D ≤ V` and
`Q ⊓ V = ⊥`) and `Q ◁ K`.  Mirror of `card_H_eq` — but *without* evaluating `|Q|`
(the `S`-side's `|P| = p^q` needs the carried `S_typeP2`; the `T`-analogue is (14.9)-gated,
and the downstream index `[T:K] = v·p` cancels `|Q|` anyway). -/
theorem Hypothesis.card_K_val [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.K = Nat.card ↥hyp.Q * hyp.d := by
  haveI := hyp.finiteG
  have hQK : hyp.Q ≤ hyp.K := le_sup_left
  have hDK : hyp.D ≤ hyp.K := le_sup_right
  have hK_le_T : hyp.K ≤ hyp.T := hyp.K_le_T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer hyp.Q := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn : (hyp.Q.subgroupOf hyp.K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr (hK_le_T.trans hT_le_NQ)
  have hinf : hyp.Q.subgroupOf hyp.K ⊓ hyp.D.subgroupOf hyp.K = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxD⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) :=
      ⟨hxQ, (hyp.D_eq ▸ inf_le_left : hyp.D ≤ hyp.V) hxD⟩
    rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
  have hsup : hyp.Q.subgroupOf hyp.K ⊔ hyp.D.subgroupOf hyp.K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQK hDK]
    exact Subgroup.subgroupOf_self hyp.K
  have hcompl : Subgroup.IsComplement' (hyp.Q.subgroupOf hyp.K) (hyp.D.subgroupOf hyp.K) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, ← hyp.d_eq_card_D] at hmul
  exact hmul.symm

/-- **`[T : K] = v·p`** (Peterfalvi (13.2), `T`-side): the index of `K = QD` in `T`.  From
`|T| = |Q|·(v·d)·p` (`card_T_eq_deriv_mul_p` + `card_deriv_T_eq` + `card_V_eq_vd`) and
`|K| = |Q|·d` (`card_K_val`) — the Fitting order `|Q|` cancels.  Mirror of `H_index_eq_uq`;
the degree index of the (13.3.a)-at-`T` `ν_i = Ind_{QD}^T (linear)`. -/
theorem Hypothesis.K_index_eq_vp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.K.subgroupOf hyp.T).index = hyp.v * hyp.p := by
  have hm := Subgroup.card_mul_index (hyp.K.subgroupOf hyp.T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.K_le_T).toEquiv, hyp.card_K_val,
    hyp.card_T_eq_deriv_mul_p hG, hyp.card_deriv_T_eq hG] at hm
  have hpos : (0 : ℕ) < Nat.card ↥hyp.Q * hyp.d :=
    Nat.mul_pos Nat.card_pos (hyp.d_eq_card_D ▸ Nat.card_pos)
  have hmm : Nat.card ↥hyp.Q * hyp.d * (hyp.K.subgroupOf hyp.T).index
      = Nat.card ↥hyp.Q * hyp.d * (hyp.v * hyp.p) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

/-- **`v·d = |V| ≠ 1`**: `T` is type non-I; a type-II/III/IV witness has a nontrivial
complement whose order is `|V|` (witness-independence `card_U_eq_index`), and type V is
excluded unconditionally by Peterfalvi Theorem (10.10) (`no_typeV_maximal_unconditional`).
This discharges the `hvd` nontriviality input of `toTypesIIIIIIVSetupT` with no extra
hypothesis. -/
theorem Hypothesis.vd_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.v * hyp.d ≠ 1 := by
  intro h1
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  rcases hyp.T_nonI with h | h | h | h
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · exact OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
      ⟨hyp.T, hyp.T_maximal, h⟩

/-- **Peterfalvi `v ≡ 1 (mod p)`** (the (13.3.c) `δ'`-crux): the `T`-side `V W₂` is a
Frobenius group (`typeP_uW1_frobenius` on the reconciled type-`P` datum of `T`), so for the
conjugation homomorphism `φ : V W₂ →* Aut(Q)` the kernel-image `φ(V) = V/C_V(Q) = V̄`
satisfies `|V̄| ≡ 1 (mod |W₂|)` (`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`,
Isaacs Lemma 6.1); with `|V| = v·d` (`card_V_eq_vd`, `D = V ⊓ C_G(Q)`) and `|W₂| = p` this
is `v ≡ 1 (mod p)`.  Mirror of `u_modEq_one`; crucially **ungated** — uses only the
reconciled `V W₂` Frobenius structure, with nontriviality from `vd_ne_one`. -/
theorem Hypothesis.v_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.v ≡ 1 [MOD hyp.p] := by
  haveI := hyp.finiteG
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    apply hyp.vd_ne_one hG
    rw [← hyp.card_V_eq_vd, ← hU, hbot, Subgroup.card_bot]
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hUne
  have hUW1leT : tpd.U ⊔ tpd.W1 ≤ hyp.T :=
    sup_le (tpd.U_le.trans (Subgroup.map_subtype_le _)) tpd.W1_le
  have hTnormQ : hyp.T ≤ Subgroup.normalizer hyp.Q := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hUW1normQ : tpd.U ⊔ tpd.W1 ≤ Subgroup.normalizer hyp.Q :=
    le_trans hUW1leT hTnormQ
  letI : MulDistribMulAction ↥(tpd.U ⊔ tpd.W1) ↥hyp.Q :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.Q)) ↥hyp.Q
      (Subgroup.inclusion hUW1normQ)
  set φ : ↥(tpd.U ⊔ tpd.W1) →* MulAut ↥hyp.Q :=
    MulDistribMulAction.toMulAut ↥(tpd.U ⊔ tpd.W1) ↥hyp.Q with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(tpd.W1.subgroupOf (tpd.U ⊔ tpd.W1)) = hyp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      tpd.W1 ≤ tpd.U ⊔ tpd.W1)).toEquiv, hW1, ← hyp.p_eq_card_W2]
  have hφapply : ∀ (a : ↥(tpd.U ⊔ tpd.W1)) (x : ↥hyp.Q),
      ((φ a x : ↥hyp.Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ := fun a x => rfl
  have hker_iff : ∀ a : ↥(tpd.U ⊔ tpd.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.Q : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 x hx
      have hcg := congrArg (fun e : MulAut ↥hyp.Q => ((e ⟨x, hx⟩ : ↥hyp.Q) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext x
      simp only [hφapply, MulAut.one_apply]
      have hxc := hc (x : G) x.2
      rw [← hxc]; group
  set N := tpd.U.subgroupOf (tpd.U ⊔ tpd.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.Q := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (tpd.U ⊔ tpd.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (tpd.U ⊔ tpd.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.D := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.Q : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ tpd.U := Subgroup.mem_subgroupOf.mp n.2
      have hgV : (ρ n : G) ∈ hyp.V := by rw [← hU]; exact hgU
      rw [hyp.D_eq]
      exact ⟨hgV, hgC⟩
    · intro hgD
      rw [hyp.D_eq, Subgroup.mem_inf] at hgD
      obtain ⟨hgV, hgc⟩ := hgD
      have hgUd : g ∈ tpd.U := by rw [hU]; exact hgV
      have hgUW1 : g ∈ tpd.U ⊔ tpd.W1 := (le_sup_left : tpd.U ≤ _) hgUd
      have hgN : (⟨g, hgUW1⟩ : ↥(tpd.U ⊔ tpd.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUd
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.d := by
    rw [hyp.d_eq_card_D, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.v * hyp.d := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      tpd.U ≤ tpd.U ⊔ tpd.W1)).toEquiv, hU, hyp.card_V_eq_vd]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.v := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hd0 : 0 < hyp.d := hyp.d_eq_card_D ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hd0 hsplit).symm
  have hrv : Nat.card ↥((φ.comp N.subtype).range) = hyp.v := hrangecard
  rw [hrv, hAcard] at hmod
  exact hmod

open scoped FiniteInduce in
/-- **Row-constant degree** (Peterfalvi (13.1.e)/(4.3.c), `T`-side): within a row `i`, all
`ν_{ij}(1)` are equal.  From `nu_definition` at `1`: the LHS `Ind_W^T(ω_{ij} − ω_{i0})(1)` is
`[T:W]·(ω_{ij}(1) − ω_{i0}(1)) = 0` (`omega_apply_one`), so the RHS
`δ'_i·(ν_{ij}(1) − ν_{i0}(1)) = 0`, and `δ'_i = ±1 ≠ 0` (`delta_pm_one.2`).  Mirror of
`mu_apply_one_column_const`. -/
theorem Hypothesis.nu_apply_one_row_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.nu i j (1 : ↥hyp.T) = hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) := by
  haveI := hyp.finiteG
  have hdef := hyp.nu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.T ℂ => f (1 : ↥hyp.T)) hdef
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_right)).toMonoidHom
        (hyp.omega i j - hyp.omega i ⟨0, hyp.p_prime.pos⟩))
      (1 : ↥(hyp.W.subgroupOf hyp.T)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  have hδ : (hyp.deltaPrime i : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.2 i) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.nu i j (1 : ↥hyp.T) - hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped Classical in
/-- **The `ν`-row sums are reducible** ((13.3.a)-at-`T` entry condition): `ν_i = ∑_j ν_{ij}`
is a sum of `p ≥ 2` *distinct* irreducible characters (`nu_irreducible`,
`nu_row_injective`), so its norm is `p ≠ 1`.  Mirror of `mu_colSum_not_irreducible`,
parametric in the ν-grid supply. -/
theorem Hypothesis.nu_rowSum_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter (∑ j : Fin hyp.p, hyp.nu i j) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro hirr
  set a : Fin hyp.p → OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T :=
    fun j => ⟨hyp.nu i j, pins.nu_irreducible i j⟩ with ha
  have hcond : ∀ j j' : Fin hyp.p, a j = a j' ↔ j = j' := by
    intro j j'
    constructor
    · intro h
      exact pins.nu_row_injective i (congrArg
        (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T =>
          (χ : ClassFunction ↥hyp.T ℂ)) h)
    · rintro rfl
      rfl
  have hinner : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu i j)
      (∑ j : Fin hyp.p, hyp.nu i j) = (hyp.p : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu i j) (∑ j' : Fin hyp.p, hyp.nu i j')
        = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, ClassFunction.inner (hyp.nu i j) (hyp.nu i j') := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, if j = j' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [pins.nu_orthonormal i i j j']
          exact if_congr (by simp) rfl rfl
      _ = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp
      _ = (hyp.p : ℂ) := by simp
  have h1 : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu i j)
      (∑ j : Fin hyp.p, hyp.nu i j) = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨∑ j : Fin hyp.p, hyp.nu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T)
      (⟨∑ j : Fin hyp.p, hyp.nu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T)
    simpa using hite
  rw [hinner] at h1
  have : hyp.p = 1 := by exact_mod_cast h1
  exact hyp.p_prime.one_lt.ne' this

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a) at `T`, per-entry degree**: `ν_{ij}(1) = v` for `i ≥ 1`.

**Residual (precisely named)**: the `T`-mirror of `mu_apply_one_eq_u` — the row sum
`ν_i = ∑_j ν_{ij}` is a reducible member of the §9-on-`T` family `𝒮_T(H₀)`
(`nu_rowSum_eq_induce` + `nu_rowSum_not_irreducible`), so the §9 `isIndHC`
(`reducible_sOf_H0_isIndHC` at the `toTypesIIIIIIVSetupT` instance, nontriviality
`vd_ne_one`) gives `ν_i = Ind_{QD}^T(linear)` of degree `[T:K] = v·p` (`K_index_eq_vp`),
and row constancy (`nu_apply_one_row_const`) yields `ν_{ij}(1) = v`.

**The gate, precisely**: the `sOf`-membership needs the `T`-instance chief kernel
triviality `H₀ = ⊥` (mirror of `toTypesIIIIIIVSetupS_chief_H0_eq_bot`), which needs
`|Q| = q^p` — (13.2.b)-at-`T` content.  On the `S`-side this reads off the carried
`S_typeP2` (type II via the BG dictionary + the (9.3) Wielandt order relation); `T` has no
such carrier at §13 — `IsTypeII T` *is* the (14.9) conclusion, and the type-III branch
needs the (11.7) chain (`S13_ElementaryAbelianKernel`) whose §11 hypothesis is
noncoherence-conditional.  Discharge routes: (i) the canonical certain-type readout at the
FT-layer construction site (`FeitThompsonNuGrid.lean`, where `T = mp.certainTypeT` carries
the §16 structure; a-owned carrier threading, issue 9096 follow-up), or (ii) the §11
(11.7)-chain `T`-instantiation.  Tracked in issue 2035. -/
theorem Hypothesis.nu_apply_one_eq_v [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_pins : NuGridSupplyData hyp)
    (i : Fin hyp.q) (j : Fin hyp.p) (_hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    hyp.nu i j (1 : ↥hyp.T) = ((hyp.v : ℕ) : ℂ) := by
  sorry

/-- **Peterfalvi (13.3.c), the `T`-side signs are `1` off the anchor row**: `δ'_i = 1` for
`i ≥ 1`.  The (4.3.d)-at-`T` congruence `ν_{i0}(1) = δ'_i + p·a`
(`nu_degree_modEq_deltaPrime`) with `ν_{i0}(1) = v` (`nu_apply_one_eq_v`) and `v ≡ 1 (mod p)`
(`v_modEq_one`) gives `p ∣ δ'_i − 1`; since `δ'_i = ±1` (`delta_pm_one.2`) and `p ≥ 3` odd,
`δ'_i = -1` would force `p ∣ 2`, so `δ'_i = 1`.  Mirror of `delta_eq_one_of_ne_zero`. -/
theorem Hypothesis.deltaPrime_eq_one_of_ne_zero_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    hyp.deltaPrime i = 1 := by
  obtain ⟨a, ha⟩ := pins.nu_degree_modEq_deltaPrime i ⟨0, hyp.p_prime.pos⟩
  rw [hyp.nu_apply_one_eq_v hG pins i ⟨0, hyp.p_prime.pos⟩ hi] at ha
  have haZ : (hyp.v : ℤ) = hyp.deltaPrime i + (hyp.p : ℤ) * a := by exact_mod_cast ha
  have hpv : (hyp.p : ℤ) ∣ (hyp.v : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.v_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hpδ : (hyp.p : ℤ) ∣ hyp.deltaPrime i - 1 := by
    have hsub : hyp.deltaPrime i - 1 = ((hyp.v : ℤ) - 1) - (hyp.p : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hpv (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.2 i with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hpδ
    have hp2 : (hyp.p : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hpδ)
    have hple : hyp.p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hp2)
    have h2le := hyp.p_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.p_odd
    omega

end OddOrder.Peterfalvi.S15
