import OddOrder.Peterfalvi.S16_NonExistenceG.BetaVanishing
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.OrderRelayer
import OddOrder.Peterfalvi.S16_NonExistenceG.ComparingLMBasic

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceG.ComparingLM` (2000-line limit, issue 0103 第
2 パス).
-/

namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]


namespace OrthogonalitySwitchData

/-- **`|H_L| = h`** — the (7.8) kernel of any coherence bundle on the (14.3) `L` is the
canonical `H = L_F`, so its order is the `NonConjugateHypothesis` parameter `h`. -/
theorem typeICoherent78_card_kernel_eq_h [Finite G]
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp)
    (dataL : TypeICoherent78Data nc.Ldata.L) :
    Nat.card ↥dataL.typeIHyp.H = nc.h := by
  have hHeq : dataL.typeIHyp.H = nc.Ldata.H := by
    change dataL.typeIHyp.typeI.typeF.H = nc.Ldata.H
    rw [dataL.typeIHyp.typeI.typeF.H_eq, nc.Ldata.H_eq_LF]
  rw [nc.h_eq_card_H, hHeq]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the L-side signed `η`-grid expansion.**  Under case-(b)
(`(q,p) = (3,5)`) and the two gap inequalities, (13.19.c) applied on the S- and T-sides gives
the (14.11.2)-style signed expansion `β_L^τ = Σ_{ij} ε_ij η_ij − ε ζ_i^ν` of the L-side, with
the removed unit-norm member an `L`-family coherent image (`i ≠ ind1H`; the `−ψ̄^{τ₁}`
alternative is the conjugate member `conjIndex`).

Proven (lane c, issue 0115 Campaign A) from the honest (14.11.2) L-side conclusion
`lSide_expansion_classification`: the removed member is the distinguished coherent image
`ζ_0^ν` with `ε = 1` **or** the conjugate family member `ζ_{j₁}^ν = ν(ζ̄_0)`
(`exists_conjIndex`) with `ε = −1`, matching the Coq `FTtype2_support_coherence` alternatives
`chi = tau1L phi \/ chi = - tau1L phi^*`.  The strict gap inputs `ub_u`/`ub_v` of the
(c1)-branch refutations are derived here from the (14.14) gap chain `hhv`/`hvu` through the
`e_L = p q` and `|H_L| = h` bridges. -/
theorem lSide_signed_eta_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) := by
  -- `e_L = |L : H_L| = p q` (`typeICoherent78_complementIndex_eq_pq`, the (14.3) Frobenius order).
  have hepq := typeICoherent78_complementIndex_eq_pq hG nc.Ldata dataL
  -- (14.11.2)-style strict gap inputs for the (13.19.c) dichotomy branches, in `dataL`
  -- coordinates: `(v−1)/p < (h−1)/e` is `hhv` (after `e = pq`, `|H_L| = h`), and
  -- `(u−1)/q < (h−1)/e` chains it with `hvu`.
  have hindex : ((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index
      = hyp.base.p * hyp.base.q := typeICoherent78_index_eq_pq hG nc.Ldata dataL
  have hcardH : Nat.card ↥dataL.typeIHyp.H = nc.h :=
    typeICoherent78_card_kernel_eq_h nc dataL
  have hub_v : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index : ℚ) := by
    rw [hcardH, hindex]
    exact hhv
  have hub_u : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index : ℚ) :=
    lt_trans hvu hub_v
  obtain ⟨signs, chi, hsigns, hclass, hexp⟩ :=
    lSide_expansion_classification hG hnoV hncH0C nc.Ldata.L_maximal dataL hq3 hp5 hepq
      hub_u hub_v
  rcases hclass with hchi | hchi
  · -- `χ = ζ_0^ν`: the removed member is the distinguished image (`i = zetaDistinct`, `ε = 1`)
    refine ⟨signs, hsigns, (dataL.h78 hG).zetaDistinct, ?_, 1, Or.inl rfl, ?_⟩
    · have h := (dataL.h78 hG).zetaDistinct_ne_ind1H
      rwa [dataL.h78_ind1H_eq] at h
    · rw [hexp, hchi]
      norm_num
  · -- `χ = −(ζ̄_0)^ν`: the removed member is the conjugate family member (`ε = −1`)
    obtain ⟨j₁, hj₁ne, hj₁⟩ := dataL.exists_conjIndex hG
    refine ⟨signs, hsigns, j₁, ?_, -1, Or.inr rfl, ?_⟩
    · rwa [dataL.h78_ind1H_eq] at hj₁ne
    · rw [hexp, hchi, ← congrArg (dataL.h78 hG).nu hj₁]
      push_cast
      rw [neg_smul, one_smul]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (14.16) expansion input** — the §13-gated character content of the case-(b)
contradiction, split into its two genuine textbook gates and the sorry-free (13.19.b) engine.
Under case-(b) (`(q,p) = (3,5)`) and the two gap inequalities:

* the L-side signed `η`-grid expansion `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is the named (13.19.c)
  producer `lSide_signed_eta_expansion`;
* the M-side orthogonality `(η_ij, ψ^{τ₁}) = 0` (`ψ^{τ₁} = ζ_M^ν`) is **proven** by the
  (3.6)–(3.8)/(13.19.b) engine `caseB_eta_orthogonal_psi`, whose one residual input is the
  named (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`. -/
theorem caseB_expansion_input [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 _hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i)) ∧
        ∀ (i' : Fin hyp.base.q) (j : Fin hyp.base.p),
          ClassFunction.inner (hyp.base.eta i' j)
            ((dataM.h78 _hG).nu
              ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)) = 0 := by
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp⟩ :=
    lSide_signed_eta_expansion _hG hnoV hncH0C dataL hq3 hp5 hhv hvu
  exact ⟨signs, hsigns, i, hi, ε, hε, hexp,
    caseB_eta_orthogonal_psi _hG hyp.base dataM
      (mSide_dadeSupport_avoids_regular _hG hnoV hncH0C nc.Mdata.M_maximal dataM)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §16 producer for the (14.16) case-(b) contradiction inputs.**  The case-(b)
pairing comes from the enriched `OrthogonalitySwitchData.caseB_pairing` ((7.9) dichotomy);
the `χ_L ⊥ ψ^{τ₁}` orthogonality is the proven (4.1) cross-orthogonality
`pair_cross_orthogonal`; the remaining (13.19.c)/(14.11.2) grid content is the named
`caseB_expansion_input`. -/
theorem caseB_contradiction_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    Nonempty (CaseBContradictionData nc) := by
  obtain ⟨hq3, hp5⟩ := data.caseB_params hcaseB
  obtain ⟨dataL, dataM, hpair⟩ := data.caseB_pairing hcaseB _hG
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp, horth⟩ :=
    caseB_expansion_input _hG hnoV hncH0C dataL dataM hq3 hp5 hhv hvu
  have hjne : (dataM.h78 _hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 _hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  refine ⟨{
    betaL := (dataL.h78 _hG).beta
    chiL := (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i))
    psiImg := (dataM.h78 _hG).nu ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)
    signs := signs
    signs_pm_one := hsigns
    betaL_expansion := hexp
    eta_orthogonal_psi := horth
    chiL_orthogonal_psi := ?_
    pairing_ne_zero := hpair }⟩
  rw [ClassFunction.inner_smul_left,
    pair_cross_orthogonal dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj hi hjne, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.16)**: character-theoretic endpoint of the exceptional
case.  The two strict gap inequalities let (13.19.c) be applied on both the
S- and T-sides, giving the same signed `eta_ij` expansion as in (14.11.2) for
`beta_L^tau`; this contradicts the nonzero pairing in case-(b) of (14.14).

De-opacified (W4 §16, lane-h): the genuine character theory (the `β_L^τ` expansion, the `η`-grid /
`χ_L` orthogonalities to `ψ^{τ₁}`, and the case-(b) pairing) is the faithful
`CaseBContradictionData`;
the contradiction itself is the pure inner-product computation
`(β_L^τ, ψ^{τ₁}) = (Σ ±η_ij − χ_L, ψ^{τ₁})
= Σ ±·0 − 0 = 0`, contradicting `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
theorem caseB_character_contradiction_of_gap_inequalities
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    False := by
  -- The (14.11.2)-style signed `eta_ij` expansion of `beta_L^tau` and its orthogonalities.
  obtain ⟨⟨betaL, chiL, psiImg, signs, _hsigns, hexp, heta_orth, hchiL_orth, hpair_ne⟩⟩ :=
    caseB_contradiction_data _hG hnoV hncH0C data hcaseB hhv hvu
  -- `(beta_L^tau, psi^tau_1) = 0` by linearity + orthogonality, contradicting case-(b).
  refine hpair_ne ?_
  rw [hexp, ClassFunction.inner_sub_left, hchiL_orth, sub_zero, inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [ClassFunction.inner_smul_left, heta_orth i j, mul_zero]

/-- **Peterfalvi (14.16)**: consumer form of the exceptional case-(b) branch
under `H > U`.  All numerical work in the paragraph is discharged here; only
the named character-theoretic endpoint remains as a producer. -/
theorem caseB_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  have hu_full := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  have hh_lower := h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    _hG hu_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q hx_ne_one_of_quotient
  rcases data.caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
      Tdata Sdata hcaseB hh_lower with ⟨hhv, hvu⟩
  exact data.caseB_character_contradiction_of_gap_inequalities _hG hnoV hncH0C hcaseB hhv hvu

end OrthogonalitySwitchData

/-- For `p ≥ 7`, `p² ≤ 3^(p-3)`: the monotonicity input for the `p = 5` step of Peterfalvi
(14.14.b).
The paper's `f(x) = 3^(x-3)/x²` is increasing for `x ≥ 2` (`f(x+1)/f(x) = 3(1 − 1/(x+1))² > 1`);
this
is the integer form `p² ≤ 3^(p-3)` proved by induction from `p = 7` (`7² = 49 ≤ 81 = 3⁴`). -/
private theorem sq_le_three_pow_sub_three {p : ℕ} (hp : 7 ≤ p) : p ^ 2 ≤ 3 ^ (p - 3) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hsucc : 3 ^ (p + 1 - 3) = 3 * 3 ^ (p - 3) := by
        rw [show p + 1 - 3 = (p - 3) + 1 by omega, pow_succ]; ring
      rw [hsucc]
      calc (p + 1) ^ 2 ≤ 3 * p ^ 2 := by nlinarith [hp]
        _ ≤ 3 * 3 ^ (p - 3) := by gcongr

namespace Hypothesis

/-- **Peterfalvi (14.14.b)/(14.15) arithmetic core**: in case (b) of the orthogonality switch, the
`(β_L, ψ)`-pairing bound `(v−1)/(pq) ≤ pq−1` together with the (14.4) cyclotomic value
`v = (q^p−1)/(q−1)` and the (14.8.a) exponential comparison `q^(p+1) > p^(q+1)` force the
exceptional primes `q = 3` and `p = 5`.

Proof (Pf p.91): `(v−1)/(pq) < pq` gives `q^(p−1) ≤ v−1 < p²q²`, hence `q^(p−3) < p²`.  By (14.8.a)
`q^(p+1) > p^(q+1)` and `q < p`, one gets `q^(p−3) > p^(q−3)`, so `p^(q−3) < p²`, whence `q = 3`.
Then `3^(p−3) < p²`, contradicting `p² ≤ 3^(p−3)` for `p ≥ 7`, so `p = 5`. -/
theorem caseB_forces_q_three_and_p_five (hyp : Hypothesis (G := G))
    (hv : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hbound : ((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) :
    hyp.base.q = 3 ∧ hyp.base.p = 5 := by
  have hp_prime := hyp.base.p_prime
  have hq_prime := hyp.base.q_prime
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  have hq3le : 3 ≤ hyp.base.q := by
    rcases hyp.base.q_odd with ⟨k, hk⟩; have := hq_prime.two_le; omega
  have hp5le : 5 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  -- Step 1: `v − 1 < p² q²` from the case-(b) bound.
  have hpq_pos : 0 < hyp.base.p * hyp.base.q := Nat.mul_pos hp_prime.pos hq_prime.pos
  have hpqQ : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by exact_mod_cast hpq_pos
  have hv1_le : (hyp.base.v - 1 : ℕ) ≤
      (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := by
    have h := (div_le_iff₀ hpqQ).mp hbound
    exact_mod_cast h
  have hv1_lt : hyp.base.v - 1 < hyp.base.p ^ 2 * hyp.base.q ^ 2 := by
    have hlt : (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q)
        < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) :=
      mul_lt_mul_of_pos_right (by omega) hpq_pos
    calc hyp.base.v - 1
        ≤ (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := hv1_le
      _ < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := hlt
      _ = hyp.base.p ^ 2 * hyp.base.q ^ 2 := by ring
  -- Step 2: `q^(p−1) ≤ v − 1` from the geometric-sum lower bound.
  have hlow : hyp.base.q ^ (hyp.base.p - 1) ≤ hyp.base.v - 1 := by
    have h := cyclotomic_quotient_sub_one_ge_pow_pred hq_prime.two_le hp_prime.two_le
    rw [← hv] at h
    exact_mod_cast h
  -- Step 3: `q^(p−3) < p²`.
  have hqpm3 : hyp.base.q ^ (hyp.base.p - 3) < hyp.base.p ^ 2 := by
    have he : hyp.base.q ^ (hyp.base.p - 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hlt : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
        < hyp.base.p ^ 2 * hyp.base.q ^ 2 :=
      calc hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
          = hyp.base.q ^ (hyp.base.p - 1) := he.symm
        _ ≤ hyp.base.v - 1 := hlow
        _ < hyp.base.p ^ 2 * hyp.base.q ^ 2 := hv1_lt
    exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  -- Step 4: `p^(q−3) < q^(p−3)` from (14.8.a).
  have hkey : hyp.base.p ^ (hyp.base.q + 1) < hyp.base.q ^ (hyp.base.p + 1) := hyp.q_pow_gt_p_pow
  have hgt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.q ^ (hyp.base.p - 3) := by
    by_contra hle
    rw [not_lt] at hle
    have e1 : hyp.base.q ^ (hyp.base.p + 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have e2 : hyp.base.p ^ (hyp.base.q + 1)
        = hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have hq4p4 : hyp.base.q ^ 4 < hyp.base.p ^ 4 := Nat.pow_lt_pow_left hqp (by norm_num)
    have hppos : 0 < hyp.base.p ^ (hyp.base.q - 3) := pow_pos hp_prime.pos _
    have h1 : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4
        ≤ hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4 := by gcongr
    have h2 : hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4
        < hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 :=
      mul_lt_mul_of_pos_left hq4p4 hppos
    have hchain := lt_of_le_of_lt h1 h2
    rw [← e1, ← e2] at hchain
    omega
  -- Step 5: `q = 3`.
  have hq3 : hyp.base.q = 3 := by
    have hplt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.p ^ 2 := lt_trans hgt hqpm3
    have hexp : hyp.base.q - 3 < 2 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd hplt (not_lt.mpr (Nat.pow_le_pow_right (by omega) hge))
    rcases hyp.base.q_odd with ⟨k, hk⟩
    omega
  refine ⟨hq3, ?_⟩
  -- Step 6: `p = 5`.
  rw [hq3] at hqpm3
  by_contra hp_ne
  have hp7 : 7 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  have := sq_le_three_pow_sub_three hp7
  omega

end Hypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14) character dichotomy** — the genuine §7/§8 content of the orthogonality
switch.  By (8.17.c) the Dade supports `Ã₁(L)` and `Ã₁(M)` are disjoint, so by (7.9) either the
`M`-side pairing `(β_M^τ, φ^τ₁) ≠ 0` or the `L`-side pairing `(β_L^τ, ψ^τ₁) ≠ 0`.  In the first
case the (7.8.b) coherence-norm bound on the `β_M`-expansion `β_M^τ = a Σ aᵢ φᵢ^{τ₁} + Δ` gives
`Σ aᵢ² ≤ pq − 1`, i.e. `(h−1)/pq ≤ pq−1`; in the second the same estimate on the `β_L`-expansion
gives `(v−1)/pq ≤ pq−1`.  This isolates the character-theoretic input to `orthogonality_switch`;
the case-(b) passage to `q = 3`, `p = 5` is the arithmetic
`Hypothesis.caseB_forces_q_three_and_p_five`. -/
theorem orthogonality_switch_pairing_bounds [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) ∨
      ((∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
          ∃ (dataL : TypeICoherent78Data nc.Ldata.L)
            (dataM : TypeICoherent78Data nc.Mdata.M),
            ClassFunction.inner
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).first.beta)
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0) ∧
        (((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))) := by
  classical
  -- The two (14.14) coherence bundles, for `L ⊇ N_G(U)` and `M ⊇ N_G(V)`.
  obtain ⟨dataL⟩ := TypeICoherent78Data.nonempty _hG hnoV nc.Ldata.L_maximal nc.Ldata.isTypeI
  obtain ⟨dataM⟩ := TypeICoherent78Data.nonempty _hG hnoV nc.Mdata.M_maximal
    ⟨nc.Mdata.typeIHyp.typeI⟩
  have hnc' : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup nc.Mdata.M nc.Ldata.L :=
    fun h => nc.not_conj h.symm
  -- `L`-side sizes: `|H| = h` and `[L : H] = p q`.
  have hcardL : Nat.card ↥dataL.kernelIn = nc.h := by
    have h1 : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
    have h2 : dataL.kernel = nc.Ldata.H := by
      rw [show dataL.kernel = maxNilpotentNormalHall nc.Ldata.L from
          dataL.typeIHyp.typeI.typeF.H_eq, ← nc.Ldata.H_eq_LF]
    rw [h1, h2, nc.h_eq_card_H]
  have hidxL : (dataL.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h := OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement
      nc.Ldata.typeI_data.frobenius
    have h2 : dataL.kernelIn
        = (maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L := by
      rw [show dataL.kernelIn = (dataL.typeIHyp.typeI.typeF.H).subgroupOf nc.Ldata.L
          from rfl, dataL.typeIHyp.typeI.typeF.H_eq]
    rw [h2, ← nc.Ldata.typeI_data_L_eq]
    exact h.trans nc.Ldata.typeI_complement_card_eq_pq
  -- `M`-side sizes: `|K| = v` ((14.11) `K = V`, `|V| = v·d`, `d = 1`) and `[M : K] = p q`.
  obtain ⟨hKV, hepq⟩ := K_eq_V_index_pq _hG hnoV hncH0C hyp nc.Ldata nc.Mdata
  have hkerM : dataM.kernel = nc.Mdata.K := by
    rw [show dataM.kernel = maxNilpotentNormalHall nc.Mdata.M from
        dataM.typeIHyp.typeI.typeF.H_eq, ← nc.Mdata.K_eq_MF]
  have hd1 : hyp.base.d = 1 := by
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot _hG
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hcardM : Nat.card ↥dataM.kernelIn = hyp.base.v := by
    have h1 : Nat.card ↥dataM.kernelIn = Nat.card ↥dataM.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataM.kernel_le).toEquiv
    rw [h1, hkerM, hKV, hyp.base.card_V_eq_vd, hd1, mul_one]
  have hidxM : (dataM.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h1 : dataM.kernelIn = nc.Mdata.K.subgroupOf nc.Mdata.M := by
      rw [show dataM.kernelIn = (dataM.kernel).subgroupOf nc.Mdata.M from rfl, hkerM]
    rw [h1, ← nc.Mdata.e_eq_index]
    exact hepq
  -- Convert the `ℚ`-subtractions to the `ℕ`-subtraction casts of the statement.
  have hpq1 : 1 ≤ hyp.base.p * hyp.base.q :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hyp.base.p_prime.pos.ne' hyp.base.q_prime.pos.ne')
  have hv1 : 1 ≤ hyp.base.v := by
    have hVpos : 0 < Nat.card ↥hyp.base.V := Nat.card_pos
    rw [hyp.base.card_V_eq_vd, hd1, mul_one] at hVpos
    exact hVpos
  have hh1 : 1 ≤ nc.h := (nc.h_odd _hG).pos
  -- The (7.9) pairing dichotomy, with the pairing itself retained in the case-(b) branch.
  rcases pairing_dichotomy dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj with hfirst | hsecond
  · -- `⟨β_L, ζ_M^ν⟩ ≠ 0`: the `M`-kernel Bessel bound `(v − 1)/pq ≤ pq − 1` + the pairing.
    right
    have hMK := bessel_bound_of_inner_beta_zeta_ne_zero dataM dataL _hG
      nc.Mdata.M_maximal nc.Ldata.L_maximal hnc' hfirst
    rw [dataL.complementIndex_eq _hG, hcardM, hidxM, hidxL] at hMK
    refine ⟨fun hG' => ⟨dataL, dataM, hfirst⟩, ?_⟩
    rw [Nat.cast_sub hv1, Nat.cast_sub hpq1]
    push_cast at hMK ⊢
    convert hMK using 2
  · -- `⟨β_M, ζ_L^ν⟩ ≠ 0`: the `L`-kernel Bessel bound `(h − 1)/pq ≤ pq − 1`.
    left
    have hLH := bessel_bound_of_inner_beta_zeta_ne_zero dataL dataM _hG
      nc.Ldata.L_maximal nc.Mdata.M_maximal nc.not_conj hsecond
    rw [dataM.complementIndex_eq _hG, hcardL, hidxL, hidxM] at hLH
    rw [Nat.cast_sub hh1, Nat.cast_sub hpq1]
    push_cast at hLH ⊢
    convert hLH using 2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14)**: either the case-(a) bound `(h − 1)/pq ≤ pq − 1` holds (the
`β_M`--`φ` pairing is nonzero), or the case-(b) exceptional primes `q = 3`, `p = 5` hold (the
`β_L`--`ψ` pairing is nonzero).

Assembled from the (7.9)+(8.17.c) character dichotomy `orthogonality_switch_pairing_bounds`, whose
two branches supply the case-(a) norm bound and the case-(b) `(v−1)/pq ≤ pq−1` bound; in case (b)
the arithmetic `caseB_forces_q_three_and_p_five` ((14.15)/(14.8.a)) turns that bound, together with
the (14.4) cyclotomic value of `v`, into `q = 3`, `p = 5`.  The abstract `caseA`/`caseB` props of
`OrthogonalitySwitchData` are taken to be the case-(a) bound and the `(q,p)=(3,5)` conclusion
themselves, so the downstream (14.15)/(14.16) machinery reads them off directly. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  obtain ⟨_Tdata, _, hv⟩ := caseB_for_T _hG hyp
  refine ⟨{
    caseA := ((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)
    caseA_bound := fun h => h
    caseB := (hyp.base.q = 3 ∧ hyp.base.p = 5) ∧
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
        ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
          ClassFunction.inner
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).first.beta)
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0
    caseB_params := fun h => h.1
    caseB_pairing := fun h => h.2 }, ?_⟩
  rcases orthogonality_switch_pairing_bounds _hG hnoV hncH0C hyp nc with hA | ⟨hpair, hB⟩
  · exact Or.inl hA
  · exact Or.inr ⟨hyp.caseB_forces_q_three_and_p_five hv hB, hpair⟩

/-- **Peterfalvi (14.14)--(14.15)**: the full `u` value once the
cardinality consequences of (14.5) have been materialized.  The case-(b)
alternative of (14.14) is already full by the S-side order data; in case (a),
assuming the non-full value contradicts the fixed-point-free cardinal
congruences for `H` and `U`. -/
theorem u_final_value_of_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases orthogonality_switch _hG hnoV hncH0C hyp nc with ⟨data, hcase⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  rcases hcase with hcaseA | hcaseB
  · by_contra hu_not_full
    exact data.caseA_contradiction_of_nonfull_fpf_card_congruences
      _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q
  · exact data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`.

The proof consumes the cardinal consequences of (14.5): `u ∣ h`, the two
Frobenius-kernel congruences for `h`, and the fixed-point-free cardinal
congruence for `U`.  The arithmetic contradiction is packaged in
`u_final_value_of_fpf_card_congruences`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  exact u_final_value_of_fpf_card_congruences _hG hnoV hncH0C hyp nc (nc.u_dvd_h _hG)
    hh_mod_p hh_mod_q (hyp.u_modEq_one_mod_q _hG)

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  by_contra hHU
  rcases orthogonality_switch _hG hnoV hncH0C hyp nc with ⟨data, hcase⟩
  rcases caseB_for_T _hG hyp with ⟨Tdata, _hT_caseB, _hv_eq⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  have hu_full := u_final_value _hG hnoV hncH0C hyp nc
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hx_ne_one_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1 := by
    intro x hh_eq hx1
    have hH_card_eq_U_card : Nat.card ↥nc.Ldata.H = Nat.card ↥hyp.base.U := by
      rw [← nc.h_eq_card_H, hh_eq, hx1, mul_one, hU_card]
    have hU_eq_H : hyp.base.U = nc.Ldata.H :=
      Subgroup.eq_of_le_of_card_ge hU_le_H (le_of_eq hH_card_eq_U_card)
    exact hHU hU_eq_H.symm
  rcases hcase with hcaseA | hcaseB
  · exact data.caseA_contradiction_of_full_u_card_congruences
      _hG Sdata hcaseA hu_full (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient
  · exact data.caseB_contradiction_of_full_u_card_congruences
      _hG hnoV hncH0C Tdata Sdata hcaseB (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient

/-- **Peterfalvi §8 / BG 15.7(a)**: the type-`P` Fitting core `P = S_F` is a TI-subgroup of `G`.
The symmetric `S_nonI` carrier gives the type-II/type-III TI conclusion, whence the Fitting core
`S_F#` is TI (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`; `sharpSubgroup = ·∖{1}`
matches `Subgroup.IsTI`).  Supplies the `P_isTI` field of `MHypothesis`. -/
theorem base_P_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Subgroup.IsTI hyp.base.P := by
  rw [hyp.base.P_eq_SF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.S_maximal
    (OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI
      hG hyp.base.S_maximal hyp.base.S_nonI)

/-- **Peterfalvi §8, `T`-side**: the type-`P` Fitting core `Q = T_F` is a TI-subgroup of `G`.
`T`-side dual of `base_P_isTI` via `fittingIsTI_T` (`T` type II ⟹ type-`P₂`).  Supplies the `Q_isTI`
field of `MHypothesis`. -/
theorem base_Q_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) : Subgroup.IsTI hyp.base.Q := by
  rw [hyp.base.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp.base hTII)

/-- **Peterfalvi §13 `normalizer_V` (the `W`-exceptional-set normalizer)**: every nonempty
`X ⊆ W − (W₁ ∪ W₂)` has `N_G(X) = W`.  Read off the S-side type-`P` data `Sdata.normalizer_V`
((8.8) `W = W₁ × W₂` cyclic-TI structure), reconciled to the base `W`/`W₁`/`W₂`
(`Sdata_W1_eq`/`Sdata_W2_eq`, `W_eq_join`).  Supplies `MHypothesis`'s `W_normalizer_V`. -/
theorem base_W_normalizer_V (hyp : Hypothesis (G := G)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
      Subgroup.normalizer X = hyp.base.W := by
  have hWeq : hyp.base.Sdata.W = hyp.base.W := by
    rw [hyp.base.Sdata.W_eq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
    exact hyp.base.W_eq_join.symm
  intro X hX hXsub
  rw [← hWeq]
  refine hyp.base.Sdata.normalizer_V X hX ?_
  rw [hWeq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
  exact hXsub

/-- **Order factorization of the type-`P` maximal `S`**: `|P| · |U| · |W₁| = |S|`
(`S = (P ⋊ U) ⋊ W₁`, `P = S_F`, `S' = P ⋊ U`).  From the `Sdata` complement indices
`card_W1_eq_derived_index` (`|W₁| = [S:S']`) and `card_U_eq_index` (`|U| = [S':P]`) via
`Subgroup.card_mul_index`. -/
theorem base_card_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.base.P * Nat.card ↥hyp.base.U * Nat.card ↥hyp.base.W1
      = Nat.card ↥hyp.base.S := by
  have hW1 : Nat.card ↥hyp.base.W1 = Nat.card ↥hyp.base.Sdata.W1 := by rw [hyp.base.Sdata_W1_eq]
  have hU : Nat.card ↥hyp.base.U = Nat.card ↥hyp.base.Sdata.U := by rw [hyp.base.Sdata_U_eq]
  have hP : hyp.base.P = maxNilpotentNormalHall hyp.base.S := hyp.base.P_eq_SF
  have hDle : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hPle : maxNilpotentNormalHall hyp.base.S ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU, ← hP]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.S) * Nat.card ↥hyp.base.Sdata.W1
      = Nat.card ↥hyp.base.S := by
    rw [hyp.base.Sdata.card_W1_eq_derived_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.S) * Nat.card ↥hyp.base.Sdata.U
      = Nat.card ↥(derivedInG hyp.base.S) := by
    rw [hyp.base.Sdata.card_U_eq_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW1, hU, hP, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| · u · q`.  The Fitting core `P = S_F` is normal in
the maximal `S` and nontrivial (`W₂ ≤ P`), so `N_G(P) = S`
(`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`); then `|S| = |P|·|U|·|W₁|` (`base_card_S_eq`)
with `|U| = u·c`, `c = 1` (`c_eq_one_of_lambda_dichotomy`), `|W₁| = q`.  Supplies `MHypothesis`'s
`card_normalizer_P_eq`. -/
theorem base_card_normalizer_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
      = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q := by
  have hPne : maxNilpotentNormalHall hyp.base.S ≠ ⊥ := by
    intro hbot
    have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base
    rw [hyp.base.P_eq_SF, hbot, le_bot_iff] at hW2
    have hp1 : hyp.base.p = 1 := by rw [hyp.base.p_eq_card_W2, hW2, Subgroup.card_bot]
    exact hyp.base.p_prime.one_lt.ne' hp1
  have hNP : Subgroup.normalizer (hyp.base.P : Set G) = hyp.base.S := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.S_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hPne
  rw [hNP, ← base_card_S_eq hyp, hyp.base.card_U_eq_uc,
    hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply, mul_one,
    hyp.base.q_eq_card_W1]

/-- **Order factorization of the type-`P` maximal `T`** (T-side dual of `base_card_S_eq`):
`|Q| · |V| · |W₂| = |T|`, from a reconciled `TypePData T` (`tpd.U = V`, `tpd.W1 = W₂`, `Q = T_F`)
via `card_W1_eq_derived_index` / `card_U_eq_index` and `Subgroup.card_mul_index`. -/
theorem base_card_T_eq [Finite G] (hyp : Hypothesis (G := G))
    (tpd : OddOrder.GroupTheory.TypePData hyp.base.T) (hU : tpd.U = hyp.base.V)
    (hW1 : tpd.W1 = hyp.base.W2) :
    Nat.card ↥hyp.base.Q * Nat.card ↥hyp.base.V * Nat.card ↥hyp.base.W2
      = Nat.card ↥hyp.base.T := by
  have hW2c : Nat.card ↥hyp.base.W2 = Nat.card ↥tpd.W1 := by rw [hW1]
  have hVc : Nat.card ↥hyp.base.V = Nat.card ↥tpd.U := by rw [hU]
  have hQ : hyp.base.Q = maxNilpotentNormalHall hyp.base.T := hyp.base.Q_eq_TF
  have hDle : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQle : maxNilpotentNormalHall hyp.base.T ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV, ← hQ]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥tpd.W1 = Nat.card ↥hyp.base.T := by
    rw [tpd.card_W1_eq_derived_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.T) * Nat.card ↥tpd.U
      = Nat.card ↥(derivedInG hyp.base.T) := by
    rw [tpd.card_U_eq_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW2c, hVc, hQ, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| · v · p` (T-side dual of `base_card_normalizer_P_eq`).
`Q = T_F` is normal in the maximal `T` and nontrivial (`W₁ ≤ Q`), so `N_G(Q) = T`; then
`|T| = |Q|·|V|·|W₂|` (`base_card_T_eq`) with `|V| = v·d`, `d = 1` (`V_inf_centralizer_Q_eq_bot`,
`D = V ⊓ C_G(Q) = ⊥`), `|W₂| = p`.  Supplies `MHypothesis`'s `card_normalizer_Q_eq`. -/
theorem base_card_normalizer_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hTII : IsTypeII hyp.base.T) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
      = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p := by
  obtain ⟨tpd, hU, hW1, hW2⟩ := OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base
  have hQne : maxNilpotentNormalHall hyp.base.T ≠ ⊥ := by
    intro hbot
    have hW1le : hyp.base.W1 ≤ maxNilpotentNormalHall hyp.base.T := by
      rw [← hW2]
      exact le_trans tpd.W2_le (le_trans inf_le_left (le_of_eq tpd.H_eq))
    rw [hbot, le_bot_iff] at hW1le
    have hq1 : hyp.base.q = 1 := by rw [hyp.base.q_eq_card_W1, hW1le, Subgroup.card_bot]
    exact hyp.base.q_prime.one_lt.ne' hq1
  have hNQ : Subgroup.normalizer (hyp.base.Q : Set G) = hyp.base.T := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne
  have hd1 : hyp.base.d = 1 := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot hG
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  rw [hNQ, ← base_card_T_eq hyp tpd hU hW1, hyp.base.card_V_eq_vd, hd1, mul_one,
    hyp.base.p_eq_card_W2]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8) for the V-side `M`** — the §7 coherence datum `S09.Hypothesis78` of the
type-I maximal subgroup `M` over `N_G(V)`, together with its structural data (maximality and
`N_G(V) ≤ M`).

This is the **V-side dual of `witness_L_hypothesis78`** (the (12.16) witness-side coherence):
`M`'s coherence is produced by the general type-I Frobenius engine `S14.frobenius_typeI_coherent`
(`M` is the witness from the faithful `S15.exists_M_structural_dichotomy`, and (12.7)
`S14.typeI_frobenius` supplies its Frobenius structure with kernel `M_F`),
and the (7.8) datum is assembled by the same `hypothesis78OfDade` construction (placed family
`exists_witness_placed_family`, `nu_isometry` from `coherence_extension_inner_eq_on_family`,
`hagree` from `coherence_hagree_dadeMap`).  It exports exactly the faithful (13.17.c)-dual
alternatives `|M:M_F| = p ∨ |M:M_F| = p q`, never the unconditional second branch, and additionally
supplies the `h78` field of `MHypothesis`. -/
theorem exists_M_hypothesis78 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) :
    ∃ (M : Subgroup G) (typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.base.V : Set G) ≤ M ∧
          (((maxNilpotentNormalHall M).subgroupOf M).index = hyp.base.p ∨
            ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.base.p * hyp.base.q) ∧
          ∃ h78 : OddOrder.Peterfalvi.S09.Hypothesis78 G
              (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M,
            h78.hyp76.H = maxNilpotentNormalHall M ∧
              h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade ∧
              h78.hyp76.zeta h78.ind1H (1 : M)
                = (((maxNilpotentNormalHall M).subgroupOf M).index : ℂ) ∧
              ClassFunction.inner (h78.hyp76.zeta h78.zetaDistinct)
                (h78.hyp76.zeta h78.zetaDistinct) = 1 ∧
              (1 : ℝ) - (h78.complementIndex : ℝ) / (h78.kernelOrder : ℝ)
                ≤ h78.zetaNuRhoNormSq := by
  classical
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply
  obtain ⟨M, typeIHyp, hMmax, hnormV, hindexCases⟩ :=
    OddOrder.Peterfalvi.S15.exists_M_structural_dichotomy_of_c_eq_one
      hG hnoV hyp.base hc1 hTII
  obtain ⟨fdata, _⟩ :=
    OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hMmax ⟨typeIHyp.typeI⟩
  refine ⟨M, typeIHyp, hMmax, hnormV, hindexCases, ?_⟩
  -- Coherence for `M` via the general type-I Frobenius engine: the Frobenius witness for
  -- `typeIHyp.H = M_F` comes from (12.7) (both kernels are `maxNilpotentNormalHall M`).
  have hHeq : typeIHyp.typeI.typeF.H = fdata.typeI.typeF.H := by
    rw [typeIHyp.typeI.typeF.H_eq, fdata.typeI.typeF.H_eq]
  have hfrob : ∃ C : Subgroup ↥M,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((typeIHyp.typeI.typeF.H).subgroupOf M) C :=
    ⟨fdata.complement, by rw [hHeq]; exact fdata.frobenius⟩
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp hfrob
  -- Mirror `witness_L_hypothesis78`'s `hypothesis78OfDade` assembly (generic in the hypothesis).
  have hHL : typeIHyp.typeI.typeF.H ≤ M := typeIHyp.typeI.typeF.H_le
  have hKnormal : ((typeIHyp.typeI.typeF.H).subgroupOf M).Normal := by
    rw [typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  have hAH : OddOrder.GroupTheory.typeIA M typeIHyp.typeI
      = (typeIHyp.typeI.typeF.H : Set G) \ {1} :=
    OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG hnoV typeIHyp
  have hHnorm : ∀ (l : ↥M) {h : G}, h ∈ typeIHyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ typeIHyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ M := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥M) ∈ (typeIHyp.typeI.typeF.H).subgroupOf M :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
          (θ i : ClassFunction _ ℂ) ∈ typeIHyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
          (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf M) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf M))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf M) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf M)) := fun _ => rfl
  have hdeg : ∀ i, ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ i : ClassFunction _ ℂ) (1 : ↥M)
      = d i * ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥M) := by
    intro i
    rw [ClassFunction.induce_apply_one ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  have hdeg_match : ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥M)
      = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥M) := by
    rw [hdeg0, htriv]
    change (((typeIHyp.typeI.typeF.H).subgroupOf M).index : ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
          (trivialClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf M)) (1 : ↥M)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  have psi_support : ∀ i, (ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf M)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff typeIHyp.typeI.typeF.H hAH x).mpr
      ⟨hx.1, hx.2⟩
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf M) (θ i : ClassFunction _ ℂ)))
        (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf M) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf M) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ j : ClassFunction _ ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      typeIHyp.toHypothesis71.τ ⟨ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf M) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = coh.extension (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ i : ClassFunction _ ℂ))
          - d i • coh.extension (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf M) (θ 0 : ClassFunction _ ℂ)) := by
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap typeIHyp.dadeData.dade coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)
  refine ⟨hypothesis78OfDade typeIHyp.toHypothesis71
    (typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeIsometryData.isDadeIsometry
    typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
    hdeg_match coh.extension hnu_isometry hagree, ?_, rfl, ?_, ?_, ?_⟩
  · exact typeIHyp.typeI.typeF.H_eq
  · -- **Peterfalvi (7.6)/(14.10)**: the induced principal `ζ_{ind1H} = Ind_K 1_K` has
    -- degree `[M:K]` at `1` (`θ ind1H = 1_K` + `induce_trivialChar_apply_eq_index`).
    change ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
        (θ ind1H : ClassFunction _ ℂ) (1 : M)
        = (((maxNilpotentNormalHall M).subgroupOf M).index : ℂ)
    rw [htriv, ← typeIHyp.typeI.typeF.H_eq]
    exact induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)
  · -- **Peterfalvi (7.8)**: the distinguished `ζ = ζ_0 = Ind_K θ_0` (`θ_0 ≠ 1_K`) is irreducible
    -- (Frobenius, [Is] 6.34), hence `‖ζ‖² = 1` — the `ζ_0` unit-norm input to the (7.5)/(7.8)
    -- machinery.
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf M) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    change ClassFunction.inner
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
          (θ 0 : ClassFunction _ ℂ))
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
          (θ 0 : ClassFunction _ ℂ)) = 1
    exact inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne
  · -- **Peterfalvi (7.8.b)**: the coherence-norm lower bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²` for the
    -- `V`-side `M`, via the concrete §7 producer `zetaNuRhoNormSqGeOfDade` (the `V`-side dual of
    -- `witness_L_zeta_bound`): feed the Dade witness `Hypothesis78` its four genuine (7.8) inputs —
    -- `ζ_0^ν ⊥ 1_G` (`witness_L_hzeta0nu`), `‖ζ_0‖² = 1` (Frobenius), `(β, ζ_0^ν) + 1 ∈ ℤ`
    -- (`exists_betaDecomp_a`), and `2e + 1 ≤ h`
    -- (`frobenius_two_mul_card_complement_add_one_le_card_kernel`).
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf M) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf M)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    set H78 := hypothesis78OfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree with hH78def
    have hKcard : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf M)
        = Nat.card typeIHyp.typeI.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    have hKodd : Odd (Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf M)) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card _)
    have hCodd : Odd (Nat.card ↥C) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card C)
    obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
      (coh.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
    have hsmall : H78.smallIndex := by
      have hfrobB :=
        OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
        hFrobG hKodd hCodd hFrobG.ne_bot_kernel
      change 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
      have hke : H78.kernelOrder = Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf M) := by
        rw [hKcard]; rfl
      have hcompl : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf M) * Nat.card ↥C
          = Nat.card ↥M := hFrobG.isComplement.card_mul_card
      have hce : H78.complementIndex = Nat.card ↥C := by
        change Nat.card ↥M / Nat.card typeIHyp.typeI.typeF.H = Nat.card ↥C
        rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
      rw [hke, hce]; exact hfrobB
    exact zetaNuRhoNormSqGeOfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree
      (OddOrder.Peterfalvi.S14.witness_L_hzeta0nu hG typeIHyp hFrobG coh hAH (θ 0) hθ0_ne)
      (inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne) a ha hsmall

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: a type-I maximal subgroup `M` over `N_G(V)` together
with its Dade data exists.  Symmetric to `exists_LHypothesis`, packaging (13.17)
for the `V`-side with the Dade data and the virtual character `β_M` of (14.10).

The structural subgroup and the faithful (13.17.c)-dual index dichotomy come from
`S15.exists_M_structural_dichotomy`.  The complete §5--§8 character data then comes from
`TypeICoherent78Data.nonempty`: one bundle supplies the Dade setup, coherent extension, placed
family, distinguished `ψ = ζ₀`, and its canonical `Hypothesis78`.  Thus `τ`, `τ₁`, `ψ`, and `β_M`
are computed accessors of the same bundle rather than independently chosen carrier fields.

The TI / normalizer facts are the `base_*` helpers.  The two `G0` covering facts are elementary
set algebra on the (14.11.3) complement
`G₀ = G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`.

No conclusion of (14.11) is packaged here: `e = p q`, the `±1` signs, and the η-grid expansion
are produced only in the `K ≠ V` branch by `betaM_expansion_data`. -/
theorem exists_MHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (MHypothesis hyp) := by
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply
  obtain ⟨M, structuralHyp, hM_max, hnorm_V, hindexCases⟩ :=
    OddOrder.Peterfalvi.S15.exists_M_structural_dichotomy_of_c_eq_one
      _hG hnoV hyp.base hc1 hTII
  obtain ⟨dataM⟩ :=
    TypeICoherent78Data.nonempty _hG hnoV hM_max ⟨structuralHyp.typeI⟩
  refine ⟨{
    M := M
    K := maxNilpotentNormalHall M
    M_maximal := hM_max
    normalizer_V_le_M := hnorm_V
    K_eq_MF := rfl
    hG := _hG
    coherent78 := dataM
    e := ((maxNilpotentNormalHall M).subgroupOf M).index
    k := Nat.card ↥(maxNilpotentNormalHall M)
    e_eq_index := rfl
    complementIndex_cases := hindexCases
    k_eq_card_K := rfl
    G0 := Set.univ \ (dataM.typeIHyp.dadeData.dade.dadeSupport ∪
      (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ conjClassSet (sharpSubgroup hyp.base.P)
        ∪ conjClassSet (sharpSubgroup hyp.base.Q)))
    G0_off_dadeSupport := ?offDade
    G0_orbit_cover := ?orbCover
    G0_avoid := ?avoid
    W_normalizer_V := base_W_normalizer_V hyp
    P_isTI := base_P_isTI _hG hyp
    Q_isTI := base_Q_isTI _hG hyp hTII
    card_normalizer_P_eq := base_card_normalizer_P_eq _hG hyp
    card_normalizer_Q_eq := base_card_normalizer_Q_eq _hG hyp hTII
  }⟩
  case offDade =>
    intro g hg hin
    exact hg.2 (Set.mem_union_left _ hin)
  -- **Peterfalvi (14.11.3)**: the concrete `G₀` avoids the three singular orbits — direct
  -- set algebra on the defining complement.
  case avoid =>
    intro g hg
    exact ⟨fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_left _ h))),
      fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_right _ h))),
      fun h => hg.2 (Set.mem_union_right _ (Set.mem_union_right _ h))⟩
  case orbCover =>
    intro g hgd hg0
    have hmem : g ∈ dataM.typeIHyp.dadeData.dade.dadeSupport ∪
        (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
          ∪ conjClassSet (sharpSubgroup hyp.base.P)
          ∪ conjClassSet (sharpSubgroup hyp.base.Q)) := by
      by_contra h
      exact hg0 ⟨Set.mem_univ g, h⟩
    rcases hmem with h | h
    · exact absurd h hgd
    · exact h

/-- **Peterfalvi (14.16)**→(14.7) bridge: if the Fitting kernel `H` of `L`
coincides with `U`, then `U` is characteristic in `H` — it is the whole of `H`,
and `⊤` is characteristic.  This is what lets the non-conjugate case `H = U` of
(14.16) feed back into (14.7). -/
theorem U_characteristic_of_H_eq_U {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (hHU : Ldata.H = hyp.base.U) :
    (hyp.base.U.subgroupOf Ldata.H).Characteristic := by
  have htop : hyp.base.U.subgroupOf Ldata.H = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (le_of_eq hHU)
  rw [htop]
  exact Subgroup.topCharacteristic

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses.

This assembles Peterfalvi's concluding paragraph "By (14.12), (14.16) and (14.7),
the proof of Theorem (14.2) is complete."  Take the type-I subgroup `L` over
`N_G(U)` ((14.3), `exists_LHypothesis`) and split on whether `U` is characteristic
in `H`:

* if it is, (14.7) `field_normalizer_of_U_characteristic` finishes;
* otherwise take the type-I subgroup `M` over `N_G(V)` ((14.10),
  `exists_MHypothesis`) and split on whether `L` is conjugate to `M`:
  * if it is, (14.12) `field_normalizer_of_L_conj_M` finishes;
  * otherwise (14.13)–(14.16) `H_eq_U` give `H = U`, so `U` is characteristic in
    `H` (`U_characteristic_of_H_eq_U`), contradicting the branch assumption. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  by_cases hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic
  · exact field_normalizer_of_U_characteristic _hG hnoV hncH0C hyp Ldata hchar
  · obtain ⟨Mdata⟩ := exists_MHypothesis _hG hnoV hncH0C hyp
    by_cases hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
    · exact field_normalizer_of_L_conj_M _hG hnoV hncH0C hyp Ldata Mdata hconj
    · exact absurd
        (U_characteristic_of_H_eq_U Ldata
          (H_eq_U _hG hnoV hncH0C hyp
            { Ldata := Ldata, Mdata := Mdata, not_conj := hconj,
              h := Nat.card ↥Ldata.H, h_eq_card_H := rfl }))
        hchar

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hnoV hncH0C hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16
