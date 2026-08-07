/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.OrderRelayerCore
import OddOrder.Peterfalvi.S15_CharacterDegreeSupply

/-!
# Peterfalvi §13 (pp. 85–86) — Core-typed order consequences

This downstream leaf discharges the Core order API using the honest (13.3.b) dichotomy and
actual Clifford certificates, rather than the legacy `CharacterDegreeData` carrier.
-/

namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section /- (13.11)–(13.15): consequences of the Core analytic inequality -/

/-- **Peterfalvi (13.10), the book statement** — *"Suppose that `𝒮` contains an irreducible
character `λ` of degree `uq` induced from a linear character of `PC`. Let
`m = 1 − 1/(q−1) − (q−1)/q^p + 1/((q−1)q^p)`.  Then `u/c > m·p^{q−1}/q`"* (p. 79).

The Core endpoint `analytic_inequality_of_caseB_facts` carries three inputs the book does not
state as hypotheses, because in the book they are *consequences* of the λ-cluster:
* `hD`/`hv` — the case-B facts `D = 1`, `v = (q^p−1)/(q−1)`, which are exactly (13.4)
  (`lambda_forces_T_caseB_core`), the very first step of the (13.10) proof;
* `hQcomm` — commutativity of `Q = T_F`, from (13.2.b) applied to `T`
  (`Hypothesis.Q_elementaryAbelian`).

Discharging all three here gives the book's own hypothesis/conclusion pair (issue 0172 §13
audit).  `core` is `characterDegreeCore_nonempty`; `pins` is the ν-side grid supply that the
book's "in this section `S` and `T` play the same role" remark provides. -/
theorem Hypothesis.analytic_inequality_of_lambdaCluster [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (lam : LambdaClusterData hyp) (pins : NuGridSupplyData hyp) :
    (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
  have hQcomm : IsMulCommutative ↥hyp.Q :=
    IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
  exact core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins

/-- **Peterfalvi (13.11), the book statement** — *"Under the hypothesis of (13.10) we have:
(a) if `q ≥ 7` then `m > 8/10`; (b) if `q ≥ 5` then `m > 7/10`; (c) if `q = 3` then
`m > 49/100` and `u/c > (p²−1)/6`"* (p. 81), with the book's own hypothesis (the λ-cluster of
(13.10)) rather than the Core endpoint's case-B inputs.  Purely numerical consequence of
`analytic_inequality_of_lambdaCluster` via `numeric_bounds_of_analytic_inequality`. -/
theorem Hypothesis.numeric_bounds_of_lambdaCluster [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (lam : LambdaClusterData hyp) (pins : NuGridSupplyData hyp) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) :=
  numeric_bounds_of_analytic_inequality hyp
    (hyp.analytic_inequality_of_lambdaCluster hG lam pins)

/-- **Peterfalvi (13.12), honest dichotomy form**: `c = 1`.

This is the unconditional replacement for the legacy monolithic character-degree carrier.
If the (13.3.b) λ-cluster exists, `lambda_forces_T_caseB_core` supplies the `T`-side case-B
facts and the general type-`P` theorem `Q_elementaryAbelian` supplies the commutativity needed
by the Core analytic endpoint.  This avoids the circular route through the later (14.9)
`T_typeII`, whose character proof itself consumes (13.12).  If no λ-cluster exists, the
faithful Galois branch already gives `C = ⊥`. -/
theorem Hypothesis.c_eq_one_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.c = 1 := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨hCbot, _hu⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, _hQ⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.c_eq_one_of_caseB_facts hG lam hD hv hQcomm pins
  · exact hyp.c_eq_card_C.trans (Subgroup.card_eq_one.mpr hCbot)

/-- **Peterfalvi (13.13), honest Clifford-case form**: an actual case-(9.7.a)
certificate supplies its own λ-witness, so the Core analytic relayer gives the sharp
parameters without the legacy monolithic character-degree carrier. -/
theorem Hypothesis.caseA_parameters_of_clifford_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := lambdaWitness_of_caseA hG hyp chief caseA
  obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
  have hQcomm : IsMulCommutative ↥hyp.Q :=
    IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
  exact core.caseA_parameters_of_caseB_facts hG lam hD hv hQcomm pins caseA

/-- **Peterfalvi (13.15), honest λ-dichotomy form**: an actual Clifford case-(9.7.b)
certificate has the two Singer-order alternatives without using the legacy character-degree
carrier.  In the λ-branch the Core analytic relayer proves (13.15).  In the no-λ Galois branch
`u` already has the full Singer order; the `p ≡ 1 (mod q)` alternative is impossible because
that congruence makes `q` divide the Singer quotient while the Frobenius congruence
`u ≡ 1 (mod q)` gives `q ∤ u`. -/
theorem Hypothesis.caseB_order_u_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  have hq_not_dvd_u : ¬ hyp.q ∣ hyp.u := by
    intro hqu
    have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := hqu
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨_hCbot, hufull⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.caseB_order_u_of_caseB_facts hG lam hD hv hQcomm pins caseB
  · refine ⟨?_, fun _ => hufull⟩
    intro hmod
    have hqdvd : hyp.q ∣ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) :=
      cyclotomic_quotient_dvd_of_modEq_one hyp.p_prime hmod
    have hqu : hyp.q ∣ hyp.u := by rwa [hufull]
    exact (hq_not_dvd_u hqu).elim

end

end OddOrder.Peterfalvi.S15
