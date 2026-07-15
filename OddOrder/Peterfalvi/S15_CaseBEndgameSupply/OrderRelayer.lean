/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.AnalyticRelayer
import OddOrder.Peterfalvi.S15_SAndT_Setup.CaseBOrder

/-!
# Peterfalvi §13 (pp. 85–86) — Core-typed order consequences

This file feeds the honest Core endpoint for (13.10) into the arithmetic and order-theoretic
engines for (13.11)–(13.15).  The resulting API depends on `CharacterDegreeCore`,
`LambdaClusterData`, and explicit case-B facts, rather than the legacy `CharacterDegreeData`
carrier.
-/

namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section /- (13.11)–(13.15): consequences of the Core analytic inequality -/

/-- **Peterfalvi (13.11), Core form**: the numerical bounds for `m`, supplied by the
Core character-degree analysis and explicit case-B structural facts. -/
theorem CharacterDegreeCore.numeric_bounds_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  exact numeric_bounds_of_analytic_inequality hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm)

/-- **Peterfalvi (13.12), Core form**: the centralizer parameter `c` is one, using the
Core analytic inequality instead of the legacy norm-cascade carrier. -/
theorem CharacterDegreeCore.c_eq_one_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) :
    hyp.c = 1 := by
  exact c_eq_one_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm)

/-- **Peterfalvi (13.13), Core form**: Clifford case (9.7.a) forces the sharp parameters,
with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseA_parameters_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  exact caseA_parameters_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm) caseA

/-- **Peterfalvi (13.15), Core form**: Clifford case (9.7.b) determines the Singer
cyclotomic order of `u`, with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseB_order_u_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  exact caseB_order_u_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm) caseB

end

end OddOrder.Peterfalvi.S15
