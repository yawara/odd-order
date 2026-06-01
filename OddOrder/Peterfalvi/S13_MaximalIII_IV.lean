/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V

/-!
# Peterfalvi Section 13: Maximal Subgroups of Types III and IV

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 13, pp. 64--68.

This section specializes the type-III/IV/V setup of §12 to types III and IV.  It
establishes the commutator-layer identities `M'' = H C`, `H_0 = H'`, `C = U'`,
then proves that `H` is elementary abelian of order `p^q`.  The final character
calculation (11.8)--(11.9) rules out the reducible Clifford case and identifies
the subgroup as type III.

The scaffold keeps the structural and orthogonality calculations as named
propositions on the §13 hypothesis.  This gives later sections stable endpoints
without pretending that the quotient-module and `omega_ij^sigma` API is already
available.
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (11.1): the auxiliary prime inequality -/

/-- **Peterfalvi (11.1)**: if `p` and `q` are distinct odd primes, then
`p^q > 4 q^2 + 1`. -/
theorem prime_pow_gt_four_mul_sq_add_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q) :
    4 * q ^ 2 + 1 < p ^ q := by
  sorry

/-! ## (11.2): Type III/IV setup -/

/-- **Peterfalvi (11.2)**: the Type III/IV specialization of §12.

`SOf X` is Peterfalvi's `S(X) = {chi in S | X <= Ker chi}`.  The fields ending
in `Formula` are the named algebraic or character-theoretic calculations proved
throughout §13. -/
structure Hypothesis (M : Subgroup G) where
  base : OddOrder.Peterfalvi.S12.Hypothesis M
  params : OddOrder.Peterfalvi.S12.CharacterParameters base
  type_alt : IsTypeIII M ∨ IsTypeIV M
  s11Setup : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M
  chief : OddOrder.Peterfalvi.S11.ChiefFactorData s11Setup
  C : Subgroup G
  C_le_U : C ≤ base.typeP.U
  C_eq_centralizer : Prop
  Hprime : Subgroup G
  Hprime_eq : Hprime = derivedInAmbient base.typeP.H
  Uprime : Subgroup G
  Uprime_eq : Uprime = derivedInAmbient base.typeP.U
  SOf : Subgroup G → Set (ClassFunction ↥M ℂ)
  quotientBoundFormula : Subgroup G → Prop
  secondDerived_eq_HC : Prop
  H_is_pgroup : Prop
  U_centralizes_H0 : Prop
  H0_eq_Hprime : Prop
  C_eq_Uprime : Prop
  H_elementaryAbelian : Prop
  H_order_prime_power : Nat.card ↥base.typeP.H = base.w2 ^ base.w1
  H0_eq_bot : chief.H0 = ⊥
  notOrthogonalFormula : ClassFunction ↥M ℂ → Prop
  finalOrthogonalityFormula : ClassFunction ↥M ℂ → Prop
  caseB_of_97 : Prop

namespace Hypothesis

/-- Peterfalvi's `H`. -/
def H {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.base.typeP.H

/-- Peterfalvi's `U`. -/
def U {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.base.typeP.U

/-- Peterfalvi's `p = |W_2|`. -/
noncomputable def p {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  hyp.base.w2

/-- Peterfalvi's `q = |W_1|`. -/
noncomputable def q {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  hyp.base.w1

/-- Peterfalvi's `H_0 C`. -/
def H0C {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.chief.H0 ⊔ hyp.C

/-- Peterfalvi's `H C`. -/
def HC {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.H ⊔ hyp.C

end Hypothesis

/-! ## (11.3)--(11.5): commutator-chain consequences -/

/-- **Peterfalvi (11.3)**: `S(H_0 C)` is not coherent. -/
theorem S_H0C_not_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := by
  sorry

/-- **Peterfalvi (11.4)**: if `S(H_1)` is coherent for a normal subgroup
`H_1 < M'`, then the quotient bound from Theorem (6.2) holds. -/
theorem coherent_quotient_bound [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H1 : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (hH1_norm : M ≤ Subgroup.normalizer (H1 : Set G))
    (hH1_lt : H1 < derivedInAmbient M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0)) :
    hyp.quotientBoundFormula H1 := by
  sorry

/-- **Peterfalvi (11.5)**: the second derived subgroup is `H C`. -/
theorem secondDerived_eq_HC [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.secondDerived_eq_HC := by
  sorry

/-! ## (11.6)--(11.7): the core structure of `H` and `U` -/

/-- **Peterfalvi (11.6)**: `H` is a `p`-group, `U` centralizes `H_0`,
`H_0 = H'`, and `C = U'`. -/
theorem core_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H_is_pgroup ∧ hyp.U_centralizes_H0 ∧ hyp.H0_eq_Hprime ∧ hyp.C_eq_Uprime := by
  sorry

/-- **Peterfalvi (11.7)**: `H` is elementary abelian of order `p^q`, and
`H_0 = 1`. -/
theorem H_elementaryAbelian [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H_elementaryAbelian ∧ Nat.card ↥hyp.H = hyp.p ^ hyp.q ∧ hyp.chief.H0 = ⊥ := by
  sorry

/-! ## (11.8): the main orthogonality calculation -/

/-- Carrier for the five substeps of Peterfalvi (11.8). -/
structure OrthogonalityData {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_SHC : zeta ∈ hyp.SOf hyp.HC
  S1 : Set (ClassFunction ↥M ℂ)
  S2 : Set (ClassFunction ↥M ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau2 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  beta : ClassFunction G ℂ
  coefficientA : ℤ
  frobenius_setup : Prop
  omega_support_reduction : Prop
  average_formula : Prop
  coefficient_formula : Prop
  coefficient_zero : coefficientA = 0
  conclusion_formula : Prop

/-- **Peterfalvi (11.8.1)--(11.8.4)**: the setup for the coefficient calculation
in the proof of (11.8). -/
theorem orthogonality_setup [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ data : OrthogonalityData hyp,
      data.frobenius_setup ∧ data.omega_support_reduction ∧
        data.average_formula ∧ data.coefficient_formula := by
  sorry

/-- **Peterfalvi (11.8.5)**: the coefficient `a` in the orthogonality
calculation is zero. -/
theorem orthogonality_coefficient_zero [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    data.coefficientA = 0 := by
  sorry

/-- **Peterfalvi (11.8)**: for `zeta in S(HC)`, the residual character is not
orthogonal to `(Irr W)^sigma`. -/
theorem not_orthogonal_mu0_sub_zeta [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.notOrthogonalFormula data.zeta := by
  sorry

/-! ## (11.9): final Type III conclusion -/

/-- **Peterfalvi (11.9)**: the final three conclusions of §13: the symmetric
orthogonality statement, `q > p`, and the fact that case (b) of (9.7) holds,
so `M` is of type III. -/
theorem final_typeIII_conclusions [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.finalOrthogonalityFormula data.zeta ∧ hyp.q > hyp.p ∧
      hyp.caseB_of_97 ∧ IsTypeIII M := by
  sorry

end OddOrder.Peterfalvi.S13
