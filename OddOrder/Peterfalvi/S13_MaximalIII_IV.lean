/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V
import OddOrder.GroupTheory.ElementaryAbelian

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
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (11.1): the auxiliary prime inequality -/

/-- For `n >= 5`, the elementary estimate used in **Peterfalvi (11.1)**. -/
private theorem four_mul_sq_add_one_lt_three_pow {n : ℕ} (hn : 5 ≤ n) :
    4 * n ^ 2 + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      have hstep : 4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := by
        nlinarith [hn]
      calc
        4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := hstep
        _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 ih.le
        _ = 3 ^ (n + 1) := by rw [pow_succ]; omega

/-- **Peterfalvi (11.1)**: if `p` and `q` are distinct odd primes, then
`p^q > 4 q^2 + 1`. -/
theorem prime_pow_gt_four_mul_sq_add_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q) :
    4 * q ^ 2 + 1 < p ^ q := by
  have hp_three : 3 ≤ p := by
    have hp_two : 2 ≤ p := hp.two_le
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      rcases hpodd with ⟨k, hk⟩
      omega
    omega
  have hq_three : 3 ≤ q := by
    have hq_two : 2 ≤ q := hq.two_le
    have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    omega
  rcases lt_trichotomy p q with hp_lt_q | hp_eq_q | hq_lt_p
  · have hq_five : 5 ≤ q := by
      have hpq_succ : p + 1 ≤ q := Nat.succ_le_of_lt hp_lt_q
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        subst q
        rcases hqodd with ⟨k, hk⟩
        omega
      omega
    calc
      4 * q ^ 2 + 1 < 3 ^ q := four_mul_sq_add_one_lt_three_pow hq_five
      _ ≤ p ^ q := Nat.pow_le_pow_left hp_three q
  · exact (hpq hp_eq_q).elim
  · have hbase : q + 1 ≤ p := Nat.succ_le_of_lt hq_lt_p
    have hqpow_le : (q + 1) ^ q ≤ p ^ q := Nat.pow_le_pow_left hbase q
    have hqpow_large : 4 * q ^ 2 + 1 < (q + 1) ^ q := by
      have hqpow_three : (q + 1) ^ 3 ≤ (q + 1) ^ q :=
        pow_le_pow_right' (by omega) hq_three
      have hpoly : 4 * q ^ 2 + 1 < (q + 1) ^ 3 := by
        nlinarith [hq_three]
      exact hpoly.trans_le hqpow_three
    exact hqpow_large.trans_le hqpow_le

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
  /-- **(11.2)**: `C = C_U(H)`, the centralizer of `H` in `U`. -/
  C_eq_centralizer :
    C = base.typeP.U ⊓ Subgroup.centralizer (base.typeP.H : Set G)
  Hprime : Subgroup G
  Hprime_eq : Hprime = derivedInG base.typeP.H
  Uprime : Subgroup G
  Uprime_eq : Uprime = derivedInG base.typeP.U
  SOf : Subgroup G → Set (ClassFunction ↥M ℂ)
  quotientBoundFormula : Subgroup G → Prop
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

/-- **Peterfalvi (11.5), inclusion `M'' ⊆ HC` (= (8.4.c)/(8.5.a))**: the second derived
subgroup is contained in `HC`.  This is the unconditional half of (11.5); it follows from
the type-`P` Fitting bound `TypePData.secondDerived_le_fitting` (`M'' ≤ H ⊔ (U ∩ C_G(H))`,
Peterfalvi (8.5.a)) together with `C = C_U(H) = U ∩ C_G(H)` (the `C_eq_centralizer` field).
The reverse inclusion is the coherence content carried by `S13.secondDerived_eq_HC`. -/
theorem secondDerived_le_HC {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.HC := by
  change secondDerivedInAmbient M ≤ hyp.base.typeP.H ⊔ hyp.C
  rw [hyp.C_eq_centralizer]
  exact hyp.base.typeP.secondDerived_le_fitting

/-- **Peterfalvi (11.6), inclusion `U' ⊆ C`**: the derived subgroup `U' = [U,U]` is contained
in `C = C_U(H)`.  This is the unconditional half of the `C = U'` clause of (11.6): `[U,U]`
centralizes `H` (Peterfalvi (8.5.b), `S11.typeP_commutator_U_centralizes_H`) and lies in `U`,
so `U' = [U,U] ⊆ U ∩ C_G(H) = C`.  The reverse inclusion `C ⊆ U'` is the coherence content
carried by `S13.core_structure`. -/
theorem derivedU_le_C {M : Subgroup G} (hyp : Hypothesis M) :
    derivedInG hyp.U ≤ hyp.C := by
  change derivedInG hyp.base.typeP.U ≤ hyp.C
  rw [hyp.C_eq_centralizer]
  refine le_inf (Subgroup.map_subtype_le _) ?_
  rw [show derivedInG hyp.base.typeP.U = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
        from Subgroup.map_subtype_commutator hyp.base.typeP.U]
  exact OddOrder.Peterfalvi.S11.typeP_commutator_U_centralizes_H hyp.base.typeP

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
    (hH1_lt : H1 < derivedInG M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0)) :
    hyp.quotientBoundFormula H1 := by
  sorry

/-- **Peterfalvi (11.5)**: the second derived subgroup is `H C`, i.e. `M'' = HC`. -/
theorem secondDerived_eq_HC [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M = hyp.HC := by
  refine le_antisymm hyp.secondDerived_le_HC ?_
  -- Reverse inclusion `HC ⊆ M''`: since `M'/M''` is abelian, `S(M'')` is coherent (5.7);
  -- the quotient bound (11.4) with (11.1)/(9.6) forces `M'' = HC`.  Coherence-gated: this
  -- bottoms out in Theorem (10.8) [`S12.S_not_coherent`] via (11.3)/(11.4).
  sorry

/-! ## (11.6)--(11.7): the core structure of `H` and `U` -/

/-- **Peterfalvi (11.6)**: `H` is a `p`-group, `U` centralizes `H_0`, `H_0 = H'`, and `C = U'`.

The inclusion `U' ⊆ C` of the last clause is unconditional (`Hypothesis.derivedU_le_C`,
from (8.5.b)); the remaining content needs (9.3) [`U` centralizes `O_{p'}(H)`], (9.6)
[`C_{H_0}(W_1) = 1`] with (9.1) Wielandt, `[BG] 1.6(d)`, and (11.5) `secondDerived_eq_HC`
(itself coherence-gated). -/
theorem core_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsPGroup hyp.p ↥hyp.H ∧
      hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) ∧
      hyp.chief.H0 = hyp.Hprime ∧ hyp.C = hyp.Uprime := by
  sorry

/-- **Peterfalvi (11.7)**: `H` is elementary abelian of order `p^q`, and
`H_0 = 1`. -/
theorem H_elementaryAbelian [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsElementaryAbelian hyp.p ↥hyp.H ∧ Nat.card ↥hyp.H = hyp.p ^ hyp.q ∧
      hyp.chief.H0 = ⊥ := by
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
    data.coefficientA = 0 :=
  -- (11.8.5) is carried as the `coefficient_zero` field of `OrthogonalityData`; the
  -- real `a = 0` content lives in `orthogonality_setup` (11.8.1)-(11.8.4), which
  -- constructs the data.  This is the intended public-name wiring for that field.
  data.coefficient_zero

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
