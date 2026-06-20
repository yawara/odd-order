/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI
import OddOrder.Peterfalvi.S10_CoherenceWiring
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Peterfalvi Section 15: The Subgroups S and T

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 15, pp. 75--86.

This section works under the case-(b) alternative of Theorem (8.8), whose
existence was forced in Section 14.  It fixes the two maximal subgroups `S` and
`T`, their common cyclic subgroup `W = W_1 W_2`, the Fitting kernels `P` and
`Q`, and the Dade character grids `omega`, `eta`, `mu`, and `nu`.

The scaffold follows the four blocks of the text:

* (13.1)--(13.4): setup, type determination, and character degrees;
* (13.5)--(13.10): norm estimates and the analytic inequality;
* (13.11)--(13.15): the numerical contradiction giving `c = 1` and `u`;
* (13.16)--(13.19): normalizers, Frobenius structure, and type-I interaction.

The character-grid identities (13.1.d,e) are materialized as genuine equalities
`η_{ij} = τ(ω_{ij})` and `Ind_W^{S/T}(ω_{ij} − ω) = ±(μ/ν - μ/ν)` over carried
`ℂ`-linear transfer maps `tau3`/`indWS`/`indWT`.  This forces the `η`/`μ`/`ν`
grids to be linear images of the `ω`-grid (a genuine, non-vacuous constraint);
pinning those maps to the concrete (3.2)/(4.3) constructions is the remaining
§3/§4 layer.
-/

namespace OddOrder.Peterfalvi.S15
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/- Scoped instances that make canonical `ClassFunction.induce` usable inside the
`(13.1)` hypothesis-structure field types (`Ind_W^S`, `Ind_W^T`).  Kept `scoped`
so the `noncomputable` `Fintype`/`Invertible` data is contained: it is opened only
for the `Hypothesis` structure (and for proofs that manipulate `mu_definition` /
`nu_definition`), never leaking globally. -/
namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

/-! ## (13.1): the `S,T` hypothesis -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.1)**: the main setup for the two maximal subgroups `S` and
`T` in case (b) of Theorem (8.8).

`G` is finite (carried as the instance field `finiteG`, so consumers need not
re-assume `[Finite G]`); this finiteness is what makes the canonical inductions
`Ind_W^S`/`Ind_W^T` in `mu_definition`/`nu_definition` well-defined. -/
structure Hypothesis where
  [finiteG : Finite G]
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  P : Subgroup G
  Q : Subgroup G
  U : Subgroup G
  V : Subgroup G
  C : Subgroup G
  D : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  theorem88_caseB :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
        (∃ g : G, MulAut.conj g • M = T)
  W_eq_inter : W = S ⊓ T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  P_eq_SF : P = maxNilpotentNormalHall S
  Q_eq_TF : Q = maxNilpotentNormalHall T
  S_deriv_eq_PU : derivedInG S = P ⊔ U
  T_deriv_eq_QV : derivedInG T = Q ⊔ V
  C_eq : C = U ⊓ Subgroup.centralizer (P : Set G)
  D_eq : D = V ⊓ Subgroup.centralizer (Q : Set G)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_odd : Odd q
  p_odd : Odd p
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥C
  d_eq_card_D : d = Nat.card ↥D
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  Sset : Set (ClassFunction ↥S ℂ)
  Tset : Set (ClassFunction ↥T ℂ)
  A0S : Set ↥S
  A0T : Set ↥T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥T G
  omega : Fin q → Fin p → ClassFunction ↥W ℂ
  eta : Fin q → Fin p → ClassFunction G ℂ
  mu : Fin q → Fin p → ClassFunction ↥S ℂ
  nu : Fin q → Fin p → ClassFunction ↥T ℂ
  delta : Fin p → ℤ
  deltaPrime : Fin q → ℤ
  /-- The Peterfalvi (3.2)/(3.3) transfer map `τ`, typed as an integral
  (virtual-character) map via the same `IntegralCharacterMap` convention as
  `tauS`/`tauT` — faithful to `τ` being defined on the `ℤ`-lattice of virtual
  characters.  Pinning `tau3` to the *concrete* (3.2) Dade isometry (built from a
  `S05.TICyclicHypothesis` for `W` through `S04.dadeIntegralCharacterMap`, with the
  `ω`-grid materialized as the (3.3) characters) is a dedicated §3/§5 construction;
  `eta_eq_tau_omega` already forces the `η`-grid to be the integral-linear image of
  the `ω`-grid. -/
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  /-- **Peterfalvi (13.1.d)**: `η_{ij} = ω_{ij}^τ`. -/
  eta_eq_tau_omega : ∀ (i : Fin q) (j : Fin p), eta i j = tau3 (omega i j)
  /-- **Peterfalvi (13.1.e)**: `Ind_W^S (ω_{ij} − ω_{0j}) = δ_j (μ_{ij} − μ_{0j})`,
  where the induction is the canonical `Ind_W^S = ClassFunction.induce (W.subgroupOf S)`
  (transporting the `W`-grid into `S` via `W ≤ S`) and `δ_j = ±1` is `delta`. -/
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  /-- **Peterfalvi (13.1.e)**: `Ind_W^T (ω_{ij} − ω_{i0}) = δ'_i (ν_{ij} − ν_{i0})`,
  with the canonical `Ind_W^T = ClassFunction.induce (W.subgroupOf T)` and
  `δ'_i = ±1` is `deltaPrime`. -/
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  m : ℚ
  m_eq : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
    1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)

namespace Hypothesis

/-- Peterfalvi's `H = P C` in (13.5)--(13.10). -/
def H (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.P ⊔ hyp.C

/-- Peterfalvi's `K = Q D`, used symmetrically for `T`. -/
def K (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.Q ⊔ hyp.D

/-- The generic set `G_0 = G# - ((H#)^G union (Q#)^G)` from (13.9). -/
def G0 (hyp : Hypothesis (G := G)) : Set G :=
  sharpSubgroup (⊤ : Subgroup G) \
    (conjClassSet (sharpSubgroup hyp.H) ∪
      conjClassSet (sharpSubgroup hyp.Q))


/-- Under **Peterfalvi (13.1)**, the prime `q` is odd, hence not `2`. -/
theorem q_ne_two (hyp : Hypothesis (G := G)) : hyp.q ≠ 2 := by
  intro hq2
  have hodd : Odd 2 := by simpa [hq2] using hyp.q_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, the prime `p` is odd, hence not `2`. -/
theorem p_ne_two (hyp : Hypothesis (G := G)) : hyp.p ≠ 2 := by
  intro hp2
  have hodd : Odd 2 := by simpa [hp2] using hyp.p_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, `q` is at least `3`. -/
theorem three_le_q (hyp : Hypothesis (G := G)) : 3 ≤ hyp.q := by
  have htwo : 2 ≤ hyp.q := hyp.q_prime.two_le
  have hne : hyp.q ≠ 2 := hyp.q_ne_two
  omega

/-- Under **Peterfalvi (13.1)**, `p` is at least `3`. -/
theorem three_le_p (hyp : Hypothesis (G := G)) : 3 ≤ hyp.p := by
  have htwo : 2 ≤ hyp.p := hyp.p_prime.two_le
  have hne : hyp.p ≠ 2 := hyp.p_ne_two
  omega
end Hypothesis

/-! ## (13.2): basic structure -/

/-- Carrier for the basic structural conclusions of Peterfalvi (13.2). -/
structure BasicStructureData (hyp : Hypothesis (G := G)) where
  S_typeII_or_typeIII : IsTypeII hyp.S ∨ IsTypeIII hyp.S
  q_lt_p_forces_typeII : hyp.q < hyp.p → IsTypeII hyp.S
  U_commutative : IsMulCommutative ↥hyp.U
  UW1_frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
      (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **Peterfalvi (13.2.a--c,e)**: `S` is type II or III, `P` is elementary
abelian of order `p^q`, `u` is bounded, and `A_0(S)` is a TI-subset. -/
theorem basic_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : BasicStructureData hyp,
      (IsTypeII hyp.S ∨ IsTypeIII hyp.S) ∧ IsElementaryAbelian hyp.p ↥hyp.P ∧
        Nat.card ↥hyp.P = hyp.p ^ hyp.q ∧
        hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ∧ data.A0S_TI := by
  sorry

/-- **Structural input for Peterfalvi (13.2.d) — §14-gated.**

The type II/III maximal subgroup `S` carries the Sibley Dade setup of (6.8) realizing its
integral character map `tauS`, base family `Sset`, and support `A0S` (a `SibleyTarget`).
Exhibiting this witness is the maximal-subgroup structure obligation of Pf §14 — exactly what
Peterfalvi's proof of (13.2.d) reads off before invoking "(6.8) applies to `S`".  It is the sole
remaining gap in `S_coherent`: once it lands, and once lane B supplies the (6.8) proof body of
`S08.sibleySetup_is_coherent`, `S_coherent` is unconditional. -/
noncomputable def sibleyTarget_S [Fintype G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    CoherenceWiring.SibleyTarget hyp.tauS hyp.Sset hyp.A0S := sorry

/-- **Peterfalvi (13.2.d)**: the family `S` is coherent.

Wired to the (6.8) capstone `S08.sibleySetup_is_coherent` through the coherence-wiring bridge:
given the §14 structural witness `sibleyTarget_S`, coherence is exactly (6.8).  The proof carries
no `sorry` of its own — its dependencies are `sibleyTarget_S` (§14, this file) and (6.8) (lane B),
each of which closes `S_coherent` automatically as it lands. -/
theorem S_coherent [Finite G] [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tauS hyp.Sset hyp.A0S) :=
  CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_S hG hyp)

/-! ## (13.3)--(13.4): character degrees and the first case split -/

/-- Character-degree and Dade-extension data from Peterfalvi (13.3). -/
structure CharacterDegreeData (hyp : Hypothesis (G := G)) where
  tau1S : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G
  tau1T : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G
  lambda : ClassFunction ↥hyp.S ℂ
  lambda_mem : lambda ∈ hyp.Sset
  lambda_irreducible : Prop
  lambda_degree : lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ)
  lambda_induced_from_PC_linear : Prop
  mu_j_linear_induced : Prop
  mu_j_linear_induced_holds : mu_j_linear_induced
  no_lambda_forces_caseB_S : Prop
  /-- **Peterfalvi (13.3.c)**: the signs `δ_j`, `δ'_i` of (13.1.e) are all equal
  to `1` (materialized as a concrete statement about `delta`/`deltaPrime`). -/
  delta_eq_one : (∀ j : Fin hyp.p, hyp.delta j = 1) ∧ (∀ i : Fin hyp.q, hyp.deltaPrime i = 1)
  mu_tau1_formula : Prop
  mu_tau1_formula_holds : mu_tau1_formula
  sign_flip_exception : Prop

/-- **Peterfalvi (13.3)**: the `mu_j` have degree `u q`, the signs are `1`,
and the `tau_1` images are controlled by the `eta_ij` grid. -/
theorem character_degree_analysis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : CharacterDegreeData hyp,
      data.mu_j_linear_induced ∧ data.no_lambda_forces_caseB_S ∧
        data.mu_tau1_formula := by
  sorry

/-- **Peterfalvi (13.4)**: if `S` contains a degree-`u q` character induced
from a linear character of `P C`, then case (9.7.b) holds for `T`, with
`D = 1` and `v = (q^p - 1) / (q - 1)`. -/
theorem lambda_forces_T_caseB [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) (hlambda : chars.lambda_induced_from_PC_linear) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  sorry

/-! ## (13.5)--(13.10): norm estimates -/

/-- Carrier for Peterfalvi (13.5), the TI-subset orthogonality calculation. -/
structure TISubsetOrthogonalityData (hyp : Hypothesis (G := G)) where
  S1 : Set (ClassFunction ↥hyp.S ℂ)
  zeta0 : ClassFunction ↥hyp.S ℂ
  zeta1 : ClassFunction ↥hyp.S ℂ
  chi : ClassFunction G ℂ
  alpha : ClassFunction ↥hyp.H ℂ
  a : ℤ
  alpha_kernel_contains_P : Prop
  point_formula : Prop
  norm_formula : Prop
  alpha_norm_bound : Prop

/-- **Peterfalvi (13.5)**: the TI-subset calculation on `H = P C` gives a
pointwise formula and two norm estimates. -/
theorem tiSubset_character_orthogonality [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : TISubsetOrthogonalityData hyp,
      data.point_formula ∧ data.norm_formula ∧ data.alpha_norm_bound := by
  sorry

/-- Carrier for the norm cascade (13.6)--(13.10). -/
structure NormCascadeData (hyp : Hypothesis (G := G)) where
  chars : CharacterDegreeData hyp
  lambda_norm_lower : Prop
  eta10_norm_lower : Prop
  eta01_norm_lower : Prop
  global_cover : Prop
  global_norm_lower : Prop
  analytic_inequality : Prop

/-- **Peterfalvi (13.6)**: the degree-`u q` character gives the first norm lower
bound on `H#`. -/
theorem lambda_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.lambda_norm_lower := by
  sorry

/-- **Peterfalvi (13.7)**: the character `eta_10` has norm at least `|H#|` on
`H#`. -/
theorem eta10_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.eta10_norm_lower := by
  sorry

/-- **Peterfalvi (13.8)**: the character `eta_01` has the corresponding lower
bound on `H#`. -/
theorem eta01_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.eta01_norm_lower := by
  sorry

/-- **Peterfalvi (13.9)**: outside the conjugates of `H#` and `Q#`, the
characters `lambda^tau1` and `eta_10` cover every element. -/
theorem global_character_bound [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.global_cover ∧ data.global_norm_lower := by
  sorry

/-- **Peterfalvi (13.10)**: the norm estimates imply `u / c > m p^(q-1) / q`. -/
theorem analytic_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp,
      data.analytic_inequality ∧
        (hyp.u : ℚ) / (hyp.c : ℚ) >
          hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  sorry

/-! ## (13.11)--(13.15): order and divisor determination -/

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

/-- The `m`-only part of **Peterfalvi (13.11)**.  The full `numeric_bounds`
theorem below also packages the `u/c` inequality in the `q = 3` branch, so it
still waits for the analytic estimate (13.10). -/
theorem numeric_m_bounds (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 → 5 ≤ hyp.p → hyp.m > (49 / 100 : ℚ)) := by
  exact ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q,
    fun hq3 hp5 => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5⟩

end Hypothesis

/-- **Peterfalvi (13.11)**: the elementary numerical bounds for `m`.

The `q ≥ 7` and `q ≥ 5` bounds are the genuine arithmetic estimates
`m_value_gt_four_fifths` / `m_value_gt_seven_tenths` applied through the now
concrete value `m_eq` (they need only `p ≥ 3`, supplied by `three_le_p`).  The
`q = 3` value bound is available as `m_value_q_three_gt_49_hundredths` under
`p ≥ 5`, which Section 16 supplies from `q < p`; this bundled Section 15
statement still keeps the branch open because its `u/c` bound is the analytic
inequality (13.10). -/
theorem numeric_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  refine ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q, fun hq3 => ?_⟩
  · -- `q = 3`: the `m`-only API needs `p ≥ 5`, and the bundled `u/c` bound
    -- still needs the analytic inequality (13.10).
    sorry

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`. -/
theorem c_eq_one [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.c = 1 := by
  sorry

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`. -/
theorem caseA_parameters [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseA_for_S : Prop) :
    caseA_for_S → hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  sorry

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

/-- The coprimality part of **Peterfalvi (13.14)** when `p` is not `1 mod q`. -/
theorem cyclotomic_quotient_coprime_of_not_modEq_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpmod : p ≡ 1 [MOD p - 1] := Nat.modEq_sub (le_of_lt hp.one_lt)
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD p - 1] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpmod
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  have hmod : (∑ k ∈ Finset.range q, p ^ k) ≡ q [MOD p - 1] := by
    exact hterms.trans (by rw [hsum_one])
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp <|
    hq.coprime_iff_not_dvd.mpr fun hdiv => hpq <| by
      exact ((Nat.modEq_iff_dvd'
        (show 1 ≤ p from le_of_lt hp.one_lt)).mpr hdiv).symm

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  haveI : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_pow_primeFactors_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

/-- **Peterfalvi (13.14)**: divisibility facts for
`(p^q - 1) / (p - 1)`. -/
theorem cyclotomic_divisor_facts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) ∧
      (p ≡ 1 [MOD q] → q ∣ (p ^ q - 1) / (p - 1)) ∧
      (¬ (p ≡ 1 [MOD q]) →
        Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ∧
          ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q]) := by
  refine ⟨cyclotomic_quotient_odd hp hpodd hqodd, ?_, ?_⟩
  · exact cyclotomic_quotient_dvd_of_modEq_one hp
  · intro hpq
    exact ⟨cyclotomic_quotient_coprime_of_not_modEq_one hp hq hpq,
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hpq⟩

/-- **Peterfalvi (13.15)**: in case (9.7.b), `u` has the final cyclotomic
value, depending on whether `p` is `1 mod q`. -/
theorem caseB_order_u [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) :
    caseB_for_S →
      ((p_mod : hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
        (¬ (hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  sorry

/-- Carrier for the `u`-order conclusion in **Peterfalvi (13.15)** under
case (9.7.b).  It packages the two congruence branches so Section 16 can carry
the order data together with the case-(b) certificate. -/
structure CaseBOrderUData (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) where
  caseB_holds : caseB_for_S
  u_eq_of_p_modEq_one :
    hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))
  u_eq_of_not_modEq_one :
    ¬ hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)

/-- Data form of **Peterfalvi (13.15)**, derived from `caseB_order_u`. -/
theorem caseB_order_u_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {caseB_for_S : Prop} (hcase : caseB_for_S) :
    CaseBOrderUData hyp caseB_for_S := by
  rcases caseB_order_u hG hyp caseB_for_S hcase with ⟨hmod, hnot⟩
  exact
    { caseB_holds := hcase
      u_eq_of_p_modEq_one := hmod
      u_eq_of_not_modEq_one := hnot }

/-! ## (13.16)--(13.19): normalizers and type-I interaction -/

/-- **Peterfalvi (13.16)**: the normalizer and centralizer of `W_1` are
`Q W_2`. -/
theorem normalizer_W1 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W1 : Set G) = Subgroup.centralizer (hyp.W1 : Set G) ∧
      Subgroup.centralizer (hyp.W1 : Set G) = hyp.Q ⊔ hyp.W2 := by
  sorry

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

/-- **Peterfalvi (13.17.b) `U ⊆ L_F` for the type-`I` `L`**: when `S` is type II and `L` is a
type-`I` maximal subgroup over `N_G(U)`, the complement `U` lies in the Fitting kernel `L_F`.

*Proof (Pf p.82, the gate-4 structural core):* `L` is non-conjugate to `S` and `T` (it is type `I`
while `S`, `T` are type II/non-I and type is conjugacy-invariant), so (8.17.a) =
`card_LF_coprime_pq` (B2) gives `|L_F|` prime to `p q`, in particular to `q = |W₁|`; hence
`W₁ ⊓ L_F = 1`.  Were `U ⊓ L_F = 1`, the Frobenius group `U W₁ ⊆ L` (from (13.2.a)) would
act fixed-point-freely on `L_F` (a coprime action, `U, W₁ ≤ L ≤ N_G(L_F)`), so Wielandt's
formula (9.1) = `wielandt_fixedPoint_frobenius` would force `|L_F| = 1`, contradicting `L_F ≠ 1`
(type `I`, `TypeFData.H_nontrivial`).  Thus `U ⊓ L_F ≠ 1`, and as `L_F` is nilpotent normal in
`L` the self-centralizing property gives `U ⊆ C_L(U ⊓ L_F) ⊆ L_F`.

This producer is the isolated residual of gate 4 alongside `card_LF_coprime_pq`: its body assembles
the (8.17.a)+(9.1) fixed-point-free argument, whose two genuinely deep inputs are the BG-Theorem-E
coprimality `card_LF_coprime_pq` (owner = F) and the Wielandt formula
`wielandt_fixedPoint_frobenius` (already a sorried §9 producer).  Declared `:= sorry`; see
issue 2013 / `notes/peterfalvi/s13_17_structural_program.md`. -/
theorem typeI_overNormalizer_U_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    hyp.U ≤ maxNilpotentNormalHall L := sorry

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
  -- (Phase 0(b), F-ask) the configuration complement meets the Fitting kernel trivially.
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := sorry
  have hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) :=
    coprime_card_U_card_P_of_disjoint hyp tdata hdisj
  -- (Phase 1) the type-II property transferred to `hyp.U`: `N_G(U) ⊄ S`.
  have hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S :=
    not_normalizer_U_le_S _hG hyp tdata (exists_conj_typeP_U_of_coprime _hG hyp tdata hcop)
  -- `U ≠ ⊥` (else `M' = P ⊔ ⊥ = P`, against `fitting_lt_derived`).
  have hUne : hyp.U ≠ ⊥ := by
    intro hUbot
    have heq : derivedInG hyp.S = hyp.P := by rw [hyp.S_deriv_eq_PU, hUbot, sup_bot_eq]
    have hlt := tdata.typeP.fitting_lt_derived
    rw [← hyp.P_eq_SF, heq] at hlt
    exact lt_irrefl _ hlt
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
    have hUhall_cop : Nat.Coprime (Nat.card ↥hyp.U) ((hyp.U.subgroupOf hyp.S).index) := sorry
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

/-- **Peterfalvi (13.17.c)/(14.5)**: the Frobenius complement of the type-I subgroup `L` over
`N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).  *Proof (Pf p.82):* a
complement `E ⊇ W₁` to `L_F` in `L` is a Frobenius complement of odd order, so its prime-order
subgroups are normal ([H] V.8.18); hence `E ⊆ N_G(W₁) ⊆ Q W₂` ((13.16)) with cyclic Sylow
subgroups ([BG] 3.9, `S03g_Thm310`), forcing `E = W₁` or `|E| = p q` with `E = W₁ W₂^y`.  The
`W₁` alternative is excluded by (14.5).  The genuine §13/§14 obligation feeding (13.17). -/
theorem typeI_overNormalizer_complement [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := sorry

/-- **Peterfalvi (13.17)**: if `S` is type II, a maximal subgroup over `N_G(U)` is type-I
Frobenius, contains `U` in its kernel, and has the stated complement alternatives (order `p q`,
containing a conjugate `W₂^y`).  Assembled (`sorry`-free) from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), the (12.7) Frobenius structure
`OddOrder.Peterfalvi.S14.typeI_frobenius`, and the complement structure (13.17.c,
`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII
  obtain ⟨frob, hker⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hLmax hLtypeI
  obtain ⟨hcard, hy⟩ := typeI_overNormalizer_complement _hG hyp hSTypeII hLmax hNUL hUH frob
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

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
