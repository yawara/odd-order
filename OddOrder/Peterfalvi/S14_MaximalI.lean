/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV

/-!
# Peterfalvi Section 14: Maximal Subgroups of Type I

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 14, pp. 69--74.

This section proves that every maximal subgroup of type I is a Frobenius group
with kernel `M_F`.  The proof first sets up the Dade isometry attached to a
type-I maximal subgroup, proves orthogonality and constancy properties for the
families `R(chi)`, and then excludes a minimal counterexample with a non-cyclic
Sylow subgroup in `M / M_F`.

The scaffold records the named endpoints (12.1)--(12.17).  The detailed
character decompositions, rho maps, and integer congruence calculations are kept
as proposition fields until the lower-level Dade/rho API is ready for this
maximal-subgroup layer.
-/

namespace OddOrder.Peterfalvi.S14
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (12.1): the type-I hypothesis -/

/-- **Peterfalvi (12.1)**: setup for a maximal subgroup `L` of type I.

`Sset` is the family `{Ind_H^L theta | theta in Irr H, theta != 1_H}`.
`R chi` is the union of the two-element image blocks `R_1(phi)` appearing in
(12.2).  The fields whose names end in `Formula` name the character calculations
proved across (12.2)--(12.5). -/
structure Hypothesis (L : Subgroup G) where
  maximal : L ∈ maximalSubgroups G
  typeI : TypeIData L
  Sset : Set (ClassFunction ↥L ℂ)
  A : Set ↥L
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  R : ClassFunction ↥L ℂ → Set (ClassFunction G ℂ)
  decompositionFormula : ClassFunction ↥L ℂ → Prop
  dadeDomainFormula : ClassFunction ↥L ℂ → Prop
  characterOrthogonalToR : ClassFunction G ℂ → Prop
  rhoConstantFormula : ClassFunction G ℂ → Prop
  integerValueFormula : ClassFunction G ℂ → Prop

namespace Hypothesis

/-- Peterfalvi's `H = L_F`. -/
def H {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  hyp.typeI.typeF.H

/-- Peterfalvi's `H'`, represented as an ambient subgroup. -/
def Hprime {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  derivedInAmbient hyp.H

/-- Peterfalvi's ambient `A(L)` set from Definition (8.3). -/
def ambientA {L : Subgroup G} (hyp : Hypothesis L) : Set G :=
  typeIA L hyp.typeI

end Hypothesis

/-! ## (12.2): character decomposition and Dade domain -/

/-- Carrier for the decomposition of `chi in S` used in Peterfalvi (12.2). -/
structure CharacterDecompositionData {L : Subgroup G} (hyp : Hypothesis L)
    (chi : ClassFunction ↥L ℂ) where
  chi_mem : chi ∈ hyp.Sset
  components : Set (ClassFunction ↥L ℂ)
  components_nonempty : components.Nonempty
  R1 : ClassFunction ↥L ℂ → Set (ClassFunction G ℂ)
  equal_degree : Prop
  equal_degree_holds : equal_degree
  tau_restriction_domain : Prop
  tau_restriction_domain_holds : tau_restriction_domain
  difference_image_formula : Prop
  difference_image_formula_holds : difference_image_formula
  R_eq_union : Prop
  R_eq_union_holds : R_eq_union

/-- **Peterfalvi (12.2)**: each `chi in S` decomposes into irreducible components
of equal degree, and the restricted Dade map has the stated two-element image
blocks. -/
theorem character_decomposition_and_dade_domain [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi,
      data.chi_mem = hchi ∧ data.tau_restriction_domain ∧
        data.difference_image_formula ∧ data.R_eq_union := by
  sorry

/-! ## (12.3)--(12.5): orthogonality and rho-constancy -/

/-- Carrier for Peterfalvi (12.3), comparing two non-conjugate type-I maximal
subgroups. -/
structure CrossOrthogonalityData {L1 L2 : Subgroup G}
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2) where
  chi1 : ClassFunction ↥L1 ℂ
  chi1_mem : chi1 ∈ hyp1.Sset
  chi2 : ClassFunction ↥L2 ℂ
  chi2_mem : chi2 ∈ hyp2.Sset
  R1 : Set (ClassFunction G ℂ)
  R1_eq : R1 = hyp1.R chi1
  R2 : Set (ClassFunction G ℂ)
  R2_eq : R2 = hyp2.R chi2
  orthogonal : Prop
  orthogonal_holds : orthogonal

/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups, the
families `R(chi)` are mutually orthogonal. -/
theorem nonconjugate_typeI_R_orthogonal [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L1 L2 : Subgroup G}
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2) :
    ∃ data : CrossOrthogonalityData hyp1 hyp2, data.orthogonal := by
  sorry

/-- **Peterfalvi (12.4)**: a class function orthogonal to every type-I
`R(chi)` is constant on each coset `xH` with `x in L - H`. -/
theorem orthogonal_character_constant_on_coset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {psi : ClassFunction G ℂ} (horth : hyp.characterOrthogonalToR psi)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  sorry

/-- **Peterfalvi (12.5)**: after the rho-reduction, the resulting character is
constant on `H - H'`. -/
theorem rho_constant_on_H_minus_Hprime [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {psi : ClassFunction G ℂ} (hrho : hyp.rhoConstantFormula psi) :
    ∀ h : G, h ∈ hyp.H → h ∉ hyp.Hprime → psi h = psi 1 := by
  sorry

/-! ## (12.6)--(12.7): type-I Frobenius structure -/

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Peterfalvi (12.6)**: if `L` is already Frobenius with kernel `H`, then the
family `S` is coherent. -/
theorem frobenius_typeI_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  sorry

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with
kernel equal to `M_F`. -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  sorry

/-! ## (12.8)--(12.12): minimal counterexample analysis -/

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7). -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  pi_nonempty : Prop
  minimal_p : Prop
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInAmbient K
  P0_le_M : P0 ≤ M
  P0_sylow_quotient : Prop
  P0_noncyclic_quotient : Prop

/-- The rank-two witness extracted in Peterfalvi (12.9). -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  P0_le_Ls : Prop
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  x_mem_omega1 : Prop
  CKx_not_le_Kprime : Prop
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  centralizer_x_not_le_L : Prop
  centralizer_x_not_le_L_holds : centralizer_x_not_le_L
  M_inter_L_complements_K : Prop
  M_inter_L_le_H : Prop

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧
      ∃ data : RankTwoWitnessData ctr,
        data.CKx_not_le_Kprime ∧ data.centralizer_x_not_le_L := by
  sorry

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is
Frobenius with kernel `L_F`. -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  sorry

/-- **Peterfalvi (12.11)**: `M inter L` complements `K` in `M` and lies in the
Fitting kernel `H` of the witness subgroup `L`. -/
theorem intersection_complement_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    data.M_inter_L_complements_K ∧ data.M_inter_L_le_H := by
  sorry

/-- **Peterfalvi (12.12)**: the Frobenius complement in the witness subgroup is
cyclic, with order dividing `p - 1` or `p + 1`. -/
theorem complement_cyclic_order_dvd [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (frob : TypeIFrobeniusData L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  sorry

/-! ## (12.13)--(12.16): Dade notation and contradiction -/

/-- **Peterfalvi (12.13)**: notation for the final Dade calculation in the
minimal counterexample. -/
structure DadeNotation {L : Subgroup G} (hyp : Hypothesis L) where
  e : ℕ
  e_eq_index : Prop
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  chi : ClassFunction ↥L ℂ
  chi_mem : chi ∈ hyp.Sset
  chi_degree_eq_e : chi 1 = (e : ℂ)
  psi : ClassFunction G ℂ
  psi_eq_tau1_chi : psi = tau1 chi
  rhoFormula : Prop
  rhoMFormula : Prop

/-- **Peterfalvi (12.14)**: the character `psi` is constant on the coset `xK`. -/
theorem psi_constant_on_xK [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (hyp : Hypothesis L) (witness : RankTwoWitnessData ctr)
    (dade : DadeNotation hyp) :
    ∀ g : G, g ∈ ctr.K → dade.psi (witness.x * g) = dade.psi witness.x := by
  sorry

/-- **Peterfalvi (12.15)**: the rho image is unchanged on `K#`, constant on
`K - K'`, and has integer values there. -/
theorem rhoM_integer_values [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    {hyp : Hypothesis L} (dade : DadeNotation hyp) :
    dade.rhoMFormula ∧
      (∀ g : G, g ∈ ctr.K → g ∉ ctr.Kprime → ∃ z : ℤ, dade.psi g = (z : ℂ)) := by
  sorry

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  sorry

/-! ## (12.17): forcing case (b) of Theorem (8.8) -/

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible,
so the case-(b) data of (8.8) exists. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  sorry

end OddOrder.Peterfalvi.S14
