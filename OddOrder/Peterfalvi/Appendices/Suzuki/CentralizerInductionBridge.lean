/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerQuotient
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSL
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisSuzuki
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSU

/-!
# Peterfalvi Part II, Ch. I §3: applying induction to the centralizer quotient

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Theorem A (pp. 96–97) and Ch. I §3, Proposition 1(c)
(pp. 106–107).

This file records the conclusion of Suzuki's Theorem A as concrete standard
action coordinates for its three target families.  Applying the source
induction hypothesis to `C_G(X)/𝒩(C_G(X))` then makes the quotient root group
a `2`-group.  The quotient map is injective on `C_Q(X)`, because its kernel
lies in the odd complement while `C_Q(X)` meets that complement trivially;
the resulting explicit equivalence transports the `2`-group conclusion back
to `C_Q(X)`.

No simplicity or permutation-degree input is stored in the conclusion
carrier: those facts are derived from the concrete standard models by the
three existing Lemma 1 endpoints.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open scoped LinearAlgebra.Projectivization

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

section /- Suzuki Theorem A: conclusion and induction hypothesis (pp. 96–97) -/

/-- **Peterfalvi Part II, Suzuki Theorem A (`PSL(2,q)` case).**
Concrete coordinates identifying the normal subgroup and its action with
the usual projective-line action of `PSL(2,F)`, where `F` is a finite field
of characteristic two and order greater than two. -/
structure PSL2InductionTarget (L : Subgroup G) where
  F : Type u
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  cardF_gt_two : 2 < Nat.card F
  groupEquiv : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F
  actionEquiv : Omega →ₑ[groupEquiv.toMonoidHom] ℙ F (Fin 2 → F)
  actionEquiv_bijective : Function.Bijective actionEquiv

/-- **Peterfalvi Part II, Suzuki Theorem A (`Sz(q)` case).**
Concrete coordinates identifying the normal subgroup and its action with
the standard Suzuki group acting on its ovoid. -/
structure SuzukiInductionTarget (L : Subgroup G) where
  m : ℕ
  m_pos : 0 < m
  groupEquiv : L ≃*
    OddOrder.GroupTheory.SpecificGroups.Suzuki.standardPermGroup m
  actionEquiv : Omega →ₑ[groupEquiv.toMonoidHom]
    OddOrder.GroupTheory.SpecificGroups.Suzuki.Ovoid m
  actionEquiv_bijective : Function.Bijective actionEquiv

/-- **Peterfalvi Part II, Suzuki Theorem A (`PSU(3,q)` case).**
Concrete coordinates identifying the normal subgroup and its action with
the standard projective unitary group acting on its Hermitian unital. -/
structure PSU3InductionTarget (L : Subgroup G) where
  n : ℕ
  one_lt_n : 1 < n
  groupEquiv : L ≃*
    OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.standardPermGroup n
  actionEquiv : Omega →ₑ[groupEquiv.toMonoidHom]
    OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Unital n
  actionEquiv_bijective : Function.Bijective actionEquiv

/-- The three concrete standard-action alternatives in the conclusion of
**Peterfalvi Part II, Suzuki Theorem A**. -/
inductive TheoremATarget (L : Subgroup G) where
  | psl2 (data : PSL2InductionTarget (Omega := Omega) L)
  | suzuki (data : SuzukiInductionTarget (Omega := Omega) L)
  | psu3 (data : PSU3InductionTarget (Omega := Omega) L)

/-- **Peterfalvi Part II, Suzuki Theorem A.**
The honest structural conclusion: a normal subgroup of odd index together
with one of the three concrete standard permutation models. -/
structure TheoremAConclusion (G : Type u) (Omega : Type v)
    [Group G] [MulAction G Omega] [Finite G] where
  L : Subgroup G
  normal : L.Normal
  oddIndex : Odd L.index
  target : TheoremATarget (Omega := Omega) L

/-- **Peterfalvi Part II, Ch. I §3, induction hypothesis.**
Every smaller finite group satisfying (A1)--(A3) has the concrete conclusion
of Suzuki's Theorem A. -/
def TheoremAInductionBelow (G : Type u) (Omega : Type v)
    [Group G] [MulAction G Omega] [Finite G] : Prop :=
  ∀ {A : Type u} {Lambda : Type v} [Group A] [MulAction A Lambda] [Finite A],
    Nat.card A < Nat.card G → Hypothesis A Lambda →
      Nonempty (TheoremAConclusion A Lambda)

/-- **Peterfalvi Part II, Ch. I §3, Lemma 1.**
Each concrete alternative in Theorem A makes `Q` a `2`-group and identifies
the supplied normal subgroup with both `O^{2′}(G)` and the normal closure of
`Q`.  Simplicity and the degree calculation are derived from the standard
model rather than accepted as carrier fields. -/
theorem TheoremAConclusion.Q_and_residual (result : TheoremAConclusion G Omega)
    (hyp : Hypothesis G Omega) :
    IsPGroup 2 hyp.Q ∧
      hyp.Q ≤ result.L ∧
      result.L = Subgroup.primeComplementResidual 2 G ∧
      result.L = (⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom) := by
  cases result.target with
  | psl2 data =>
      letI : Field data.F := data.fieldF
      letI : Finite data.F := data.finiteF
      letI : CharP data.F 2 := data.charTwoF
      exact hyp.Q_and_residual_of_psl2_target result.L result.normal
        result.oddIndex data.cardF_gt_two data.groupEquiv data.actionEquiv
        data.actionEquiv_bijective
  | suzuki data =>
      exact hyp.Q_and_residual_of_suzuki_target result.L result.normal
        result.oddIndex data.m_pos data.groupEquiv data.actionEquiv
        data.actionEquiv_bijective
  | psu3 data =>
      exact hyp.Q_and_residual_of_psu3_target result.L result.normal
        result.oddIndex data.one_lt_n data.groupEquiv data.actionEquiv
        data.actionEquiv_bijective

end

section /- Ch. I §3 Proposition 1(c): the centralizer root group (pp. 106–107) -/

variable (hyp : Hypothesis G Omega) {X : Subgroup G}

/-- **Peterfalvi Part II, Ch. I §1 Proposition 4(c), used in §3
Proposition 1(c).**  The quotient map induces the explicit source
equivalence

`C_Q(X) ≃ Q̄`

because `𝒩(C_G(X)) ≤ C_D(X)` and `C_Q(X) ∩ C_D(X) = 1`. -/
noncomputable def centralizerQQuotientEquiv (hXV : X ≤ hyp.V) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      ↥(hyp.centralizerQuotientHypothesisA1 hXV).Q := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let pi : L →* L ⧸ N := QuotientGroup.mk' N
  letI := hyp.centralizerQuotientMulAction hXV
  change Q_L ≃* Q_L.map pi
  have hNleD : N ≤ hyp.D.subgroupOf L := by
    dsimp only [N, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hQD : Q_L ⊓ hyp.D.subgroupOf L = ⊥ :=
    (hyp.centralizerHypothesisA1 hXV).Q_inf_D_eq_bot
  have hinj : Function.Injective (pi.subgroupMap Q_L) := by
    intro q r hqr
    have hqr' : pi (q : L) = pi (r : L) := congrArg Subtype.val hqr
    have hquot : pi ((q : L) * (r : L)⁻¹) = 1 := by
      rw [map_mul, map_inv, hqr', mul_inv_cancel]
    have hmemN : (q : L) * (r : L)⁻¹ ∈ N :=
      (QuotientGroup.eq_one_iff _).mp hquot
    have hmemD : (q : L) * (r : L)⁻¹ ∈ hyp.D.subgroupOf L :=
      hNleD hmemN
    have hmemQ : (q : L) * (r : L)⁻¹ ∈ Q_L :=
      Q_L.mul_mem q.2 (Q_L.inv_mem r.2)
    have hbot : (q : L) * (r : L)⁻¹ ∈ Q_L ⊓ hyp.D.subgroupOf L :=
      ⟨hmemQ, hmemD⟩
    rw [hQD, Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  exact MulEquiv.ofBijective (pi.subgroupMap Q_L)
    ⟨hinj, pi.subgroupMap_surjective Q_L⟩

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c).**
The source equivalence `C_Q(X) ≃ Q̄` transports the `2`-group property from
the faithful quotient action back to the actual centralizer root group. -/
theorem centralizer_cQ_isPGroup_of_quotient (hXV : X ≤ hyp.V)
    (hQbar :
      letI := hyp.centralizerQuotientMulAction hXV
      IsPGroup 2 (hyp.centralizerQuotientHypothesisA1 hXV).Q) :
    IsPGroup 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact hQbar.of_equiv (hyp.centralizerQQuotientEquiv hXV).symm

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c), induction step.**
Apply the source induction hypothesis to the honest faithful action of
`C_G(X)/𝒩(C_G(X))`.  Lemma 1 makes its root group a `2`-group, and the
explicit quotient equivalence gives `IsPGroup 2 C_Q(X)`. -/
theorem centralizer_cQ_isPGroup_of_induction
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (inductionHypothesis : TheoremAInductionBelow G Omega) :
    IsPGroup 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hsmall : Nat.card (hyp.centralizerActionQuotient X) < Nat.card G :=
    hyp.card_centralizerActionQuotient_lt hXV hX
  obtain ⟨result⟩ := inductionHypothesis hsmall qhyp
  have hQbar : IsPGroup 2 qhyp.Q := (result.Q_and_residual qhyp).1
  exact hyp.centralizer_cQ_isPGroup_of_quotient hXV hQbar

end


end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
