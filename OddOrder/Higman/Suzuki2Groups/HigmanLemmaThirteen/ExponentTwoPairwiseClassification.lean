/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommutingFactors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorModels
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseJoins

/-!
# Higman's Lemma 13: classification of the exponent-two pairwise joins

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Each pair of the three xi-length-two `A(n, phi)` factors generates a proper
invariant subgroup of exact xi-length three. The two factors cannot commute:
otherwise equal square roots in their common Frattini subgroup produce an
ambient involution outside that subgroup. Higman's Lemma 12 therefore applies
to every pairwise join and classifies it as type B, C, or D.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uP uF uE

variable {P : Type uP} [Group P]

/-- Two invariant type-A factors meeting exactly in the ambient Frattini subgroup
generate a noncommutative join, provided ambient involutions lie in that subgroup
and it has exponent two. -/
theorem not_isMulCommutative_sup_of_typeA_factors
    {Y : Subgroup (MulAut P)}
    {R S : Subgroup P}
    (hxi : IsXiActor Y)
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hRSinf : R ⊓ S = frattini P)
    (dataR : XiLengthTwoTypeAData.{uP, uF} R)
    (dataS : XiLengthTwoTypeAData.{uP, uE} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ¬ IsMulCommutative ↥(R ⊔ S) := by
  obtain ⟨x, y, hxy⟩ :=
    exists_not_commute_of_typeA_factors_inf_eq_frattini
      hxi hRinv hSinv hRSinf dataR dataS hinvPhi htwo
  intro hcomm
  apply hxy
  exact congrArg (R ⊔ S).subtype
    (hcomm.is_comm.comm
      (⟨x, (le_sup_left : R ≤ R ⊔ S) x.property⟩ : ↥(R ⊔ S))
      (⟨y, (le_sup_right : S ≤ R ⊔ S) y.property⟩ : ↥(R ⊔ S)))

/-- **Higman Lemma 13 (p. 93), one pairwise join.**
The proper join of two invariant exponent-two factors meeting exactly in the
ambient Frattini subgroup is one of the three groups in Higman's Lemma 12 list. -/
theorem pairwise_join_isTypeBCD_of_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiR : frattini P < R)
    (hPhiS : frattini P < S)
    (hRSinf : R ⊓ S = frattini P)
    (hRStop : R ⊔ S < (⊤ : Subgroup P))
    (dataR : XiLengthTwoTypeAData.{uP, uF} R)
    (dataS : XiLengthTwoTypeAData.{uP, uE} S) :
    IsTypeB.{uP, 0} ↥(R ⊔ S) ∨
      IsTypeC.{uP, 0} ↥(R ⊔ S) ∨
        IsTypeD.{uP, 0} ↥(R ⊔ S) := by
  let hJoinInv : IsAInvariant Y.subtype (R ⊔ S) :=
    hRinv.sup hSinv
  have hRJoin : R < R ⊔ S := by
    apply lt_of_le_of_ne le_sup_left
    intro hEq
    have hSleR : S ≤ R := by
      rw [hEq]
      exact le_sup_right
    have hSphi : S = frattini P := by
      calc
        S = R ⊓ S := (inf_eq_right.mpr hSleR).symm
        _ = frattini P := hRSinf
    exact hPhiS.ne hSphi.symm
  have hbotPhi : (⊥ : Subgroup P) < frattini P := by
    exact (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hlenJoin : HasXiLengthThree hJoinInv.restrict.range.subtype :=
    restricted_range_hasXiLengthThree_of_two_step_exponent_two
      hP hxi hlen htwo hRinv hJoinInv hbotPhi hPhiR hRJoin hRStop
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
        (IsAInvariant.of_characteristic Y.subtype) hbotPhi.ne'
  have hncommJoin : ¬ IsMulCommutative ↥(R ⊔ S) :=
    not_isMulCommutative_sup_of_typeA_factors
      hxi hRinv hSinv hRSinf dataR dataS hinvPhi htwo
  have hinvJoin : involutions P ⊆ (R ⊔ S : Subgroup P) := fun _ hx =>
    (le_sup_left : R ≤ R ⊔ S) (hPhiR.le (hinvPhi hx))
  have hmultiJoin : ∃ x y : ↥(R ⊔ S),
      x ∈ involutions ↥(R ⊔ S) ∧
        y ∈ involutions ↥(R ⊔ S) ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvJoin hmulti
  have hxiJoin : IsXiActor hJoinInv.restrict.range :=
    restricted_range_isXiActor hxi hJoinInv
  have hprimeJoin : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card hJoinInv.restrict.range →
        p ∣ (involutions ↥(R ⊔ S)).ncard :=
    restricted_range_primeSupport hJoinInv hinvJoin hprime
  exact higmanLemmaTwelve
    (hP.to_subgroup (R ⊔ S)) hncommJoin hmultiJoin
      hxiJoin hlenJoin hprimeJoin

/-- **Higman Lemma 13 (p. 93), all three pairwise joins.**

There are three type-A factors whose three pairwise joins all belong to
Higman's B/C/D list. -/
theorem exists_three_typeA_factors_with_classified_pairwise_joins
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ (X Z T : Subgroup P),
      IsXiLengthTwoTypeA.{uP, 0} X ∧
        IsXiLengthTwoTypeA.{uP, 0} Z ∧
        IsXiLengthTwoTypeA.{uP, 0} T ∧
        (IsTypeB.{uP, 0} ↥(X ⊔ Z) ∨
          IsTypeC.{uP, 0} ↥(X ⊔ Z) ∨
            IsTypeD.{uP, 0} ↥(X ⊔ Z)) ∧
        (IsTypeB.{uP, 0} ↥(X ⊔ T) ∨
          IsTypeC.{uP, 0} ↥(X ⊔ T) ∨
            IsTypeD.{uP, 0} ↥(X ⊔ T)) ∧
        (IsTypeB.{uP, 0} ↥(Z ⊔ T) ∨
          IsTypeC.{uP, 0} ↥(Z ⊔ T) ∨
            IsTypeD.{uP, 0} ↥(Z ⊔ T)) := by
  obtain ⟨X, Z, T, hXinv, hZinv, hTinv,
      _hXnormal, _hlenX, hmodelX,
      _hZnormal, _hlenZ, hmodelZ,
      _hTnormal, _hlenT, hmodelT,
      hPhiX, _hXtop, hPhiZ, _hZtop, hPhiT, _hTtop,
      hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop, _hXZ_Tsup⟩ :=
    exists_three_typeA_xiLengthTwo_frattini_preimages_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  obtain ⟨dataX⟩ := hmodelX
  obtain ⟨dataZ⟩ := hmodelZ
  obtain ⟨dataT⟩ := hmodelT
  have hclassXZ :=
    pairwise_join_isTypeBCD_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
        hXinv hZinv hPhiX hPhiZ hXZinf hXZtop dataX dataZ
  have hclassXT :=
    pairwise_join_isTypeBCD_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
        hXinv hTinv hPhiX hPhiT hXTinf hXTtop dataX dataT
  have hclassZT :=
    pairwise_join_isTypeBCD_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
        hZinv hTinv hPhiZ hPhiT hZTinf hZTtop dataZ dataT
  exact ⟨X, Z, T, ⟨dataX⟩, ⟨dataZ⟩, ⟨dataT⟩,
    hclassXZ, hclassXT, hclassZT⟩

end

end OddOrder.Higman.Suzuki2Groups
