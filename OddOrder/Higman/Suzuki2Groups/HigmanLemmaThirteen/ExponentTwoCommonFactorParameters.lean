/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllDistinctParameters
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPrescribedFactorTransport

/-!
# Higman Lemma 13: parameters on two joins with a common factor

G. Higman, *Suzuki 2-groups*, p. 93.  Coordinate data for one actual
factor may be returned as prescribed factors in two different pairwise
joins.  Transport identifies the two normalized square-law parameters.
The all-distinct B/C/D list check then says that either two of the three
actual-factor parameters agree, or the common parameter is `Frob²` over
the field of degree five.

This is the parameter-level bridge only.  The equal-parameter alternatives
are converted into the group-theoretic cases in downstream leaves.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

/-- A lower-half normalized factor parameter, including the odd-order
witness supplied by the factor-coordinate normalization theorem. -/
def IsNormalizedFactorParameter (n : ℕ)
    (theta : RingAut (GaloisField 2 n)) : Prop :=
  theta = 1 ∨
    ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
      theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
      Odd (orderOf theta)

/-- **Higman Lemma 13 (p. 93), common-factor parameter check.**

The prescribed right factors in `J` and `K` are copies of the same actual
ambient factor `W`.  Their normalized parameters therefore agree.  For
the two oriented factor-pair relations, either two of the resulting three
parameters agree, or the common parameter is `Frob²` in degree five.

The explicit factor records and `subgroupOf` equalities prevent the
statement from forgetting its connection to the actual ambient factor. -/
theorem normalized_factorPairRelations_on_common_prescribedFactor_eq_or_frobenius_sq
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)} {W J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hWJ : W ≤ J) (hWK : W ≤ K)
    [IsMulCommutative (frattini J)]
    [Module (ZMod 2) (Additive (frattini J))]
    [IsMulCommutative (frattini K)]
    [Module (ZMod 2) (Additive (frattini K))]
    (fJ : XiLengthThreeTypeAFactorData J hJinv.restrict.range)
    (fK : XiLengthThreeTypeAFactorData K hKinv.restrict.range)
    (hCommonJ : fJ.right = W.subgroupOf J)
    (hCommonK : fK.right = W.subgroupOf K)
    (c : Y) {n : ℕ}
    {ePhiJ : Additive (frattini J) ≃ₗ[ZMod 2] GaloisField 2 n}
    {ePhiK : Additive (frattini K) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataLeftJ : FactorCoordinateData fJ.left_invariant
      fJ.frattini_lt_left.le
      (hJinv.restrict.rangeRestrict c) ePhiJ nu)
    (dataCommonJ : FactorCoordinateData fJ.right_invariant
      fJ.frattini_lt_right.le
      (hJinv.restrict.rangeRestrict c) ePhiJ nu)
    (dataLeftK : FactorCoordinateData fK.left_invariant
      fK.frattini_lt_left.le
      (hKinv.restrict.rangeRestrict c) ePhiK nu)
    (dataCommonK : FactorCoordinateData fK.right_invariant
      fK.frattini_lt_right.le
      (hKinv.restrict.rangeRestrict c) ePhiK nu)
    (hn : n ≠ 0)
    (hLeftJnorm : IsNormalizedFactorParameter n dataLeftJ.theta)
    (hCommonJnorm : IsNormalizedFactorParameter n dataCommonJ.theta)
    (hLeftKnorm : IsNormalizedFactorParameter n dataLeftK.theta)
    (hCommonKnorm : IsNormalizedFactorParameter n dataCommonK.theta)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hrelJ : NormalizedFactorPairRelation n
      dataLeftJ.theta dataCommonJ.theta)
    (hrelK : NormalizedFactorPairRelation n
      dataLeftK.theta dataCommonK.theta) :
    dataCommonJ.theta = dataCommonK.theta ∧
      (dataLeftJ.theta = dataLeftK.theta ∨
        dataLeftJ.theta = dataCommonJ.theta ∨
        dataLeftK.theta = dataCommonJ.theta ∨
        (n = 5 ∧ dataCommonJ.theta =
          frobeniusEquiv (GaloisField 2 n) 2 ^ 2)) := by
  have hCommon :=
    dataCommonJ.theta_eq_of_prescribedPairwiseFactorCopies
      hJinv hKinv hWJ hWK hCommonJ hCommonK
      fJ.right_invariant fK.right_invariant c
      dataCommonK hn hCommonJnorm hCommonKnorm hnuPrimitive
  refine ⟨hCommon, ?_⟩
  have hrelK' :
      NormalizedFactorPairRelation n
        dataLeftK.theta dataCommonJ.theta := by
    rw [hCommon]
    exact hrelK
  by_cases hleft : dataLeftJ.theta = dataLeftK.theta
  · exact Or.inl hleft
  by_cases hleftCommon : dataLeftJ.theta = dataCommonJ.theta
  · exact Or.inr (Or.inl hleftCommon)
  by_cases hrightCommon : dataLeftK.theta = dataCommonJ.theta
  · exact Or.inr (Or.inr (Or.inl hrightCommon))
  exact Or.inr (Or.inr (Or.inr
    (normalized_factorPairRelations_common_eq_frobenius_sq_of_normalized
      (Nat.pos_of_ne_zero hn)
      hLeftJnorm hLeftKnorm hCommonJnorm
      hleft hleftCommon hrightCommon hrelJ hrelK')))

end

end OddOrder.Higman.Suzuki2Groups
