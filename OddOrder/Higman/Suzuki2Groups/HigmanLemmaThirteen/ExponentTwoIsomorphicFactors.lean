/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoParameterCoincidence
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorIsomorphism

/-!
# Higman's Lemma 13: two of the exponent-two factors are isomorphic

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

For three actual factors measured in one ambient Frattini coordinate, the
three normalized pair relations force two square-law parameters to coincide.
The common-parameter extension classification then gives an isomorphism
between that pair of actual factors.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

section /- Higman Lemma 13 (p. 93) -/

/-- **Higman Lemma 13 (p. 93), isomorphic factors in the exponent-two case.**

Among three actual factors with normalized pair relations over one common
ambient coordinate, at least two are isomorphic as groups. -/
theorem exists_isomorphic_factor_pair_of_normalized_factorPairRelations
    {P : Type uP} [Group P] [Finite P]
    {A : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {X Y W : Subgroup P}
    {hXinv : IsAInvariant A.subtype X}
    {hYinv : IsAInvariant A.subtype Y}
    {hWinv : IsAInvariant A.subtype W}
    {hPhiX : frattini P ≤ X}
    {hPhiY : frattini P ≤ Y}
    {hPhiW : frattini P ≤ W}
    {c : A} {n : ℕ}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataX : FactorCoordinateData hXinv hPhiX c ePhi nu)
    (dataY : FactorCoordinateData hYinv hPhiY c ePhi nu)
    (dataW : FactorCoordinateData hWinv hPhiW c ePhi nu)
    (hn : 0 < n)
    (hXnorm :
      dataX.theta = 1 ∨
        ∃ x : ℕ, 0 < x ∧ 2 * x ≤ n ∧
          dataX.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ x ∧
          Odd (orderOf dataX.theta))
    (hYnorm :
      dataY.theta = 1 ∨
        ∃ y : ℕ, 0 < y ∧ 2 * y ≤ n ∧
          dataY.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ y ∧
          Odd (orderOf dataY.theta))
    (hWnorm :
      dataW.theta = 1 ∨
        ∃ w : ℕ, 0 < w ∧ 2 * w ≤ n ∧
          dataW.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ w ∧
          Odd (orderOf dataW.theta))
    (hXY : NormalizedFactorPairRelation n dataX.theta dataY.theta)
    (hXW : NormalizedFactorPairRelation n dataX.theta dataW.theta)
    (hYW : NormalizedFactorPairRelation n dataY.theta dataW.theta) :
    Nonempty (X ≃* Y) ∨ Nonempty (X ≃* W) ∨ Nonempty (Y ≃* W) := by
  rcases normalized_factorPairRelations_force_parameter_coincidence
      hn hXnorm hYnorm hWnorm hXY hXW hYW with htheta | htheta | htheta
  · exact Or.inl ⟨dataX.factorMulEquivOfThetaEq dataY hn htheta⟩
  · exact Or.inr (Or.inl
      ⟨dataX.factorMulEquivOfThetaEq dataW hn htheta⟩)
  · exact Or.inr (Or.inr
      ⟨dataY.factorMulEquivOfThetaEq dataW hn htheta⟩)

end

end OddOrder.Higman.Suzuki2Groups
