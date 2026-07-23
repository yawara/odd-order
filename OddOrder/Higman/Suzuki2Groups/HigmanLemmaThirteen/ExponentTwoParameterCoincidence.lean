/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAllDistinctParameters

/-!
# Higman Lemma 13: coincidence of exponent-two parameters

G. Higman, *Suzuki 2-groups*, p. 93.  In the exponent-two branch,
the three length-two factors `X`, `Y`, and `W` cannot all be
nonisomorphic.  Higman applies the Lemma 12 list first to the joins
`XW` and `YW`, obtaining the degree-five parameter `Frob²` for `W`,
and then invokes symmetry to obtain the same parameter for the other
factors.

This file carries out the parameter-level cyclic check.  Three normalized
parameters equipped with the three pair relations cannot be pairwise
distinct.  The conversion from parameter equality to isomorphism of the
actual `A(n, θ)` factors belongs to the downstream group-theoretic layer.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- **Higman Lemma 13 (p. 93), parameter-level cyclic list check.**

If all three normalized parameters were distinct, applying the
all-distinct common-factor check at `W` would identify `thetaW` with
`Frob²` in degree five.  Reversing the two relations incident with `X`
and applying the same check there would identify `thetaX` with that same
automorphism, contradicting distinctness. -/
theorem normalized_factorPairRelations_force_parameter_coincidence
    {n : ℕ}
    {thetaX thetaY thetaW : RingAut (GaloisField 2 n)}
    (hn : 0 < n)
    (hXnorm :
      thetaX = 1 ∨
        ∃ x : ℕ, 0 < x ∧ 2 * x ≤ n ∧
          thetaX = frobeniusEquiv (GaloisField 2 n) 2 ^ x ∧
          Odd (orderOf thetaX))
    (hYnorm :
      thetaY = 1 ∨
        ∃ y : ℕ, 0 < y ∧ 2 * y ≤ n ∧
          thetaY = frobeniusEquiv (GaloisField 2 n) 2 ^ y ∧
          Odd (orderOf thetaY))
    (hWnorm :
      thetaW = 1 ∨
        ∃ w : ℕ, 0 < w ∧ 2 * w ≤ n ∧
          thetaW = frobeniusEquiv (GaloisField 2 n) 2 ^ w ∧
          Odd (orderOf thetaW))
    (hXY : NormalizedFactorPairRelation n thetaX thetaY)
    (hXW : NormalizedFactorPairRelation n thetaX thetaW)
    (hYW : NormalizedFactorPairRelation n thetaY thetaW) :
    thetaX = thetaY ∨ thetaX = thetaW ∨ thetaY = thetaW := by
  by_cases hxy : thetaX = thetaY
  · exact Or.inl hxy
  by_cases hxw : thetaX = thetaW
  · exact Or.inr (Or.inl hxw)
  by_cases hyw : thetaY = thetaW
  · exact Or.inr (Or.inr hyw)
  have hW :=
    normalized_factorPairRelations_common_eq_frobenius_sq_of_normalized
      hn hXnorm hYnorm hWnorm hxy hxw hyw hXW hYW
  have hX :=
    normalized_factorPairRelations_common_eq_frobenius_sq_of_normalized
      hn hYnorm hWnorm hXnorm hyw (Ne.symm hxy) (Ne.symm hxw)
        hXY.symm hXW.symm
  exact (hxw (hX.2.trans hW.2.symm)).elim

end OddOrder.Higman.Suzuki2Groups
