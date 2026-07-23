/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommutingFactors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantGraphCommutativity

/-!
# Higman's Lemma 13: the invariant graph factor gives a contradiction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Once the invariant graph preimage commutes elementwise with the common
factor, their exact Frattini intersection contradicts the ambient
involution condition.  This leaf records that final group-theoretic
interface independently of the coordinate construction which supplies the
two factors.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

section /- Higman Lemma 13 (p. 93) -/

/-- **Higman Lemma 13 (p. 93), invariant-graph contradiction.**

Two invariant type-A factors with exact ambient Frattini intersection
cannot commute elementwise in the exponent-two branch. -/
theorem false_of_typeA_factors_inf_eq_frattini_pairwise_commute
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {U W : Subgroup P}
    (hxi : IsXiActor Y)
    (hUinv : IsAInvariant Y.subtype U)
    (hWinv : IsAInvariant Y.subtype W)
    (hUW : U ⊓ W = frattini P)
    (hmodelU : IsXiLengthTwoTypeA.{uP, 0} U)
    (hmodelW : IsXiLengthTwoTypeA.{uP, 0} W)
    (hinvPhi : involutions P ⊆ frattini P)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    (hcomm : ∀ u : U, ∀ w : W, Commute (u : P) (w : P)) :
    False := by
  rcases hmodelU with ⟨dataU⟩
  rcases hmodelW with ⟨dataW⟩
  obtain ⟨u, w, hncomm⟩ :=
    exists_not_commute_of_typeA_factors_inf_eq_frattini
      hxi hUinv hWinv hUW dataU dataW hinvPhi htwo
  exact hncomm (hcomm u w)

end

end OddOrder.Higman.Suzuki2Groups
