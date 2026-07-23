/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourReduction

/-!
# Higman's Lemma 13: exact length-four contradiction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

Higman's prime-support normalization makes the Frattini subgroup
commutative and reduces its exponent to the two cases treated by the
preceding developments.  Both exponent two and genuine exponent four
contradict exact `ξ`-length four.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group

universe uP

/-- **Higman Lemma 13 (pp. 92–93), exact length-four contradiction.**

A noncommutative finite `2`-group with multiple involutions and a
prime-supported `ξ`-actor cannot have exact `ξ`-length four.  The Frattini
exponent split is derived from the standing hypotheses rather than exposed
as an additional assumption. -/
theorem false_of_hasXiLengthFour
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    False := by
  have hPhiComm : IsMulCommutative (frattini P) :=
    frattini_isMulCommutative_of_primeSupport
      hP hncomm hmulti hxi hprime
  rcases
      frattini_exponent_two_or_four_of_primeSupport
        hP hncomm hmulti hxi hprime with
    htwo | ⟨hfour, hexists⟩
  · exact false_of_hasXiLengthFour_of_frattini_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  · exact false_of_hasXiLengthFour_of_frattini_exponent_four
      hP hncomm hmulti hxi hlen hprime
      hPhiComm hfour hexists

end OddOrder.Higman.Suzuki2Groups
