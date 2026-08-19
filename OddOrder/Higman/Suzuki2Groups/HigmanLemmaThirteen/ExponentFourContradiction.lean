/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourFactors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorTypeCParameter
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourTypeBTypeB
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourTypeCTypeB
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourTypeCTypeC

/-!
# Higman's Lemma 13: contradiction in the exponent-four branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

The two complementary restricted length-three factors are placed over one
common Singer coordinate on `Φ(P)²`.  Their normalized right factors are
each either type B or type C.  The B/B, C/B, B/C, and C/C alternatives are
then discharged by the corresponding cross-commutator contradictions.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (pp. 92–93), exponent-four branch.**

An actor satisfying the Lemma 13 hypotheses cannot have exact `ξ`-length
four when the Frattini subgroup has exponent four but not exponent two. -/
theorem false_of_hasXiLengthFour_of_frattini_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    False := by
  classical
  obtain ⟨X, Z, hXinv, hZinv, hXnormal, hlenX,
      hZnormal, hlenZ, hPhiX, hXtop, hPhiZ, hZtop,
      _hXZinf, hsup⟩ :=
    exists_two_xiLengthThree_frattini_preimages_of_exponent_four
      hP hncomm hmulti hxi hlen hprime hPhiComm hfour hexists
  let phiTerm := frattiniNormalInvariant Y.subtype
  let xTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨X, ⟨hXnormal, hXinv⟩⟩
  let zTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨Z, ⟨hZnormal, hZinv⟩⟩
  have hLower := frattiniSquare_composition_series_of_exponent_four
    hP hxi hPhiComm hfour hexists
  have hXcovers := hlen.covers_of_chain
    hLower.1.lt hLower.2.lt
      (show phiTerm < xTerm from hPhiX)
      (show xTerm < normalInvariantTop Y.subtype from hXtop)
  have hZcovers := hlen.covers_of_chain
    hLower.1.lt hLower.2.lt
      (show phiTerm < zTerm from hPhiZ)
      (show zTerm < normalInvariantTop Y.subtype from hZtop)
  let hPhiXCover : NormalInvariantCover Y.subtype (frattini P) X :=
    { left := phiTerm.2
      right := xTerm.2
      covBy := hXcovers.2.2.1 }
  let hPhiZCover : NormalInvariantCover Y.subtype (frattini P) Z :=
    { left := phiTerm.2
      right := zTerm.2
      covBy := hZcovers.2.2.1 }
  let hXTopCover : NormalInvariantCover Y.subtype X ⊤ :=
    { left := xTerm.2
      right := (normalInvariantTop Y.subtype).2
      covBy := hXcovers.2.2.2 }
  let hZTopCover : NormalInvariantCover Y.subtype Z ⊤ :=
    { left := zTerm.2
      right := (normalInvariantTop Y.subtype).2
      covBy := hZcovers.2.2.2 }
  have hncommX : ¬ IsMulCommutative X :=
    restricted_lengthThree_not_isMulCommutative_of_covBy_top
      hP hncomm hmulti hxi hprime hXinv hXTopCover hlenX
  have hncommZ : ¬ IsMulCommutative Z :=
    restricted_lengthThree_not_isMulCommutative_of_covBy_top
      hP hncomm hmulti hxi hprime hZinv hZTopCover hlenZ
  let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive (frattiniSquare P))
  have hSinger :=
    exists_frattiniSquareSingerCoordinates_of_exponent_four
      hP hmulti hxi hPhiComm hfour hexists
  dsimp only at hSinger
  obtain ⟨c, eSquare, nu, _basis, hn, hcgen, hnuPrimitive,
      hconj, _hadjoin, _hbasis⟩ := hSinger
  have hCoordsX :=
    exists_sharpRestrictedFactorPairCoordinates_of_frattiniSquareSinger
      (n := n)
      hP hmulti hxi hprime hPhiComm hfour hexists
      hXinv hPhiXCover hlenX hncommX
  obtain ⟨factorsX, leftX, rightX, hleftX, hleftThetaX,
      _hleftSourceX, _hrightSourceX, hrightCaseX⟩ :=
    hCoordsX c eSquare nu hn hcgen hnuPrimitive hconj
  have hCoordsZ :=
    exists_sharpRestrictedFactorPairCoordinates_of_frattiniSquareSinger
      (n := n)
      hP hmulti hxi hprime hPhiComm hfour hexists
      hZinv hPhiZCover hlenZ hncommZ
  obtain ⟨factorsZ, leftZ, rightZ, hleftZ, hleftThetaZ,
      _hleftSourceZ, _hrightSourceZ, hrightCaseZ⟩ :=
    hCoordsZ c eSquare nu hn hcgen hnuPrimitive hconj
  rcases hrightCaseX with hrightOneX |
    ⟨rX, hrX, _hrhalfX, h2r1X, hrightThetaX, _hrightOddX⟩
  · rcases hrightCaseZ with hrightOneZ |
      ⟨rZ, hrZ, _hrhalfZ, h2r1Z, hrightThetaZ, _hrightOddZ⟩
    · exact false_of_two_typeB_sharpRestrictedFactorPairs_of_exponent_four
        hP hmulti hxi hprime hPhiComm hfour hexists
        hXinv hPhiXCover hlenX hncommX
        hZinv hPhiZCover hlenZ hncommZ hsup
        hn c eSquare nu hnuPrimitive hconj
        factorsX rightX hleftX hrightOneX
        factorsZ leftZ rightZ hleftZ hleftThetaZ hrightOneZ
    · have hsupZX : Z ⊔ X = (⊤ : Subgroup P) := by
        simpa [sup_comm] using hsup
      exact false_of_typeC_typeB_sharpRestrictedFactorPairs_of_exponent_four
        hP hmulti hxi hprime hPhiComm hfour hexists
        hZinv hPhiZCover hlenZ hncommZ
        hXinv hPhiXCover hlenX hncommX hsupZX
        hn hrZ h2r1Z c eSquare nu hnuPrimitive hconj
        factorsZ rightZ hleftZ hrightThetaZ
        factorsX leftX rightX hleftX hleftThetaX hrightOneX
  · rcases hrightCaseZ with hrightOneZ |
      ⟨rZ, hrZ, _hrhalfZ, h2r1Z, hrightThetaZ, _hrightOddZ⟩
    · exact false_of_typeC_typeB_sharpRestrictedFactorPairs_of_exponent_four
        hP hmulti hxi hprime hPhiComm hfour hexists
        hXinv hPhiXCover hlenX hncommX
        hZinv hPhiZCover hlenZ hncommZ hsup
        hn hrX h2r1X c eSquare nu hnuPrimitive hconj
        factorsX rightX hleftX hrightThetaX
        factorsZ leftZ rightZ hleftZ hleftThetaZ hrightOneZ
    · have hrZX : rZ = rX := by omega
      have hrightThetaZ' := hrightThetaZ
      rw [hrZX] at hrightThetaZ'
      exact false_of_two_typeC_sharpRestrictedFactorPairs_of_exponent_four
        hP hmulti hxi hprime hPhiComm hfour hexists
        hXinv hPhiXCover hlenX hncommX
        hZinv hPhiZCover hlenZ hncommZ hsup
        hn hrX h2r1X c eSquare nu hnuPrimitive hconj
        factorsX leftX rightX hleftX hleftThetaX hrightThetaX
        factorsZ leftZ rightZ hleftZ hleftThetaZ hrightThetaZ'

end OddOrder.Higman.Suzuki2Groups
