/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleDiagonalAxis
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniTripleBaseChangeJacobi

/-!
# Higman's Lemma 13: vanishing of type-B diagonal middle brackets

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For two Frobenius eigenfamilies of the canonical type-B weight, every
same-index middle Frattini commutator vanishes when the second family pairs
nontrivially with the corresponding canonical middle basis vectors in the
square layer. Otherwise the middle bracket lies on the successor eigenline,
and the three vectors contradict Jacobi.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniDiagonalMiddleZeroLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance
    frattiniDiagonalMiddleZeroLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), abstract B/B diagonal vanishing.**

Suppose `f` and `g` are Frobenius eigenfamilies of the canonical middle
weight. If every canonical middle basis vector has nonzero square bracket
with the matching member of `g`, then every same-index middle bracket between
`f` and `g` vanishes. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_diagonal_eq_zero_of_square_ne_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat} (hn : 2 ≤ n) (c : Y)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hconj :
      let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
        (frattiniSquareNormalInvariant Y.subtype).2.2
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eSquare.conj (elabRepresentation 2 hSquareInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (f g : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
      GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0))
    (hf : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (f i) =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • f i)
    (hg : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (g i) =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • g i)
    (hsquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : CommGroup (frattini P) :=
        { (inferInstance : Group (frattini P)) with
          mul_comm := hPhiComm.is_comm.comm }
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      let eMiddle :=
        frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
      let middleBasis :=
        conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
      ∀ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (g k) ≠ 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ i : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists (f i) (g i) = 0 := by
  classical
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let : Fact (1 < n) := ⟨by omega⟩
  let eMiddle :=
    frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
  let middleBasis :=
    conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
  let middleBracket :=
    frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hexists
  let squareBracket :=
    frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hfour hexists
  have hsquare' : ∀ k, squareBracket (middleBasis k) (g k) ≠ 0 := by
    simpa only [squareBracket, middleBasis, eMiddle] using hsquare
  intro i
  by_contra hdiag
  obtain ⟨k, epsilon, hk, hepsilon, haxis⟩ :=
    exists_ne_zero_smul_frattiniMiddleConjugateBasis_of_diagonal_bracket
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i (f i) (g i) (hf i) (hg i) hdiag
  have hki : k ≠ i := by
    intro h
    subst k
    have hone : (1 : ZMod n) = 0 := by
      simpa only [add_eq_left] using hk.symm
    exact (one_ne_zero : (1 : ZMod n) ≠ 0) hone
  have hrightOff : middleBracket (g i) (g k) = 0 := by
    exact frattiniMiddleCommutatorBilinearBaseChange_eq_zero_of_ne
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i k (g i) (g k) (hg i) (hg k) hki.symm
  have hcrossOff : middleBracket (f i) (g k) = 0 := by
    exact frattiniMiddleCommutatorBilinearBaseChange_eq_zero_of_ne
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i k (f i) (g k) (hf i) (hg k) hki.symm
  have htriple :
      squareBracket (middleBracket (f i) (g i)) (g k) ≠ 0 := by
    rw [haxis]
    simpa only [map_smul, LinearMap.smul_apply] using
      smul_ne_zero hepsilon (hsquare' k)
  exact false_of_frattiniDiagonalSquareCommutator_ne_zero
    (GaloisField 2 n) hP hxi hPhiComm hfour hexists
    (f i) (g i) (g k) hrightOff hcrossOff htriple

end OddOrder.Higman.Suzuki2Groups
