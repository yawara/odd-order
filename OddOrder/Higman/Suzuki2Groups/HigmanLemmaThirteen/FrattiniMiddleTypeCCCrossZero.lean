/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleTypeCCAxis
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniTripleBaseChangeJacobi

/-!
# Higman's Lemma 13: vanishing of type-C/C middle brackets

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

For two type-C source families with the same sharp parameter, the only
possible nonzero middle brackets have one of the two supports displayed by
Higman.  In either branch the supported middle axis has a nonzero square
bracket with the corresponding vector from its own source family.  The other
two terms vanish, contradicting Jacobi.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleTypeCCCrossZeroLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance
    frattiniMiddleTypeCCCrossZeroLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (printed p. 93), type-C/C middle vanishing.**

Let `f` and `g` be type-C eigenfamilies with the common sharp parameter
`r`.  Assume same-family middle brackets vanish and each canonical middle
axis has a nonzero square bracket with the shifted member of the corresponding
family.  Then every middle bracket between the two families vanishes. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_typeCC_eq_zero_of_square_ne_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n r : Nat} (hn : 2 ≤ n) (hr : 0 < r) (h2r1 : 2 * r + 1 = n)
    (c : Y)
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
    (lambda rho : GaloisField 2 n)
    (theta psi : RingAut (GaloisField 2 n))
    (hlambdaSource : nu = lambda * theta lambda)
    (hrhoSource : nu = rho * psi rho)
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hpsi : psi = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (f g : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
      GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0))
    (hf : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (f i) =
        lambda ^ (2 ^ i.val) • f i)
    (hg : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (g i) =
        rho ^ (2 ^ i.val) • g i)
    (hfSame :
      letI : CommGroup (frattini P) :=
        { (inferInstance : Group (frattini P)) with
          mul_comm := hPhiComm.is_comm.comm }
      ∀ i j, frattiniMiddleCommutatorBilinearBaseChange
        (GaloisField 2 n) hP hxi hPhiComm hexists (f i) (f j) = 0)
    (hgSame :
      letI : CommGroup (frattini P) :=
        { (inferInstance : Group (frattini P)) with
          mul_comm := hPhiComm.is_comm.comm }
      ∀ i j, frattiniMiddleCommutatorBilinearBaseChange
        (GaloisField 2 n) hP hxi hPhiComm hexists (g i) (g j) = 0)
    (hfSquare :
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
      ∀ k a : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        (a.val : ZMod n) + 1 =
            (k.val : ZMod n) + (r : ZMod n) →
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (f a) ≠ 0)
    (hgSquare :
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
      ∀ k a : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        (a.val : ZMod n) + 1 =
            (k.val : ZMod n) + (r : ZMod n) →
        frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hfour hexists (middleBasis k) (g a) ≠ 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists (f i) (g j) = 0 := by
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
  have hfSame' : ∀ i j, middleBracket (f i) (f j) = 0 := by
    simpa only [middleBracket] using hfSame
  have hgSame' : ∀ i j, middleBracket (g i) (g j) = 0 := by
    simpa only [middleBracket] using hgSame
  have hfSquare' : ∀ k a,
      (a.val : ZMod n) + 1 =
          (k.val : ZMod n) + (r : ZMod n) →
      squareBracket (middleBasis k) (f a) ≠ 0 := by
    simpa only [squareBracket, middleBasis, eMiddle] using hfSquare
  have hgSquare' : ∀ k a,
      (a.val : ZMod n) + 1 =
          (k.val : ZMod n) + (r : ZMod n) →
      squareBracket (middleBasis k) (g a) ≠ 0 := by
    simpa only [squareBracket, middleBasis, eMiddle] using hgSquare
  have hrn : r < n := by omega
  have hrz : (r : ZMod n) ≠ 0 := by
    rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
      Nat.mod_eq_of_lt hrn]
    omega
  have hcrossDiagonal : ∀ a,
      middleBracket (f a) (g a) = 0 := by
    intro a
    by_contra hcross
    obtain ⟨_, hsupport⟩ :=
      frattiniMiddleCommutatorBilinearBaseChange_typeCC_support_of_ne_zero
        hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
        hnuPrimitive hconj lambda rho theta psi hlambdaSource hrhoSource
        htheta hpsi a a (f a) (g a) (hf a) (hg a) hcross
    rcases hsupport with hsupport | hsupport
    · exact hrz (by linear_combination (-1 : ZMod n) * hsupport.1)
    · exact hrz (by linear_combination (-1 : ZMod n) * hsupport.1)
  intro i j
  by_contra hcross
  obtain ⟨k, epsilon, hsupport, hepsilon, haxis⟩ :=
    exists_ne_zero_smul_frattiniMiddleConjugateBasis_of_typeCC_bracket
      hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
      hnuPrimitive hconj lambda rho theta psi hlambdaSource hrhoSource
      htheta hpsi i j (f i) (g j) (hf i) (hg j) hcross
  rcases hsupport with hright | hleft
  · have hjShift :
        (j.val : ZMod n) + 1 =
          (k.val : ZMod n) + (r : ZMod n) := by
      linear_combination hright.1 - hright.2
    have hrightOff : middleBracket (g j) (f j) = 0 := by
      rw [frattiniMiddleCommutatorBilinearBaseChange_comm]
      exact hcrossDiagonal j
    have hsameOff : middleBracket (f i) (f j) = 0 :=
      hfSame' i j
    have htriple :
        squareBracket (middleBracket (f i) (g j)) (f j) ≠ 0 := by
      rw [haxis]
      simpa only [map_smul, LinearMap.smul_apply] using
        smul_ne_zero hepsilon (hfSquare' k j hjShift)
    exact false_of_frattiniDiagonalSquareCommutator_ne_zero
      (GaloisField 2 n) hP hxi hPhiComm hfour hexists
      (f i) (g j) (f j) hrightOff hsameOff htriple
  · have hiShift :
        (i.val : ZMod n) + 1 =
          (k.val : ZMod n) + (r : ZMod n) := by
      linear_combination hleft.1 - hleft.2
    have hleftOff : middleBracket (f i) (g i) = 0 :=
      hcrossDiagonal i
    have hsameOff : middleBracket (g j) (g i) = 0 :=
      hgSame' j i
    have haxis' :
        middleBracket (g j) (f i) = epsilon • middleBasis k := by
      rw [frattiniMiddleCommutatorBilinearBaseChange_comm]
      exact haxis
    have htriple :
        squareBracket (middleBracket (g j) (f i)) (g i) ≠ 0 := by
      rw [haxis']
      simpa only [map_smul, LinearMap.smul_apply] using
        smul_ne_zero hepsilon (hgSquare' k i hiShift)
    exact false_of_frattiniDiagonalSquareCommutator_ne_zero
      (GaloisField 2 n) hP hxi hPhiComm hfour hexists
      (g j) (f i) (g i) hleftOff hsameOff htriple

end OddOrder.Higman.Suzuki2Groups
