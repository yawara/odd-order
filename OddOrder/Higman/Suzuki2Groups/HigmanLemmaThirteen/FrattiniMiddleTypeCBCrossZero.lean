/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleTypeCBAxis
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleSupport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniTripleBaseChangeJacobi

/-!
# Higman's Lemma 13: vanishing of type-C/B middle brackets

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

A nonzero supported type-C/B middle bracket lies on the canonical middle
eigenline at index `i + 2`.  Pairing that line with the matching member of
the type-B family contradicts Jacobi: the other B/B and C/B middle brackets
have distinct support indices.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleTypeCBCrossZeroLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance
    frattiniMiddleTypeCBCrossZeroLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), type-C/B middle vanishing.**

Suppose `f` is a type-C eigenfamily and `g` is the canonical type-B
eigenfamily.  If every canonical middle basis vector has nonzero square
bracket with the matching member of `g`, then every middle bracket between
`f` and `g` vanishes. -/
theorem
    frattiniMiddleCommutatorBilinearBaseChange_typeCB_eq_zero_of_square_ne_zero
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
    (lambda : GaloisField 2 n)
    (theta : RingAut (GaloisField 2 n))
    (hsource : nu = lambda * theta lambda)
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (f g : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
      GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0))
    (hf : ∀ i,
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (f i) =
        lambda ^ (2 ^ i.val) • f i)
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
  have hsquare' : ∀ k, squareBracket (middleBasis k) (g k) ≠ 0 := by
    simpa only [squareBracket, middleBasis, eMiddle] using hsquare
  have hrn : r < n := by omega
  have hrz : (r : ZMod n) ≠ 0 := by
    rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
      Nat.mod_eq_of_lt hrn]
    omega
  intro i j
  by_contra hdiag
  obtain ⟨k, epsilon, hj, hk, hepsilon, haxis⟩ :=
    exists_ne_zero_smul_frattiniMiddleConjugateBasis_of_typeCB_bracket
      hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
      hnuPrimitive hconj lambda theta hsource htheta
      i j (f i) (g j) (hf i) (hg j) hdiag
  have hjk : j ≠ k := by
    intro hjk
    subst k
    apply hrz
    linear_combination hk - hj
  have hrightOff : middleBracket (g j) (g k) = 0 := by
    exact frattiniMiddleCommutatorBilinearBaseChange_eq_zero_of_ne
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      j k (g j) (g k) (hg j) (hg k) hjk
  have hcrossOff : middleBracket (f i) (g k) = 0 := by
    by_contra hcross
    obtain ⟨_, hkSupported, _⟩ :=
      frattiniMiddleCommutatorBilinearBaseChange_typeCB_support_of_ne_zero
        hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
        hnuPrimitive hconj lambda theta hsource htheta
        i k (f i) (g k) (hf i) (hg k) hcross
    apply hrz
    linear_combination hk - hkSupported
  have htriple :
      squareBracket (middleBracket (f i) (g j)) (g k) ≠ 0 := by
    rw [haxis]
    simpa only [map_smul, LinearMap.smul_apply] using
      smul_ne_zero hepsilon (hsquare' k)
  exact false_of_frattiniDiagonalSquareCommutator_ne_zero
    (GaloisField 2 n) hP hxi hPhiComm hfour hexists
    (f i) (g j) (g k) hrightOff hcrossOff htriple

end OddOrder.Higman.Suzuki2Groups
