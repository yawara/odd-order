/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleDiagonalZero
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleDiagonalSupport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCrossCommutatorInclusion

/-!
# Higman's Lemma 13: cross commutators of type-B eigenfamily spans

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

This file composes the three fixed layers of the type-B/type-B argument.
Jacobi kills every diagonal middle bracket, Frobenius support extends that
vanishing to the two eigenfamily spans, and faithful scalar descent places
the subgroup cross commutator in `Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped commutatorElement IsMulCommutative TensorProduct

universe uP

local instance typeBEigenfamilyCrossCommutatorLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance
    typeBEigenfamilyCrossCommutatorLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), type-B/type-B cross commutator.**

Let `f` and `g` be the canonical-weight Frobenius eigenfamilies associated
to two type-B factors.  If the canonical middle basis pairs nontrivially
with `g`, and the spans of `f` and `g` contain all ambient ground classes
from `X` and `Z`, respectively, then `[X,Z] ≤ Φ(P)²`.

The proof only composes diagonal Jacobi vanishing, diagonal support, and the
existing group-level span descent theorem. -/
theorem commutator_le_frattiniSquare_of_typeB_eigenfamily_spans
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
            hP hxi hPhiComm hfour hexists (middleBasis k) (g k) ≠ 0)
    (X Z : Subgroup P)
    (hXspan : ∀ x : lowerCentralTerm X 0,
      (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
              (subgroupLowerCentralTermZeroHom X x)) ∈
        Submodule.span (GaloisField 2 n) (Set.range f))
    (hZspan : ∀ z : lowerCentralTerm Z 0,
      (1 : GaloisField 2 n) ⊗ₜ[ZMod 2]
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
              (subgroupLowerCentralTermZeroHom Z z)) ∈
        Submodule.span (GaloisField 2 n) (Set.range g)) :
    ⁅X, Z⁆ ≤ frattiniSquare P := by
  classical
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  have hdiagonal : ∀ i,
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists (f i) (g i) = 0 :=
    frattiniMiddleCommutatorBilinearBaseChange_diagonal_eq_zero_of_square_ne_zero
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      f g hf hg hsquare
  have hsupport :
      Submodule.map₂
          (frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
            hP hxi hPhiComm hexists)
          (Submodule.span (GaloisField 2 n) (Set.range f))
          (Submodule.span (GaloisField 2 n) (Set.range g)) =
        Submodule.span (GaloisField 2 n)
          (Set.range fun i ↦
            frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
              hP hxi hPhiComm hexists (f i) (g i)) :=
    frattiniMiddleCommutatorBilinearBaseChange_map₂_span_range_eq_span_diagonal
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      f g hf hg
  exact commutator_le_frattiniSquare_of_diagonal_eq_zero
    hP hxi hPhiComm hexists X Z f g hXspan hZspan hdiagonal hsupport

end OddOrder.Higman.Suzuki2Groups
