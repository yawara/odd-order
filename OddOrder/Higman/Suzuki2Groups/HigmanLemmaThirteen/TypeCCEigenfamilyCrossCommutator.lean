/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleTypeCCCrossZero
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorCrossCommutatorInclusion

/-!
# Higman's Lemma 13: cross commutators of type-C/C eigenfamily spans

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

This is the generic span connector for two type-C eigenfamilies.  Same-family
middle vanishing and shifted type-C square nondegeneracy are explicit inputs;
the restricted-factor layer supplies them later.  The Jacobi argument kills
every generator pair, bilinearity kills the image of both spans, and faithful
scalar descent places the subgroup cross commutator in `Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped commutatorElement IsMulCommutative TensorProduct

universe uP

local instance typeCCEigenfamilyCrossCommutatorLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance
    typeCCEigenfamilyCrossCommutatorLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (printed p. 93), type-C/type-C span connector.**

Let `f` and `g` be type-C Frobenius eigenfamilies with their common sharp
parameter.  If same-family middle brackets vanish, the required shifted
middle-square brackets are nonzero, and the two spans contain all ambient
ground classes from `X` and `Z`, then `[X,Z] ≤ Φ(P)²`. -/
theorem commutator_le_frattiniSquare_of_typeCC_eigenfamily_spans
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
            hP hxi hPhiComm hfour hexists (middleBasis k) (g a) ≠ 0)
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
  let beta := frattiniMiddleCommutatorBilinearBaseChange
    (GaloisField 2 n) hP hxi hPhiComm hexists
  have hzero : ∀ i j, beta (f i) (g j) = 0 :=
    frattiniMiddleCommutatorBilinearBaseChange_typeCC_eq_zero_of_square_ne_zero
      hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
      hnuPrimitive hconj lambda rho theta psi hlambdaSource hrhoSource
      htheta hpsi f g hf hg hfSame hgSame hfSquare hgSquare
  have hmap : Submodule.map₂ beta
        (Submodule.span (GaloisField 2 n) (Set.range f))
        (Submodule.span (GaloisField 2 n) (Set.range g)) = ⊥ := by
    rw [Submodule.map₂_span_span]
    apply (Submodule.span_eq_bot).2
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hzero i j
  exact commutator_le_frattiniSquare_of_map₂_eq_bot
    hP hxi hPhiComm hexists X Z f g hXspan hZspan hmap

end OddOrder.Higman.Suzuki2Groups
