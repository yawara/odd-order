/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoPowerCongruence

/-!
# Higman's Lemma 13: support of middle Frattini commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For type-B factors the outer eigenvalue is the canonical square root of the
Singer scalar on `Φ(P)²`.  Higman's two-power congruence then shows that the
actual middle commutator can be nonzero only on equal Frobenius indices; its
output index is their cyclic successor.  In particular, distinct eigenspaces
commute in the middle graded layer.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleSupportLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniMiddleSupportLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), type-B middle weight.**

A factor with trivial semilinear automorphism has the canonical middle-layer
weight `Frob⁻¹(ν)`. -/
theorem FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : Nat}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : FactorCoordinateData hSinv hPhiS c ePhi nu)
    (htheta : data.theta = 1) :
    data.lambda =
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu := by
  cases data with
  | commutative d =>
      exact d.lambda_eq
  | noncommutative _ d =>
      exact (d.theta_ne_one htheta).elim

/-- **Higman Lemma 13 (p. 92), B/B middle support.**

If the actual middle Frattini bracket is nonzero on two conjugate eigenvectors
of weight `Frob⁻¹(ν)`, their indices agree and the output weight has the cyclic
successor index. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_support_of_ne_zero
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
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (u v : GaloisField 2 n ⊗[ZMod 2]
        Additive (lowerCentralLayer P 0)),
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) u =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ j.val) • v →
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v ≠ 0 →
      i = j ∧
        ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
          (k.val : ZMod n) = (i.val : ZMod n) + 1 := by
  classical
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro i j u v hu hv hne
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  obtain ⟨k, hweight⟩ :=
    exists_frattiniMiddleFrobeniusWeight_of_ne_zero
      hP hxi hPhiComm hfour hexists c eSquare nu hconj
      hu hv hne
  have hprimMiddle : IsPrimitiveRoot middleWeight (2 ^ n - 1) :=
    hnuPrimitive.map_of_injective
      (frobeniusEquiv (GaloisField 2 n) 2).symm.injective
  have hordMiddle : orderOf middleWeight = 2 ^ n - 1 :=
    hprimMiddle.eq_orderOf.symm
  have hpow : middleWeight ^ (2 ^ i.val + 2 ^ j.val) =
      middleWeight ^ 2 ^ k.val := by
    rw [pow_add]
    exact hweight
  have hcongruence := higman_two_pow_add_congruence_of_pow_eq
    (by omega : 0 < n) hordMiddle hpow
  obtain ⟨hij, hk⟩ := higman_two_pow_add_eq_two_pow
    (by omega : 0 < n) hcongruence
  refine ⟨?_, ⟨k, hk⟩⟩
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 (by omega)
  have hi : i.val < n := by simpa [hfinrank] using i.isLt
  have hj : j.val < n := by simpa [hfinrank] using j.isLt
  apply Fin.ext
  have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val n).mp hij
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

/-- **Higman Lemma 13 (p. 92), off-diagonal B/B vanishing.**

Distinct Frobenius eigenspaces of the canonical middle weight have zero
middle Frattini commutator. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_eq_zero_of_ne
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
    (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
    (u v : GaloisField 2 n ⊗[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (hu : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) u =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ i.val) • u)
    (hv : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) v =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ j.val) • v)
    (hij : i ≠ j) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hexists u v = 0 := by
  classical
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  by_contra hne
  exact hij
    (frattiniMiddleCommutatorBilinearBaseChange_support_of_ne_zero
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i j u v hu hv hne).1

end OddOrder.Higman.Suzuki2Groups
