/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniGradedCommutatorEquivariance
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedEigenweights
import OddOrder.GroupTheory.RepresentationTheory.BaseChange

/-!
# Higman's Lemma 13: eigenweights of middle Frattini commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

In the exponent-four branch, scalar extension turns the actual bracket
`P / Φ(P) × P / Φ(P) → Φ(P) / Φ(P)²` into a bilinear map over the common
Singer field.  Its equivariance forces every nonzero product of actor
eigenvectors to have one of the Frobenius-conjugate weights of the middle
Frattini layer.  The middle scalar is the canonical square root
`Frob⁻¹(ν)` of the scalar `ν` on `Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP uF

local instance instFrattiniMiddleEigenweightsLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniMiddleEigenweightsLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- Scalar extension of the middle Frattini commutator. -/
noncomputable def frattiniMiddleCommutatorBilinearBaseChange
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    (F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)) →ₗ[F]
      (F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)) →ₗ[F]
        (F ⊗[ZMod 2] Additive (frattiniMiddleLayer P)) := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  exact (frattiniMiddleCommutatorBilinear
    hP hxi hPhiComm hexists).baseChange₂ F

@[simp]
theorem frattiniMiddleCommutatorBilinearBaseChange_tmul
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (a b : F) (u v : Additive (lowerCentralLayer P 0)) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinearBaseChange F
        hP hxi hPhiComm hexists
        (a ⊗ₜ[ZMod 2] u) (b ⊗ₜ[ZMod 2] v) =
      (a * b) ⊗ₜ[ZMod 2]
        frattiniMiddleCommutatorBilinear
          hP hxi hPhiComm hexists u v := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  exact LinearMap.baseChange₂_tmul
    (frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists) a b u v

/-- Equivariance of the middle Frattini commutator survives scalar extension. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_equivariant
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (c : Y)
      (u v : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)),
      (actualAgemoOneQuotientRepresentation hPhiInv.restrict c).baseChange F
          (frattiniMiddleCommutatorBilinearBaseChange F
            hP hxi hPhiComm hexists u v) =
        frattiniMiddleCommutatorBilinearBaseChange F
          hP hxi hPhiComm hexists
            ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F u)
            ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro c u v
  exact LinearMap.baseChange₂_equivariant
    (frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists)
    (lowerCentralLayerRepresentation Y.subtype 0 c)
    (lowerCentralLayerRepresentation Y.subtype 0 c)
    (actualAgemoOneQuotientRepresentation hPhiInv.restrict c)
    (frattiniMiddleCommutatorBilinear_equivariant
      hP hxi hPhiComm hexists c) u v

/-- A nonzero ground middle bracket remains nonzero after scalar extension. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_one_tmul_ne_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (u v : Additive (lowerCentralLayer P 0))
    (huv : frattiniMiddleCommutatorBilinear
      hP hxi hPhiComm hexists u v ≠ 0) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hexists
        ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] u)
        ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] v) ≠ 0 := by
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  rw [frattiniMiddleCommutatorBilinearBaseChange_tmul, one_mul]
  exact one_tmul_ne_zero_of_ne_zero
    (frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare) huv

/-- **Higman Lemma 13 (p. 92), the middle Frattini weight equation.**

If the scalar-extended middle bracket is nonzero on two actor eigenvectors,
the product of their eigenvalues is a Frobenius conjugate of the canonical
middle scalar `Frob⁻¹(ν)`. -/
theorem exists_frattiniMiddleFrobeniusWeight_of_ne_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat} (c : Y)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
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
    ∀ {u v : GaloisField 2 n ⊗[ZMod 2]
          Additive (lowerCentralLayer P 0)}
      {a b : GaloisField 2 n},
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) u = a • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v = b • v →
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v ≠ 0 →
      ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        a * b =
          ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
            (2 ^ k.val) := by
  classical
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let eMiddle :=
    frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  intro u v a b hu hv hne
  have hMiddleCompat : ∀ q,
      eMiddle (actualAgemoOneQuotientRepresentation hPhiInv.restrict c q) =
        middleWeight * eMiddle q :=
    frattiniMiddleCoordinate_generator_compatible
      hP hxi hPhiComm hfour hexists c eSquare nu hconj
  have hMiddleEigen : ∀ k,
      (actualAgemoOneQuotientRepresentation hPhiInv.restrict c).baseChange
          (GaloisField 2 n)
          (conjugateTensorBasisOfLinearEquiv
            (GaloisField 2 n) eMiddle k) =
        middleWeight ^ (2 ^ k.val) •
          conjugateTensorBasisOfLinearEquiv
            (GaloisField 2 n) eMiddle k := by
    intro k
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 n) eMiddle
      (actualAgemoOneQuotientRepresentation hPhiInv.restrict c)
      middleWeight hMiddleCompat k
  exact exists_weight_eq_of_bilinear_ne_zero
    ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
      (GaloisField 2 n))
    ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
      (GaloisField 2 n))
    ((actualAgemoOneQuotientRepresentation hPhiInv.restrict c).baseChange
      (GaloisField 2 n))
    (frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hexists)
    (conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle)
    (fun k => middleWeight ^ (2 ^ k.val))
    hMiddleEigen
    (frattiniMiddleCommutatorBilinearBaseChange_equivariant
      (GaloisField 2 n) hP hxi hPhiComm hexists c)
    hu hv hne

end OddOrder.Higman.Suzuki2Groups
