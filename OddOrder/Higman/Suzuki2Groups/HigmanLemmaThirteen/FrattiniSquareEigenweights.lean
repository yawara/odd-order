/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareCommutatorEquivariance

/-!
# Higman's Lemma 13: eigenweights of Frattini-square commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

Scalar extension turns the actual bracket
`Phi(P)/Phi(P)^2 × P/Phi(P) → Phi(P)^2` into a bilinear map over the
common Singer field.  Its actor equivariance forces every nonzero product of
middle and outer eigenvectors to have one of the Frobenius-conjugate weights
of the Frattini square.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP uF

local instance frattiniSquareEigenweightsLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniSquareEigenweightsLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- Scalar extension of the Frattini-square-valued commutator. -/
noncomputable def frattiniSquareCommutatorBilinearBaseChange
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    (F ⊗[ZMod 2] Additive (frattiniMiddleLayer P)) →ₗ[F]
      (F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)) →ₗ[F]
        (F ⊗[ZMod 2] Additive (frattiniSquare P)) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact (frattiniSquareCommutatorBilinear
    hP hxi hPhiComm hfour hexists).baseChange₂ F

/-- Evaluation of the scalar-extended bracket on pure tensors. -/
@[simp]
theorem frattiniSquareCommutatorBilinearBaseChange_tmul
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (a b : F) (u : Additive (frattiniMiddleLayer P))
    (v : Additive (lowerCentralLayer P 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniSquareCommutatorBilinearBaseChange F
        hP hxi hPhiComm hfour hexists
        (a ⊗ₜ[ZMod 2] u) (b ⊗ₜ[ZMod 2] v) =
      (a * b) ⊗ₜ[ZMod 2]
        frattiniSquareCommutatorBilinear
          hP hxi hPhiComm hfour hexists u v := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact LinearMap.baseChange₂_tmul
    (frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists) a b u v

/-- Equivariance of the Frattini-square-valued commutator survives scalar
extension. -/
theorem frattiniSquareCommutatorBilinearBaseChange_equivariant
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ (c : Y)
      (u : F ⊗[ZMod 2] Additive (frattiniMiddleLayer P))
      (v : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)),
      (elabRepresentation 2 hSquareInv.restrict c).baseChange F
          (frattiniSquareCommutatorBilinearBaseChange F
            hP hxi hPhiComm hfour hexists u v) =
        frattiniSquareCommutatorBilinearBaseChange F
          hP hxi hPhiComm hfour hexists
            ((actualAgemoOneQuotientRepresentation
              hPhiInv.restrict c).baseChange F u)
            ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro c u v
  exact LinearMap.baseChange₂_equivariant
    (frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists)
    (actualAgemoOneQuotientRepresentation hPhiInv.restrict c)
    (lowerCentralLayerRepresentation Y.subtype 0 c)
    (elabRepresentation 2 hSquareInv.restrict c)
    (frattiniSquareCommutatorBilinear_equivariant
      hP hxi hPhiComm hfour hexists c) u v

/-- A nonzero ground Frattini-square bracket remains nonzero after scalar
extension. -/
theorem frattiniSquareCommutatorBilinearBaseChange_one_tmul_ne_zero
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
    (u : Additive (frattiniMiddleLayer P))
    (v : Additive (lowerCentralLayer P 0))
    (huv : frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists u v ≠ 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hfour hexists
        ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] u)
        ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] v) ≠ 0 := by
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
  rw [frattiniSquareCommutatorBilinearBaseChange_tmul, one_mul]
  exact one_tmul_ne_zero_of_ne_zero eSquare huv

/-- **Higman Lemma 13 (p. 92), the Frattini-square weight equation.**

If the scalar-extended square-valued bracket is nonzero on a middle
eigenvector of weight `a` and an outer eigenvector of weight `b`, then `a*b`
is a Frobenius conjugate of the common Singer scalar `nu`. -/
theorem exists_frattiniSquareFrobeniusWeight_of_ne_zero
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
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ {u : GaloisField 2 n ⊗[ZMod 2]
          Additive (frattiniMiddleLayer P)}
      {v : GaloisField 2 n ⊗[ZMod 2]
          Additive (lowerCentralLayer P 0)}
      {a b : GaloisField 2 n},
      (actualAgemoOneQuotientRepresentation
          (IsAInvariant.of_characteristic Y.subtype).restrict c).baseChange
          (GaloisField 2 n) u = a • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v = b • v →
      frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hfour hexists u v ≠ 0 →
      ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        a * b = nu ^ (2 ^ k.val) := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
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
  intro u v a b hu hv hne
  have hSquareCompat : ∀ q,
      eSquare (elabRepresentation 2 hSquareInv.restrict c q) =
        nu * eSquare q := by
    intro q
    have h := DFunLike.congr_fun hconj (eSquare q)
    simpa [LinearEquiv.conj_apply] using h
  have hSquareEigen : ∀ k,
      (elabRepresentation 2 hSquareInv.restrict c).baseChange
          (GaloisField 2 n)
          (conjugateTensorBasisOfLinearEquiv
            (GaloisField 2 n) eSquare k) =
        nu ^ (2 ^ k.val) •
          conjugateTensorBasisOfLinearEquiv
            (GaloisField 2 n) eSquare k := by
    intro k
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 n) eSquare
      (elabRepresentation 2 hSquareInv.restrict c)
      nu hSquareCompat k
  exact exists_weight_eq_of_bilinear_ne_zero
    ((actualAgemoOneQuotientRepresentation
      hPhiInv.restrict c).baseChange (GaloisField 2 n))
    ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
      (GaloisField 2 n))
    ((elabRepresentation 2 hSquareInv.restrict c).baseChange
      (GaloisField 2 n))
    (frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hfour hexists)
    (conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eSquare)
    (fun k => nu ^ (2 ^ k.val))
    hSquareEigen
    (frattiniSquareCommutatorBilinearBaseChange_equivariant
      (GaloisField 2 n) hP hxi hPhiComm hfour hexists c)
    hu hv hne

end OddOrder.Higman.Suzuki2Groups
