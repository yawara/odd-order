/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniTripleJacobi

/-!
# Higman's Lemma 13: Jacobi after scalar extension

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The symmetry of the middle Frattini bracket and the Jacobi identity for the
actual `Phi(P)^2`-valued triple commutator survive extension of scalars to the
common Singer field.  In particular, a nonzero diagonal triple bracket is
incompatible with the two off-diagonal vanishings used in Higman's B/B case.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative TensorProduct

universe uP uF

local instance frattiniTripleBaseChangeJacobiLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniTripleBaseChangeJacobiLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- Symmetry of the middle Frattini bracket survives extension of scalars. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_comm
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
    ∀ (x y : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)),
      frattiniMiddleCommutatorBilinearBaseChange F
          hP hxi hPhiComm hexists x y =
        frattiniMiddleCommutatorBilinearBaseChange F
          hP hxi hPhiComm hexists y x := by
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          simp only [frattiniMiddleCommutatorBilinearBaseChange_tmul]
          rw [mul_comm, frattiniMiddleCommutatorBilinear_comm]
      | add y z hy hz => simp [hy, hz]
  | add x z hx hz => simp [hx, hz]

/-- **Higman Lemma 13 (p. 92), Jacobi after scalar extension.**

The Jacobi identity for the actual triple commutator remains valid after
extending all three source variables and the target to the Singer field. -/
theorem frattiniTripleCommutatorBaseChange_jacobi
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
    ∀ (x y z : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)),
      frattiniSquareCommutatorBilinearBaseChange F
            hP hxi hPhiComm hfour hexists
            (frattiniMiddleCommutatorBilinearBaseChange F
              hP hxi hPhiComm hexists x y) z +
          frattiniSquareCommutatorBilinearBaseChange F
            hP hxi hPhiComm hfour hexists
            (frattiniMiddleCommutatorBilinearBaseChange F
              hP hxi hPhiComm hexists y z) x +
          frattiniSquareCommutatorBilinearBaseChange F
            hP hxi hPhiComm hfour hexists
            (frattiniMiddleCommutatorBilinearBaseChange F
              hP hxi hPhiComm hexists z x) y = 0 := by
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
  let J := fun
      (x y z : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)) =>
    frattiniSquareCommutatorBilinearBaseChange F
          hP hxi hPhiComm hfour hexists
          (frattiniMiddleCommutatorBilinearBaseChange F
            hP hxi hPhiComm hexists x y) z +
        frattiniSquareCommutatorBilinearBaseChange F
          hP hxi hPhiComm hfour hexists
          (frattiniMiddleCommutatorBilinearBaseChange F
            hP hxi hPhiComm hexists y z) x +
        frattiniSquareCommutatorBilinearBaseChange F
          hP hxi hPhiComm hfour hexists
          (frattiniMiddleCommutatorBilinearBaseChange F
            hP hxi hPhiComm hexists z x) y
  change ∀ x y z, J x y z = 0
  have J_add_left (x w y z) :
      J (x + w) y z = J x y z + J w y z := by
    dsimp only [J]
    simp only [map_add, LinearMap.add_apply]
    abel
  have J_add_middle (x y w z) :
      J x (y + w) z = J x y z + J x w z := by
    dsimp only [J]
    simp only [map_add, LinearMap.add_apply]
    abel
  have J_add_right (x y z w) :
      J x y (z + w) = J x y z + J x y w := by
    dsimp only [J]
    simp only [map_add, LinearMap.add_apply]
    abel
  intro x y z
  induction x using TensorProduct.induction_on with
  | zero => simp [J]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [J]
      | tmul b y =>
          induction z using TensorProduct.induction_on with
          | zero => simp [J]
          | tmul c z =>
              have hJ := frattiniTripleCommutatorTrilinear_jacobi
                hP hxi hPhiComm hfour hexists x y z
              simp only [frattiniTripleCommutatorTrilinear_apply] at hJ
              dsimp only [J]
              simp only [frattiniMiddleCommutatorBilinearBaseChange_tmul,
                frattiniSquareCommutatorBilinearBaseChange_tmul]
              rw [show (b * c) * a = (a * b) * c by ring,
                show (c * a) * b = (a * b) * c by ring,
                ← TensorProduct.tmul_add, ← TensorProduct.tmul_add,
                hJ, TensorProduct.tmul_zero]
          | add z w hz hw => rw [J_add_right, hz, hw, add_zero]
      | add y w hy hw => rw [J_add_middle, hy, hw, add_zero]
  | add x w hx hw => rw [J_add_left, hx, hw, add_zero]

/-- **Higman Lemma 13 (p. 92), abstract B/B Jacobi obstruction.**

If the diagonal middle bracket brackets nontrivially once more with the
successor vector, while the two off-diagonal brackets required by Jacobi
vanish, the exponent-four branch is contradictory. -/
theorem false_of_frattiniDiagonalSquareCommutator_ne_zero
    (F : Type uF) [Field F] [Algebra (ZMod 2) F]
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y y' : F ⊗[ZMod 2] Additive (lowerCentralLayer P 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniMiddleCommutatorBilinearBaseChange F
        hP hxi hPhiComm hexists y y' = 0 →
    frattiniMiddleCommutatorBilinearBaseChange F
        hP hxi hPhiComm hexists x y' = 0 →
    frattiniSquareCommutatorBilinearBaseChange F
        hP hxi hPhiComm hfour hexists
        (frattiniMiddleCommutatorBilinearBaseChange F
          hP hxi hPhiComm hexists x y) y' ≠ 0 →
    False := by
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
  intro hyy' hxy' hne
  have hy'x : frattiniMiddleCommutatorBilinearBaseChange F
      hP hxi hPhiComm hexists y' x = 0 := by
    rw [frattiniMiddleCommutatorBilinearBaseChange_comm]
    exact hxy'
  have hJ := frattiniTripleCommutatorBaseChange_jacobi F
    hP hxi hPhiComm hfour hexists x y y'
  rw [hyy', hy'x] at hJ
  simp only [map_zero, LinearMap.zero_apply, add_zero] at hJ
  exact hne hJ

end OddOrder.Higman.Suzuki2Groups
