/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorTypeBSquareNonzero

/-!
# Higman Lemma 13: type-B square brackets on Frobenius eigenvectors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The type-B monomial formula survives scalar extension. On each matching pair
of the canonical common-middle basis and the restricted factor ambient
eigenfamily, the square-valued bracket is a nonzero multiple of the matching
canonical square basis vector.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP uK uU uV uW

variable {K : Type uK} [Field K] [Finite K] [Algebra (ZMod 2) K]

private theorem transported_repr_tmul {W : Type uW}
    [AddCommGroup W] [Module (ZMod 2) W]
    (eW : W ≃ₗ[ZMod 2] K) (a : K) (w : W)
    (q : Fin (Module.finrank (ZMod 2) K)) :
    (conjugateTensorBasisOfLinearEquiv K eW).repr
        (a ⊗ₜ[ZMod 2] w) q =
      a * (eW w) ^ (2 ^ q.val) := by
  change (conjugateTensorBasis K).repr
    (eW.baseChange (ZMod 2) K W K (a ⊗ₜ[ZMod 2] w)) q = _
  rw [LinearEquiv.baseChange_tmul,
    conjugateTensorBasis_repr_apply,
    frobeniusTensorCoordinates_tmul]

private theorem transported_monomial_coordinate
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (eU : U ≃ₗ[ZMod 2] K) (eW : W ≃ₗ[ZMod 2] K)
    (iota : K →ₗ[ZMod 2] V)
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (c0 : K)
    (hB : ∀ u beta, eW (B u (iota beta)) =
      c0 * (eU u * beta))
    (x : K ⊗[ZMod 2] U) (y : K ⊗[ZMod 2] K)
    (q : Fin (Module.finrank (ZMod 2) K)) :
    (conjugateTensorBasisOfLinearEquiv K eW).repr
        (B.baseChange₂ K x (iota.baseChange K y)) q =
      c0 ^ (2 ^ q.val) *
        (conjugateTensorBasisOfLinearEquiv K eU).repr x q *
        (conjugateTensorBasisOfLinearEquiv K
          (LinearEquiv.refl (ZMod 2) K)).repr y q := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b beta =>
          simp only [LinearMap.baseChange_tmul, LinearMap.baseChange₂_tmul]
          rw [transported_repr_tmul, transported_repr_tmul,
            transported_repr_tmul]
          rw [hB, LinearEquiv.refl_apply, mul_pow, mul_pow]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply]
          rw [hy, hz]
          ring
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply]
      rw [hx, hz]
      ring

private theorem transported_monomial_diagonal
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (eU : U ≃ₗ[ZMod 2] K) (eW : W ≃ₗ[ZMod 2] K)
    (iota : K →ₗ[ZMod 2] V)
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (c0 : K)
    (hB : ∀ u beta, eW (B u (iota beta)) =
      c0 * (eU u * beta))
    (i : Fin (Module.finrank (ZMod 2) K)) :
    B.baseChange₂ K
        (conjugateTensorBasisOfLinearEquiv K eU i)
        (iota.baseChange K
          (conjugateTensorBasisOfLinearEquiv K
            (LinearEquiv.refl (ZMod 2) K) i)) =
      c0 ^ (2 ^ i.val) •
        conjugateTensorBasisOfLinearEquiv K eW i := by
  apply (conjugateTensorBasisOfLinearEquiv K eW).repr.injective
  ext q
  rw [transported_monomial_coordinate eU eW iota B c0 hB]
  simp only [(conjugateTensorBasisOfLinearEquiv K eU).repr_self_apply,
    (conjugateTensorBasisOfLinearEquiv K
      (LinearEquiv.refl (ZMod 2) K)).repr_self_apply,
    map_smul, Finsupp.smul_apply,
    (conjugateTensorBasisOfLinearEquiv K eW).repr_self_apply]
  by_cases hiq : i = q
  · subst q
    simp
  · simp [hiq]

/-- **Higman Lemma 13 (p. 92), type-B diagonal square bracket.**

For the exact ambient eigenfamily constructed by
`exists_restrictedFactorAmbientEigenFamily`, every matching canonical middle
basis vector has a nonzero square-valued bracket with the factor vector.
More precisely, the bracket is `c₀^(2^i)` times the matching canonical
square basis vector, for one fixed nonzero `c₀`. -/
theorem exists_restrictedFactorTypeBSquareEigenCommutator
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P} [Finite S]
    (hSinv : IsAInvariant Y.subtype S)
    (hEAS : IsElementaryAbelian 2 (frattini S))
    (hMap : (frattini S).map S.subtype = frattiniSquare P)
    (hxiS : IsXiActor hSinv.restrict.range)
    (hinvPhiS : involutions S ⊆ frattini S)
    {n : Nat} (hn : 0 < n)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (eS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      Additive (frattini S) ≃ₗ[ZMod 2] GaloisField 2 n)
    (heS :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eS = (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare)
    (nu : GaloisField 2 n)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (c : Y)
    (hconjS :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      eS.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic
              hSinv.restrict.range.subtype).restrict
              (hSinv.restrict.rangeRestrict c)) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (factors : XiLengthThreeTypeAFactorData S hSinv.restrict.range)
    (left :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.left_invariant
        factors.frattini_lt_left.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (right :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      FactorCoordinateData factors.right_invariant
        factors.frattini_lt_right.le
        (hSinv.restrict.rangeRestrict c) eS nu)
    (hleft : factors.left = (frattini P).subgroupOf S)
    (hleftTheta :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      left.theta = 1)
    (hrightTheta :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      right.theta = 1)
    (hK1S : lowerCentralLayerKernel S 1 = ⊥)
    (htermS : lowerCentralTerm S 1 = frattini S)
    (hSqS : LowerCentralSquaresLieInSecond S)
    (hAgemoS : Agemo S 2 1 = frattini S)
    (hK0S : lowerCentralLayerKernel S 0 =
      (frattini S).subgroupOf (lowerCentralTerm S 0)) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
    letI : IsMulCommutative (lowerCentralLayer P 0) :=
      lowerCentralLayerIsMulCommutative P 0
    letI : CommGroup (lowerCentralLayer P 0) :=
      { (inferInstance : Group (lowerCentralLayer P 0)) with
        mul_comm := (lowerCentralLayer_isElementaryAbelian P 0).comm }
    letI : Module (ZMod 2) (Additive (lowerCentralLayer P 0)) :=
      lowerCentralLayerZmodModule P 0
    let eMiddle :=
      frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
    let middleBasis :=
      conjugateTensorBasisOfLinearEquiv
        (GaloisField 2 n) eMiddle
    let squareBasis :=
      conjugateTensorBasisOfLinearEquiv
        (GaloisField 2 n) eSquare
    let middleWeight :=
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu
    let iota :=
      restrictedFactorAmbientInclusion hSinv hEAS eS c right
        hK1S htermS hSqS hAgemoS hK0S
    let family :=
      factorAmbientEigenFamily
        (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
    let bracket :=
      frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hfour hexists
    ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
      ∀ i : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
              (GaloisField 2 n) (family i) =
            middleWeight ^ (2 ^ i.val) • family i ∧
          bracket (middleBasis i) (family i) =
              c0 ^ (2 ^ i.val) • squareBasis i ∧
            bracket (middleBasis i) (family i) ≠ 0 := by
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
  let : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  let : CommGroup (frattini S) := inferInstance
  let : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
  let : IsMulCommutative (lowerCentralLayer P 0) :=
    lowerCentralLayerIsMulCommutative P 0
  let : CommGroup (lowerCentralLayer P 0) :=
    { (inferInstance : Group (lowerCentralLayer P 0)) with
      mul_comm := (lowerCentralLayer_isElementaryAbelian P 0).comm }
  let : Module (ZMod 2) (Additive (lowerCentralLayer P 0)) :=
    lowerCentralLayerZmodModule P 0
  let eMiddle :=
    frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
  let middleBasis :=
    conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
  let squareBasis :=
    conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eSquare
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  let iota :=
    restrictedFactorAmbientInclusion hSinv hEAS eS c right
      hK1S htermS hSqS hAgemoS hK0S
  let family :=
    factorAmbientEigenFamily
      (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
  let B :=
    frattiniSquareCommutatorBilinear
      hP hxi hPhiComm hfour hexists
  let bracket :=
    frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hfour hexists
  obtain ⟨c0, hc0, hmono⟩ :=
    exists_restrictedFactorTypeBSquareCommutator_monomial
      hP hxi hPhiComm hfour hexists hSinv hEAS hMap hxiS hinvPhiS
      hn eSquare eS heS nu hnuPrimitive c hconjS factors left right
      hleft hleftTheta hrightTheta hK1S htermS hSqS hAgemoS hK0S
  have hB : ∀ u beta, eSquare (B u (iota beta)) =
      c0 * (eMiddle u * beta) := by
    intro u beta
    have h := hmono (eMiddle u) beta
    simpa only [B, iota, eMiddle,
      LinearEquiv.symm_apply_apply] using h
  refine ⟨c0, hc0, fun i => ?_⟩
  have hrightLambda : right.lambda = middleWeight :=
    FactorCoordinateData.lambda_eq_middleWeight_of_theta_eq_one
      right hrightTheta
  let eRefl :=
    LinearEquiv.refl (ZMod 2) (GaloisField 2 n)
  let Aq : Module.End (ZMod 2) (GaloisField 2 n) :=
    Algebra.lmul (ZMod 2) (GaloisField 2 n) right.lambda
  have hAq : ∀ v, eRefl (Aq v) = right.lambda * eRefl v := by
    intro v
    rfl
  have hiota : ∀ v, iota (Aq v) =
      lowerCentralLayerRepresentation Y.subtype 0 c (iota v) := by
    intro v
    rw [show Aq v = right.lambda • v by rfl]
    exact (restrictedFactorAmbientInclusion_representation
      hSinv hEAS eS c right hK1S htermS hSqS hAgemoS hK0S v).symm
  have heigenRaw := factorAmbientEigenFamily_eigen
    c eRefl Aq right.lambda hAq iota hiota i
  have heigen :
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
        middleWeight ^ (2 ^ i.val) • family i := by
    simpa only [family, eRefl, hrightLambda] using heigenRaw
  have hdiag := transported_monomial_diagonal
    eMiddle eSquare iota B c0 hB i
  have heq : bracket (middleBasis i) (family i) =
      c0 ^ (2 ^ i.val) • squareBasis i := by
    simpa only [bracket, middleBasis, family, squareBasis, B,
      factorAmbientEigenFamily, iota,
      frattiniSquareCommutatorBilinearBaseChange, id_eq] using hdiag
  refine ⟨heigen, heq, ?_⟩
  rw [heq]
  exact smul_ne_zero (pow_ne_zero _ hc0) (squareBasis.ne_zero i)

end OddOrder.Higman.Suzuki2Groups
