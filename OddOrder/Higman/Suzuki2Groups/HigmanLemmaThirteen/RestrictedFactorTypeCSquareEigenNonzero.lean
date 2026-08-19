/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorAmbientEigenvectors
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorTypeCSquareNonzero

/-!
# Higman's Lemma 13: type-C square brackets on Frobenius eigenvectors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

The type-C monomial formula survives scalar extension.  Its two Frobenius
exponents shift the source and middle indices, and the sharp equation
`2r + 1 = n` makes the two shifts meet in one square coordinate.  Consequently
every pair required by Higman's type-C/C Jacobi argument has nonzero
square-valued bracket.
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

/-- Add `s` cyclically to a Frobenius-coordinate index. -/
private noncomputable def frobeniusCoordinateShift
    (i : Fin (Module.finrank (ZMod 2) K)) (s : Nat) :
    Fin (Module.finrank (ZMod 2) K) :=
  ⟨(i.val + s) % Module.finrank (ZMod 2) K,
    Nat.mod_lt _ Module.finrank_pos⟩

private theorem pow_two_frobeniusCoordinateShift (x : K)
    (i : Fin (Module.finrank (ZMod 2) K)) (s : Nat) :
    x ^ (2 ^ (frobeniusCoordinateShift (K := K) i s).val) =
      (x ^ (2 ^ s)) ^ (2 ^ i.val) := by
  let m := Module.finrank (ZMod 2) K
  let sigma := FiniteField.frobeniusAlgHom (ZMod 2) K
  have hsigmaOrder : orderOf sigma = m :=
    FiniteField.orderOf_frobeniusAlgHom (ZMod 2) K
  have hsigmaPow : sigma ^ m = 1 := by
    rw [← hsigmaOrder]
    exact pow_orderOf_eq_one sigma
  have hmod : Nat.ModEq m
      (frobeniusCoordinateShift (K := K) i s).val (i.val + s) :=
    Nat.mod_modEq (i.val + s) m
  have happ := DFunLike.congr_fun
    (pow_eq_pow_of_modEq hmod hsigmaPow) x
  have hraw :
      x ^ (2 ^ (frobeniusCoordinateShift (K := K) i s).val) =
        x ^ (2 ^ (i.val + s)) := by
    simpa only [sigma, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom,
      pow_iterate, ZMod.card, AlgHom.one_apply] using happ
  calc
    x ^ (2 ^ (frobeniusCoordinateShift (K := K) i s).val) =
        x ^ (2 ^ (i.val + s)) := hraw
    _ = x ^ (2 ^ i.val * 2 ^ s) := by rw [pow_add]
    _ = x ^ (2 ^ s * 2 ^ i.val) := by rw [mul_comm]
    _ = (x ^ (2 ^ s)) ^ (2 ^ i.val) := pow_mul x _ _

private theorem frobeniusCoordinateShift_injective (s : Nat) :
    Function.Injective
      (fun i : Fin (Module.finrank (ZMod 2) K) =>
        frobeniusCoordinateShift (K := K) i s) := by
  let m := Module.finrank (ZMod 2) K
  let : NeZero m := ⟨Module.finrank_pos.ne'⟩
  let sFin : Fin m := ⟨s % m, Nat.mod_lt _ Module.finrank_pos⟩
  have hshift (i : Fin m) :
      frobeniusCoordinateShift (K := K) i s = i + sFin := by
    apply Fin.ext
    simp [frobeniusCoordinateShift, sFin, m, Fin.val_add, Nat.add_mod]
  intro i j hij
  apply (Equiv.addRight sFin).injective
  simpa only [Equiv.coe_addRight, ← hshift] using hij

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

private theorem transported_frobenius_monomial_coordinate
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (eU : U ≃ₗ[ZMod 2] K) (eW : W ≃ₗ[ZMod 2] K)
    (iota : K →ₗ[ZMod 2] V)
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (c0 : K) (s t : Nat)
    (hB : ∀ u beta, eW (B u (iota beta)) =
      c0 * (beta ^ 2 ^ t * (eU u) ^ 2 ^ s))
    (x : K ⊗[ZMod 2] U) (y : K ⊗[ZMod 2] K)
    (q : Fin (Module.finrank (ZMod 2) K)) :
    (conjugateTensorBasisOfLinearEquiv K eW).repr
        (B.baseChange₂ K x (iota.baseChange K y)) q =
      c0 ^ (2 ^ q.val) *
        (conjugateTensorBasisOfLinearEquiv K
          (LinearEquiv.refl (ZMod 2) K)).repr y
            (frobeniusCoordinateShift (K := K) q t) *
        (conjugateTensorBasisOfLinearEquiv K eU).repr x
          (frobeniusCoordinateShift (K := K) q s) := by
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
          rw [← pow_two_frobeniusCoordinateShift beta q t,
            ← pow_two_frobeniusCoordinateShift (eU u) q s]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply]
          rw [hy, hz]
          ring
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply]
      rw [hx, hz]
      ring

private theorem transported_frobenius_monomial_basis
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (eU : U ≃ₗ[ZMod 2] K) (eW : W ≃ₗ[ZMod 2] K)
    (iota : K →ₗ[ZMod 2] V)
    (B : U →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (c0 : K) (s t : Nat)
    (hB : ∀ u beta, eW (B u (iota beta)) =
      c0 * (beta ^ 2 ^ t * (eU u) ^ 2 ^ s))
    (k a q : Fin (Module.finrank (ZMod 2) K))
    (hk : frobeniusCoordinateShift (K := K) q s = k)
    (ha : frobeniusCoordinateShift (K := K) q t = a) :
    B.baseChange₂ K
        (conjugateTensorBasisOfLinearEquiv K eU k)
        (iota.baseChange K
          (conjugateTensorBasisOfLinearEquiv K
            (LinearEquiv.refl (ZMod 2) K) a)) =
      c0 ^ (2 ^ q.val) •
        conjugateTensorBasisOfLinearEquiv K eW q := by
  apply (conjugateTensorBasisOfLinearEquiv K eW).repr.injective
  ext p
  rw [transported_frobenius_monomial_coordinate
    eU eW iota B c0 s t hB]
  simp only [(conjugateTensorBasisOfLinearEquiv K eU).repr_self_apply,
    (conjugateTensorBasisOfLinearEquiv K
      (LinearEquiv.refl (ZMod 2) K)).repr_self_apply,
    map_smul, Finsupp.smul_apply,
    (conjugateTensorBasisOfLinearEquiv K eW).repr_self_apply]
  by_cases hpq : p = q
  · subst p
    simp [hk, ha]
  · have hps : frobeniusCoordinateShift (K := K) p s ≠ k := by
      intro hp
      apply hpq
      exact frobeniusCoordinateShift_injective (K := K) s
        (hp.trans hk.symm)
    have hkps : k ≠ frobeniusCoordinateShift (K := K) p s := hps.symm
    have hqp : q ≠ p := Ne.symm hpq
    simp [hkps, hqp]

private theorem fin_eq_of_zmod_val_eq {m n : Nat} (hmn : m = n)
    {i j : Fin m} (h : (i.val : ZMod n) = (j.val : ZMod n)) : i = j := by
  apply Fin.ext
  have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val n).mp h
  have hi : i.val < n := by omega
  have hj : j.val < n := by omega
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

/-- **Higman Lemma 13 (printed p. 93), shifted type-C square bracket.**

For the canonical ambient eigenfamily of a restricted type-C factor, a
middle basis vector at index `k` has nonzero square bracket with every family
vector at index `a` satisfying `a + 1 = k + r` modulo `n`.  This is exactly
the nondegeneracy input used in the type-C/C Jacobi argument.
-/
theorem exists_restrictedFactorTypeCSquareEigenCommutator
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
    {n r : Nat} (hn : 2 ≤ n)
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
    (hleftSource :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      nu = left.lambda * left.lambda)
    (hrightSource :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      nu = right.lambda * right.theta right.lambda)
    (hr : 0 < r)
    (h2r : 2 * r ≤ n)
    (hrightTheta :
      letI : IsMulCommutative (frattini S) :=
        IsMulCommutative.of_comm hEAS.comm
      letI : Module (ZMod 2) (Additive (frattini S)) := hEAS.zmodModule
      right.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
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
      conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
    let iota :=
      restrictedFactorAmbientInclusion hSinv hEAS eS c right
        hK1S htermS hSqS hAgemoS hK0S
    let family := factorAmbientEigenFamily
      (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
    let bracket :=
      frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hfour hexists
    2 * r + 1 = n ∧
      ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
        (∀ i,
          (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
              (GaloisField 2 n) (family i) =
            right.lambda ^ (2 ^ i.val) • family i) ∧
        ∀ k a,
          (a.val : ZMod n) + 1 =
              (k.val : ZMod n) + (r : ZMod n) →
          bracket (middleBasis k) (family a) ≠ 0 := by
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
  let iota :=
    restrictedFactorAmbientInclusion hSinv hEAS eS c right
      hK1S htermS hSqS hAgemoS hK0S
  let family := factorAmbientEigenFamily
    (LinearEquiv.refl (ZMod 2) (GaloisField 2 n)) iota
  let B := frattiniSquareCommutatorBilinear
    hP hxi hPhiComm hfour hexists
  let bracket :=
    frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
      hP hxi hPhiComm hfour hexists
  obtain ⟨h2r1, c0, hc0, hmono⟩ :=
    exists_restrictedFactorTypeCSquareCommutator_monomial
      hP hxi hPhiComm hfour hexists hSinv hEAS hMap hxiS hinvPhiS
      hn eSquare eS heS nu hnuPrimitive c hconjS factors left right
      hleft hleftSource hrightSource hr h2r hrightTheta
      hK1S htermS hSqS hAgemoS hK0S
  have hB : ∀ u beta, eSquare (B u (iota beta)) =
      c0 * (beta ^ 2 ^ (n - 1) * (eMiddle u) ^ 2 ^ (r + 1)) := by
    intro u beta
    have h := hmono (eMiddle u) beta
    simpa only [B, iota, eMiddle,
      LinearEquiv.symm_apply_apply] using h
  refine ⟨h2r1, c0, hc0, ?_, ?_⟩
  · intro i
    let eRefl := LinearEquiv.refl (ZMod 2) (GaloisField 2 n)
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
    simpa only [family, eRefl] using heigenRaw
  · intro k a hindex
    have hn0 : n ≠ 0 := by omega
    have hfinrank :
        Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
      GaloisField.finrank 2 hn0
    let q := frobeniusCoordinateShift
      (K := GaloisField 2 n) a 1
    have hperiod :
        (2 : ZMod n) * (r : ZMod n) + 1 = 0 := by
      calc
        (2 : ZMod n) * (r : ZMod n) + 1 =
            ((2 * r + 1 : Nat) : ZMod n) := by norm_num
        _ = (n : ZMod n) := by rw [h2r1]
        _ = 0 := ZMod.natCast_self n
    have hqk : frobeniusCoordinateShift
        (K := GaloisField 2 n) q (r + 1) = k := by
      apply fin_eq_of_zmod_val_eq hfinrank
      simp only [q, frobeniusCoordinateShift]
      simp only [hfinrank, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
      linear_combination hindex + hperiod
    have hnminus : ((n - 1 : Nat) : ZMod n) + 1 = 0 := by
      calc
        ((n - 1 : Nat) : ZMod n) + 1 =
            ((n - 1 + 1 : Nat) : ZMod n) := by norm_num
        _ = (n : ZMod n) := by rw [show n - 1 + 1 = n by omega]
        _ = 0 := ZMod.natCast_self n
    have hqa : frobeniusCoordinateShift
        (K := GaloisField 2 n) q (n - 1) = a := by
      apply fin_eq_of_zmod_val_eq hfinrank
      simp only [q, frobeniusCoordinateShift]
      simp only [hfinrank, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
      linear_combination hnminus
    have hdiag := transported_frobenius_monomial_basis
      eMiddle eSquare iota B c0 (r + 1) (n - 1) hB k a q hqk hqa
    have heq : bracket (middleBasis k) (family a) =
        c0 ^ (2 ^ q.val) • squareBasis q := by
      simpa only [bracket, middleBasis, family, squareBasis, B,
        factorAmbientEigenFamily, iota,
        frattiniSquareCommutatorBilinearBaseChange, id_eq] using hdiag
    rw [heq]
    exact smul_ne_zero (pow_ne_zero _ hc0) (squareBasis.ne_zero q)

end OddOrder.Higman.Suzuki2Groups
