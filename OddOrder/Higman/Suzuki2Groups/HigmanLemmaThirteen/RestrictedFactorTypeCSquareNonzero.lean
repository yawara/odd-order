/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorMixedTermBridge
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman's Lemma 13: nonzero type-C square commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed pp. 92--93 (PDF pages 13--14).

For a restricted length-three factor pair whose right factor has type C,
Lemma 12 makes the internal mixed term a nonzero Frobenius monomial.  After
transposing the factor order, the restricted mixed-term bridge transports
that formula to the actual ambient pairing
`Φ(P)/Φ(P)² × P/Φ(P) → Φ(P)²`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (printed pp. 92--93), type-C square monomial.**

Let the left factor be the common commutative middle factor and let the right
factor have type-C parameter `Frob^r`.  The actual ambient square commutator,
expressed in the common middle, source, and square coordinates, is

`c₀ * (β^(2^(n-1)) * α^(2^(r+1)))`

for one fixed `c₀ ≠ 0`.  Here `α` is the middle coordinate and `β` is the
right-factor source coordinate.  The same support calculation also returns
Higman's sharp equation `2r + 1 = n`.
-/
theorem exists_restrictedFactorTypeCSquareCommutator_monomial
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
    2 * r + 1 = n ∧
      ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
        ∀ alpha beta : GaloisField 2 n,
          eSquare
              (frattiniSquareCommutatorBilinear
                hP hxi hPhiComm hfour hexists
                ((frattiniMiddleCoordinate
                  hP hxi hPhiComm hfour hexists eSquare).symm alpha)
                (restrictedFactorAmbientInclusion hSinv hEAS eS c right
                  hK1S htermS hSqS hAgemoS hK0S beta)) =
            c0 * (beta ^ 2 ^ (n - 1) * alpha ^ 2 ^ (r + 1)) := by
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
  let L := left.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  let R := right.toInclusionData hEAS eS hK1S htermS hSqS hAgemoS hK0S
  have hequivRL : ∀ alpha beta : GaloisField 2 n,
      mixedTermBilinear R L
          (right.lambda * alpha) (left.lambda * beta) =
        nu * mixedTermBilinear R L alpha beta := by
    intro alpha beta
    exact mixedTermBilinear_lambda_equivariance
      hEAS eS right left hK1S htermS hSqS hAgemoS hK0S hconjS
        alpha beta
  have hM0LR : ∃ alpha beta : GaloisField 2 n,
      mixedTermBilinear L R alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxiS hinvPhiS
  have hM0RL : ∃ alpha beta : GaloisField 2 n,
      mixedTermBilinear R L alpha beta ≠ 0 := by
    obtain ⟨alpha, beta, hne⟩ := hM0LR
    refine ⟨beta, alpha, ?_⟩
    rw [mixedTermBilinear_swap L R alpha beta]
    exact hne
  have hleftSquare : left.lambda ^ 2 = nu := by
    simpa [pow_two] using hleftSource.symm
  have hrightPower : right.lambda ^ (1 + 2 ^ r) = nu := by
    have hthetaApply :
        right.theta right.lambda = right.lambda ^ 2 ^ r := by
      rw [hrightTheta, frobeniusEquiv_pow_apply]
    calc
      right.lambda ^ (1 + 2 ^ r) =
          right.lambda * right.lambda ^ 2 ^ r := by
            rw [pow_add, pow_one]
      _ = right.lambda * right.theta right.lambda := by rw [hthetaApply]
      _ = nu := hrightSource.symm
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordNu : orderOf nu = 2 ^ n - 1 := hnuPrimitive.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnuNe : nu ≠ 0 := by
    intro hzero
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordNu]
      exact pow_orderOf_eq_one nu
    rw [hzero, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hrightNe : right.lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by simp)] at hrightPower
    exact hnuNe hrightPower.symm
  have hleftNe : left.lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num)] at hleftSquare
    exact hnuNe hleftSquare.symm
  have hrightFieldPower : right.lambda ^ (2 ^ n - 1) = 1 := by
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one right.lambda hrightNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hleftFieldPower : left.lambda ^ (2 ^ n - 1) = 1 := by
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one left.lambda hleftNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordRight, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by simp : 1 + 2 ^ r ≠ 0) hordNu hrightPower hrightFieldPower
  obtain ⟨h2r1, c0, hc0, hmono⟩ :=
    mixedTerm_monomial_typeC hr h2r (mixedTermBilinear R L)
      right.lambda left.lambda nu hordRight hrightPower hleftSquare
      hleftFieldPower hequivRL hM0RL
  refine ⟨h2r1, c0, hc0, fun alpha beta => ?_⟩
  rw [restrictedFactorMixedTerm_eq_frattiniSquareCommutator
    hP hxi hPhiComm hfour hexists hSinv hEAS hMap eSquare eS heS c
    factors left right hleft hK1S htermS hSqS hAgemoS hK0S]
  rw [← mixedTermBilinear_swap L R alpha beta]
  exact hmono beta alpha

end OddOrder.Higman.Suzuki2Groups
