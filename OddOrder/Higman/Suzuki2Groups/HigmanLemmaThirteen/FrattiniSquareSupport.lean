/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniSquareEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoPowerCongruence

/-!
# Higman's Lemma 13: support of Frattini-square commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For type-B factors both the middle and outer eigenvalues are Frobenius
conjugates of the canonical square root of the Singer scalar on `Φ(P)²`.
Higman's two-power congruence therefore forces a nonzero square-valued
commutator to pair equal Frobenius indices, and its output has that same
index in the square layer.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniSquareSupportLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniSquareSupportLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), B/B square support.**

If the scalar-extended square-valued bracket is nonzero on middle and outer
eigenvectors of the canonical square-root weight, their Frobenius indices
agree.  The Frobenius index of the resulting square-layer weight is the same
index as well. -/
theorem frattiniSquareCommutatorBilinearBaseChange_support_of_ne_zero
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
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (u : GaloisField 2 n ⊗[ZMod 2]
        Additive (frattiniMiddleLayer P))
      (v : GaloisField 2 n ⊗[ZMod 2]
        Additive (lowerCentralLayer P 0)),
      (actualAgemoOneQuotientRepresentation
          (IsAInvariant.of_characteristic Y.subtype).restrict c).baseChange
          (GaloisField 2 n) u =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ i.val) • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ j.val) • v →
      frattiniSquareCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hfour hexists u v ≠ 0 →
      i = j ∧
        ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
          ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
                (2 ^ i.val) *
              ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
                (2 ^ j.val) =
            nu ^ (2 ^ k.val) ∧
          k = i := by
  classical
  dsimp only
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
  intro i j u v hu hv hne
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  obtain ⟨k, hweight⟩ :=
    exists_frattiniSquareFrobeniusWeight_of_ne_zero
      hP hxi hPhiComm hfour hexists c eSquare nu hconj
      hu hv hne
  have hprimMiddle : IsPrimitiveRoot middleWeight (2 ^ n - 1) :=
    hnuPrimitive.map_of_injective
      (frobeniusEquiv (GaloisField 2 n) 2).symm.injective
  have hordMiddle : orderOf middleWeight = 2 ^ n - 1 :=
    hprimMiddle.eq_orderOf.symm
  have hmiddleSquare : middleWeight ^ 2 = nu :=
    frobeniusEquiv_symm_pow_p (GaloisField 2 n) 2 nu
  have hpow : middleWeight ^ (2 ^ i.val + 2 ^ j.val) =
      middleWeight ^ 2 ^ (k.val + 1) := by
    rw [pow_add]
    calc
      middleWeight ^ 2 ^ i.val * middleWeight ^ 2 ^ j.val =
          nu ^ 2 ^ k.val := hweight
      _ = (middleWeight ^ 2) ^ 2 ^ k.val := by rw [hmiddleSquare]
      _ = middleWeight ^ (2 * 2 ^ k.val) := by rw [pow_mul]
      _ = middleWeight ^ 2 ^ (k.val + 1) := by rw [pow_succ, mul_comm]
  have hcongruence := higman_two_pow_add_congruence_of_pow_eq
    (by omega : 0 < n) hordMiddle hpow
  obtain ⟨hij, hki⟩ := higman_two_pow_add_eq_two_pow
    (by omega : 0 < n) hcongruence
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 (by omega)
  have hi : i.val < n := by simpa [hfinrank] using i.isLt
  have hj : j.val < n := by simpa [hfinrank] using j.isLt
  have hk : k.val < n := by simpa [hfinrank] using k.isLt
  have hij' : i = j := by
    apply Fin.ext
    have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val n).mp hij
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod
  have hki' : k = i := by
    apply Fin.ext
    have hkiZ : (k.val : ZMod n) = (i.val : ZMod n) := by
      push_cast at hki
      exact add_right_cancel hki
    have hmod := (ZMod.natCast_eq_natCast_iff' k.val i.val n).mp hkiZ
    simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hi] using hmod
  exact ⟨hij', ⟨k, hweight, hki'⟩⟩

/-- **Higman Lemma 13 (p. 92), off-diagonal B/B square vanishing.**

The square-valued commutator vanishes between distinct Frobenius indices of
the canonical square-root weight. -/
theorem frattiniSquareCommutatorBilinearBaseChange_eq_zero_of_ne
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
    (u : GaloisField 2 n ⊗[ZMod 2]
      Additive (frattiniMiddleLayer P))
    (v : GaloisField 2 n ⊗[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (hu : (actualAgemoOneQuotientRepresentation
        (IsAInvariant.of_characteristic Y.subtype).restrict c).baseChange
        (GaloisField 2 n) u =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ i.val) • u)
    (hv : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) v =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ j.val) • v)
    (hij : i ≠ j) :
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
        hP hxi hPhiComm hfour hexists u v = 0 := by
  classical
  dsimp only
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
  by_contra hne
  exact hij
    (frattiniSquareCommutatorBilinearBaseChange_support_of_ne_zero
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i j u v hu hv hne).1

end OddOrder.Higman.Suzuki2Groups
