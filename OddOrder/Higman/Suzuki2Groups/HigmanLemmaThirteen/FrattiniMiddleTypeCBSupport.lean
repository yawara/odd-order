/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SupportPinning

/-!
# Higman's Lemma 13: type-C/B support in the middle Frattini layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The first input has a type-C weight `lambda ^ (2 ^ i)` and the second has the
canonical type-B weight `Frob⁻¹(nu) ^ (2 ^ j)`.  A nonzero middle bracket has
output weight `Frob⁻¹(nu) ^ (2 ^ k)`.  Squaring and cyclically shifting all
Frobenius indices reduces this equation to Higman's type-C support pinning.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleTypeCBSupportLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniMiddleTypeCBSupportLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

private theorem pow_two_index_mod
    {F : Type*} [Monoid F] {x : F} {n : ℕ}
    (hx : x ^ (2 ^ n - 1) = 1) (a : ℕ) :
    x ^ (2 ^ a) = x ^ (2 ^ (a % n)) := by
  apply pow_eq_pow_of_modEq _ hx
  apply (ZMod.natCast_eq_natCast_iff (2 ^ a) (2 ^ (a % n))
    (2 ^ n - 1)).mp
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    two_pow_zmod_eq_pow_mod n a

/-- The pure weight arithmetic behind type-C/B middle support. -/
theorem typeCB_middleWeight_index_laws
    {n r : ℕ} (hr : 0 < r) (h2r1 : 2 * r + 1 = n)
    {lambda middleWeight nu : GaloisField 2 n}
    (hord : orderOf lambda = 2 ^ n - 1)
    (hnu : lambda ^ (1 + 2 ^ r) = nu)
    (hmiddleSquare : middleWeight ^ 2 = nu)
    (hmiddlePow : middleWeight ^ (2 ^ n - 1) = 1)
    (i j k : Fin n)
    (hsupport : lambda ^ (2 ^ i.val) * middleWeight ^ (2 ^ j.val) =
      middleWeight ^ (2 ^ k.val)) :
    (j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n) + 2 ∧
      (k.val : ZMod n) = (i.val : ZMod n) + 2 := by
  have hn : 0 < n := by omega
  have h2r : 2 * r ≤ n := by omega
  let s : ℕ := n + 1 - k.val
  have hks : k.val + s = n + 1 := by
    dsimp only [s]
    omega
  have hshift :
      lambda ^ (2 ^ (i.val + s)) * middleWeight ^ (2 ^ (j.val + s)) =
        middleWeight ^ (2 ^ (k.val + s)) := by
    calc
      lambda ^ (2 ^ (i.val + s)) * middleWeight ^ (2 ^ (j.val + s)) =
          (lambda ^ (2 ^ i.val) * middleWeight ^ (2 ^ j.val)) ^ (2 ^ s) := by
            rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      _ = (middleWeight ^ (2 ^ k.val)) ^ (2 ^ s) := by rw [hsupport]
      _ = middleWeight ^ (2 ^ (k.val + s)) := by
        rw [← pow_mul, ← pow_add]
  have hlambdaPow : lambda ^ (2 ^ n - 1) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one lambda
  have hiRed := pow_two_index_mod hlambdaPow (i.val + s)
  have hjRed := pow_two_index_mod hmiddlePow (j.val + s)
  have hmiddleFrob : middleWeight ^ (2 ^ n) = middleWeight := by
    have he : 2 ^ n = (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [he, pow_succ, hmiddlePow, one_mul]
  have hrhs : middleWeight ^ (2 ^ (k.val + s)) = nu := by
    rw [hks, pow_succ, pow_mul, hmiddleFrob, hmiddleSquare]
  have hsupportRed :
      lambda ^ (2 ^ ((i.val + s) % n)) *
          middleWeight ^ (2 ^ ((j.val + s) % n)) = nu := by
    rw [← hiRed, ← hjRed, hshift, hrhs]
  have hiLt : (i.val + s) % n < n := Nat.mod_lt _ hn
  have hjLt : (j.val + s) % n < n := Nat.mod_lt _ hn
  obtain ⟨-, hiPin, hjPin⟩ :=
    higman_typeC_support_pinning hr h2r hiLt hjLt hord hnu
      hmiddleSquare hmiddlePow hsupportRed
  have hiZ :
      ((i.val + s : ℕ) : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    apply (ZMod.natCast_eq_natCast_iff' (i.val + s) (n - 1) n).mpr
    simpa [Nat.mod_eq_of_lt (show n - 1 < n by omega)] using hiPin
  have hjZ :
      ((j.val + s : ℕ) : ZMod n) = ((r + 1 : ℕ) : ZMod n) := by
    apply (ZMod.natCast_eq_natCast_iff' (j.val + s) (r + 1) n).mpr
    simpa [Nat.mod_eq_of_lt (show r + 1 < n by omega)] using hjPin
  have hkZ :
      ((k.val + s : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by
    rw [hks]
  push_cast at hiZ hjZ hkZ
  have hnMinus : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  rw [hnMinus] at hiZ
  simp at hkZ
  constructor
  · linear_combination hjZ - hiZ
  · linear_combination hkZ - hiZ

/-- **Higman Lemma 13 (p. 92), type-C/B middle support.**

If a type-C eigenvector of weight `lambda ^ (2 ^ i)` and a type-B
eigenvector of weight `Frob⁻¹(nu) ^ (2 ^ j)` have nonzero middle bracket,
then the second input and output indices are respectively `i + r + 2` and
`i + 2` modulo `n`.  The full order of `lambda` is recovered here from the
source equation and the primitivity of `nu`; it is not an extra hypothesis. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_typeCB_support_of_ne_zero
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (h2r1 : 2 * r + 1 = n)
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
    (lambda : GaloisField 2 n)
    (theta : RingAut (GaloisField 2 n))
    (hsource : nu = lambda * theta lambda)
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (u v : GaloisField 2 n ⊗[ZMod 2]
        Additive (lowerCentralLayer P 0)),
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) u = lambda ^ (2 ^ i.val) • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v =
        ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
          (2 ^ j.val) • v →
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v ≠ 0 →
      ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        (j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n) + 2 ∧
          (k.val : ZMod n) = (i.val : ZMod n) + 2 := by
  classical
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro i j u v hu hv hne
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  have hthetaApply : theta lambda = lambda ^ (2 ^ r) := by
    rw [htheta, frobeniusEquiv_pow_apply]
  have hlambdaNu : lambda ^ (1 + 2 ^ r) = nu := by
    calc
      lambda ^ (1 + 2 ^ r) = lambda * lambda ^ (2 ^ r) := by
        rw [pow_add, pow_one]
      _ = lambda * theta lambda := by rw [hthetaApply]
      _ = nu := hsource.symm
  have hordNu : orderOf nu = 2 ^ n - 1 :=
    hnuPrimitive.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnuNe : nu ≠ 0 := by
    intro hzero
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordNu]
      exact pow_orderOf_eq_one nu
    rw [hzero, zero_pow (ne_of_gt hNpos)] at hone
    exact zero_ne_one hone
  have hlambdaNe : lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by positivity)] at hlambdaNu
    exact hnuNe hlambdaNu.symm
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hlambdaPow : lambda ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordLambda, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by positivity : 1 + 2 ^ r ≠ 0) hordNu hlambdaNu hlambdaPow
  have hmiddleSquare : middleWeight ^ 2 = nu :=
    frobeniusEquiv_symm_pow_p (GaloisField 2 n) 2 nu
  have hmiddleNe : middleWeight ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num)] at hmiddleSquare
    exact hnuNe hmiddleSquare.symm
  have hmiddlePow : middleWeight ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one middleWeight hmiddleNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨k, hweight⟩ :=
    exists_frattiniMiddleFrobeniusWeight_of_ne_zero
      hP hxi hPhiComm hfour hexists c eSquare nu hconj hu hv hne
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 hn0
  let i' : Fin n := ⟨i.val, by simpa [hfinrank] using i.isLt⟩
  let j' : Fin n := ⟨j.val, by simpa [hfinrank] using j.isLt⟩
  let k' : Fin n := ⟨k.val, by simpa [hfinrank] using k.isLt⟩
  have hlaws := typeCB_middleWeight_index_laws hr h2r1 hordLambda
    hlambdaNu hmiddleSquare hmiddlePow i' j' k' hweight
  exact ⟨k, by simpa [i', j'] using hlaws.1,
    by simpa [i', k'] using hlaws.2⟩

end OddOrder.Higman.Suzuki2Groups
