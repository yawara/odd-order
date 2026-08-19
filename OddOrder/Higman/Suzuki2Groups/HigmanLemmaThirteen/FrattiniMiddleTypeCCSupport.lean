/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleEigenweights
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SupportPinning

/-!
# Higman's Lemma 13: type-C/C support in the middle Frattini layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

For two type-C restricted factors with the common Frobenius parameter `r`,
the two source eigenvalues are first identified from their common source
equation.  A nonzero middle bracket then has one of Higman's two cyclic
supports: `j = i + r`, with output index `i + 1`, or the swapped support
`i = j + r`, with output index `j + 1`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleTypeCCSupportLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniMiddleTypeCCSupportLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

private theorem typeCC_pow_two_index_mod
    {F : Type*} [Monoid F] {x : F} {n : ℕ}
    (hx : x ^ (2 ^ n - 1) = 1) (a : ℕ) :
    x ^ (2 ^ a) = x ^ (2 ^ (a % n)) := by
  apply pow_eq_pow_of_modEq _ hx
  apply (ZMod.natCast_eq_natCast_iff (2 ^ a) (2 ^ (a % n))
    (2 ^ n - 1)).mp
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    two_pow_zmod_eq_pow_mod n a

/-- The pure weight arithmetic behind type-C/C middle support. -/
theorem typeCC_middleWeight_index_laws
    {n r : ℕ} (hr : 0 < r) (h2r1 : 2 * r + 1 = n)
    {lambda middleWeight nu : GaloisField 2 n}
    (hord : orderOf lambda = 2 ^ n - 1)
    (hnu : lambda ^ (1 + 2 ^ r) = nu)
    (hmiddleSquare : middleWeight ^ 2 = nu)
    (hmiddlePow : middleWeight ^ (2 ^ n - 1) = 1)
    (i j k : Fin n)
    (hsupport : lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val) =
      middleWeight ^ (2 ^ k.val)) :
    ((j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n) ∧
        (k.val : ZMod n) = (i.val : ZMod n) + 1) ∨
      ((i.val : ZMod n) = (j.val : ZMod n) + (r : ZMod n) ∧
        (k.val : ZMod n) = (j.val : ZMod n) + 1) := by
  have hrn : r < n := by omega
  have hn : 0 < n := lt_trans hr hrn
  let s : ℕ := n + 1 - k.val
  have hks : k.val + s = n + 1 := by
    dsimp only [s]
    omega
  have hshift :
      lambda ^ (2 ^ (i.val + s)) * lambda ^ (2 ^ (j.val + s)) =
        middleWeight ^ (2 ^ (k.val + s)) := by
    calc
      lambda ^ (2 ^ (i.val + s)) * lambda ^ (2 ^ (j.val + s)) =
          (lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val)) ^ (2 ^ s) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        simp only [pow_add]
      _ = (middleWeight ^ (2 ^ k.val)) ^ (2 ^ s) := by rw [hsupport]
      _ = middleWeight ^ (2 ^ (k.val + s)) := by
        rw [← pow_mul, ← pow_add]
  have hlambdaPow : lambda ^ (2 ^ n - 1) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one lambda
  have hiRed := typeCC_pow_two_index_mod hlambdaPow (i.val + s)
  have hjRed := typeCC_pow_two_index_mod hlambdaPow (j.val + s)
  have hmiddleFrob : middleWeight ^ (2 ^ n) = middleWeight := by
    have he : 2 ^ n = (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [he, pow_succ, hmiddlePow, one_mul]
  have hrhs : middleWeight ^ (2 ^ (k.val + s)) = nu := by
    rw [hks, pow_succ, pow_mul, hmiddleFrob, hmiddleSquare]
  have hsupportRed :
      lambda ^ (2 ^ ((i.val + s) % n)) *
          lambda ^ (2 ^ ((j.val + s) % n)) = nu := by
    rw [← hiRed, ← hjRed, hshift, hrhs]
  have hiLt : (i.val + s) % n < n := Nat.mod_lt _ hn
  have hjLt : (j.val + s) % n < n := Nat.mod_lt _ hn
  rcases higman_typeB_support_pinning hrn hiLt hjLt hord hnu hsupportRed with
    ⟨hiPin, hjPin⟩ | ⟨hiPin, hjPin⟩
  · have hiZ :
        ((i.val + s : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by
      apply (ZMod.natCast_eq_natCast_iff' (i.val + s) 0 n).mpr
      simpa using hiPin
    have hjZ :
        ((j.val + s : ℕ) : ZMod n) = (r : ZMod n) := by
      apply (ZMod.natCast_eq_natCast_iff' (j.val + s) r n).mpr
      simpa [Nat.mod_eq_of_lt hrn] using hjPin
    have hkZ :
        ((k.val + s : ℕ) : ZMod n) = 1 := by
      rw [hks]
      simp
    push_cast at hiZ hjZ hkZ
    exact Or.inl ⟨by linear_combination hjZ - hiZ,
      by linear_combination hkZ - hiZ⟩
  · have hiZ :
        ((i.val + s : ℕ) : ZMod n) = (r : ZMod n) := by
      apply (ZMod.natCast_eq_natCast_iff' (i.val + s) r n).mpr
      simpa [Nat.mod_eq_of_lt hrn] using hiPin
    have hjZ :
        ((j.val + s : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by
      apply (ZMod.natCast_eq_natCast_iff' (j.val + s) 0 n).mpr
      simpa using hjPin
    have hkZ :
        ((k.val + s : ℕ) : ZMod n) = 1 := by
      rw [hks]
      simp
    push_cast at hiZ hjZ hkZ
    exact Or.inr ⟨by linear_combination hiZ - hjZ,
      by linear_combination hkZ - hjZ⟩

/-- **Higman Lemma 13 (printed p. 93), type-C/C middle support.**

The two type-C source equations have the same Frobenius parameter `r` and
the same primitive target `nu`, hence their source eigenvalues coincide.
If eigenvectors at indices `i` and `j` have a nonzero middle bracket, its
axis index `k` satisfies one of the two cyclic support laws from Higman's
type-C/C paragraph. -/
theorem frattiniMiddleCommutatorBilinearBaseChange_typeCC_support_of_ne_zero
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
    (lambda rho : GaloisField 2 n)
    (theta psi : RingAut (GaloisField 2 n))
    (hlambdaSource : nu = lambda * theta lambda)
    (hrhoSource : nu = rho * psi rho)
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hpsi : psi = frobeniusEquiv (GaloisField 2 n) 2 ^ r) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (u v : GaloisField 2 n ⊗[ZMod 2]
        Additive (lowerCentralLayer P 0)),
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) u = lambda ^ (2 ^ i.val) • u →
      (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) v = rho ^ (2 ^ j.val) • v →
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v ≠ 0 →
      ∃ k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)),
        (((j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n) ∧
            (k.val : ZMod n) = (i.val : ZMod n) + 1) ∨
          ((i.val : ZMod n) = (j.val : ZMod n) + (r : ZMod n) ∧
            (k.val : ZMod n) = (j.val : ZMod n) + 1)) := by
  classical
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro i j u v hu hv hne
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  have hthetaApply : theta lambda = lambda ^ (2 ^ r) := by
    rw [htheta, frobeniusEquiv_pow_apply]
  have hpsiApply : psi rho = rho ^ (2 ^ r) := by
    rw [hpsi, frobeniusEquiv_pow_apply]
  have hlambdaNu : lambda ^ (1 + 2 ^ r) = nu := by
    calc
      lambda ^ (1 + 2 ^ r) = lambda * lambda ^ (2 ^ r) := by
        rw [pow_add, pow_one]
      _ = lambda * theta lambda := by rw [hthetaApply]
      _ = nu := hlambdaSource.symm
  have hrhoNu : rho ^ (1 + 2 ^ r) = nu := by
    calc
      rho ^ (1 + 2 ^ r) = rho * rho ^ (2 ^ r) := by
        rw [pow_add, pow_one]
      _ = rho * psi rho := by rw [hpsiApply]
      _ = nu := hrhoSource.symm
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
  have hrhoNe : rho ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by positivity)] at hrhoNu
    exact hnuNe hrhoNu.symm
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hlambdaPow : lambda ^ (2 ^ n - 1) = 1 := by
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hrhoPow : rho ^ (2 ^ n - 1) = 1 := by
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one rho hrhoNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hrhoLambda : rho = lambda :=
    eq_of_pow_eq_pow_orderOf hNpos (by positivity : 1 + 2 ^ r ≠ 0)
      hordNu hlambdaNu hrhoNu hlambdaPow hrhoPow
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
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one middleWeight hmiddleNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨k, hweight⟩ :=
    exists_frattiniMiddleFrobeniusWeight_of_ne_zero
      hP hxi hPhiComm hfour hexists c eSquare nu hconj hu hv hne
  rw [hrhoLambda] at hweight
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 hn0
  let i' : Fin n := ⟨i.val, by simpa [hfinrank] using i.isLt⟩
  let j' : Fin n := ⟨j.val, by simpa [hfinrank] using j.isLt⟩
  let k' : Fin n := ⟨k.val, by simpa [hfinrank] using k.isLt⟩
  have hlaws := typeCC_middleWeight_index_laws hr h2r1 hordLambda
    hlambdaNu hmiddleSquare hmiddlePow i' j' k' hweight
  exact ⟨k, by simpa [i', j', k'] using hlaws⟩

end OddOrder.Higman.Suzuki2Groups
