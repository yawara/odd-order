/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleTypeCCSupport

/-!
# Higman's Lemma 13: the type-C/C middle-commutator axes

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, printed p. 93 (PDF page 14).

For two type-C source families with the common sharp parameter `r`, a
nonzero middle Frattini commutator has one of the two supports displayed by
Higman.  In the first case it lies on the canonical middle eigenline at
`i + 1`; in the second it lies on the eigenline at `j + 1`.  All index
identities are read modulo `n`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleTypeCCAxisLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniMiddleTypeCCAxisLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

private theorem exists_ne_zero_smul_basis_of_unique_eigenweight_typeCC
    {F : Type*} [Field F]
    {W : Type*} [AddCommGroup W] [Module F W]
    {L : Type*} [Finite L]
    (T : Module.End F W) (b : Module.Basis L F W) (weight : L → F)
    (hb : ∀ s, T (b s) = weight s • b s)
    {w : W} {a : F}
    (hwEigen : T w = a • w) (hw : w ≠ 0)
    (k : L) (hunique : ∀ s, a = weight s → s = k) :
    ∃ epsilon : F, epsilon ≠ 0 ∧ w = epsilon • b k := by
  classical
  have hcoordZero (s : L) (hsk : s ≠ k) : b.repr w s = 0 := by
    by_contra hs
    exact hsk (hunique s
      (eigenvalue_eq_of_basis_repr_ne_zero T b weight hb hwEigen s hs))
  let epsilon : F := b.repr w k
  have hepsilon : epsilon ≠ 0 := by
    intro hepsilonZero
    apply hw
    apply b.repr.injective
    ext s
    simp only [map_zero, Finsupp.zero_apply]
    by_cases hsk : s = k
    · subst s
      exact hepsilonZero
    · exact hcoordZero s hsk
  refine ⟨epsilon, hepsilon, ?_⟩
  apply b.repr.injective
  ext s
  by_cases hsk : s = k
  · subst s
    simp [epsilon]
  · rw [hcoordZero s hsk]
    simp [hsk]

/-- **Higman Lemma 13 (printed p. 93, PDF page 14), type-C/C middle axes.**

Let `u` and `v` belong to two type-C eigenfamilies whose sharp parameters
are both `r`.  If their middle bracket is nonzero, it is a nonzero scalar
multiple of the canonical middle basis vector at `i + 1` when
`j = i + r`, or at `j + 1` when `i = j + r` (indices modulo `n`). -/
theorem exists_ne_zero_smul_frattiniMiddleConjugateBasis_of_typeCC_bracket
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
    (hpsi : psi = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (i j : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
    (u v : GaloisField 2 n ⊗[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (hu : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) u = lambda ^ (2 ^ i.val) • u)
    (hv : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) v = rho ^ (2 ^ j.val) • v)
    (hne :
      letI : CommGroup (frattini P) :=
        { (inferInstance : Group (frattini P)) with
          mul_comm := hPhiComm.is_comm.comm }
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
        hP hxi hPhiComm hexists u v ≠ 0) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    let eMiddle :=
      frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
    let middleBasis :=
      conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
    ∃ (k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
        (epsilon : GaloisField 2 n),
      (((j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n) ∧
          (k.val : ZMod n) = (i.val : ZMod n) + 1) ∨
        ((i.val : ZMod n) = (j.val : ZMod n) + (r : ZMod n) ∧
          (k.val : ZMod n) = (j.val : ZMod n) + 1)) ∧
      epsilon ≠ 0 ∧
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v = epsilon • middleBasis k := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : Fact (1 < n) := ⟨by omega⟩
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
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
  let eMiddle :=
    frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
  let middleWeight :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  let middleBasis :=
    conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eMiddle
  let TZero :=
    (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
      (GaloisField 2 n)
  let TMiddle :=
    (actualAgemoOneQuotientRepresentation hPhiInv.restrict c).baseChange
      (GaloisField 2 n)
  let beta := frattiniMiddleCommutatorBilinearBaseChange
    (GaloisField 2 n) hP hxi hPhiComm hexists
  let w := beta u v
  obtain ⟨k, hk⟩ :=
    frattiniMiddleCommutatorBilinearBaseChange_typeCC_support_of_ne_zero
      hP hxi hPhiComm hfour hexists hn hr h2r1 c eSquare nu
      hnuPrimitive hconj lambda rho theta psi hlambdaSource hrhoSource
      htheta hpsi i j u v hu hv hne
  have hMiddleCompat : ∀ q,
      eMiddle (actualAgemoOneQuotientRepresentation hPhiInv.restrict c q) =
        middleWeight * eMiddle q :=
    frattiniMiddleCoordinate_generator_compatible
      hP hxi hPhiComm hfour hexists c eSquare nu hconj
  have hMiddleEigen : ∀ s,
      TMiddle (middleBasis s) =
        middleWeight ^ (2 ^ s.val) • middleBasis s := by
    intro s
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 n) eMiddle
      (actualAgemoOneQuotientRepresentation hPhiInv.restrict c)
      middleWeight hMiddleCompat s
  have hw : w ≠ 0 := by
    simpa only [w, beta] using hne
  have hwEigen :
      TMiddle w =
        (lambda ^ (2 ^ i.val) * rho ^ (2 ^ j.val)) • w := by
    calc
      TMiddle w = beta (TZero u) (TZero v) := by
        exact frattiniMiddleCommutatorBilinearBaseChange_equivariant
          (GaloisField 2 n) hP hxi hPhiComm hexists c u v
      _ = beta
          (lambda ^ (2 ^ i.val) • u)
          (rho ^ (2 ^ j.val) • v) := by
        rw [show TZero u = lambda ^ (2 ^ i.val) • u from hu,
          show TZero v = rho ^ (2 ^ j.val) • v from hv]
      _ = (lambda ^ (2 ^ i.val) * rho ^ (2 ^ j.val)) • w := by
        simp [w, smul_smul, mul_comm]
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
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 hn0
  have hbranchesExclusive
      (hji : (j.val : ZMod n) = (i.val : ZMod n) + (r : ZMod n))
      (hij : (i.val : ZMod n) = (j.val : ZMod n) + (r : ZMod n)) :
      False := by
    have hparameter :
        (2 : ZMod n) * (r : ZMod n) + 1 = 0 := by
      have hcast := congrArg (fun t : ℕ => (t : ZMod n)) h2r1
      push_cast at hcast
      simpa using hcast
    have hone : (1 : ZMod n) = 0 := by
      linear_combination hji + hij + hparameter
    exact (one_ne_zero : (1 : ZMod n) ≠ 0) hone
  have hindexEq
      (a b : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (hab : (a.val : ZMod n) = (b.val : ZMod n)) : a = b := by
    have halt : a.val < n := by simpa [hfinrank] using a.isLt
    have hblt : b.val < n := by simpa [hfinrank] using b.isLt
    apply Fin.ext
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' a.val b.val n).mp hab
    simpa [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] using hmod
  have hunique
      (s : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (hsweight :
        lambda ^ (2 ^ i.val) * rho ^ (2 ^ j.val) =
          middleWeight ^ (2 ^ s.val)) : s = k := by
    rw [hrhoLambda] at hsweight
    let i' : Fin n := ⟨i.val, by simpa [hfinrank] using i.isLt⟩
    let j' : Fin n := ⟨j.val, by simpa [hfinrank] using j.isLt⟩
    let s' : Fin n := ⟨s.val, by simpa [hfinrank] using s.isLt⟩
    have hslaws := typeCC_middleWeight_index_laws hr h2r1 hordLambda
      hlambdaNu hmiddleSquare hmiddlePow i' j' s' hsweight
    rcases hk with hkA | hkB
    · rcases hslaws with hsA | hsB
      · exact hindexEq s k (by
          simpa [s'] using hsA.2.trans hkA.2.symm)
      · exact (hbranchesExclusive hkA.1 (by simpa [i', j'] using hsB.1)).elim
    · rcases hslaws with hsA | hsB
      · exact (hbranchesExclusive (by simpa [i', j'] using hsA.1) hkB.1).elim
      · exact hindexEq s k (by
          simpa [s'] using hsB.2.trans hkB.2.symm)
  obtain ⟨epsilon, hepsilon, haxis⟩ :=
    exists_ne_zero_smul_basis_of_unique_eigenweight_typeCC
      TMiddle middleBasis (fun s => middleWeight ^ (2 ^ s.val))
      hMiddleEigen hwEigen hw k hunique
  exact ⟨k, epsilon, hk, hepsilon, haxis⟩

end OddOrder.Higman.Suzuki2Groups
