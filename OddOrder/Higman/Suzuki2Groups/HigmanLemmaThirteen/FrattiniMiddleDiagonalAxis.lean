/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleSupport

/-!
# Higman's Lemma 13: the diagonal middle-commutator axis

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For two type-B Frobenius eigenvectors with the same index, a nonzero middle
Frattini commutator lies on the canonical middle eigenline whose index is the
cyclic successor of the input index.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory
open scoped IsMulCommutative TensorProduct

universe uP

local instance frattiniMiddleDiagonalAxisLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance frattiniMiddleDiagonalAxisLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), B/B diagonal middle axis.**

A nonzero same-index middle commutator is a nonzero scalar multiple of the
canonical common-middle basis vector at the cyclic successor index. -/
theorem exists_ne_zero_smul_frattiniMiddleConjugateBasis_of_diagonal_bracket
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
    (i : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
    (u v : GaloisField 2 n ⊗[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (hu : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) u =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ i.val) • u)
    (hv : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
        (GaloisField 2 n) v =
      ((frobeniusEquiv (GaloisField 2 n) 2).symm nu) ^
        (2 ^ i.val) • v)
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
      (k.val : ZMod n) = (i.val : ZMod n) + 1 ∧
      epsilon ≠ 0 ∧
      frattiniMiddleCommutatorBilinearBaseChange (GaloisField 2 n)
          hP hxi hPhiComm hexists u v = epsilon • middleBasis k := by
  classical
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
  obtain ⟨_, k, hk⟩ :=
    frattiniMiddleCommutatorBilinearBaseChange_support_of_ne_zero
      hP hxi hPhiComm hfour hexists hn c eSquare nu hnuPrimitive hconj
      i i u v hu hv hne
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
        (middleWeight ^ (2 ^ i.val) * middleWeight ^ (2 ^ i.val)) • w := by
    calc
      TMiddle w = beta (TZero u) (TZero v) := by
        exact frattiniMiddleCommutatorBilinearBaseChange_equivariant
          (GaloisField 2 n) hP hxi hPhiComm hexists c u v
      _ = beta
          (middleWeight ^ (2 ^ i.val) • u)
          (middleWeight ^ (2 ^ i.val) • v) := by
        rw [show TZero u = middleWeight ^ (2 ^ i.val) • u from hu,
          show TZero v = middleWeight ^ (2 ^ i.val) • v from hv]
      _ = (middleWeight ^ (2 ^ i.val) *
          middleWeight ^ (2 ^ i.val)) • w := by
        simp [w, smul_smul]
  have hprimMiddle : IsPrimitiveRoot middleWeight (2 ^ n - 1) :=
    hnuPrimitive.map_of_injective
      (frobeniusEquiv (GaloisField 2 n) 2).symm.injective
  have hordMiddle : orderOf middleWeight = 2 ^ n - 1 :=
    hprimMiddle.eq_orderOf.symm
  have hfinrank :
      Module.finrank (ZMod 2) (GaloisField 2 n) = n :=
    GaloisField.finrank 2 (by omega)
  have hcoordZero
      (s : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)))
      (hsk : s ≠ k) : middleBasis.repr w s = 0 := by
    by_contra hscoord
    have hweight := eigenvalue_eq_of_basis_repr_ne_zero
      TMiddle middleBasis
      (fun t => middleWeight ^ (2 ^ t.val)) hMiddleEigen
      hwEigen s hscoord
    have hpow :
        middleWeight ^ (2 ^ i.val + 2 ^ i.val) =
          middleWeight ^ (2 ^ s.val) := by
      rw [pow_add]
      exact hweight
    have hcongruence := higman_two_pow_add_congruence_of_pow_eq
      (by omega : 0 < n) hordMiddle hpow
    obtain ⟨_, hs⟩ := higman_two_pow_add_eq_two_pow
      (by omega : 0 < n) hcongruence
    have hskZMod : (s.val : ZMod n) = (k.val : ZMod n) :=
      hs.trans hk.symm
    have hslt : s.val < n := by simpa [hfinrank] using s.isLt
    have hklt : k.val < n := by simpa [hfinrank] using k.isLt
    have hskVal : s.val = k.val := by
      have hmod :=
        (ZMod.natCast_eq_natCast_iff' s.val k.val n).mp hskZMod
      simpa [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt hklt] using hmod
    exact hsk (Fin.ext hskVal)
  let epsilon : GaloisField 2 n := middleBasis.repr w k
  have hepsilon : epsilon ≠ 0 := by
    intro hepsilonZero
    apply hw
    apply middleBasis.repr.injective
    ext s
    simp only [map_zero, Finsupp.zero_apply]
    by_cases hsk : s = k
    · subst s
      exact hepsilonZero
    · exact hcoordZero s hsk
  refine ⟨k, epsilon, hk, hepsilon, ?_⟩
  change w = epsilon • middleBasis k
  apply middleBasis.repr.injective
  ext s
  by_cases hsk : s = k
  · subst s
    simp [epsilon]
  · rw [hcoordZero s hsk]
    simp [hsk]

end OddOrder.Higman.Suzuki2Groups
