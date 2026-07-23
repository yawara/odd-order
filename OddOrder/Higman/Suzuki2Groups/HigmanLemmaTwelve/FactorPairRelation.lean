/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.FixedFactorPairRelation

/-!
# Higman's Lemma 12: parameter relations for a prescribed factor pair

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 12, pp. 90–92.

The B/C/D dispatch in Lemma 12 is strengthened here to retain the actual
two complementary type-A factors supplied by the caller.  After choosing one
common Singer datum and normalizing both factor coordinates, the result
records one of five oriented relations.

This coordinate-existence wrapper is deliberately finer than the public
disjunction `IsTypeB P ∨ IsTypeC P ∨ IsTypeD P`.  Its ambient coordinates
are existential; cross-join applications use the fixed-coordinate core
instead.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 12 (pp. 90–92) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

/-- **Higman Lemma 12 (pp. 90–92), prescribed-factor parameter dispatch.**

Choose common coordinates for the specified complementary type-A factors,
normalize both factor coordinates, and return their oriented B/C/D parameter
relation. -/
theorem XiLengthThreeTypeAFactorData.exists_normalizedFactorPairRelation
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (factors : XiLengthThreeTypeAFactorData P Y) :
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
    ∃ (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : FactorCoordinateData
        factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
      (right : FactorCoordinateData
        factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
      NormalizedFactorPairRelation n left.theta right.theta := by
  classical
  dsimp only
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
  obtain ⟨c, ePhi, nu, left, right, hnTwo, _hcgen, hnuPrimitive,
      hconj, _hsourceL, _hsourceR⟩ :=
    exists_factorPairCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
      factors.left_invariant factors.frattini_lt_left
      factors.left_lt_top
      factors.right_invariant factors.frattini_lt_right
      factors.right_lt_top
  obtain ⟨left', right', hrelation⟩ :=
    factors.exists_normalizedFactorPairRelation_of_fixedCoordinates
      hP hncomm hmulti hxi hlen hprime
      c ePhi nu hnTwo hnuPrimitive hconj left right
  exact ⟨c, ePhi, nu, left', right', hrelation⟩

end

end

end OddOrder.Higman.Suzuki2Groups
