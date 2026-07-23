/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.XiLengthTwoTypeAClassification
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedLengths

/-!
# Higman's Lemma 13: models for the exponent-two factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The exponent-two branch supplies three invariant Frattini preimages of exact
restricted xi-length two. Restricting the actor preserves its xi-properties
and Higman's prime-support condition, while actor transitivity puts all
ambient involutions in every nontrivial invariant factor. The inclusive
xi-length-two classification therefore gives an honest `A(n, phi)` model
for each factor, including the abelian case `phi = 1`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), factor model.**

An invariant subgroup strictly above the ambient Frattini subgroup inherits
the hypotheses needed for the inclusive xi-length-two classification. -/
theorem isXiLengthTwoTypeA_invariant_subgroup
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hlenS : HasXiLengthTwo hSinv.restrict.range.subtype) :
    IsXiLengthTwoTypeA.{uP, 0} S := by
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hprimeS : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  exact isXiLengthTwoTypeA_of_xiLengthTwo
    (hP.to_subgroup S) hmultiS hxiS hlenS hprimeS

/-- **Higman Lemma 13 (p. 93), three classified factors.**

In the exponent-two branch the three independent Frattini preimages all
have inclusive `A(n, phi)` models. -/
theorem exists_three_typeA_xiLengthTwo_frattini_preimages_of_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ (X Z T : Subgroup P)
        (hXinv : IsAInvariant Y.subtype X)
        (hZinv : IsAInvariant Y.subtype Z)
        (hTinv : IsAInvariant Y.subtype T),
      X.Normal ∧ HasXiLengthTwo hXinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} X ∧
        Z.Normal ∧ HasXiLengthTwo hZinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} Z ∧
        T.Normal ∧ HasXiLengthTwo hTinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} T ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        frattini P < T ∧ T < ⊤ ∧
        X ⊓ Z = frattini P ∧ X ⊓ T = frattini P ∧
        Z ⊓ T = frattini P ∧
        X ⊔ Z < ⊤ ∧ X ⊔ T < ⊤ ∧ Z ⊔ T < ⊤ ∧
          X ⊔ Z ⊔ T = ⊤ := by
  obtain ⟨X, Z, T, hXinv, hZinv, hTinv,
      hXnormal, hlenX, hZnormal, hlenZ, hTnormal, hlenT,
      hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
      hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop, hXZ_Tsup⟩ :=
    exists_three_xiLengthTwo_frattini_preimages_of_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  have hmodelX : IsXiLengthTwoTypeA.{uP, 0} X :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hXinv hPhiX hlenX
  have hmodelZ : IsXiLengthTwoTypeA.{uP, 0} Z :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hZinv hPhiZ hlenZ
  have hmodelT : IsXiLengthTwoTypeA.{uP, 0} T :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hTinv hPhiT hlenT
  exact ⟨X, Z, T, hXinv, hZinv, hTinv,
    hXnormal, hlenX, hmodelX,
    hZnormal, hlenZ, hmodelZ,
    hTnormal, hlenT, hmodelT,
    hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
    hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop, hXZ_Tsup⟩

end

end OddOrder.Higman.Suzuki2Groups
