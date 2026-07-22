/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorNormalForms
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman's Lemma 13: the type-C parameter equation

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

In the exponent-four branch, a normalized noncommutative right factor has
Frobenius parameter `r` with `0 < r` and `2 * r ≤ n`.  The actual nonzero
mixed commutator in the restricted length-three group, together with Higman's
type-C support pinning, sharpens this half-range normalization to the source
equation `2 * r + 1 = n`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- **Higman Lemma 13 (p. 92), type-C parameter equation.**

For a complementary factor pair over one Singer coordinate, if the left
factor has source equation `ν = μ²` and the right factor has automorphism
`Frob^r` with source equation `ν = λ * Frob^r(λ)`, then the actual nonzero
mixed commutator forces `2r + 1 = n`.  The nonzero map is constructed from
the two genuine factor inclusions; it is not supplied as an extra hypothesis. -/
theorem factorPair_frobenius_parameter_eq
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (factors : XiLengthThreeTypeAFactorData P Y) :
    let hEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (ePhi : Additive (frattini P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : FactorCoordinateData factors.left_invariant
        factors.frattini_lt_left.le c ePhi nu)
      (right : FactorCoordinateData factors.right_invariant
        factors.frattini_lt_right.le c ePhi nu)
      (r : Nat),
      2 ≤ n →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj
          (elabRepresentation 2
            (IsAInvariant.of_characteristic Y.subtype).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      nu = left.lambda * left.lambda →
      nu = right.lambda * right.theta right.lambda →
      0 < r →
      2 * r ≤ n →
      right.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r →
      2 * r + 1 = n := by
  classical
  dsimp only
  let hEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hEA.zmodModule
  intro n c ePhi nu left right r hnTwo hnuPrimitive hconj
    hleftSource hrightSource hr0 hrhalf htheta
  have hK0 :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hK1 := lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hterm := lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hSq := lowerCentralSquaresLieInSecond_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hAgemo := agemo_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  set L := left.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0
  set R := right.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0
  have hequivRL : ∀ alpha beta : GaloisField 2 n,
      mixedTermBilinear R L
          (right.lambda * alpha) (left.lambda * beta) =
        nu * mixedTermBilinear R L alpha beta := fun alpha beta =>
    mixedTermBilinear_lambda_equivariance hEA ePhi right left
      hK1 hterm hSq hAgemo hK0 hconj alpha beta
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) :=
    frattini_ne_bot_of_not_isMulCommutative hP hncomm
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  have hM0LR : ∃ alpha beta : GaloisField 2 n,
      mixedTermBilinear L R alpha beta ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxi hinvPhi
  have hM0RL : ∃ alpha beta : GaloisField 2 n,
      mixedTermBilinear R L alpha beta ≠ 0 := by
    obtain ⟨alpha, beta, hne⟩ := hM0LR
    refine ⟨beta, alpha, ?_⟩
    rw [mixedTermBilinear_swap L R alpha beta]
    exact hne
  have hmu2 : left.lambda ^ 2 = nu := by
    simpa [pow_two] using hleftSource.symm
  have hlamnu : right.lambda ^ (1 + 2 ^ r) = nu := by
    have hthetaApply :
        right.theta right.lambda = right.lambda ^ 2 ^ r := by
      rw [htheta, frobeniusEquiv_pow_apply]
    calc
      right.lambda ^ (1 + 2 ^ r) =
          right.lambda * right.lambda ^ 2 ^ r := by
            rw [pow_add, pow_one]
      _ = right.lambda * right.theta right.lambda := by
        rw [hthetaApply]
      _ = nu := hrightSource.symm
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordnu : orderOf nu = 2 ^ n - 1 :=
    hnuPrimitive.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnune : nu ≠ 0 := by
    intro hzero
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [hzero, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hlamne : right.lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by simp)] at hlamnu
    exact hnune hlamnu.symm
  have hmune : left.lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num)] at hmu2
    exact hnune hmu2.symm
  have hlampow : right.lambda ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one right.lambda hlamne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hmupow : left.lambda ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one left.lambda hmune
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordlam, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by simp : 1 + 2 ^ r ≠ 0) hordnu hlamnu hlampow
  obtain ⟨h2r1, -, -, -⟩ :=
    mixedTerm_monomial_typeC hr0 hrhalf (mixedTermBilinear R L)
      right.lambda left.lambda nu hordlam hlamnu hmu2 hmupow
      hequivRL hM0RL
  exact h2r1

/-- **Higman Lemma 13 (p. 92), source-sharp restricted-factor coordinates.**

This refines the normalized restricted-factor package.  The commutative
alternative remains `right.theta = 1`; in the noncommutative type-C
alternative, the returned half-range Frobenius parameter additionally
satisfies Higman's exact equation `2 * r + 1 = n`. -/
theorem exists_sharpRestrictedFactorPairCoordinates_of_frattiniSquareSinger
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S) :
    let hSneBot : S ≠ (⊥ : Subgroup P) :=
      ne_of_gt (lt_of_le_of_lt bot_le hPhiS.lt)
    let hinvS : involutions P ⊆ S :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hSinv hSneBot
    let hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi hSinv
    let hmultiS : ∃ x y : S,
        x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvS hmulti
    let hprimeS : ∀ p : Nat, p.Prime →
        p ∣ Nat.card hSinv.restrict.range →
          p ∣ (involutions S).ncard :=
      restricted_range_primeSupport hSinv hinvS hprime
    let hEAS : IsElementaryAbelian 2 (frattini S) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
    let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    let hMap : (frattini S).map S.subtype = frattiniSquare P :=
      frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
        hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
    letI : IsMulCommutative (frattini S) :=
      IsMulCommutative.of_comm hEAS.comm
    letI : Module (ZMod 2) (Additive (frattini S)) :=
      hEAS.zmodModule
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (eSquare : Additive (frattiniSquare P) ≃ₗ[ZMod 2]
        GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      eSquare.conj
          (elabRepresentation 2
            ((frattiniSquareNormalInvariant Y.subtype).2.2).restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (factors : XiLengthThreeTypeAFactorData
          S hSinv.restrict.range)
        (left : FactorCoordinateData factors.left_invariant
          factors.frattini_lt_left.le
          (hSinv.restrict.rangeRestrict c)
          ((restrictedFrattiniLinearEquivFrattiniSquare
            hEAS hSquareEA hMap).trans eSquare) nu)
        (right : FactorCoordinateData factors.right_invariant
          factors.frattini_lt_right.le
          (hSinv.restrict.rangeRestrict c)
          ((restrictedFrattiniLinearEquivFrattiniSquare
            hEAS hSquareEA hMap).trans eSquare) nu),
        factors.left = (frattini P).subgroupOf S ∧
        left.theta = 1 ∧
        nu = left.lambda * left.lambda ∧
        nu = right.lambda * right.theta right.lambda ∧
        (right.theta = 1 ∨
          ∃ r : Nat, 0 < r ∧ 2 * r ≤ n ∧ 2 * r + 1 = n ∧
            right.theta =
              frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
            Odd (orderOf right.theta)) := by
  classical
  dsimp only
  let hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS.lt)
  let hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  let hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  let hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  let hprimeS : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  let hEAS : IsElementaryAbelian 2 (frattini S) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
  let hSquareEA : IsElementaryAbelian 2 (frattiniSquare P) :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let hMap : (frattini S).map S.subtype = frattiniSquare P :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
  letI : IsMulCommutative (frattini S) :=
    IsMulCommutative.of_comm hEAS.comm
  letI : Module (ZMod 2) (Additive (frattini S)) :=
    hEAS.zmodModule
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro n c eSquare nu hnTwo hcgen hnuPrimitive hconj
  obtain ⟨factors, left, right, hleft, hleftTheta, hleftSource,
      hrightSource, hrightCase⟩ :=
    exists_normalizedRestrictedFactorPairCoordinates_of_frattiniSquareSinger
      hP hmulti hxi hprime hPhiComm hfour hexists
      hSinv hPhiS hlenS hncommS c eSquare nu hnTwo hcgen
      hnuPrimitive hconj
  rcases hrightCase with hrightOne |
    ⟨r, hr0, hrhalf, hrightTheta, hrightOdd⟩
  · exact ⟨factors, left, right, hleft, hleftTheta, hleftSource,
      hrightSource, Or.inl hrightOne⟩
  · let eS := (restrictedFrattiniLinearEquivFrattiniSquare
        hEAS hSquareEA hMap).trans eSquare
    let cS : hSinv.restrict.range := hSinv.restrict.rangeRestrict c
    have hconjS : eS.conj
        (elabRepresentation 2
          (IsAInvariant.of_characteristic
            hSinv.restrict.range.subtype).restrict cS) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu :=
      restrictedFrattiniSingerCoordinate_conj
        hSinv hEAS hSquareEA hMap c eSquare nu hconj
    have h2r1 : 2 * r + 1 = n :=
      factorPair_frobenius_parameter_eq
        (P := S) (Y := hSinv.restrict.range)
        (hP.to_subgroup S) hncommS hmultiS hxiS hlenS hprimeS
        factors cS eS nu left right r hnTwo hnuPrimitive hconjS
        hleftSource hrightSource hr0 hrhalf hrightTheta
    exact ⟨factors, left, right, hleft, hleftTheta, hleftSource,
      hrightSource,
      Or.inr ⟨r, hr0, hrhalf, h2r1, hrightTheta, hrightOdd⟩⟩

end OddOrder.Higman.Suzuki2Groups
