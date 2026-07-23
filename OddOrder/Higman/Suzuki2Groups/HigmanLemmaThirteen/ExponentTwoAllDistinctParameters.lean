/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoParameterArithmetic

/-!
# Higman Lemma 13: the all-distinct exponent-two parameter check

G. Higman, *Suzuki 2-groups*, p. 93.  Suppose three normalized
`A(n, φ)` factors have pairwise distinct parameters.  Applying the B/C/D
list to the two joins which share one factor leaves only a mixed C/D
configuration.  It forces the shared factor to have parameter `Frob²` over
the field of degree five.

This file converts `NormalizedFactorPairRelation` into arithmetic relations
between lower-half Frobenius exponents and performs Higman's finite list
check.  The downstream group-theoretic leaf supplies the three actual
factors and transports one factor's coordinates between its two joins.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

private theorem frobenius_pow_zmod_eq_of_eq
    {n a b : ℕ}
    (hn : 0 < n)
    (h :
      frobeniusEquiv (GaloisField 2 n) 2 ^ a =
        frobeniusEquiv (GaloisField 2 n) 2 ^ b) :
    (a : ZMod n) = (b : ZMod n) := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using
      GaloisField.card 2 n (Nat.ne_of_gt hn)
  have horder :
      orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
  rw [pow_eq_pow_iff_modEq, horder] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

private theorem normalized_frobenius_pow_injective
    {n a b : ℕ} (hn : 0 < n)
    (ha : 2 * a ≤ n) (hb : 2 * b ≤ n)
    (h :
      frobeniusEquiv (GaloisField 2 n) 2 ^ a =
        frobeniusEquiv (GaloisField 2 n) 2 ^ b) :
    a = b := by
  have ha_lt : a < n := by omega
  have hb_lt : b < n := by omega
  have hz := frobenius_pow_zmod_eq_of_eq hn h
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hm

/-- The four arithmetic shapes of a normalized factor-pair relation. -/
inductive NormalizedExponentPairRelation (n a b : ℕ) : Prop
  | same (h : a = b)
  | typeCLeft (right_zero : b = 0) (dimension : 2 * a + 1 = n)
  | typeCRight (left_zero : a = 0) (dimension : 2 * b + 1 = n)
  | typeD (relation : NormalizedTypeDExponentRelation n a b)

private theorem normalized_factorPairRelation_to_exponents
    {n a b : ℕ} {theta phi : RingAut (GaloisField 2 n)}
    (hn : 0 < n)
    (ha : 2 * a ≤ n) (hb : 2 * b ≤ n)
    (htheta :
      theta = frobeniusEquiv (GaloisField 2 n) 2 ^ a)
    (hphi :
      phi = frobeniusEquiv (GaloisField 2 n) 2 ^ b)
    (hrel : NormalizedFactorPairRelation n theta phi) :
    NormalizedExponentPairRelation n a b := by
  rcases hrel with hsame |
      ⟨r, hr0, hthetaR, hphiOne, hdim⟩ |
      ⟨r, hr0, hthetaOne, hphiR, hdim⟩ |
      ⟨r, hr0, hrhalf, hthetaR, hphiSq, hfive⟩ |
      ⟨r, hr0, hrhalf, hphiR, hthetaSq, hfive⟩
  · apply NormalizedExponentPairRelation.same
    apply normalized_frobenius_pow_injective hn ha hb
    rw [← htheta, ← hphi]
    exact hsame
  · have hrhalf : 2 * r ≤ n := by omega
    have har : a = r := by
      apply normalized_frobenius_pow_injective hn ha hrhalf
      rw [← htheta, ← hthetaR]
    have hb0 : b = 0 := by
      apply normalized_frobenius_pow_injective hn hb (by omega)
      rw [← hphi, hphiOne, pow_zero]
    exact .typeCLeft hb0 (by omega)
  · have hrhalf : 2 * r ≤ n := by omega
    have ha0 : a = 0 := by
      apply normalized_frobenius_pow_injective hn ha (by omega)
      rw [← htheta, hthetaOne, pow_zero]
    have hbr : b = r := by
      apply normalized_frobenius_pow_injective hn hb hrhalf
      rw [← hphi, ← hphiR]
    exact .typeCRight ha0 (by omega)
  · have har : a = r := by
      apply normalized_frobenius_pow_injective hn ha hrhalf
      rw [← htheta, ← hthetaR]
    have hpowers :
        frobeniusEquiv (GaloisField 2 n) 2 ^ b =
          frobeniusEquiv (GaloisField 2 n) 2 ^ (2 * a) := by
      rw [← hphi, hphiSq, htheta, ← pow_mul]
      congr 1
      omega
    have habz :
        (b : ZMod n) = 2 * (a : ZMod n) := by
      have := frobenius_pow_zmod_eq_of_eq hn hpowers
      push_cast at this
      simpa [mul_comm] using this
    apply NormalizedExponentPairRelation.typeD
    left
    refine ⟨habz, ?_⟩
    simpa [har] using hfive
  · have hbr : b = r := by
      apply normalized_frobenius_pow_injective hn hb hrhalf
      rw [← hphi, ← hphiR]
    have hpowers :
        frobeniusEquiv (GaloisField 2 n) 2 ^ a =
          frobeniusEquiv (GaloisField 2 n) 2 ^ (2 * b) := by
      rw [← htheta, hthetaSq, hphi, ← pow_mul]
      congr 1
      omega
    have habz :
        (a : ZMod n) = 2 * (b : ZMod n) := by
      have := frobenius_pow_zmod_eq_of_eq hn hpowers
      push_cast at this
      simpa [mul_comm] using this
    apply NormalizedExponentPairRelation.typeD
    right
    refine ⟨habz, ?_⟩
    simpa [hbr] using hfive

private theorem normalizedTypeDExponentRelation_endpoints_pos
    {n a b : ℕ} (hn : 0 < n)
    (ha : 2 * a ≤ n) (hb : 2 * b ≤ n)
    (hab : a ≠ b)
    (hrel : NormalizedTypeDExponentRelation n a b) :
    0 < a ∧ 0 < b := by
  have ha_lt : a < n := by omega
  have hb_lt : b < n := by omega
  rcases hrel with ⟨hba, ha5⟩ | ⟨habz, hb5⟩
  · constructor
    · by_contra ha0
      have ha0' : a = 0 := by omega
      subst a
      have hbcast : (b : ZMod n) = 0 := by simpa using hba
      have hbmod := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hbcast
      rw [Nat.mod_eq_of_lt hb_lt] at hbmod
      exact hab (by omega)
    · by_contra hb0
      have hb0' : b = 0 := by omega
      subst b
      have htwo : 2 * (a : ZMod n) = 0 := by simpa using hba.symm
      have hacast : (a : ZMod n) = 0 := by
        linear_combination 3 * htwo - ha5
      have hamod := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hacast
      rw [Nat.mod_eq_of_lt ha_lt] at hamod
      exact hab (by omega)
  · constructor
    · by_contra ha0
      have ha0' : a = 0 := by omega
      subst a
      have htwo : 2 * (b : ZMod n) = 0 := by simpa using habz.symm
      have hbcast : (b : ZMod n) = 0 := by
        linear_combination 3 * htwo - hb5
      have hbmod := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hbcast
      rw [Nat.mod_eq_of_lt hb_lt] at hbmod
      exact hab (by omega)
    · by_contra hb0
      have hb0' : b = 0 := by omega
      subst b
      have hacast : (a : ZMod n) = 0 := by simpa using habz
      have hamod := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hacast
      rw [Nat.mod_eq_of_lt ha_lt] at hamod
      exact hab (by omega)

private theorem normalized_exponent_pair_relations_force_degree_five
    {n x y w : ℕ} (hn : 0 < n)
    (hxhalf : 2 * x ≤ n) (hyhalf : 2 * y ≤ n)
    (hwhalf : 2 * w ≤ n)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hXW : NormalizedExponentPairRelation n x w)
    (hYW : NormalizedExponentPairRelation n y w) :
    n = 5 ∧ w = 2 := by
  have hn2 : 2 ≤ n := by omega
  rcases hXW with hsameX | ⟨hw0X, hdimX⟩ |
      ⟨hx0, hdimX⟩ | hDX
  · exact (hxw hsameX).elim
  · rcases hYW with hsameY | ⟨hw0Y, hdimY⟩ |
        ⟨hy0, hdimY⟩ | hDY
    · exact (hyw hsameY).elim
    · exact (hxy (by omega)).elim
    · exact (hyw (by omega)).elim
    · have hwpos :=
        (normalizedTypeDExponentRelation_endpoints_pos
          hn hyhalf hwhalf hyw hDY).2
      omega
  · rcases hYW with hsameY | ⟨hw0, hdimY⟩ |
        ⟨hy0, hdimY⟩ | hDY
    · exact (hyw hsameY).elim
    · exact (hxw (by omega)).elim
    · exact (hxy (by omega)).elim
    · rcases hDY with ⟨hwy, hy5⟩ | ⟨hywz, hw5⟩
      · exact exponent_eq_two_of_dimension_and_doubled_five_congruence
          hn2 hdimX hwy hy5
      · exact exponent_eq_two_of_dimension_and_five_congruence
          hn2 hdimX hw5
  · rcases hYW with hsameY | ⟨hw0, hdimY⟩ |
        ⟨hy0, hdimY⟩ | hDY
    · exact (hyw hsameY).elim
    · have hwpos :=
        (normalizedTypeDExponentRelation_endpoints_pos
          hn hxhalf hwhalf hxw hDX).2
      omega
    · rcases hDX with ⟨hwx, hx5⟩ | ⟨hxwz, hw5⟩
      · exact exponent_eq_two_of_dimension_and_doubled_five_congruence
          hn2 hdimY hwx hx5
      · exact exponent_eq_two_of_dimension_and_five_congruence
          hn2 hdimY hw5
    · have hxpos :=
        (normalizedTypeDExponentRelation_endpoints_pos
          hn hxhalf hwhalf hxw hDX).1
      have hypos :=
        (normalizedTypeDExponentRelation_endpoints_pos
          hn hyhalf hwhalf hyw hDY).1
      have hxyEq :=
        normalizedTypeDExponentRelation_neighbors_eq
          hxpos hypos hxhalf hyhalf hDX.symm hDY.symm
      exact (hxy hxyEq).elim

/-- **Higman Lemma 13 (p. 93), all-distinct parameter list check.**
For three normalized lower-half Frobenius parameters, pairwise relations
from the two joins sharing `W` force the common parameter to be `Frob²`
over the field of degree five. -/
theorem normalized_factorPairRelations_common_eq_frobenius_sq
    {n x y w : ℕ}
    {thetaX thetaY thetaW : RingAut (GaloisField 2 n)}
    (hn : 0 < n)
    (hxhalf : 2 * x ≤ n) (hyhalf : 2 * y ≤ n)
    (hwhalf : 2 * w ≤ n)
    (hthetaX :
      thetaX = frobeniusEquiv (GaloisField 2 n) 2 ^ x)
    (hthetaY :
      thetaY = frobeniusEquiv (GaloisField 2 n) 2 ^ y)
    (hthetaW :
      thetaW = frobeniusEquiv (GaloisField 2 n) 2 ^ w)
    (hxy : thetaX ≠ thetaY) (hxw : thetaX ≠ thetaW)
    (hyw : thetaY ≠ thetaW)
    (hXW : NormalizedFactorPairRelation n thetaX thetaW)
    (hYW : NormalizedFactorPairRelation n thetaY thetaW) :
    n = 5 ∧
      thetaW = frobeniusEquiv (GaloisField 2 n) 2 ^ 2 := by
  have hxyExp : x ≠ y := by
    intro h
    apply hxy
    rw [hthetaX, hthetaY, h]
  have hxwExp : x ≠ w := by
    intro h
    apply hxw
    rw [hthetaX, hthetaW, h]
  have hywExp : y ≠ w := by
    intro h
    apply hyw
    rw [hthetaY, hthetaW, h]
  have hXWExp :=
    normalized_factorPairRelation_to_exponents
      hn hxhalf hwhalf hthetaX hthetaW hXW
  have hYWExp :=
    normalized_factorPairRelation_to_exponents
      hn hyhalf hwhalf hthetaY hthetaW hYW
  obtain ⟨hn5, hw2⟩ :=
    normalized_exponent_pair_relations_force_degree_five
      hn hxhalf hyhalf hwhalf hxyExp hxwExp hywExp hXWExp hYWExp
  exact ⟨hn5, by simpa [hw2] using hthetaW⟩

private theorem exists_lowerHalf_frobenius_exponent_of_normalized
    {n : ℕ} {theta : RingAut (GaloisField 2 n)}
    (hnorm :
      theta = 1 ∨
        ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
          theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
          Odd (orderOf theta)) :
    ∃ r : ℕ, 2 * r ≤ n ∧
      theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r := by
  rcases hnorm with htheta | ⟨r, _hr0, hrhalf, htheta, _hodd⟩
  · exact ⟨0, by omega, by simpa using htheta⟩
  · exact ⟨r, hrhalf, htheta⟩

/-- The all-distinct list check stated directly with the normalization
witnesses returned by
`FactorCoordinateData.exists_normalized_frobenius_le_half`.  The odd-order
clauses belong to the coordinate package; the list check itself only needs
the selected lower-half representatives. -/
theorem normalized_factorPairRelations_common_eq_frobenius_sq_of_normalized
    {n : ℕ}
    {thetaX thetaY thetaW : RingAut (GaloisField 2 n)}
    (hn : 0 < n)
    (hXnorm :
      thetaX = 1 ∨
        ∃ x : ℕ, 0 < x ∧ 2 * x ≤ n ∧
          thetaX = frobeniusEquiv (GaloisField 2 n) 2 ^ x ∧
          Odd (orderOf thetaX))
    (hYnorm :
      thetaY = 1 ∨
        ∃ y : ℕ, 0 < y ∧ 2 * y ≤ n ∧
          thetaY = frobeniusEquiv (GaloisField 2 n) 2 ^ y ∧
          Odd (orderOf thetaY))
    (hWnorm :
      thetaW = 1 ∨
        ∃ w : ℕ, 0 < w ∧ 2 * w ≤ n ∧
          thetaW = frobeniusEquiv (GaloisField 2 n) 2 ^ w ∧
          Odd (orderOf thetaW))
    (hxy : thetaX ≠ thetaY) (hxw : thetaX ≠ thetaW)
    (hyw : thetaY ≠ thetaW)
    (hXW : NormalizedFactorPairRelation n thetaX thetaW)
    (hYW : NormalizedFactorPairRelation n thetaY thetaW) :
    n = 5 ∧
      thetaW = frobeniusEquiv (GaloisField 2 n) 2 ^ 2 := by
  obtain ⟨x, hxhalf, hthetaX⟩ :=
    exists_lowerHalf_frobenius_exponent_of_normalized hXnorm
  obtain ⟨y, hyhalf, hthetaY⟩ :=
    exists_lowerHalf_frobenius_exponent_of_normalized hYnorm
  obtain ⟨w, hwhalf, hthetaW⟩ :=
    exists_lowerHalf_frobenius_exponent_of_normalized hWnorm
  exact normalized_factorPairRelations_common_eq_frobenius_sq
    hn hxhalf hyhalf hwhalf hthetaX hthetaY hthetaW
      hxy hxw hyw hXW hYW

end OddOrder.Higman.Suzuki2Groups
