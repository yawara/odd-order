/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.FactorPairRelationDefinition

/-!
# Higman Lemma 13: exponent-two parameter arithmetic

G. Higman, *Suzuki 2-groups*, p. 93.  In the exponent-two branch, two
type-D pair relations sharing one factor force the other normalized
Frobenius exponents to agree.  The only remaining all-distinct
configuration mixes a type-C dimension equation with a type-D order-five
congruence.  Those two equations force `n = 5` and exponent `r = 2`, hence
the automorphism `Frob² : α ↦ α⁴`.

This file isolates the arithmetic over `ZMod n`; the downstream factor
theorem supplies these equations from the normalized B/C/D relations.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- The exponent relation carried by one type-D factor pair, with either
endpoint allowed to be Higman's distinguished exponent `r`. -/
def NormalizedTypeDExponentRelation (n a b : ℕ) : Prop :=
  ((b : ZMod n) = 2 * (a : ZMod n) ∧
      5 * (a : ZMod n) = 0) ∨
    ((a : ZMod n) = 2 * (b : ZMod n) ∧
      5 * (b : ZMod n) = 0)

/-- A type-D exponent relation is symmetric in its two endpoints. -/
theorem NormalizedTypeDExponentRelation.symm
    {n a b : ℕ} (h : NormalizedTypeDExponentRelation n a b) :
    NormalizedTypeDExponentRelation n b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Two type-D edges with a common endpoint make their other endpoints
equal or additive inverses modulo `n`. -/
theorem normalizedTypeDExponentRelation_neighbors_zmod
    {n w x y : ℕ}
    (hWX : NormalizedTypeDExponentRelation n w x)
    (hWY : NormalizedTypeDExponentRelation n w y) :
    (x : ZMod n) = (y : ZMod n) ∨
      (x : ZMod n) + (y : ZMod n) = 0 := by
  rcases hWX with ⟨hx, hw5⟩ | ⟨hwx, hx5⟩ <;>
    rcases hWY with ⟨hy, _hw5'⟩ | ⟨hwy, hy5⟩
  · left
    rw [hx, hy]
  · right
    rw [hx, hwy]
    linear_combination hy5
  · right
    rw [hy, hwx]
    linear_combination hx5
  · left
    linear_combination -3 * hwx + 3 * hwy - hx5 + hy5

/-- Positive lower-half representatives at the two free endpoints of
type-D edges with a common endpoint are equal as natural numbers. -/
theorem normalizedTypeDExponentRelation_neighbors_eq
    {n w x y : ℕ}
    (hx0 : 0 < x) (hy0 : 0 < y)
    (hxhalf : 2 * x ≤ n) (hyhalf : 2 * y ≤ n)
    (hWX : NormalizedTypeDExponentRelation n w x)
    (hWY : NormalizedTypeDExponentRelation n w y) :
    x = y := by
  rcases normalizedTypeDExponentRelation_neighbors_zmod hWX hWY with
    hxy | hsum
  · have hxlt : x < n := by omega
    have hylt : y < n := by omega
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod
  · have hcast : ((x + y : ℕ) : ZMod n) = 0 := by
      push_cast
      exact hsum
    have hmod := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hcast
    have hsumle : x + y ≤ n := by omega
    have hsumeq : x + y = n := by
      by_contra hne
      have hlt : x + y < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    omega

/-- **Higman Lemma 13 (p. 93), type-C/type-D arithmetic.**  The type-C
dimension equation and the type-D order-five congruence force the field
degree and normalized Frobenius exponent to be `5` and `2`. -/
theorem exponent_eq_two_of_dimension_and_five_congruence
    {n r : ℕ} (hn : 2 ≤ n)
    (hdim : 2 * r + 1 = n)
    (hfive : 5 * (r : ZMod n) = 0) :
    n = 5 ∧ r = 2 := by
  have hdimz : 2 * (r : ZMod n) + 1 = 0 := by
    have h : (((2 * r + 1 : ℕ) : ZMod n)) = 0 := by
      rw [hdim]
      exact ZMod.natCast_self n
    push_cast at h
    exact h
  have h5z : (5 : ZMod n) = 0 := by
    linear_combination 5 * hdimz - 2 * hfive
  have hndvd5 : n ∣ 5 :=
    Nat.dvd_of_mod_eq_zero
      (natCast_zmod_eq_zero_iff_mod_eq_zero.mp h5z)
  have hnle : n ≤ 5 := Nat.le_of_dvd (by norm_num) hndvd5
  interval_cases n <;> omega

/-- Variant where the type-C exponent is twice the type-D distinguished
exponent modulo `n`. -/
theorem exponent_eq_two_of_dimension_and_doubled_five_congruence
    {n r s : ℕ} (hn : 2 ≤ n)
    (hdim : 2 * r + 1 = n)
    (hrs : (r : ZMod n) = 2 * (s : ZMod n))
    (hfive : 5 * (s : ZMod n) = 0) :
    n = 5 ∧ r = 2 := by
  apply exponent_eq_two_of_dimension_and_five_congruence
    hn hdim
  rw [hrs]
  linear_combination 2 * hfive

end OddOrder.Higman.Suzuki2Groups
