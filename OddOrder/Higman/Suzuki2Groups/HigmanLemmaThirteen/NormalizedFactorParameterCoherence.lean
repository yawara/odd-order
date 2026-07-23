/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoPowerCongruence

/-!
# Higman Lemma 13: normalized factor-parameter coherence

G. Higman, *Suzuki 2-groups*, pp. 90--94.  The exponent-two branch of
Lemma 13 compares the same factor inside several pairwise joins.  Each join
supplies a Frobenius parameter only up to inversion.  After choosing the
representative in the lower half of `ZMod n`, the source equation
`ν = λ θ(λ)` and an equivariant identification of the factor force those
representatives to agree.

This file isolates the arithmetic part.  The equivariant identification says
that the two source eigenvalues lie in one Frobenius orbit.  Higman's
`s = ±r` congruence then leaves equality as the only possibility: the inverse
alternative would make the two positive lower-half representatives sum to
`n`, which can happen only when they are already equal.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- **Higman Lemma 13, normalized factor-parameter coherence (arithmetic
part).**  Two positive Frobenius exponents normalized to the lower half of
`ZMod n` agree when their source eigenvalues lie in the same Frobenius orbit
and solve the same kernel-eigenvalue equation, with the first eigenvalue of
full order `2 ^ n - 1`. -/
theorem normalized_frobenius_exponents_eq_of_power_bridge
    {F : Type*} [Monoid F] {lam mu nu : F} {n r s i : ℕ}
    (hn : 0 < n) (hr0 : 0 < r) (hs0 : 0 < s)
    (hrhalf : 2 * r ≤ n) (hshalf : 2 * s ≤ n)
    (hordlam : orderOf lam = 2 ^ n - 1)
    (hlam : lam ^ (1 + 2 ^ r) = nu)
    (hmu : mu ^ (1 + 2 ^ s) = nu)
    (hbridge : mu = lam ^ 2 ^ i) :
    r = s := by
  by_contra hrs
  have hrn : r < n := by omega
  have hsn : s < n := by omega
  have hrz : (r : ZMod n) ≠ 0 := by
    rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero, Nat.mod_eq_of_lt hrn]
    omega
  have hsz : (s : ZMod n) ≠ 0 := by
    rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero, Nat.mod_eq_of_lt hsn]
    omega
  have hpoweq : lam ^ (2 ^ i * (1 + 2 ^ s)) =
      lam ^ (2 ^ 0 * (1 + 2 ^ r)) := by
    have hleft : lam ^ (2 ^ i * (1 + 2 ^ s)) = nu := by
      rw [pow_mul, ← hbridge, hmu]
    have hright : lam ^ (2 ^ 0 * (1 + 2 ^ r)) = nu := by
      rw [pow_zero, one_mul]
      exact hlam
    rw [hleft, hright]
  have hcong :=
    higman_typeB_congruence_of_pow_eq hn hordlam hpoweq
  rcases higman_typeB_exponent_pm hn hrz hsz hcong with hpm | hpm
  · have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hpm
    rw [Nat.ModEq, Nat.mod_eq_of_lt hsn, Nat.mod_eq_of_lt hrn] at hmod
    exact hrs hmod.symm
  · have hrslt : r + s < n := by omega
    have hrsz : (r : ZMod n) + (s : ZMod n) ≠ 0 := by
      rw [← Nat.cast_add, Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
        Nat.mod_eq_of_lt hrslt]
      omega
    apply hrsz
    rw [add_comm]
    exact hpm

end OddOrder.Higman.Suzuki2Groups
