/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Peterfalvi (1.10): cyclotomic congruences of character values

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §1, p. 7,
result **(1.10)**.

This file develops the cyclotomic-integer arithmetic behind Peterfalvi (1.10):

* **(1.10.b)** `int_dvd_of_zeta_sub_one_dvd`: in a `p`-th cyclotomic field `L` over `ℚ`
  (`p` an odd prime, `ζ` a primitive `p`-th root of unity), if an integer `n` factors as
  `n = (ζ - 1) · a` with `a` an algebraic integer, then `p ∣ n`.  This is the divisibility
  half of (1.10), used (with (1.10.a)) in Peterfalvi (12.16) and (13.5).

The number-theoretic core is a norm computation: `N_{L/ℚ}(ζ - 1) = p`
(`IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`), `N(n) = n^{[L:ℚ]} = n^{p-1}`, and
`N(a) ∈ ℤ` (the norm of an algebraic integer), so `n^{p-1} = p · N(a)` and `p ∣ n`.
-/

namespace OddOrder.RepresentationTheory

open Polynomial Module

/-- `(1 - ε) ∣ (ε^k - 1)` in any commutative ring (the elementary divisibility behind (1.10.a)):
`ε^k - 1 = (ε - 1)·∑_{i<k} ε^i = (1 - ε)·(-∑_{i<k} ε^i)`.  Applied with `ε` a `p`-th root of unity
and `ε^k = α(x)` for a linear character `α` and an order-`p` element `x`. -/
theorem one_sub_dvd_pow_sub_one {R : Type*} [CommRing R] (ε : R) (k : ℕ) :
    (1 - ε) ∣ (ε ^ k - 1) :=
  ⟨-(∑ i ∈ Finset.range k, ε ^ i), by rw [← geom_sum_mul ε k]; ring⟩

/-- **Peterfalvi (1.10.b)** (abstract cyclotomic form): in a `p`-th cyclotomic field `L` over `ℚ`
(`p` an odd prime), if an integer `n` is divisible by `ζ - 1` (`ζ` a primitive `p`-th root of
unity) with an algebraic-integer quotient `a`, then `p ∣ n`.

Norm argument: `N_{L/ℚ}(ζ - 1) = p`, `N(n) = n^{p-1}`, `N(a) ∈ ℤ`, so `n^{p-1} = p·N(a)`. -/
theorem int_dvd_of_zeta_sub_one_dvd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    {n : ℤ} {a : L} (ha : IsIntegral ℤ a)
    (h : (algebraMap ℤ L n) = (ζ - 1) * a) :
    (p : ℤ) ∣ n := by
  haveI : NumberField L := inferInstance
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.out.pos
  -- the relative degree `[L : ℚ] = p - 1`
  have hfr : finrank ℚ L = p - 1 := by
    rw [IsCyclotomicExtension.finrank L hirr]; exact Nat.totient_prime hp.out
  -- take field norms `N_{L/ℚ}` of both sides
  have hN := congrArg (Algebra.norm ℚ) h
  rw [map_mul, hζ.norm_sub_one_of_prime_ne_two' hirr hp2] at hN
  -- `N(algebraMap ℤ L n) = (n : ℚ)^(p-1)`
  have hNn : Algebra.norm ℚ (algebraMap ℤ L n) = (n : ℚ) ^ (p - 1) := by
    have he : algebraMap ℤ L n = algebraMap ℚ L (n : ℚ) := by simp
    rw [he, Algebra.norm_algebraMap, hfr]
  -- `N(a)` is a rational integer, say `m`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Algebra.norm ℚ a = (m : ℚ) := by
    have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact ⟨y, by rw [← hy]; simp⟩
  rw [hNn, hm] at hN
  -- `(n:ℚ)^(p-1) = p * m`, so as integers `n^(p-1) = p*m`, hence `p ∣ n`
  have hZ : (n : ℤ) ^ (p - 1) = (p : ℤ) * m := by exact_mod_cast hN
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  exact hpZ.dvd_of_dvd_pow ⟨m, hZ⟩

end OddOrder.RepresentationTheory
