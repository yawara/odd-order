/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum

/-!
# Primitive prime divisors of `(p^q - 1)/(p - 1)` for `q` an odd prime

This is the easy special case `n = q` prime of **Zsygmondy's theorem**: for `q` an odd prime and
`p ≥ 2`, the number `(p^q - 1)/(p - 1) = ∑_{i<q} p^i` has a prime divisor `r` with
`orderOf (p : ZMod r) = q` (a *primitive* prime divisor of `p^q - 1`).

The proof needs no general Zsygmondy machinery.  Every prime factor `r ≠ q` of the geometric sum
`n = ∑_{i<q} p^i` has `orderOf (p : ZMod r) = q`: from `r ∣ n ∣ p^q - 1` the order divides `q`, and
it is `≠ 1` because `r = q` would follow from `p ≡ 1 [MOD r]` (`n ≡ q [MOD r]`).  Such a factor
`r ≠ q` exists because `v_q(n) ≤ 1` (lifting the exponent) while `n > q`.

Used to upgrade the Singer irreducibility lemma `isSimpleModule_of_isCyclic_faithful_card`
(`SingerField.lean`) from cyclic to **abelian** acting groups, closing the Peterfalvi (13.2.a)
`U`/`V`-cyclic obligations of §16 without the §13 type-`P` structure theory.
-/

namespace OddOrder.NumberTheory

open Finset

/-- **Any prime factor `r ≠ q` of `∑_{i<q} p^i` is a primitive prime divisor of `p^q - 1`**:
`orderOf (p : ZMod r) = q`.  (The `q`-part of the geometric sum is handled separately; here `r ≠ q`
is the hypothesis.)  From `r ∣ ∑_{i<q} p^i ∣ p^q - 1` the order divides the prime `q`; and it cannot
be `1`, since `(p : ZMod r) = 1` would give `0 = ∑ (p:ZMod r)^i = q` in `ZMod r`, i.e. `r ∣ q`. -/
theorem orderOf_eq_of_prime_dvd_geomSum {p q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hrq : r ≠ q) (hrn : r ∣ ∑ i ∈ range q, p ^ i) :
    orderOf (p : ZMod r) = q := by
  haveI : Fact r.Prime := ⟨hr⟩
  -- In `ZMod r`, the geometric sum vanishes: `∑ (p:ZMod r)^i = 0`.
  have hsum0 : ∑ i ∈ range q, (p : ZMod r) ^ i = 0 := by
    have : ((∑ i ∈ range q, p ^ i : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hrn
    push_cast at this
    exact this
  -- Hence `(p:ZMod r)^q = 1`, so `orderOf (p:ZMod r) ∣ q`.
  have hpow : (p : ZMod r) ^ q = 1 := by
    have hgm := geom_sum_mul (p : ZMod r) q
    rw [hsum0, zero_mul] at hgm
    exact sub_eq_zero.mp hgm.symm
  have hdvd : orderOf (p : ZMod r) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  -- `orderOf ≠ 1`: else `(p:ZMod r) = 1`, forcing `q = 0` in `ZMod r`, i.e. `r ∣ q`.
  have hne1 : orderOf (p : ZMod r) ≠ 1 := by
    intro h1
    have hp1 : (p : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
    have : ((q : ℕ) : ZMod r) = 0 := by
      have : ∑ i ∈ range q, (p : ZMod r) ^ i = ∑ _i ∈ range q, (1 : ZMod r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hp1, one_pow]
      rw [this, Finset.sum_const, card_range, nsmul_eq_mul, mul_one] at hsum0
      exact hsum0
    have hrdvdq : r ∣ q := (ZMod.natCast_eq_zero_iff _ _).mp this
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrdvdq)
  -- `orderOf ∣ q` (prime) and `≠ 1` ⟹ `= q`.
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h | h
  · exact absurd h hne1
  · exact h

/-- If the odd prime `q` divides `∑_{i<q} p^i`, then `q ∣ p - 1`.  In `ZMod q` the geometric sum
vanishes, so `(p:ZMod q)^q = 1`; but `(p:ZMod q)^q = (p:ZMod q)` (Frobenius), giving
`(p:ZMod q) = 1`. -/
theorem dvd_sub_one_of_dvd_geomSum {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime)
    (hqn : q ∣ ∑ i ∈ range q, p ^ i) : q ∣ p - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hsum0 : ∑ i ∈ range q, (p : ZMod q) ^ i = 0 := by
    have : ((∑ i ∈ range q, p ^ i : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqn
    push_cast at this; exact this
  have hpow : (p : ZMod q) ^ q = 1 := by
    have hgm := geom_sum_mul (p : ZMod q) q
    rw [hsum0, zero_mul] at hgm
    exact sub_eq_zero.mp hgm.symm
  have hp1 : (p : ZMod q) = 1 := by
    have hfrob : (p : ZMod q) ^ q = (p : ZMod q) := ZMod.pow_card _
    rw [hfrob] at hpow; exact hpow
  have : ((p - 1 : ℕ) : ZMod q) = 0 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ p), hp1]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- `q² ∤ ∑_{i<q} p^i` for `q` an odd prime, `p ≥ 2`.  If `q ∤ n` this is trivial; if `q ∣ n` then
`q ∣ p - 1`, and lifting the exponent gives `v_q(p^q - 1) = v_q(p - 1) + 1`, so as
`n·(p-1) = p^q - 1` we get `v_q(n) = 1`. -/
theorem not_sq_dvd_geomSum {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ ∑ i ∈ range q, p ^ i := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqn : q ∣ ∑ i ∈ range q, p ^ i
  · -- `q ∣ n`: LTE ⟹ `v_q(n) = 1`.
    have hqp1 : q ∣ p - 1 := dvd_sub_one_of_dvd_geomSum hp hq hqn
    -- `n * (p - 1) = p^q - 1`
    have hdvd : (p - 1) ∣ p ^ q - 1 := by
      have h1 : (1 : ℕ) ≡ p ^ q [MOD p - 1] := by
        have hp1 : (1 : ℕ) ≡ p [MOD p - 1] := (Nat.modEq_iff_dvd' (by omega)).mpr dvd_rfl
        simpa using hp1.pow q
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h1
    have hfact : (∑ i ∈ range q, p ^ i) * (p - 1) = p ^ q - 1 := by
      rw [Nat.geomSum_eq hp q, Nat.div_mul_cancel hdvd]
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    -- `q ∤ p` (else `q ∣ p` with `q ∣ p-1` gives `q ∣ 1`).
    have hqp : ¬ q ∣ p := by
      intro h
      have h1 : p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr hqp1).symm
      have h0 : p ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr h
      have hd : q ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num : (0 : ℕ) ≤ 1)).mp (h0.symm.trans h1)
      exact absurd (Nat.le_of_dvd one_pos hd) (by have := hq.two_le; omega)
    -- lifting the exponent: `v_q(p^q - 1) = v_q(p-1) + v_q(q) = v_q(p-1) + 1`.
    have hself : emultiplicity q q = 1 :=
      (Nat.finiteMultiplicity_iff.mpr ⟨hq.ne_one, hq.pos⟩).emultiplicity_self
    have hLTE : emultiplicity q (p ^ q - 1) = emultiplicity q (p - 1) + 1 := by
      have h := Nat.emultiplicity_pow_sub_pow hq hqodd hqp1 hqp q
      rwa [one_pow, hself] at h
    -- `v_q(n) + v_q(p-1) = v_q(p^q-1) = v_q(p-1) + 1`, cancel to `v_q(n) = 1`.
    have hfin : emultiplicity q (p - 1) ≠ ⊤ :=
      finiteMultiplicity_iff_emultiplicity_ne_top.mp
        (Nat.finiteMultiplicity_iff.mpr ⟨hq.ne_one, by omega⟩)
    have hn1 : emultiplicity q (∑ i ∈ range q, p ^ i) = 1 := by
      have hmul : emultiplicity q (∑ i ∈ range q, p ^ i) + emultiplicity q (p - 1)
          = emultiplicity q (p - 1) + 1 := by
        rw [← emultiplicity_mul hq.prime, hfact, hLTE]
      rw [add_comm (emultiplicity q (p - 1)) 1] at hmul
      exact WithTop.add_right_cancel hfin hmul
    rw [pow_dvd_iff_le_emultiplicity, hn1]
    decide
  · exact fun h => hqn (dvd_trans (dvd_pow_self q (by norm_num)) h)

/-- **Primitive prime divisor** (Zsygmondy, `n = q` prime case): for `q` an odd prime and `p ≥ 2`,
`∑_{i<q} p^i = (p^q-1)/(p-1)` has a prime divisor `r` with `orderOf (p : ZMod r) = q`. -/
theorem exists_prime_orderOf_eq {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ∣ (∑ i ∈ range q, p ^ i) ∧ orderOf (p : ZMod r) = q := by
  set n := ∑ i ∈ range q, p ^ i with hndef
  -- `q < n`: the sum of `q` terms `p^i ≥ 1`, with the `i=1` term `p ≥ 2` strict.
  have hqn : q < n := by
    calc q = ∑ _i ∈ range q, 1 := by
            rw [Finset.sum_const, card_range, smul_eq_mul, mul_one]
      _ < ∑ i ∈ range q, p ^ i := by
            refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega)) ?_
            exact ⟨1, Finset.mem_range.mpr (by have := hq.two_le; omega),
              by rw [pow_one]; omega⟩
  have hnsq : ¬ q ^ 2 ∣ n := not_sq_dvd_geomSum hp hq hq2
  -- Extract a prime factor `r ≠ q` of `n`.
  by_cases hqdvd : q ∣ n
  · -- `q ∣ n`: write `n = q·m`; then `q ∤ m` (else `q² ∣ n`) and `m > 1` (else `n = q`).
    obtain ⟨m, hm⟩ := hqdvd
    have hqm : ¬ q ∣ m := by
      rintro ⟨t, rfl⟩
      exact hnsq ⟨t, by rw [hm]; ring⟩
    have hm1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hm; omega
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hrn : r ∣ n := by rw [hm]; exact Dvd.dvd.mul_left hrm q
    have hrq : r ≠ q := by rintro rfl; exact hqm hrm
    exact ⟨r, hr, hrn, orderOf_eq_of_prime_dvd_geomSum hq hr hrq hrn⟩
  · -- `q ∤ n`: any prime factor of `n` works (it is automatically `≠ q`).
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (by have := hq.two_le; omega : n ≠ 1)
    have hrq : r ≠ q := by rintro rfl; exact hqdvd hrn
    exact ⟨r, hr, hrn, orderOf_eq_of_prime_dvd_geomSum hq hr hrq hrn⟩

end OddOrder.NumberTheory
