import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
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

end OddOrder.NumberTheory
