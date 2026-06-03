/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

/-!
# BG Appendix C: the finite-field norm-set argument

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, pp. 145--152 (mmd L4855--5005).

This file develops the finite-field side of BG Appendix C (the Carlip--Wheeler
account of Peterfalvi's generators-and-relations argument) on the *actual* field
`GaloisField p q = 𝔽_{p^q}`, as opposed to the propositional scaffold carried by
`OddOrder.BG.AppC` in `AppC_FinalContradiction.lean`.

Let `p`, `q` be primes satisfying **condition (A)**
`gcd((p^q-1)/(p-1), p-1) = 1`.  Writing `N` for the norm of `𝔽_{p^q}` over `𝔽_p`,
the key object is the **norm set**

  `E = { a ∈ 𝔽_{p^q} | N(a) = N(2-a) = 1 }`.

The contradiction `p ≤ q` (BG Theorem C) is obtained from three lemmas:

* **Lemma C.1**: `E = E⁻¹ ∧ |E| ≥ 2  ⟹  p ≤ q`  (a polynomial root count);
* **Lemma C.2**: `|E| ≥ 2`  (case `q = 3` elementary, `q ≥ 5` via the character
  theory of the Frobenius group `H = P ⋊ U`);
* **Lemma C.3**: `E = E⁻¹`  (the generators-and-relations argument; needs the
  embedding hypothesis (B) into the minimal counterexample `G`).

## Main definitions

* `normN p q x` — the norm `N(x) = ∏_{i<q} x^{p^i}` of `x ∈ 𝔽_{p^q}` over `𝔽_p`.
* `normSetE p q` — the norm set `E`.

## Main results (this file)

* `conditionA_iff_not_dvd` — **Remark (I)**: condition (A) `⟺ q ∤ (p-1)`.

Lemmas C.1, C.2 are stated here with `sorry`; their proofs and the assembly into
BG Theorem C are tracked in issue 3000 / `notes/bg/appC_normset_plan.md`.

## References

* Bender, Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188,
  1994), Appendix C.
-/

namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-! ## The norm and the norm set -/

/-- **BG App C norm** `N(x)`: the norm of `x ∈ 𝔽_{p^q}` over `𝔽_p`, written as the
product of its Frobenius conjugates `∏_{i<q} x^{p^i}` (this equals
`Algebra.norm (ZMod p) x`). -/
noncomputable def normN [Fact p.Prime] (x : GaloisField p q) : GaloisField p q :=
  ∏ i ∈ Finset.range q, x ^ (p ^ i)

/-- **BG App C norm set** `E = { a ∈ 𝔽_{p^q} | N(a) = N(2-a) = 1 }` (mmd L4853). -/
def normSetE [Fact p.Prime] : Set (GaloisField p q) :=
  {a | normN p q a = 1 ∧ normN p q (2 - a) = 1}

/-! ### Basic algebra of the norm and the norm set -/

@[simp] lemma normN_one [Fact p.Prime] : normN p q (1 : GaloisField p q) = 1 := by
  simp [normN]

/-- The norm is multiplicative (it is a product of multiplicative maps). -/
lemma normN_mul [Fact p.Prime] (x y : GaloisField p q) :
    normN p q (x * y) = normN p q x * normN p q y := by
  simp only [normN, mul_pow, Finset.prod_mul_distrib]

/-- The norm of a nonzero element is nonzero. -/
lemma normN_ne_zero [Fact p.Prime] {x : GaloisField p q} (hx : x ≠ 0) :
    normN p q x ≠ 0 := by
  simp only [normN]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hx

lemma mem_normSetE_iff [Fact p.Prime] {a : GaloisField p q} :
    a ∈ normSetE p q ↔ normN p q a = 1 ∧ normN p q (2 - a) = 1 := Iff.rfl

/-- `E` is symmetric under `a ↦ 2 - a` (the two norm conditions just swap). -/
lemma two_sub_mem_normSetE [Fact p.Prime] {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 - a) ∈ normSetE p q := by
  refine ⟨ha.2, ?_⟩
  rw [show (2 : GaloisField p q) - (2 - a) = a by ring]
  exact ha.1

/-- `1 ∈ E`, since `N(1) = N(2-1) = N(1) = 1`. -/
lemma one_mem_normSetE [Fact p.Prime] : (1 : GaloisField p q) ∈ normSetE p q := by
  refine ⟨normN_one p q, ?_⟩
  rw [show (2 : GaloisField p q) - 1 = 1 by ring]
  exact normN_one p q

/-! ## Remark (I): condition (A) ⟺ q ∤ (p-1) -/

/-- **BG Appendix C, Remark (I)** (mmd L4877): condition (A),
`gcd((p^q-1)/(p-1), p-1) = 1`, is equivalent to `q ∤ (p-1)`.

Indeed `(p^q-1)/(p-1) = ∑_{i<q} p^i ≡ q (mod p-1)` since `p ≡ 1 (mod p-1)`, so the
gcd with `p-1` is `gcd(q, p-1)`, which is `1` iff the prime `q` does not divide
`p-1`. -/
theorem conditionA_iff_not_dvd (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ (p - 1) := by
  -- `(p^q-1)/(p-1)` is the geometric sum `∑_{i<q} p^i`.
  have hsum : (p ^ q - 1) / (p - 1) = ∑ k ∈ Finset.range q, p ^ k :=
    (Nat.geomSum_eq hp q).symm
  -- `↑p = 1` in `ZMod (p-1)`.
  have hp1 : (p : ZMod (p - 1)) = 1 := by
    have hcast : (p : ZMod (p - 1)) = ((p - 1) + 1 : ℕ) := by congr 1; omega
    rw [hcast, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  -- Hence `↑(∑_{i<q} p^i) = ↑q` in `ZMod (p-1)`.
  have hsumcast : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod (p - 1)) = (q : ZMod (p - 1)) := by
    push_cast
    rw [hp1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- Translate coprimality to a unit statement in `ZMod (p-1)`.
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ Nat.Coprime q (p - 1) := by
    rw [hsum, ← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, hsumcast]
  rw [hcop]
  exact hq.coprime_iff_not_dvd

/-! ## Lemma C.1 -/

/-- **BG Appendix C, Lemma C.1** (mmd L4911): if the norm set is closed under
inversion and has at least two elements, then `p ≤ q`.

Proof (to be formalized, issue 3000): for `a ∈ E^#`, the map `τ(a) = 1/(2-a)`
sends `E` to `E` (using `E = E⁻¹`), and `∏_{j≤k} τ^j(a) = 1/((k+1)-ka)`
telescopes, giving `N((1-a)k+1) = 1` for all `k ∈ 𝔽_p`. The degree-`q` polynomial
`∏_{i<q} ((1-a)^{p^i} X + 1) - 1` (leading coefficient `N(1-a) ≠ 0`) then has all
`p` elements of `𝔽_p` as roots, so `p ≤ q`. -/
theorem lemmaC1 [Fact p.Prime] (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (hcard : 2 ≤ (normSetE p q).ncard) :
    p ≤ q := by
  sorry

/-! ## Lemma C.2 -/

/-- **BG Appendix C, Lemma C.2** (mmd L4923): the norm set has at least two
elements (assuming only that `p`, `q` are odd primes satisfying condition (A)).

Proof (to be formalized, issue 3000): for `q ≥ 5` via the character theory of the
Frobenius group `H = P ⋊ U` (`|E|` is a structure constant bounded below by
`p^{q-2} - p^{q/2} > 1` through the orthogonality relations); for `q = 3` via the
cubic `f_c(x) = x(x-2)(x-c) + (x-1)`, some `c` of which has no root in `𝔽_p`,
yielding a root `a ∈ 𝔽_{p^3}` with `N(a) = N(2-a) = 1`, so `a, 1 ∈ E`. -/
theorem lemmaC2 [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hqodd : Odd q)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    2 ≤ (normSetE p q).ncard := by
  sorry

end OddOrder.BG.AppC.NormSet
