/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
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

/-- If `E` has at least two elements then it contains an element `≠ 1` — the
`a ∈ E^#` with which the Lemma C.1 argument begins. -/
lemma exists_mem_normSetE_ne_one [Fact p.Prime]
    (hcard : 2 ≤ (normSetE p q).ncard) :
    ∃ a ∈ normSetE p q, a ≠ 1 := by
  by_contra h
  push_neg at h
  have hsub : normSetE p q ⊆ {1} := fun a ha => h a ha
  have hle : (normSetE p q).ncard ≤ ({1} : Set (GaloisField p q)).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton 1)
  rw [Set.ncard_singleton] at hle
  omega

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

/-! ## Lemma C.1 machinery: the Möbius iterate and the sequence `d_k` -/

/-- `N(0) = 0` (the `i = 0` factor `0^{p^0} = 0` makes the product vanish). -/
lemma normN_zero [Fact p.Prime] (hq : 0 < q) :
    normN p q (0 : GaloisField p q) = 0 := by
  simp only [normN]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hq) (by simp)

/-- An element of `E` is nonzero (its norm is `1 ≠ 0`). -/
lemma ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : a ≠ 0 := by
  intro h
  have := ha.1
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- For `a ∈ E`, `2 - a ≠ 0` (its norm is `1 ≠ 0`), so `(2-a)⁻¹` is genuine. -/
lemma two_sub_ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 : GaloisField p q) - a ≠ 0 := by
  intro h
  have := ha.2
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- The sequence `d_k := (k+1) - k·a = (1-a)·k + 1` of BG Lemma C.1. -/
noncomputable def dSeq [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  (k : GaloisField p q) + 1 - (k : GaloisField p q) * a

@[simp] lemma dSeq_zero [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 0 = 1 := by
  simp [dSeq]

lemma dSeq_one [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 1 = 2 - a := by
  simp only [dSeq, Nat.cast_one, one_mul]; ring

/-- The three-term recurrence `d_{k+2} = 2·d_{k+1} - d_k`. -/
lemma dSeq_recurrence [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    dSeq p q a (k + 2) = 2 * dSeq p q a (k + 1) - dSeq p q a k := by
  simp only [dSeq]
  push_cast
  ring

/-- The Möbius iterate `a₀ = a`, `a_{k+1} = (2 - aₖ)⁻¹` of BG Lemma C.1. -/
noncomputable def tauIter [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  Nat.rec a (fun _ prev => (2 - prev)⁻¹) k

@[simp] lemma tauIter_zero [Fact p.Prime] (a : GaloisField p q) : tauIter p q a 0 = a := rfl

lemma tauIter_succ [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    tauIter p q a (k + 1) = (2 - tauIter p q a k)⁻¹ := rfl

/-- Every iterate `aₖ` lies in `E` (using `E = E⁻¹`). -/
lemma tauIter_mem [Fact p.Prime] {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, tauIter p q a k ∈ normSetE p q := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [tauIter_succ]
    have h2 : (2 - tauIter p q a k) ∈ normSetE p q := two_sub_mem_normSetE p q ih
    rw [hEinv] at h2
    rwa [Set.mem_inv] at h2

/-- Closed form of the iterate: `a_{k+1} = d_k / d_{k+1}`, with `d_{k+1} ≠ 0`. -/
lemma tauIter_eq_dSeq_div [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, dSeq p q a (k + 1) ≠ 0 ∧
      tauIter p q a (k + 1) = dSeq p q a k / dSeq p q a (k + 1) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [dSeq_one]; exact two_sub_ne_zero_of_mem_normSetE p q hq ha
    · rw [tauIter_succ, tauIter_zero, dSeq_zero, dSeq_one, one_div]
  | succ k ih =>
    obtain ⟨hd1, htau⟩ := ih
    have hmem : tauIter p q a (k + 1) ∈ normSetE p q := tauIter_mem p q hEinv ha (k + 1)
    have hne : (2 : GaloisField p q) - tauIter p q a (k + 1) ≠ 0 :=
      two_sub_ne_zero_of_mem_normSetE p q hq hmem
    have hkey : (2 : GaloisField p q) - tauIter p q a (k + 1)
        = dSeq p q a (k + 2) / dSeq p q a (k + 1) := by
      rw [htau, dSeq_recurrence]
      field_simp
    refine ⟨?_, ?_⟩
    · intro hcontra
      apply hne
      rw [hkey, hcontra, zero_div]
    · rw [tauIter_succ, hkey, inv_div]

/-- The multiplied form `a_{k+1} · d_{k+1} = d_k`. -/
lemma tauIter_mul_dSeq [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) (k : ℕ) :
    tauIter p q a (k + 1) * dSeq p q a (k + 1) = dSeq p q a k := by
  obtain ⟨hd1, htau⟩ := tauIter_eq_dSeq_div p q hq hEinv ha k
  rw [htau, div_mul_cancel₀ _ hd1]

/-- **Key telescoping output**: `N(d_k) = 1` for every `k`, since each
`a_{k+1} = d_k/d_{k+1} ∈ E` has norm `1` and the norm is multiplicative. -/
lemma normN_dSeq_eq_one [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, normN p q (dSeq p q a k) = 1 := by
  intro k
  induction k with
  | zero => rw [dSeq_zero]; exact normN_one p q
  | succ k ih =>
    have hmul := tauIter_mul_dSeq p q hq hEinv ha k
    have h1 : normN p q (tauIter p q a (k + 1)) = 1 := (tauIter_mem p q hEinv ha (k + 1)).1
    have hcong := congrArg (normN p q) hmul
    rw [normN_mul, h1, one_mul] at hcong
    rw [hcong]; exact ih

/-- Elements of the prime field `𝔽_p ⊆ 𝔽_{p^q}` are fixed by every power of the
Frobenius: `(k : 𝔽_{p^q})^{p^i} = (k : 𝔽_{p^q})`. -/
lemma natCast_pow_pPow [Fact p.Prime] (k i : ℕ) :
    ((k : GaloisField p q)) ^ (p ^ i) = (k : GaloisField p q) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_mul, ih]
    have hk : ((k : ℕ) : GaloisField p q)
        = algebraMap (ZMod p) (GaloisField p q) (k : ZMod p) := (map_natCast _ k).symm
    rw [hk, ← map_pow, ZMod.pow_card]

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
  classical
  -- Start from `a ∈ E^#`.
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_ne_one p q hcard
  have h1a : (1 : GaloisField p q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  -- The norm polynomial `P(X) = ∏_{i<q} ((1-a)^{p^i} X + 1) - 1`.
  set P : (GaloisField p q)[X] :=
    (∏ i ∈ Finset.range q, (C ((1 - a) ^ (p ^ i)) * X + C 1)) - C 1 with hP_def
  have hcne : ∀ i, ((1 - a) ^ (p ^ i) : GaloisField p q) ≠ 0 := fun i => pow_ne_zero _ h1a
  have hfac_ne : ∀ i ∈ Finset.range q,
      (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]) ≠ 0 := by
    intro i _ hz
    have hd1 := natDegree_linear (a := (1 - a) ^ (p ^ i)) (b := (1 : GaloisField p q)) (hcne i)
    rw [hz, natDegree_zero] at hd1
    exact one_ne_zero hd1.symm
  -- `P` has degree exactly `q`.
  have hdeg : P.natDegree = q := by
    rw [hP_def, natDegree_sub_C, natDegree_prod _ _ hfac_ne,
      Finset.sum_congr rfl (fun i _ => natDegree_linear (b := (1 : GaloisField p q)) (hcne i)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  -- Hence `P ≠ 0`.
  have hPne : P ≠ 0 := by
    intro hz
    have h0 := hdeg
    rw [hz, natDegree_zero] at h0
    have := hq.pos
    omega
  -- Every element of `𝔽_p` is a root of `P`.
  have heval : ∀ k : ℕ, P.eval ((k : ℕ) : GaloisField p q) = 0 := by
    intro k
    rw [hP_def, eval_sub, eval_C, eval_prod]
    have hprod : ∏ i ∈ Finset.range q,
        (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval ((k : ℕ) : GaloisField p q)
          = 1 := by
      have hstep : ∀ i ∈ Finset.range q,
          (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval
            ((k : ℕ) : GaloisField p q)
            = ((1 - a) * ((k : ℕ) : GaloisField p q) + 1) ^ (p ^ i) := by
        intro i _
        simp only [eval_add, eval_mul, eval_C, eval_X]
        rw [add_pow_char_pow, mul_pow, one_pow, natCast_pow_pPow]
      rw [Finset.prod_congr rfl hstep, ← normN]
      have hd : (1 - a) * ((k : ℕ) : GaloisField p q) + 1 = dSeq p q a k := by
        rw [dSeq]; ring
      rw [hd]
      exact normN_dSeq_eq_one p q hq.pos hEinv ha k
    rw [hprod]; ring
  -- `𝔽_p` is a `p`-element finset of roots, and `#roots ≤ deg P = q`.
  have hinj : Set.InjOn ((Nat.cast : ℕ → GaloisField p q))
      (↑(Finset.range p)) := by
    rw [Finset.coe_range]; exact CharP.natCast_injOn_Iio (GaloisField p q) p
  have hScard : ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSsub : (Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))
      ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hPne, heval k⟩
  calc p = ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card := hScard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hSsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := hdeg

/-! ## Lemma C.2 machinery (`q = 3` case): the cubic `f_c` -/

/-- **BG Lemma C.2** (`q = 3`), pigeonhole step (mmd L4948): for some `c ∈ 𝔽_p` the
cubic `f_c(x) = x(x-2)(x-c) + (x-1)` has no root in `𝔽_p`.

If every `f_c` had a root `d`, then `d ∉ {0, 2}` (as `f_c(0) = -1`, `f_c(2) = 1`),
and `c` is determined by `d` (`d(d-2)(d-c) = -(d-1)` with `d(d-2) ≠ 0`), so
`c ↦ d` is injective from `𝔽_p` into `𝔽_p ∖ {0, 2}` — impossible by cardinality. -/
lemma exists_rootFree_cubic [Fact p.Prime] (hpodd : Odd p) :
    ∃ c : ZMod p, ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0 := by
  have h3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hpodd with ⟨k, hk⟩; omega
  haveI : NeZero p := ⟨by omega⟩
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have h2cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h2cast
    have := Nat.le_of_dvd (by norm_num) h2cast
    omega
  by_contra hcon
  push_neg at hcon
  choose g hg using hcon
  -- `g c ≠ 0` and `g c ≠ 2`, since `f_c(0) = -1`, `f_c(2) = 1`.
  have hg0 : ∀ c, g c ≠ 0 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination -hgc)
  have hg2 : ∀ c, g c ≠ 2 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination hgc)
  -- `c ↦ g c` is injective (`c` is determined by the common root `d = g c`).
  have hinj : Function.Injective g := by
    intro c1 c2 h
    have e1 := hg c1
    have e2 := hg c2
    rw [h] at e1
    have hdne : g c2 * (g c2 - 2) ≠ 0 := mul_ne_zero (hg0 c2) (sub_ne_zero.mpr (hg2 c2))
    have hfactor : g c2 * (g c2 - 2) * (g c2 - c1) = g c2 * (g c2 - 2) * (g c2 - c2) := by
      linear_combination e1 - e2
    have hsub := mul_left_cancel₀ hdne hfactor
    linear_combination -hsub
  -- Cardinality contradiction: injective map into `𝔽_p ∖ {0,2}` (size `p-2`).
  have himg : Finset.univ.image g ⊆ (Finset.univ : Finset (ZMod p)) \ {0, 2} := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨c, rfl⟩ := hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hg0 c, hg2 c⟩
  have hc1 : (Finset.univ.image g).card = p := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hcard02 : ({0, 2} : Finset (ZMod p)).card = 2 := Finset.card_pair h02
  have hdisj : Disjoint (Finset.univ.image g) ({0, 2} : Finset (ZMod p)) := by
    rw [Finset.disjoint_left]
    intro a ha ha2
    have := himg ha
    rw [Finset.mem_sdiff] at this
    exact this.2 ha2
  have key : (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card ≤ p :=
    calc (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card
        = (Finset.univ.image g ∪ {0, 2}).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  rw [hc1, hcard02] at key
  omega

/-- The cubic `f_c(X) = X(X-2)(X-c) + (X-1)` of BG Lemma C.2 (`q = 3`). -/
noncomputable def fCubic (c : ZMod p) : (ZMod p)[X] :=
  X * (X - C 2) * (X - C c) + (X - C 1)

lemma fCubic_eval (c x : ZMod p) :
    (fCubic p c).eval x = x * (x - 2) * (x - c) + (x - 1) := by
  simp [fCubic]

lemma fCubic_natDegree [Fact p.Prime] (c : ZMod p) : (fCubic p c).natDegree = 3 := by
  unfold fCubic
  compute_degree!

/-- A root-free `f_c` is irreducible over `𝔽_p` (a cubic with no root). -/
lemma fCubic_irreducible [Fact p.Prime] (c : ZMod p)
    (h : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    Irreducible (fCubic p c) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, fCubic_natDegree]; omega
  · intro x hx
    rw [IsRoot, fCubic_eval] at hx
    exact h x hx

/-- An irreducible cubic over `𝔽_p` has a root in `𝔽_{p^3} = GaloisField p 3`
(its root field has cardinality `p^3`, hence is isomorphic to `GaloisField p 3`). -/
lemma exists_root_fCubic [Fact p.Prime] (c : ZMod p) (hirr : Irreducible (fCubic p c)) :
    ∃ a : GaloisField p 3, (Polynomial.aeval a) (fCubic p c) = 0 := by
  haveI : Fact (Irreducible (fCubic p c)) := ⟨hirr⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hne : fCubic p c ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional (ZMod p) (AdjoinRoot (fCubic p c)) :=
    FiniteDimensional.of_fintype_basis (AdjoinRoot.powerBasis hne).basis
  haveI : Finite (AdjoinRoot (fCubic p c)) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot (fCubic p c)) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (AdjoinRoot (fCubic p c)) = 3 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, fCubic_natDegree]
  have hcard : Nat.card (AdjoinRoot (fCubic p c)) = p ^ 3 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), hfr, ZMod.card]
  let e := GaloisField.algEquivGaloisField p 3 hcard
  refine ⟨e (AdjoinRoot.root (fCubic p c)), ?_⟩
  rw [Polynomial.aeval_algHom_apply]
  have hr : (Polynomial.aeval (AdjoinRoot.root (fCubic p c))) (fCubic p c) = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root (fCubic p c)
  rw [hr, map_zero]

/-- Frobenius propagation: for `f` over `𝔽_p` and `a ∈ 𝔽_{p^q}`,
`f(a)^p = f(a^p)` (the `p`-power map fixes the `𝔽_p`-coefficients of `f`). -/
lemma aeval_pow_p [Fact p.Prime] (a : GaloisField p q) (f : (ZMod p)[X]) :
    (Polynomial.aeval a f) ^ p = Polynomial.aeval (a ^ p) f := by
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  have key : (frobenius (GaloisField p q) p).comp (Polynomial.aeval (R := ZMod p) a).toRingHom
      = (Polynomial.aeval (R := ZMod p) (a ^ p)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_C, frobenius_def]
      rw [← map_pow, ZMod.pow_card]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_X, frobenius_def]
  have h := RingHom.congr_fun key f
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobenius_def]
    using h

/-- A root `a ∈ 𝔽_{p^3}` of a root-free `f_c` does not lie in the prime field `𝔽_p`
(else `f_c` would have a root in `𝔽_p`). -/
lemma root_not_mem_range [Fact p.Prime] {c : ZMod p} {a : GaloisField p 3}
    (hroot : (Polynomial.aeval a) (fCubic p c) = 0)
    (hrf : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    a ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  rintro ⟨b, rfl⟩
  refine hrf b ?_
  rw [← fCubic_eval, ← Polynomial.coe_aeval_eq_eval]
  exact (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
    (algebraMap (ZMod p) (GaloisField p 3)).injective).mp hroot

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
