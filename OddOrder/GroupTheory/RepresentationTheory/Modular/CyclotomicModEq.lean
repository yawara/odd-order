/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CyclotomicIntegerModP

/-!
# Congruences modulo `p · ℤ[ω]`

Gorenstein Lemma 7.5 (issue 9508, 段 D) is a congruence between character values, which live in
`ℤ[ω] ⊆ K` but are most conveniently manipulated as elements of `K`.  This file introduces

`CyclotomicModEq ω p x y  ↔  x - y ∈ p · ℤ[ω]`

as a relation on `K`, together with the arithmetic the argument needs:

* it is an equivalence relation compatible with `+`, `-`, and with multiplication by an element of
  `ℤ[ω]`;
* the **freshman's dream** `(x + y)^{p^s} ≡ x^{p^s} + y^{p^s}` for `x, y ∈ ℤ[ω]`, and its sum form;
* **Fermat** `n^{p^s} ≡ n` for a natural number `n`;
* the descent `x ≡ y` with `x, y ∈ ℤ` gives `x ≡ y (mod p)` in `ℤ`.

The two "characteristic `p`" facts are proved by passing to the residue ring
`ℤ[ω] / p`, which has characteristic `p` (`charP_quotient_adjoinPrimeIdeal`), and reading the
Frobenius there.  Everything else is direct.

## Main definitions

* `OddOrder.CyclotomicModEq`

## Main results

* `OddOrder.cyclotomicModEq_iff_quotient` — the bridge to `ℤ[ω] / p`
* `OddOrder.CyclotomicModEq.add_pow_prime_pow` — the freshman's dream
* `OddOrder.CyclotomicModEq.sum_pow_prime_pow` — its sum form
* `OddOrder.CyclotomicModEq.natCast_pow_prime_pow` — Fermat
* `OddOrder.CyclotomicModEq.intCast` — the descent to `Int.ModEq`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.5 (`references/gorenstein/pages/`).
-/

namespace OddOrder

variable {K : Type*} [Field K] {ω : K} {p : ℕ}

/-- **`x ≡ y` modulo `p · ℤ[ω]`.** -/
def CyclotomicModEq (ω : K) (p : ℕ) (x y : K) : Prop :=
  ∃ r ∈ Algebra.adjoin ℤ ({ω} : Set K), x - y = (p : K) * r

namespace CyclotomicModEq

variable {x y z x' y' : K}

@[refl]
theorem refl (x : K) : CyclotomicModEq ω p x x := ⟨0, Subalgebra.zero_mem _, by simp⟩

theorem symm (h : CyclotomicModEq ω p x y) : CyclotomicModEq ω p y x := by
  obtain ⟨r, hr, hxy⟩ := h
  exact ⟨-r, Subalgebra.neg_mem _ hr, by rw [mul_neg, ← hxy]; ring⟩

theorem trans (h₁ : CyclotomicModEq ω p x y) (h₂ : CyclotomicModEq ω p y z) :
    CyclotomicModEq ω p x z := by
  obtain ⟨r₁, hr₁, h₁⟩ := h₁
  obtain ⟨r₂, hr₂, h₂⟩ := h₂
  exact ⟨r₁ + r₂, Subalgebra.add_mem _ hr₁ hr₂, by rw [mul_add, ← h₁, ← h₂]; ring⟩

theorem add (h : CyclotomicModEq ω p x y) (h' : CyclotomicModEq ω p x' y') :
    CyclotomicModEq ω p (x + x') (y + y') := by
  obtain ⟨r, hr, h⟩ := h
  obtain ⟨r', hr', h'⟩ := h'
  exact ⟨r + r', Subalgebra.add_mem _ hr hr', by rw [mul_add, ← h, ← h']; ring⟩

theorem mul_left {c : K} (hc : c ∈ Algebra.adjoin ℤ ({ω} : Set K))
    (h : CyclotomicModEq ω p x y) : CyclotomicModEq ω p (c * x) (c * y) := by
  obtain ⟨r, hr, h⟩ := h
  exact ⟨c * r, Subalgebra.mul_mem _ hc hr, by rw [← mul_sub, h]; ring⟩

theorem sum {ι : Type*} (s : Finset ι) {f g : ι → K}
    (h : ∀ i ∈ s, CyclotomicModEq ω p (f i) (g i)) :
    CyclotomicModEq ω p (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using CyclotomicModEq.refl (ω := ω) (p := p) 0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CyclotomicModEq

/-! ### The bridge to the residue ring -/

/-- **`x ≡ y` modulo `p · ℤ[ω]` is equality in `ℤ[ω] / p`.** -/
theorem cyclotomicModEq_iff_quotient {x y : K} (hx : x ∈ Algebra.adjoin ℤ ({ω} : Set K))
    (hy : y ∈ Algebra.adjoin ℤ ({ω} : Set K)) :
    CyclotomicModEq ω p x y ↔
      (Ideal.Quotient.mk (adjoinPrimeIdeal ω p)) ⟨x, hx⟩
        = (Ideal.Quotient.mk (adjoinPrimeIdeal ω p)) ⟨y, hy⟩ := by
  rw [Ideal.Quotient.eq, adjoinPrimeIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr, hxy⟩
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    have : ((⟨r, hr⟩ * (p : ↥(Algebra.adjoin ℤ ({ω} : Set K))) :
        ↥(Algebra.adjoin ℤ ({ω} : Set K))) : K) = r * (p : K) := by push_cast; rfl
    rw [this, mul_comm, ← hxy]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨(a : K), a.2, ?_⟩
    have h2 : (a : K) * (p : K) = x - y := by
      have := congrArg (Subalgebra.val (Algebra.adjoin ℤ ({ω} : Set K))) ha
      simpa using this
    rw [← h2]
    ring

/-! ### The characteristic `p` facts -/

namespace CyclotomicModEq

/-- **The freshman's dream** modulo `p · ℤ[ω]`. -/
theorem add_pow_prime_pow [CharZero K] (hω : IsIntegral ℤ ω) (hp : p.Prime) {x y : K}
    (hx : x ∈ Algebra.adjoin ℤ ({ω} : Set K)) (hy : y ∈ Algebra.adjoin ℤ ({ω} : Set K)) (s : ℕ) :
    CyclotomicModEq ω p ((x + y) ^ p ^ s) (x ^ p ^ s + y ^ p ^ s) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (↥(Algebra.adjoin ℤ ({ω} : Set K)) ⧸ adjoinPrimeIdeal ω p) p :=
    charP_quotient_adjoinPrimeIdeal hω
  haveI : ExpChar (↥(Algebra.adjoin ℤ ({ω} : Set K)) ⧸ adjoinPrimeIdeal ω p) p :=
    ExpChar.prime hp
  have hxy : (x + y) ^ p ^ s ∈ Algebra.adjoin ℤ ({ω} : Set K) :=
    Subalgebra.pow_mem _ (Subalgebra.add_mem _ hx hy) _
  have hsum : x ^ p ^ s + y ^ p ^ s ∈ Algebra.adjoin ℤ ({ω} : Set K) :=
    Subalgebra.add_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)
  rw [cyclotomicModEq_iff_quotient hxy hsum]
  have hlift : (⟨(x + y) ^ p ^ s, hxy⟩ : ↥(Algebra.adjoin ℤ ({ω} : Set K)))
      = (⟨x, hx⟩ + ⟨y, hy⟩) ^ p ^ s := Subtype.ext (by push_cast; rfl)
  have hlift' : (⟨x ^ p ^ s + y ^ p ^ s, hsum⟩ : ↥(Algebra.adjoin ℤ ({ω} : Set K)))
      = (⟨x, hx⟩ : ↥(Algebra.adjoin ℤ ({ω} : Set K))) ^ p ^ s + ⟨y, hy⟩ ^ p ^ s :=
    Subtype.ext (by push_cast; rfl)
  rw [hlift, hlift', map_pow, map_add, map_add, map_pow, map_pow, add_pow_char_pow]

/-- **Fermat** modulo `p · ℤ[ω]`. -/
theorem natCast_pow_prime_pow [CharZero K] (hω : IsIntegral ℤ ω) (hp : p.Prime) (n s : ℕ) :
    CyclotomicModEq ω p ((n : K) ^ p ^ s) (n : K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (↥(Algebra.adjoin ℤ ({ω} : Set K)) ⧸ adjoinPrimeIdeal ω p) p :=
    charP_quotient_adjoinPrimeIdeal hω
  have hn : (n : K) ∈ Algebra.adjoin ℤ ({ω} : Set K) := Subalgebra.natCast_mem _ _
  have hnp : (n : K) ^ p ^ s ∈ Algebra.adjoin ℤ ({ω} : Set K) := Subalgebra.pow_mem _ hn _
  rw [cyclotomicModEq_iff_quotient hnp hn]
  have hlift : (⟨(n : K) ^ p ^ s, hnp⟩ : ↥(Algebra.adjoin ℤ ({ω} : Set K)))
      = (n : ↥(Algebra.adjoin ℤ ({ω} : Set K))) ^ p ^ s := Subtype.ext (by push_cast; rfl)
  have hlift' : (⟨(n : K), hn⟩ : ↥(Algebra.adjoin ℤ ({ω} : Set K)))
      = (n : ↥(Algebra.adjoin ℤ ({ω} : Set K))) := Subtype.ext (by push_cast; rfl)
  rw [hlift, hlift', map_pow, map_natCast, ← map_natCast
    (ZMod.castHom (dvd_refl p) (↥(Algebra.adjoin ℤ ({ω} : Set K)) ⧸ adjoinPrimeIdeal ω p)) n,
    ← map_pow, ZMod.pow_card_pow]

/-- **`(-x)^{p^s} ≡ -(x^{p^s})`**, uniformly in `p` (including `p = 2`): apply the freshman's
dream to `x + (-x) = 0`. -/
theorem neg_pow_prime_pow [CharZero K] (hω : IsIntegral ℤ ω) (hp : p.Prime) {x : K}
    (hx : x ∈ Algebra.adjoin ℤ ({ω} : Set K)) (s : ℕ) :
    CyclotomicModEq ω p ((-x) ^ p ^ s) (-(x ^ p ^ s)) := by
  have hnx : -x ∈ Algebra.adjoin ℤ ({ω} : Set K) := Subalgebra.neg_mem _ hx
  have hzero : CyclotomicModEq ω p (0 : K) (x ^ p ^ s + (-x) ^ p ^ s) := by
    have h := add_pow_prime_pow hω hp hx hnx s
    rw [add_neg_cancel, zero_pow (pow_ne_zero s hp.ne_zero)] at h
    exact h
  obtain ⟨r, hr, hzr⟩ := hzero
  exact ⟨-r, Subalgebra.neg_mem _ hr, by rw [mul_neg, ← hzr]; ring⟩

/-- The sum form of the freshman's dream. -/
theorem sum_pow_prime_pow [CharZero K] (hω : IsIntegral ℤ ω) (hp : p.Prime) {ι : Type*}
    (t : Finset ι)
    {f : ι → K} (hf : ∀ i ∈ t, f i ∈ Algebra.adjoin ℤ ({ω} : Set K)) (s : ℕ) :
    CyclotomicModEq ω p ((∑ i ∈ t, f i) ^ p ^ s) (∑ i ∈ t, f i ^ p ^ s) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using natCast_pow_prime_pow (ω := ω) hω hp 0 s
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa : f a ∈ Algebra.adjoin ℤ ({ω} : Set K) := hf a (Finset.mem_insert_self a t)
      have hft : ∀ i ∈ t, f i ∈ Algebra.adjoin ℤ ({ω} : Set K) := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hsum : (∑ i ∈ t, f i) ∈ Algebra.adjoin ℤ ({ω} : Set K) :=
        Subalgebra.sum_mem _ fun i hi => hft i hi
      exact (add_pow_prime_pow hω hp hfa hsum s).trans
        ((CyclotomicModEq.refl _).add (ih hft))

/-! ### Descending to `ℤ` -/

/-- **A congruence between rational integers is a congruence in `ℤ`.** -/
theorem intCast [CharZero K] (hω : IsIntegral ℤ ω) {a b : ℤ}
    (h : CyclotomicModEq ω p (a : K) (b : K)) : a ≡ b [ZMOD (p : ℤ)] := by
  obtain ⟨r, hr, hab⟩ := h
  have hmem : ((a - b : ℤ) : ↥(Algebra.adjoin ℤ ({ω} : Set K))) ∈ adjoinPrimeIdeal ω p := by
    rw [adjoinPrimeIdeal, Ideal.mem_span_singleton']
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    have hcoe : ((⟨r, hr⟩ * (p : ↥(Algebra.adjoin ℤ ({ω} : Set K))) :
        ↥(Algebra.adjoin ℤ ({ω} : Set K))) : K) = r * (p : K) := by push_cast; rfl
    rw [hcoe]
    push_cast
    rw [mul_comm, ← hab]
  have hdvd := intCast_dvd_of_mem_adjoinPrimeIdeal (ω := ω) (p := p) hω hmem
  refine Int.modEq_iff_dvd.mpr ?_
  simpa [neg_sub] using dvd_neg.mpr hdvd

end CyclotomicModEq

end OddOrder
