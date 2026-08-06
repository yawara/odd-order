/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.RepresentationTheory.CharacterEigenvalues
import OddOrder.GroupTheory.RepresentationTheory.Modular.CyclotomicModEq

/-!
# Gorenstein Lemma 7.5: integer-valued elements of `ch_R(G)` are constant mod `p` on `p`-classes

Let `ω` be a primitive `m`-th root of unity in `K` with `g ^ m = 1` for every `g ∈ G`, so that all
character values lie in `R = ℤ[ω]`.  For an element `χ` of `ch_R(G) = ℤ[ω] · ch(G)` and any
`y ∈ G` with `p'`-part `u`,

`χ(y) ≡ χ(u)  (mod p)`

once both values are rational integers.  This is what Lemma 7.8 needs in order to normalise the
functions produced by Lemma 7.6 to be `≡ 1 (mod p)` on a whole `p`-class.

The proof is the classical Frobenius argument, arranged so that the coefficients cancel:

* for a genuine character, `χ(g)^{p^s} ≡ χ(g^{p^s})` — read
  `character_pow_eq_sum_finrank_smul` at `k = 1` and at `k = p^s` and connect them with the
  freshman's dream and Fermat (the multiplicities are the *same* on both sides, which is exactly
  why that lemma was stated with `k` free);
* the property `χ(y)^{p^s} ≡ χ(u)^{p^s}` is stable under `0`, `+`, `-` (the last again by the
  freshman's dream applied to `x + (-x) = 0`) and under multiplication by a power of `ω`, so two
  `AddSubgroup.closure_induction`s carry it from genuine characters to all of `ch_R(G)`;
* `y^{p^s} = u^{p^s}` for `p^s` the order of the `p`-part of `y`, so the two sides meet;
* finally `ℤ ∩ pR = pℤ` and Fermat in `ℤ` remove the exponent.

## Main results

* `OddOrder.RepresentationTheory.character_pow_prime_pow` — the genuine-character core
* `OddOrder.RepresentationTheory.mem_adjoin_of_mem_adjoinSpan_virtualCharacters` — values lie in
  `ℤ[ω]`
* `OddOrder.RepresentationTheory.pow_prime_pow_congr_of_mem_adjoinSpan` — the congruence for
  `ch_R(G)`
* `OddOrder.RepresentationTheory.intModEq_of_mem_adjoinSpan` — **Lemma 7.5**

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.5 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory Polynomial

variable {K G : Type*} [Field K] [CharZero K] [Group G] {ω : K} {p m : ℕ}

/-! ### The genuine-character core -/

/-- **`χ(g)^{p^s} ≡ χ(g^{p^s})` modulo `p·ℤ[ω]`, for a genuine character.**  Both sides are the
*same* combination `∑_ζ d_ζ ζ^{(-)}` of roots of unity; the Frobenius of `ℤ[ω]/p` matches them. -/
theorem character_pow_prime_pow (hω : IsIntegral ℤ ω) (hp : p.Prime) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G W)
    (hm : 0 < m) (hωm : IsPrimitiveRoot ω m) {g : G} (hg : g ^ m = 1) (s : ℕ) :
    CyclotomicModEq ω p (ρ.character g ^ p ^ s) (ρ.character (g ^ p ^ s)) := by
  classical
  set d : K → ℕ := fun ζ => Module.finrank K (Module.End.eigenspace (ρ g) ζ) with hd
  have h1 : ρ.character g = ∑ ζ ∈ nthRootsFinset m (1 : K), d ζ • ζ := by
    have := character_pow_eq_sum_finrank_smul ρ hm hωm hg 1
    simpa using this
  have hs : ρ.character (g ^ p ^ s) = ∑ ζ ∈ nthRootsFinset m (1 : K), d ζ • ζ ^ p ^ s :=
    character_pow_eq_sum_finrank_smul ρ hm hωm hg (p ^ s)
  have hmemR : ∀ ζ ∈ nthRootsFinset m (1 : K),
      d ζ • ζ ∈ Algebra.adjoin ℤ ({ω} : Set K) := by
    intro ζ hζ
    rw [nsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
      (mem_adjoin_of_mem_nthRootsFinset hm hωm hζ)
  have hterm : ∀ ζ ∈ nthRootsFinset m (1 : K),
      CyclotomicModEq ω p ((d ζ • ζ) ^ p ^ s) (d ζ • ζ ^ p ^ s) := by
    intro ζ hζ
    have hζp : ζ ^ p ^ s ∈ Algebra.adjoin ℤ ({ω} : Set K) :=
      Subalgebra.pow_mem _ (mem_adjoin_of_mem_nthRootsFinset hm hωm hζ) _
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_pow, mul_comm ((d ζ : K) ^ p ^ s),
      mul_comm ((d ζ : K))]
    exact CyclotomicModEq.mul_left hζp (CyclotomicModEq.natCast_pow_prime_pow hω hp _ s)
  rw [h1, hs]
  exact (CyclotomicModEq.sum_pow_prime_pow hω hp _ hmemR s).trans
    (CyclotomicModEq.sum _ hterm)

/-! ### Values lie in `ℤ[ω]` -/

variable (hm : 0 < m) (hωm : IsPrimitiveRoot ω m) (hgm : ∀ g : G, g ^ m = 1)

omit [CharZero K] in
include hm hωm hgm in
/-- Values of virtual characters are cyclotomic integers. -/
theorem mem_adjoin_of_mem_virtualCharacters {θ : G → K} (hθ : θ ∈ virtualCharacters K G) (g : G) :
    θ g ∈ Algebra.adjoin ℤ ({ω} : Set K) := by
  induction hθ using AddSubgroup.closure_induction with
  | mem θ hθ =>
      obtain ⟨n, ρ, rfl⟩ := hθ
      exact character_mem_adjoin ρ hm hωm (hgm g)
  | zero => exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
  | neg a _ ha => exact Subalgebra.neg_mem _ ha

omit [CharZero K] in
include hm hωm hgm in
/-- Values of elements of `ch_R(G) = ℤ[ω] · ch(G)` are cyclotomic integers. -/
theorem mem_adjoin_of_mem_adjoinSpan_virtualCharacters {χ : G → K}
    (hχ : χ ∈ adjoinSpan ω (virtualCharacters K G)) (g : G) :
    χ g ∈ Algebra.adjoin ℤ ({ω} : Set K) := by
  induction hχ using AddSubgroup.closure_induction with
  | mem χ hχ =>
      obtain ⟨j, w, hw, rfl⟩ := hχ
      rw [Pi.smul_apply, smul_eq_mul]
      exact Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ω) j)
        (mem_adjoin_of_mem_virtualCharacters hm hωm hgm hw g)
  | zero => exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
  | neg a _ ha => exact Subalgebra.neg_mem _ ha

/-! ### Lifting the congruence -/

include hm hωm hgm in
/-- The congruence `χ(y)^{p^s} ≡ χ(u)^{p^s}` for virtual characters. -/
theorem pow_prime_pow_congr_of_mem_virtualCharacters (hω : IsIntegral ℤ ω) (hp : p.Prime)
    {y u : G} {s : ℕ} (hyu : y ^ p ^ s = u ^ p ^ s) {θ : G → K}
    (hθ : θ ∈ virtualCharacters K G) :
    CyclotomicModEq ω p (θ y ^ p ^ s) (θ u ^ p ^ s) := by
  induction hθ using AddSubgroup.closure_induction with
  | mem θ hθ =>
      obtain ⟨n, ρ, rfl⟩ := hθ
      refine (character_pow_prime_pow hω hp ρ hm hωm (hgm y) s).trans ?_
      rw [hyu]
      exact (character_pow_prime_pow hω hp ρ hm hωm (hgm u) s).symm
  | zero => exact CyclotomicModEq.refl _
  | add a b hma hmb ha hb =>
      have hay := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hma y
      have hau := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hma u
      have hby := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hmb y
      have hbu := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hmb u
      refine (CyclotomicModEq.add_pow_prime_pow hω hp hay hby s).trans
        ((ha.add hb).trans (CyclotomicModEq.add_pow_prime_pow hω hp hau hbu s).symm)
  | neg a hma ha =>
      have hay := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hma y
      have hau := mem_adjoin_of_mem_virtualCharacters hm hωm hgm hma u
      refine (CyclotomicModEq.neg_pow_prime_pow hω hp hay s).trans
        (ha.neg.trans (CyclotomicModEq.neg_pow_prime_pow hω hp hau s).symm)

include hm hωm hgm in
/-- The congruence `χ(y)^{p^s} ≡ χ(u)^{p^s}` for elements of `ch_R(G)`. -/
theorem pow_prime_pow_congr_of_mem_adjoinSpan (hω : IsIntegral ℤ ω) (hp : p.Prime)
    {y u : G} {s : ℕ} (hyu : y ^ p ^ s = u ^ p ^ s) {χ : G → K}
    (hχ : χ ∈ adjoinSpan ω (virtualCharacters K G)) :
    CyclotomicModEq ω p (χ y ^ p ^ s) (χ u ^ p ^ s) := by
  induction hχ using AddSubgroup.closure_induction with
  | mem χ hχ =>
      obtain ⟨j, w, hw, rfl⟩ := hχ
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      exact CyclotomicModEq.mul_left
        (Subalgebra.pow_mem _ (Subalgebra.pow_mem _
          (Algebra.self_mem_adjoin_singleton ℤ ω) j) _)
        (pow_prime_pow_congr_of_mem_virtualCharacters hm hωm hgm hω hp hyu hw)
  | zero => exact CyclotomicModEq.refl _
  | add a b hma hmb ha hb =>
      have hay := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hma y
      have hau := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hma u
      have hby := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hmb y
      have hbu := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hmb u
      refine (CyclotomicModEq.add_pow_prime_pow hω hp hay hby s).trans
        ((ha.add hb).trans (CyclotomicModEq.add_pow_prime_pow hω hp hau hbu s).symm)
  | neg a hma ha =>
      have hay := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hma y
      have hau := mem_adjoin_of_mem_adjoinSpan_virtualCharacters hm hωm hgm hma u
      refine (CyclotomicModEq.neg_pow_prime_pow hω hp hay s).trans
        (ha.neg.trans (CyclotomicModEq.neg_pow_prime_pow hω hp hau s).symm)

/-! ### Lemma 7.5 -/

omit [CharZero K] in
/-- An element and its `p'`-part have the same `p^s`-th power, for `p^s` the order of the
`p`-part. -/
theorem exists_pow_prime_pow_eq_pRegularPart (hp : p.Prime) [Finite G] (y : G) :
    ∃ s : ℕ, y ^ p ^ s = pRegularPart p y ^ p ^ s := by
  obtain ⟨s, hs⟩ := isPElement_pPart hp y
  refine ⟨s, ?_⟩
  have hcomm := commute_pRegularPart_pPart (p := p) y
  have hy : pRegularPart p y * pPart p y = y :=
    pRegularPart_mul_pPart hp (isOfFinOrder_of_finite y)
  calc y ^ p ^ s = (pRegularPart p y * pPart p y) ^ p ^ s := by rw [hy]
    _ = pRegularPart p y ^ p ^ s * pPart p y ^ p ^ s := hcomm.mul_pow _
    _ = pRegularPart p y ^ p ^ s := by rw [← hs, pow_orderOf_eq_one, mul_one]

include hm hωm hgm in
/-- **Gorenstein Lemma 7.5.**  An integer-valued element of `ch_R(G)` takes congruent values
modulo `p` at an element and at its `p'`-part — hence is constant modulo `p` on every
`p`-class. -/
theorem intModEq_of_mem_adjoinSpan [Finite G] (hω : IsIntegral ℤ ω) (hp : p.Prime)
    {χ : G → K} (hχ : χ ∈ adjoinSpan ω (virtualCharacters K G)) (y : G)
    {a b : ℤ} (ha : χ y = (a : K)) (hb : χ (pRegularPart p y) = (b : K)) :
    a ≡ b [ZMOD (p : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := exists_pow_prime_pow_eq_pRegularPart hp y
  have hcongr := pow_prime_pow_congr_of_mem_adjoinSpan hm hωm hgm hω hp hs hχ
  rw [ha, hb] at hcongr
  have hint : (a ^ p ^ s) ≡ (b ^ p ^ s) [ZMOD (p : ℤ)] := by
    refine CyclotomicModEq.intCast hω ?_
    push_cast
    exact hcongr
  have hZ : ((a : ZMod p)) = ((b : ZMod p)) := by
    have := (ZMod.intCast_eq_intCast_iff' _ _ _).mpr hint
    push_cast at this
    rwa [ZMod.pow_card_pow, ZMod.pow_card_pow] at this
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp hZ

include hm hωm hgm in
/-- **At a `p`-element the value is congruent to the degree**: the `p'`-part of a `p`-element is
trivial, so Lemma 7.5 compares `χ(y)` with `χ(1)`. -/
theorem intModEq_one_of_isPElement [Finite G] (hω : IsIntegral ℤ ω) (hp : p.Prime)
    {χ : G → K} (hχ : χ ∈ adjoinSpan ω (virtualCharacters K G)) {y : G} (hy : IsPElement p y)
    {a b : ℤ} (ha : χ y = (a : K)) (hb : χ 1 = (b : K)) : a ≡ b [ZMOD (p : ℤ)] :=
  intModEq_of_mem_adjoinSpan hm hωm hgm hω hp hχ y ha
    (by rw [pRegularPart_eq_one_of_isPElement hp hy]; exact hb)

include hm hωm hgm in
/-- **An integer-valued element of `ch_R(G)` is constant modulo `p` on the `p`-elements.**

This is what Navarro p. 141 reads off the character table of `Q₈` — "`τ(t) ≡ τ(y) mod 2`" for the
involution `t` and an element `y` of order `4` — but it needs no character table: both values are
congruent to the degree by Gorenstein Lemma 7.5. -/
theorem intModEq_of_isPElement_of_isPElement [Finite G] (hω : IsIntegral ℤ ω) (hp : p.Prime)
    {χ : G → K} (hχ : χ ∈ adjoinSpan ω (virtualCharacters K G))
    {u v : G} (hu : IsPElement p u) (hv : IsPElement p v)
    {a b c : ℤ} (ha : χ u = (a : K)) (hb : χ v = (b : K)) (hc : χ 1 = (c : K)) :
    a ≡ b [ZMOD (p : ℤ)] :=
  (intModEq_one_of_isPElement hm hωm hgm hω hp hχ hu ha hc).trans
    (intModEq_one_of_isPElement hm hωm hgm hω hp hχ hv hb hc).symm

end OddOrder.RepresentationTheory
