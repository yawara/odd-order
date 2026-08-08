/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC2

/-!
# BG Appendix C, Remark (IV): the Glauberman–Norton sharpening `p ≤ 3`

Bender--Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix C, p. 148,
Preliminary Remark (IV):

> In [12], S. P. Norton and the second author have extended Theorem C to show that `p ≤ 3`.

BG carries no proof; the content is
G. Glauberman and S. P. Norton, *On a combinatorial problem associated with the odd order
theorem*, Proc. Amer. Math. Soc. **119** (1993), 1089–1094
(`references/glauberman-norton/`, issue 0179).  BG restates the conclusion combinatorially on
p. 149:

> The work mentioned in (IV) shows that whenever `p` and `q` are primes that satisfy (A)
> and `E = E⁻¹`, then `p ≤ 3`.

This file carries the elementary front of that paper: its **Lemma 4** (`p ≤ 3` forces
`E = E⁻¹`) and its **Lemma 5** (`|E| ≥ 2` except in one degenerate case).  The combinatorial
core (Proposition 6) and the main equivalence (Proposition 7) build on these.

## 🚨 The paper's Proposition 7 is false as literally stated

Proposition 7 of the paper asserts, for arbitrary primes `p` and `q`, that `E = E⁻¹ ↔ p ≤ 3`.
The forward direction fails whenever `p` is odd and `q = 2`: the paper's own Lemma 5(a) says
`E = {1}` there, so `E = E⁻¹` holds trivially while `p` may be arbitrarily large.  Brute-force
computation confirms `|E| = 1` and `E = E⁻¹` for `(p, q) = (5, 2), (7, 2), (11, 2)`.  The slip is
in the first line of the proof (p. 1092), which cites Lemma 5 for `|E| ≥ 2` without excluding
case (a).

BG's restatement is *not* affected, because it carries condition (A): under `q ∤ p - 1`, `q = 2`
forces `p = 2`, since every odd prime `p` has `2 ∣ p - 1`.

Accordingly this development proves the sharpening under the exact hypothesis that Lemma 5
needs — `q ≠ 2 ∨ p = 2` — and derives BG's condition-(A) form as a corollary.

## Main results

- `normSetE_eq_setOf_ne_zero_of_two` — Lemma 4(a): in characteristic two `E = 𝔽_{2^q} ∖ {0}`.
- `normSetE_eq_inv_of_p_eq_two` — Lemma 4(a), inverse-closure half.
- `normSetE_eq_inv_of_le_three` — Lemma 4: `p ≤ 3` gives `E = E⁻¹`
  (the `p = 3` half is `normSetE_eq_inv_of_p_eq_three`, already available as BG's Lemma C.3 note).
- `two_le_normSetE_ncard` — Lemma 5(b): `|E| ≥ 2` when `q ≠ 2 ∨ p = 2`.
-/

namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

variable (p q : ℕ)

/-- The only nonzero element of `ZMod 2` is `1`. -/
theorem zmod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  revert hx; revert x; decide

/-! ## Lemma 4(a): characteristic two -/

section CharTwo

variable [Fact (Nat.Prime 2)]

/-- In characteristic two the norm of every nonzero element is `1`: the norm lands in the prime
field `𝔽_2`, where the only nonzero element is `1`. -/
theorem normN_eq_one_of_two (hq : q ≠ 0) {a : GaloisField 2 q} (ha : a ≠ 0) :
    normN 2 q a = 1 := by
  have hbridge := normN_eq_algebraMap_norm 2 q hq a
  have hne : algebraMap (ZMod 2) (GaloisField 2 q) (Algebra.norm (ZMod 2) a) ≠ 0 := by
    rw [← hbridge]; exact normN_ne_zero 2 q ha
  have hnorm_ne : Algebra.norm (ZMod 2) a ≠ 0 := by
    intro h; rw [h, map_zero] at hne; exact hne rfl
  have hnorm : Algebra.norm (ZMod 2) a = 1 := zmod_two_eq_one_of_ne_zero hnorm_ne
  rw [hbridge, hnorm, map_one]

/-- **Glauberman–Norton, Lemma 4(a)** (p. 1090): in characteristic two the norm set is the whole
punctured field, `E = 𝔽_{2^q} ∖ {0}`.

Both defining conditions collapse: every nonzero element has norm `1`
(`normN_eq_one_of_two`), and `2 - a = a` because `2 = 0`. -/
theorem normSetE_eq_setOf_ne_zero_of_two (hq : q ≠ 0) :
    normSetE 2 q = {a : GaloisField 2 q | a ≠ 0} := by
  haveI : CharP (GaloisField 2 q) 2 := by
    rw [← Algebra.charP_iff (ZMod 2) (GaloisField 2 q) 2]; exact ZMod.charP 2
  have htwo : (2 : GaloisField 2 q) = 0 := by
    change ((2 : ℕ) : GaloisField 2 q) = 0
    rw [CharP.cast_eq_zero_iff (GaloisField 2 q) 2]
  ext a
  constructor
  · intro ha; exact ne_zero_of_mem_normSetE 2 q (Nat.pos_of_ne_zero hq) ha
  · intro (ha : a ≠ 0)
    have hsub : (2 : GaloisField 2 q) - a = a := by
      rw [htwo, zero_sub]
      exact neg_eq_of_add_eq_zero_left (by rw [← two_mul, htwo, zero_mul])
    exact ⟨normN_eq_one_of_two q hq ha, by rw [hsub]; exact normN_eq_one_of_two q hq ha⟩

/-- **Glauberman–Norton, Lemma 4(a)**, inverse-closure half: `E = E⁻¹` in characteristic two. -/
theorem normSetE_eq_inv_of_p_eq_two (hq : q ≠ 0) :
    normSetE 2 q = (normSetE 2 q)⁻¹ := by
  rw [normSetE_eq_setOf_ne_zero_of_two q hq]
  ext a
  simp only [Set.mem_inv, Set.mem_setOf_eq, ne_eq, inv_eq_zero]

end CharTwo

/-! ## Lemma 4: `p ≤ 3` gives `E = E⁻¹` -/

/-- **Glauberman–Norton, Lemma 4** (p. 1090): if `p ≤ 3` then the norm set is closed under
inversion.

For `p = 2` this is `normSetE_eq_setOf_ne_zero_of_two` (the set is all of `𝔽 ∖ {0}`, visibly
inverse-closed); for `p = 3` it is BG's own note to Lemma C.3
(`normSetE_eq_inv_of_p_eq_three`), which turns on `2 - c⁻¹ = c⁻¹(2c - 1) = c⁻¹(2 - c)` in
characteristic three. -/
theorem normSetE_eq_inv_of_le_three [Fact p.Prime] (hq : 0 < q) (hp : p ≤ 3) :
    normSetE p q = (normSetE p q)⁻¹ := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  interval_cases p
  · exact normSetE_eq_inv_of_p_eq_two q hq.ne'
  · exact normSetE_eq_inv_of_p_eq_three q hq

/-! ## Lemma 5: when the norm set has at least two elements -/

/-- **Glauberman–Norton, Lemma 5(b)** (p. 1090): `|E| ≥ 2` unless `p` is odd and `q = 2`.

The excluded case is genuine: Lemma 5(a) shows `E = {1}` for `p` odd and `q = 2`, and that is
exactly where the paper's Proposition 7 breaks (see the module docstring).

For `p = 2` the norm set is all of `𝔽_{2^q} ∖ {0}`, which has `2^q - 1 ≥ 3` elements; for `p`
and `q` both odd this is BG's Lemma C.2. -/
theorem two_le_normSetE_ncard [Fact p.Prime] (hq : q.Prime) (h : q ≠ 2 ∨ p = 2) :
    2 ≤ (normSetE p q).ncard := by
  classical
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `E = 𝔽_{2^q} ∖ {0}`, and the field has at least four elements.
    have hq0 : q ≠ 0 := hq.pos.ne'
    have hcard : Nat.card (GaloisField 2 q) = 2 ^ q := GaloisField.card 2 q hq0
    have hfour : 4 ≤ Nat.card (GaloisField 2 q) := by
      rw [hcard]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq.two_le
    -- Pick an element outside `{0, 1}`.
    have hex : ∃ a : GaloisField 2 q, a ≠ 0 ∧ a ≠ 1 := by
      by_contra hcon
      have hsub : (Set.univ : Set (GaloisField 2 q)) ⊆ {0, 1} := by
        intro a _
        rcases eq_or_ne a 0 with rfl | ha
        · exact Or.inl rfl
        · refine Or.inr ?_
          by_contra ha1
          exact hcon ⟨a, ha, ha1⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at this
      have hpair : ({0, 1} : Set (GaloisField 2 q)).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by simp)
      omega
    obtain ⟨a, ha0, ha1⟩ := hex
    have hsub : ({1, a} : Set (GaloisField 2 q)) ⊆ normSetE 2 q := by
      rw [normSetE_eq_setOf_ne_zero_of_two q hq0]
      rintro x (rfl | rfl)
      · exact one_ne_zero
      · exact ha0
    have hpair : ({1, a} : Set (GaloisField 2 q)).ncard = 2 := Set.ncard_pair (Ne.symm ha1)
    calc (2 : ℕ) = ({1, a} : Set (GaloisField 2 q)).ncard := hpair.symm
      _ ≤ (normSetE 2 q).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  · -- `p` odd, hence `q ≠ 2` by hypothesis, hence `q` odd: BG Lemma C.2.
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hq2 : q ≠ 2 := h.resolve_right hp2
    exact lemmaC2 p q hpodd hq (hq.odd_of_ne_two hq2)

end OddOrder.BG.AppC.NormSet
