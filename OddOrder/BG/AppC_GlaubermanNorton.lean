/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Extension
import OddOrder.BG.AppC_LemmaC2
import OddOrder.BG.AppC_AffineLineCondition

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

/-! ## The norm-one set `U`, and Lemma 1(a) over the whole prime field -/

/-- **BG Appendix C, Remark (VII)** / Glauberman–Norton (1): the norm-one set
`U = {b ∈ 𝔽_{p^q} | N(b) = 1}`, as a subset of the field.

This is the underlying set of `normOneUnits`; the set form is what Proposition 6 consumes. -/
def normOneSet [Fact p.Prime] : Set (GaloisField p q) := {b | normN p q b = 1}

@[simp] theorem mem_normOneSet_iff [Fact p.Prime] {b : GaloisField p q} :
    b ∈ normOneSet p q ↔ normN p q b = 1 := Iff.rfl

theorem ne_zero_of_mem_normOneSet [Fact p.Prime] (hq : 0 < q) {b : GaloisField p q}
    (hb : b ∈ normOneSet p q) : b ≠ 0 := by
  intro h
  rw [mem_normOneSet_iff, h, normN_zero p q hq] at hb
  exact zero_ne_one hb

/-- The norm of an inverse of a norm-one element is `1`. -/
theorem normN_inv_of_mem_normOneSet [Fact p.Prime] (hq : 0 < q) {b : GaloisField p q}
    (hb : b ∈ normOneSet p q) : normN p q b⁻¹ = 1 := by
  have hb0 : b ≠ 0 := ne_zero_of_mem_normOneSet p q hq hb
  have := normN_mul p q b b⁻¹
  rw [mul_inv_cancel₀ hb0, normN_one, hb, one_mul] at this
  exact this.symm

/-- **Glauberman–Norton, Lemma 1(a)** (p. 1089) over the whole prime field: if `E = E⁻¹` and
`a ∈ E`, then `1 + k(1 - a) ∈ U` for every `k ∈ 𝔽_p`.

The repository already has this for natural-number `k` (`normN_dSeq_eq_one`, the telescoping
step inside BG's Lemma C.1, where `dSeq p q a k = k + 1 - k * a`); every element of the prime
field is such a cast, so the two statements agree. -/
theorem normN_one_add_smul_one_sub [Fact p.Prime] (hq : 0 < q)
    (hEinv : normSetE p q = (normSetE p q)⁻¹) {a : GaloisField p q} (ha : a ∈ normSetE p q)
    (k : ZMod p) :
    (1 + k • (1 - a) : GaloisField p q) ∈ normOneSet p q := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hcast : (k • (1 - a) : GaloisField p q) = ((k.val : ℕ) : GaloisField p q) * (1 - a) := by
    rw [Algebra.smul_def, ← map_natCast (algebraMap (ZMod p) (GaloisField p q)) k.val,
      ZMod.natCast_val, ZMod.cast_id]
  have hd : (1 + k • (1 - a) : GaloisField p q) = dSeq p q a k.val := by
    rw [hcast, dSeq]; ring
  rw [mem_normOneSet_iff, hd]
  exact normN_dSeq_eq_one p q hq hEinv ha k.val

/-! ## Proposition 7, Step 1: `A ∩ U` satisfies condition (C) -/

/-- **Glauberman–Norton, Proposition 7, Step 1** (p. 1092): for every affine subspace
`A = a₀ + W` of `𝔽_{p^q}` over `𝔽_p`, the set `A ∩ U` satisfies condition (C).

Given `b ∈ A` and `x` in the direction `W` with `b - x, b, b + x ∈ U`, put `d = b⁻¹x` and
`c = 1 - d`.  Since `U` is closed under multiplication and inverses, `c = b⁻¹(b - x) ∈ U` and
`2 - c = 1 + d = b⁻¹(b + x) ∈ U`, so `c ∈ E`; Lemma 1(a) then gives `1 + kd ∈ U`, whence
`b + kx = b(1 + kd) ∈ U`.

The affine subspace is presented as a coset `a₀ + W` and condition (C) is stated on the
direction `W`, which is the shape `Affine.eq_univ_of_condC` consumes. -/
theorem condC_normOneSet [Fact p.Prime] (hq : 0 < q)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (W : Submodule (ZMod p) (GaloisField p q)) (a₀ : GaloisField p q) :
    Affine.CondC (p := p) {w : ↥W | a₀ + (w : GaloisField p q) ∈ normOneSet p q} := by
  intro b x hsub hb hadd k
  simp only [Set.mem_setOf_eq, Submodule.coe_add, Submodule.coe_sub] at hsub hb hadd ⊢
  set B : GaloisField p q := a₀ + (b : GaloisField p q) with hB
  set X : GaloisField p q := (x : GaloisField p q) with hX
  have hB1 : normN p q B = 1 := hb
  have hB0 : B ≠ 0 := ne_zero_of_mem_normOneSet p q hq hb
  have hBinv : normN p q B⁻¹ = 1 := normN_inv_of_mem_normOneSet p q hq hb
  -- `c = B⁻¹ (B - X) = 1 - B⁻¹X` lies in `E`.
  have hsub' : normN p q (B - X) = 1 := by
    have : a₀ + ((b : GaloisField p q) - X) = B - X := by rw [hB]; ring
    rw [← this]; exact hsub
  have hadd' : normN p q (B + X) = 1 := by
    have : a₀ + ((b : GaloisField p q) + X) = B + X := by rw [hB]; ring
    rw [← this]; exact hadd
  set d : GaloisField p q := B⁻¹ * X with hd
  have hc1 : normN p q (1 - d) = 1 := by
    have he : (1 : GaloisField p q) - d = B⁻¹ * (B - X) := by
      rw [hd]; field_simp
    rw [he, normN_mul, hBinv, hsub', one_mul]
  have hc2 : normN p q (2 - (1 - d)) = 1 := by
    have he : (2 : GaloisField p q) - (1 - d) = B⁻¹ * (B + X) := by
      rw [hd]; field_simp; ring
    rw [he, normN_mul, hBinv, hadd', one_mul]
  have hcE : (1 - d) ∈ normSetE p q := ⟨hc1, hc2⟩
  -- Lemma 1(a) applied to `c = 1 - d` gives `1 + k d ∈ U`.
  have hstep := normN_one_add_smul_one_sub p q hq hEinv hcE k
  have hone_sub : (1 : GaloisField p q) - (1 - d) = d := by ring
  rw [mem_normOneSet_iff, hone_sub] at hstep
  -- Multiply back by `B`.
  have hfinal : a₀ + ((b : GaloisField p q) + k • X) = B * (1 + k • d) := by
    rw [hB, hd, Algebra.smul_def, Algebra.smul_def]
    field_simp
    ring
  rw [mem_normOneSet_iff, Submodule.coe_smul, ← hX, hfinal, normN_mul, hB1, hstep, one_mul]

/-! ## Proposition 7, Step 2: the degree of `b` and the tower `A_r` -/

open Polynomial

/-- An element of `𝔽_{p^q}` outside the prime field has degree exactly `q` over `𝔽_p`, when `q`
is prime.

Its minimal polynomial is irreducible and divides `X^{p^q} - X`, so its degree divides `q`
(`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`); degree `1` would put the element in
the prime field. -/
theorem natDegree_minpoly_eq [Fact p.Prime] (hq : q.Prime) {b : GaloisField p q}
    (hb : b ∉ Set.range (algebraMap (ZMod p) (GaloisField p q))) :
    (minpoly (ZMod p) b).natDegree = q := by
  haveI : Fintype (GaloisField p q) := Fintype.ofFinite _
  have hirr : Irreducible (minpoly (ZMod p) b) :=
    minpoly.irreducible (IsIntegral.of_finite (ZMod p) b)
  -- `b` is a root of `X^{p^q} - X`, so its minimal polynomial divides that.
  have hcardF : Fintype.card (GaloisField p q) = p ^ q := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p q hq.pos.ne'
  have hroot : (aeval b) (X ^ (Nat.card (ZMod p)) ^ q - X : (ZMod p)[X]) = 0 := by
    have hcardZ : Nat.card (ZMod p) = p := Nat.card_zmod p
    rw [hcardZ, map_sub, map_pow, aeval_X, ← hcardF, FiniteField.pow_card, sub_self]
  have hdvd : minpoly (ZMod p) b ∣ (X ^ (Nat.card (ZMod p)) ^ q - X : (ZMod p)[X]) :=
    minpoly.dvd _ _ hroot
  have hdd : (minpoly (ZMod p) b).natDegree ∣ q :=
    hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  -- Degree `1` would mean `b` lies in the prime field.
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdd) with h1 | hq'
  · exfalso
    refine hb ⟨-(minpoly (ZMod p) b).coeff 0, ?_⟩
    have hmonic : (minpoly (ZMod p) b).Monic := minpoly.monic (IsIntegral.of_finite (ZMod p) b)
    have heq : minpoly (ZMod p) b = X + C ((minpoly (ZMod p) b).coeff 0) := by
      have := hmonic.eq_X_add_C h1
      simpa using this
    have h0 : (aeval b) (minpoly (ZMod p) b) = 0 := minpoly.aeval _ _
    rw [heq, map_add, aeval_X, aeval_C] at h0
    have : algebraMap (ZMod p) (GaloisField p q) (-(minpoly (ZMod p) b).coeff 0) = b := by
      rw [map_neg]
      linear_combination -h0
    exact this
  · exact hq'

/-- A nonzero polynomial of degree `< q` cannot vanish at an element of degree `q`. -/
theorem aeval_ne_zero_of_degree_lt [Fact p.Prime] (hq : q.Prime) {b : GaloisField p q}
    (hb : b ∉ Set.range (algebraMap (ZMod p) (GaloisField p q)))
    {f : (ZMod p)[X]} (hdeg : f.degree < (q : ℕ)) (hf : (aeval b) f = 0) : f = 0 := by
  by_contra hne
  have hdvd : minpoly (ZMod p) b ∣ f := minpoly.dvd _ _ hf
  have hle : (minpoly (ZMod p) b).degree ≤ f.degree := Polynomial.degree_le_of_dvd hdvd hne
  rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite (ZMod p) b)),
    natDegree_minpoly_eq p q hq hb] at hle
  exact absurd (hle.trans_lt hdeg) (lt_irrefl _)

end OddOrder.BG.AppC.NormSet
