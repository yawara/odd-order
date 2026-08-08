/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Extension
import OddOrder.Algebra.FiniteFieldIrreducibleCount
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

/-- The `𝔽_p`-linear map `f ↦ b · f(b)` on polynomials of degree `< r`.  Its range is the
direction of the affine space `A_r = 1 + b𝔽_p + ⋯ + b^r 𝔽_p` of the paper's Step 2. -/
noncomputable def towerMap [Fact p.Prime] (b : GaloisField p q) (r : ℕ) :
    degreeLT (ZMod p) r →ₗ[ZMod p] GaloisField p q where
  toFun f := b * (aeval b) (f : (ZMod p)[X])
  map_add' f g := by
    simp only [Submodule.coe_add, map_add]
    ring
  map_smul' c f := by
    simp only [SetLike.val_smul, map_smul, RingHom.id_apply]
    exact (mul_smul_comm c b ((aeval b) (f : (ZMod p)[X]))).symm ▸ rfl

@[simp] theorem towerMap_apply [Fact p.Prime] (b : GaloisField p q) (r : ℕ)
    (f : degreeLT (ZMod p) r) :
    towerMap p q b r f = b * (aeval b) (f : (ZMod p)[X]) := rfl

/-- The direction of `A_r`: the `𝔽_p`-span of `b, b², …, b^r`, presented as the range of
`towerMap`. -/
noncomputable def towerSubmodule [Fact p.Prime] (b : GaloisField p q) (r : ℕ) :
    Submodule (ZMod p) (GaloisField p q) :=
  LinearMap.range (towerMap p q b r)

/-- For `r ≤ q` the map `f ↦ b · f(b)` is injective on polynomials of degree `< r`: a nonzero
such polynomial cannot vanish at `b`, which has degree `q`. -/
theorem towerMap_injective [Fact p.Prime] (hq : q.Prime) {b : GaloisField p q}
    (hb : b ∉ Set.range (algebraMap (ZMod p) (GaloisField p q))) {r : ℕ} (hr : r ≤ q) :
    Function.Injective (towerMap p q b r) := by
  have hb0 : b ≠ 0 := by
    intro h
    exact hb ⟨0, by rw [map_zero, h]⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker, towerMap_apply] at hf
  have haev : (aeval b) (f : (ZMod p)[X]) = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · exact absurd h hb0
    · exact h
  have hdeg : ((f : (ZMod p)[X])).degree < (q : ℕ) :=
    lt_of_lt_of_le (mem_degreeLT.mp f.2) (by exact_mod_cast Nat.cast_le.mpr hr)
  exact Subtype.ext (aeval_ne_zero_of_degree_lt p q hq hb hdeg haev)

/-- **Glauberman–Norton, Proposition 7, Step 2** (p. 1092): `|A_r| = p^r` for `r ≤ q`.

The affine space `A_r` is a coset of `towerSubmodule`, whose cardinality is computed here. -/
theorem card_towerSubmodule [Fact p.Prime] (hq : q.Prime) {b : GaloisField p q}
    (hb : b ∉ Set.range (algebraMap (ZMod p) (GaloisField p q))) {r : ℕ} (hr : r ≤ q) :
    Nat.card ↥(towerSubmodule p q b r) = p ^ r := by
  have hequiv : ↥(towerSubmodule p q b r) ≃ degreeLT (ZMod p) r :=
    (LinearEquiv.ofInjective (towerMap p q b r) (towerMap_injective p q hq hb hr)).symm.toEquiv
  rw [Nat.card_congr hequiv, Nat.card_congr (degreeLTEquiv (ZMod p) r).toEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The affine space `A_r = {1 + k₁b + k₂b² + ⋯ + k_r b^r}` of the paper's Step 2, as a coset of
`towerSubmodule`. -/
def towerSet [Fact p.Prime] (b : GaloisField p q) (r : ℕ) : Set (GaloisField p q) :=
  {x | ∃ w ∈ towerSubmodule p q b r, x = 1 + w}

/-- `A_r` is exactly the set of values at `b` of polynomials of degree `≤ r` with constant
term `1` — the shape in which the paper's Step 3 does its case analysis
(degree drop / reducible / irreducible). -/
theorem mem_towerSet_iff [Fact p.Prime] {b : GaloisField p q} {r : ℕ} {x : GaloisField p q} :
    x ∈ towerSet p q b r ↔
      ∃ g : (ZMod p)[X], g.natDegree ≤ r ∧ g.coeff 0 = 1 ∧ x = (aeval b) g := by
  constructor
  · rintro ⟨w, ⟨f, rfl⟩, rfl⟩
    refine ⟨C 1 + X * (f : (ZMod p)[X]), ?_, ?_, ?_⟩
    · refine (natDegree_add_le _ _).trans ?_
      simp only [natDegree_C, max_le_iff]
      refine ⟨Nat.zero_le _, ?_⟩
      rcases eq_or_ne (f : (ZMod p)[X]) 0 with hf0 | hf0
      · simp [hf0]
      · have hlt : ((f : (ZMod p)[X])).natDegree < r :=
          (natDegree_lt_iff_degree_lt hf0).mpr (mem_degreeLT.mp f.2)
        refine (natDegree_mul_le).trans ?_
        rw [natDegree_X]
        omega
    · simp
    · simp [towerMap_apply]
  · rintro ⟨g, hdeg, h0, rfl⟩
    have hg0 : g ≠ 0 := fun h => by rw [h] at h0; simp at h0
    have hfmem : g.divX ∈ degreeLT (ZMod p) r := by
      rw [mem_degreeLT]
      refine lt_of_lt_of_le (degree_divX_lt hg0) ?_
      rw [degree_eq_natDegree hg0]
      exact_mod_cast hdeg
    refine ⟨towerMap p q b r ⟨g.divX, hfmem⟩, ⟨_, rfl⟩, ?_⟩
    have hrec : X * g.divX + C (g.coeff 0) = g := X_mul_divX_add g
    rw [towerMap_apply]
    calc (aeval b) g = (aeval b) (X * g.divX + C (g.coeff 0)) := by rw [hrec]
      _ = 1 + b * (aeval b) g.divX := by
          rw [map_add, map_mul, aeval_X, aeval_C, h0, map_one]; ring

/-! ### Closure properties of `U` and of the tower -/

theorem one_mem_normOneSet [Fact p.Prime] : (1 : GaloisField p q) ∈ normOneSet p q := by
  rw [mem_normOneSet_iff, normN_one]

theorem mul_mem_normOneSet [Fact p.Prime] {x y : GaloisField p q} (hx : x ∈ normOneSet p q)
    (hy : y ∈ normOneSet p q) : x * y ∈ normOneSet p q := by
  rw [mem_normOneSet_iff, normN_mul, hx, hy, one_mul]

theorem towerSet_mono [Fact p.Prime] {b : GaloisField p q} {r s : ℕ} (hrs : r ≤ s) :
    towerSet p q b r ⊆ towerSet p q b s := by
  intro x hx
  rw [mem_towerSet_iff] at hx ⊢
  obtain ⟨g, hdeg, h0, hval⟩ := hx
  exact ⟨g, hdeg.trans hrs, h0, hval⟩

/-- The easy branches of Step 3's induction: a value `aeval b g` with `g` of constant term `1`
lies in `U` as soon as `g` has degree `≤ r` (induction hypothesis) or `g` factors into two
polynomials of degree `≤ r`.

Normalizing the constant terms of the factors to `1` is possible because their product is
`g.coeff 0 = 1`, hence both are nonzero. -/
theorem aeval_mem_normOneSet_of_not_irreducible [Fact p.Prime] {b : GaloisField p q} {r : ℕ}
    (hIH : towerSet p q b r ⊆ normOneSet p q) {g : (ZMod p)[X]}
    (hdeg : g.natDegree ≤ r + 1) (h0 : g.coeff 0 = 1) (hnirr : ¬ Irreducible g) :
    (aeval b) g ∈ normOneSet p q := by
  have hg0 : g ≠ 0 := fun h => by rw [h] at h0; simp at h0
  rcases le_or_gt g.natDegree r with hle | hgt
  · exact hIH (mem_towerSet_iff p q |>.mpr ⟨g, hle, h0, rfl⟩)
  -- `g` has degree exactly `r + 1 ≥ 1`, so it is not a unit; being reducible it factors.
  have hdegeq : g.natDegree = r + 1 := by omega
  have hnunit : ¬ IsUnit g := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g₁, g₂, hmul, hu₁, hu₂⟩ : ∃ g₁ g₂, g = g₁ * g₂ ∧ ¬ IsUnit g₁ ∧ ¬ IsUnit g₂ := by
    by_contra hcon
    refine hnirr ⟨hnunit, ?_⟩
    intro a b hab
    by_contra hnn
    exact hcon ⟨a, b, hab, fun h => hnn (Or.inl h), fun h => hnn (Or.inr h)⟩
  -- Both factors have degree between `1` and `r`.
  have hg₁0 : g₁ ≠ 0 := fun h => hg0 (by rw [hmul, h, zero_mul])
  have hg₂0 : g₂ ≠ 0 := fun h => hg0 (by rw [hmul, h, mul_zero])
  have hsum : g₁.natDegree + g₂.natDegree = r + 1 := by
    rw [← hdegeq, hmul, natDegree_mul hg₁0 hg₂0]
  have hd₁ : 1 ≤ g₁.natDegree := by
    rcases Nat.eq_zero_or_pos g₁.natDegree with h | h
    · refine absurd ?_ hu₁
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hg₁0, h]
      simp
    · exact h
  have hd₂ : 1 ≤ g₂.natDegree := by
    rcases Nat.eq_zero_or_pos g₂.natDegree with h | h
    · refine absurd ?_ hu₂
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hg₂0, h]
      simp
    · exact h
  -- Normalize the constant terms to `1`.
  have hc : g₁.coeff 0 * g₂.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hmul, h0]
  have hc₁ : g₁.coeff 0 ≠ 0 := fun h => by rw [h, zero_mul] at hc; exact zero_ne_one hc
  set c : ZMod p := g₁.coeff 0 with hcdef
  have hnorm₁ : (C c⁻¹ * g₁).coeff 0 = 1 := by
    rw [mul_coeff_zero, coeff_C_zero]
    exact inv_mul_cancel₀ hc₁
  have hnorm₂ : (C c * g₂).coeff 0 = 1 := by
    rw [mul_coeff_zero, coeff_C_zero]; exact hc
  have hdeg₁ : (C c⁻¹ * g₁).natDegree ≤ r := by
    rw [natDegree_C_mul (inv_ne_zero hc₁)]; omega
  have hdeg₂ : (C c * g₂).natDegree ≤ r := by
    rw [natDegree_C_mul hc₁]; omega
  have hprod : (C c⁻¹ * g₁) * (C c * g₂) = g := by
    rw [hmul]
    rw [show (C c⁻¹ * g₁) * (C c * g₂) = (C c⁻¹ * C c) * (g₁ * g₂) by ring, ← C_mul,
      inv_mul_cancel₀ hc₁, C_1, one_mul]
  rw [← hprod, map_mul]
  exact mul_mem_normOneSet p q
    (hIH (mem_towerSet_iff p q |>.mpr ⟨_, hdeg₁, hnorm₁, rfl⟩))
    (hIH (mem_towerSet_iff p q |>.mpr ⟨_, hdeg₂, hnorm₂, rfl⟩))

/-! ### Step 3: the induction `A_r ⊆ U` -/

/-- The monic normalization of a nonzero polynomial. -/
private noncomputable def monicOf (g : (ZMod p)[X]) : (ZMod p)[X] := g * C g.leadingCoeff⁻¹

/-- A polynomial with constant term `1` is recovered from its monic normalization. -/
private theorem eq_of_monicOf_eq [Fact p.Prime] {g₁ g₂ : (ZMod p)[X]} (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0)
    (hc₁ : g₁.coeff 0 = 1) (hc₂ : g₂.coeff 0 = 1) (h : monicOf p g₁ = monicOf p g₂) :
    g₁ = g₂ := by
  have key : ∀ g : (ZMod p)[X], g ≠ 0 → g.coeff 0 = 1 →
      g = monicOf p g * C ((monicOf p g).coeff 0)⁻¹ := by
    intro g hg hc
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
    have hcoeff : (monicOf p g).coeff 0 = g.leadingCoeff⁻¹ := by
      rw [monicOf, mul_comm, coeff_C_mul, hc, mul_one]
    have hscalar : g.leadingCoeff⁻¹ * (g.leadingCoeff⁻¹)⁻¹ = 1 :=
      mul_inv_cancel₀ (inv_ne_zero hlc)
    calc g = g * C (g.leadingCoeff⁻¹ * (g.leadingCoeff⁻¹)⁻¹) := by rw [hscalar, C_1, mul_one]
      _ = g * C g.leadingCoeff⁻¹ * C (g.leadingCoeff⁻¹)⁻¹ := by rw [C_mul, mul_assoc]
      _ = monicOf p g * C ((monicOf p g).coeff 0)⁻¹ := by rw [hcoeff]; rfl
  rw [key g₁ h₁ hc₁, key g₂ h₂ hc₂, h]

/-- **Glauberman–Norton, Proposition 7, Step 3** (p. 1092–1093): the induction step
`A_r ⊆ U ⟹ A_{r+1} ⊆ U`, for `2 ≤ r + 1 ≤ q`.

Every `x ∈ A_{r+1} ∖ U` comes from a polynomial `g` of degree exactly `r + 1` with constant
term `1` which is irreducible — otherwise `aeval_mem_normOneSet_of_not_irreducible` would put
`x` in `U`.  Monic normalization is injective on such `g`, so the counting bound
`FiniteFieldCount.mul_card_le` gives `(r+1)·|A_{r+1} ∖ U| ≤ p^{r+1} - p`; since `r + 1 ≥ 2` this
makes `A_{r+1} ∩ U` more than half of `A_{r+1}`, and Step 1 plus Proposition 6 finish. -/
theorem towerSet_succ_subset_normOneSet [Fact p.Prime] (hp5 : 5 ≤ p) (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    {b : GaloisField p q} (hb : b ∉ Set.range (algebraMap (ZMod p) (GaloisField p q)))
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r + 1 ≤ q) (hIH : towerSet p q b r ⊆ normOneSet p q) :
    towerSet p q b (r + 1) ⊆ normOneSet p q := by
  classical
  set W := towerSubmodule p q b (r + 1) with hW
  haveI : Finite ↥W := Subtype.finite
  set S : Set ↥W := {w : ↥W | (1 : GaloisField p q) + (w : GaloisField p q) ∈ normOneSet p q}
    with hS
  -- Step 1 gives condition (C) for `S`.
  have hC : Affine.CondC (p := p) S := condC_normOneSet p q hq.pos hEinv W 1
  -- Every `w ∉ S` produces a monic irreducible polynomial of degree `r + 1`.
  have hpoly : ∀ w : ↥W, w ∉ S → ∃ g : (ZMod p)[X], g.natDegree = r + 1 ∧ g.coeff 0 = 1 ∧
      Irreducible g ∧ (1 : GaloisField p q) + (w : GaloisField p q) = (aeval b) g := by
    intro w hw
    obtain ⟨g, hdeg, h0, hval⟩ :=
      (mem_towerSet_iff p q (b := b) (r := r + 1)
        (x := (1 : GaloisField p q) + (w : GaloisField p q))).mp ⟨w, w.2, rfl⟩
    have hdegeq : g.natDegree = r + 1 := by
      rcases eq_or_lt_of_le hdeg with h | h
      · exact h
      · exfalso
        refine hw ?_
        change (1 : GaloisField p q) + (w : GaloisField p q) ∈ normOneSet p q
        rw [hval]
        exact hIH ((mem_towerSet_iff p q).mpr ⟨g, by omega, h0, rfl⟩)
    have hirr : Irreducible g := by
      by_contra hn
      refine hw ?_
      change (1 : GaloisField p q) + (w : GaloisField p q) ∈ normOneSet p q
      rw [hval]
      exact aeval_mem_normOneSet_of_not_irreducible p q hIH hdeg h0 hn
    exact ⟨g, hdegeq, h0, hirr, hval⟩
  -- Count the complement of `S`.
  have hcompl : (r + 1) * Nat.card ↥(Sᶜ) ≤ p ^ (r + 1) - p := by
    haveI : Fintype ↥(Sᶜ) := Fintype.ofFinite _
    have hchoice : ∀ w : ↥(Sᶜ), ∃ g : (ZMod p)[X], g.natDegree = r + 1 ∧ g.coeff 0 = 1 ∧
        Irreducible g ∧ (1 : GaloisField p q) + ((w : ↥W) : GaloisField p q) = (aeval b) g :=
      fun w => hpoly (w : ↥W) w.2
    choose G hGdeg hG0 hGirr hGval using hchoice
    have hGne : ∀ w, G w ≠ 0 := fun w hz => by
      have := hG0 w; rw [hz] at this; simp at this
    rw [Nat.card_eq_fintype_card]
    refine FiniteFieldCount.mul_card_le p (by omega) (fun w => monicOf p (G w)) ?_ ?_ ?_ ?_
    · exact fun w => monic_mul_leadingCoeff_inv (hGne w)
    · intro w
      refine (associated_mul_unit_right (G w) (C (G w).leadingCoeff⁻¹) ?_).irreducible (hGirr w)
      exact isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr (hGne w))))
    · intro w
      rw [monicOf, natDegree_mul_leadingCoeff_inv _ (hGne w)]
      exact hGdeg w
    · intro w w' hww
      have hGeq : G w = G w' := eq_of_monicOf_eq p (hGne w) (hGne w') (hG0 w) (hG0 w') hww
      have : ((w : ↥W) : GaloisField p q) = ((w' : ↥W) : GaloisField p q) := by
        have h := (hGval w).trans (hGeq ▸ (hGval w').symm)
        exact add_left_cancel h
      exact Subtype.ext (Subtype.ext this)
  -- Hence `S` is more than half of `W`, and Proposition 6 applies.
  have hWcard : Nat.card ↥W = p ^ (r + 1) := card_towerSubmodule p q hq hb hr
  have hsplit : S.ncard + (Sᶜ : Set ↥W).ncard = Nat.card ↥W := by
    rw [← Set.ncard_univ, ← Set.ncard_union_eq disjoint_compl_right (Set.toFinite _)
      (Set.toFinite _), Set.union_compl_self]
  have hcomplcard : (Sᶜ : Set ↥W).ncard = Nat.card ↥(Sᶜ) := (Nat.card_coe_set_eq _).symm
  have hle : Nat.card ↥W ≤ 2 * S.ncard := by
    rw [hcomplcard] at hsplit
    have h2 : 2 * Nat.card ↥(Sᶜ) ≤ (r + 1) * Nat.card ↥(Sᶜ) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp0 : 0 < p := by omega
    rw [hWcard] at hsplit ⊢
    omega
  have huniv : S = Set.univ := Affine.eq_univ_of_condC hp5 hC hle
  -- Read off `A_{r+1} ⊆ U`.
  intro x hx
  obtain ⟨w, hwW, rfl⟩ := hx
  have : (⟨w, hwW⟩ : ↥W) ∈ S := by rw [huniv]; trivial
  exact this

end OddOrder.BG.AppC.NormSet
