/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.FixedPointsGalois
import OddOrder.Algebra.PowSubOneDvd
import OddOrder.GroupTheory.RepresentationTheory.SemilinearFieldAut
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Subring

/-!
# The `q`-power Frobenius of a field of order `q²`

Let `E` be a finite field of order `q²`, where `q = pⁿ`.  The `q`-power map
`x ↦ x^q` is then a ring automorphism `σ₀` of `E` of order exactly `2`, and its
fixed set is the subfield `F` of order `q`.

This is the ambient field theory of Peterfalvi, *Character Theory for the Odd
Order Theorem* (LMS LNS 272, 2000), Part II, Ch. III §3, p. 120, where `E = 𝐅_{q²}`
carries the bar operation `x ↦ x̄ = x^q` and `F = 𝐅_q` is its fixed field
(issues 0167, 9504).  The book's `σ` of step (2) is an automorphism of `E`
restricting to a given `θ ∈ Aut(F)`; the two candidates it plays off against each
other are `σ` and `σ̄ = σ σ₀`, the two preimages of `θ` under the restriction
`Aut(E) → Aut(F)` whose kernel is `⟨σ₀⟩`.

## Main results

* `OddOrder.FiniteField.qFrobenius` — `x ↦ x^{pⁿ}` as a `RingAut`.
* `OddOrder.FiniteField.qFrobenius_sq` — it is an involution (on a field of order `q²`).
* `OddOrder.FiniteField.qFrobenius_ne_one`, `orderOf_qFrobenius` — of order exactly `2`.
* `OddOrder.FiniteField.natCard_fixedSet_qFrobenius` — the fixed set has `q` elements.
* `OddOrder.FiniteField.qFrobenius_eq_inv_of_pow_succ_eq_one` — `σ₀` inverts the
  norm-one subgroup `{x : x^{q+1} = 1}`, which is what makes it the book's `σ` when
  `θ = 1`.
-/

namespace OddOrder.FiniteField

open Module

/-- The `q`-power Frobenius `x ↦ x ^ pⁿ` of a finite field of characteristic `p`,
as a ring automorphism (surjectivity is automatic on a finite — hence perfect —
field). -/
noncomputable def qFrobenius (E : Type*) [Field E] [Finite E] (p n : ℕ)
    [Fact p.Prime] [CharP E p] : RingAut E :=
  iterateFrobeniusEquiv E p n

@[simp] theorem qFrobenius_apply (E : Type*) [Field E] [Finite E] (p n : ℕ)
    [Fact p.Prime] [CharP E p] (x : E) :
    qFrobenius E p n x = x ^ p ^ n :=
  iterateFrobeniusEquiv_def E p n x

section Quadratic

variable {E : Type*} [Field E] [Finite E] {p n : ℕ} [Fact p.Prime] [CharP E p]

/-- On a field of order `q²` the `q`-power Frobenius is an involution: it squares
to the `q²`-power map, which is the identity. -/
theorem qFrobenius_sq (hcard : Nat.card E = (p ^ n) ^ 2) :
    qFrobenius E p n ^ 2 = 1 := by
  haveI : Fintype E := Fintype.ofFinite E
  refine RingEquiv.ext fun x => ?_
  have hx : (qFrobenius E p n ^ 2) x = x ^ ((p ^ n) ^ 2) := by
    rw [pow_two, RingAut.mul_apply, qFrobenius_apply, qFrobenius_apply,
      ← pow_mul, ← pow_two]
  rw [hx, ← hcard, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- On a field of order `q²` with `q > 1` the `q`-power Frobenius is not the
identity: were it trivial, every unit would satisfy `x^{q-1} = 1`, so the exponent
of the cyclic group `E^×` — namely `q² - 1` — would divide `q - 1`. -/
theorem qFrobenius_ne_one (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0) :
    qFrobenius E p n ≠ 1 := by
  classical
  intro hone
  set q := p ^ n with hq
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp2 1
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hn)
  -- the Frobenius being trivial forces `x ^ (q - 1) = 1` for every unit
  have hall : ∀ x : Eˣ, orderOf x ∣ q - 1 := by
    intro x
    refine orderOf_dvd_of_pow_eq_one ?_
    have hxq : (x : E) ^ q = (x : E) := by
      have h := DFunLike.congr_fun hone (x : E)
      rwa [qFrobenius_apply] at h
    have hxu : x ^ q = x := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hxq)
    have h1 : x ^ (q - 1) * x = 1 * x := by
      rw [one_mul, ← pow_succ, show q - 1 + 1 = q by omega, hxu]
    exact mul_right_cancel h1
  have hdvd : Nat.card Eˣ ∣ q - 1 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd.mpr hall
  rw [Nat.card_units, hcard] at hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hlt : q < q ^ 2 := by nlinarith
  omega

theorem orderOf_qFrobenius (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0) :
    orderOf (qFrobenius E p n) = 2 := by
  have hdvd : orderOf (qFrobenius E p n) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (qFrobenius_sq hcard)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (qFrobenius_ne_one hcard hn)
  · exact h

/-- The fixed set of the `q`-power Frobenius is `{x : x^q = x}`.

One inclusion is `σ₀ ∈ ⟨σ₀⟩`; the other holds because `{x : σ₀ x = x}` is fixed
pointwise by every automorphism that fixes it, hence by all of `⟨σ₀⟩`. -/
theorem fixedSet_qFrobenius :
    OddOrder.RingAut.fixedSet (Subgroup.zpowers (qFrobenius E p n))
      = {x : E | x ^ p ^ n = x} := by
  ext x
  refine ⟨fun hx => ?_, fun hx τ hτ => ?_⟩
  · have h := hx (qFrobenius E p n) (Subgroup.mem_zpowers _)
    rwa [qFrobenius_apply] at h
  · have hmem : qFrobenius E p n ∈ OddOrder.RingAut.fixer {y : E | y ^ p ^ n = y} := by
      intro y hy
      rw [qFrobenius_apply]
      exact hy
    exact (Subgroup.zpowers_le.mpr hmem) hτ x hx

/-- **The subfield `F = 𝐅_q` of `E = 𝐅_{q²}`**: the fixed field of the `q`-power
Frobenius, i.e. `{x : x^q = x}`. -/
noncomputable def frobFixedSubfield (E : Type*) [Field E] [Finite E] (p n : ℕ)
    [Fact p.Prime] [CharP E p] : Subfield E :=
  FixedPoints.subfield
    (↥(Subgroup.zpowers (qFrobenius E p n))) E

@[simp] theorem mem_frobFixedSubfield {x : E} :
    x ∈ frobFixedSubfield E p n ↔ x ^ p ^ n = x := by
  have h : x ∈ (frobFixedSubfield E p n : Set E) ↔
      x ∈ OddOrder.RingAut.fixedSet (Subgroup.zpowers (qFrobenius E p n)) := by
    rw [OddOrder.RingAut.fixedSet_eq_subfield]
    exact Iff.rfl
  rw [show (x ∈ frobFixedSubfield E p n) ↔ x ∈ (frobFixedSubfield E p n : Set E) from
    Iff.rfl, h, fixedSet_qFrobenius]
  exact Iff.rfl

/-- **The fixed field of the `q`-power Frobenius has `q` elements.**

Artin's lemma (`OddOrder.RingAut.finrank_fixedSet`) applied to `B = ⟨σ₀⟩`, of
order `2`: the fixed subfield `F` satisfies `[E : F] = 2`, hence `|F|² = |E| = q²`. -/
theorem natCard_fixedSet_qFrobenius (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0) :
    Nat.card ↥(OddOrder.RingAut.fixedSet
      (Subgroup.zpowers (qFrobenius E p n))) = p ^ n := by
  classical
  let B : Subgroup (RingAut E) := Subgroup.zpowers (qFrobenius E p n)
  have hBcard : Nat.card ↥B = 2 := by
    change Nat.card ↥(Subgroup.zpowers (qFrobenius E p n)) = 2
    rw [Nat.card_zpowers]
    exact orderOf_qFrobenius hcard hn
  have hrank : finrank (FixedPoints.subfield (↥B) E) E = 2 :=
    (OddOrder.RingAut.finrank_fixedSet B).trans hBcard
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype (FixedPoints.subfield (↥B) E) := Fintype.ofFinite _
  have hpow : Fintype.card E =
      Fintype.card (FixedPoints.subfield (↥B) E) ^
        finrank (FixedPoints.subfield (↥B) E) E :=
    Module.card_eq_pow_finrank
  rw [hrank] at hpow
  have hsq : Nat.card ↥(FixedPoints.subfield (↥B) E) ^ 2 = (p ^ n) ^ 2 := by
    rw [Nat.card_eq_fintype_card, ← hpow, ← Nat.card_eq_fintype_card, hcard]
  have hcongr : Nat.card ↥(OddOrder.RingAut.fixedSet B) =
      Nat.card ↥(FixedPoints.subfield (↥B) E) := by
    rw [OddOrder.RingAut.fixedSet_eq_subfield B]
    rfl
  rw [hcongr]
  exact Nat.pow_left_injective (by omega) hsq

/-- `|F| = q` for the fixed subfield `F = {x : x^q = x}` of a field of order `q²`. -/
theorem natCard_frobFixedSubfield (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0) :
    Nat.card ↥(frobFixedSubfield E p n) = p ^ n := by
  have h := natCard_fixedSet_qFrobenius (E := E) (p := p) (n := n) hcard hn
  rwa [OddOrder.RingAut.fixedSet_eq_subfield] at h

end Quadratic

/-! ## The norm-one subgroup -/

section NormOne

variable {E : Type*} [Field E] [Finite E] {p n : ℕ} [Fact p.Prime] [CharP E p]

/-- **The `q`-power Frobenius inverts the norm-one subgroup.**  If `x^{q+1} = 1`
then `x^q = x⁻¹`.

This is the whole of step (2) of the Ch. III §3 Proposition in the case `θ = 1`:
the book takes `σ` to be `x ↦ x^q`, whose restriction to `F` is the identity
(`= θ`) and which inverts `W₁ ≤ {x : x^{1+q} = 1}`. -/
theorem qFrobenius_eq_inv_of_pow_succ_eq_one {x : Eˣ} (hx : x ^ (p ^ n + 1) = 1) :
    qFrobenius E p n (x : E) = ((x⁻¹ : Eˣ) : E) := by
  rw [qFrobenius_apply]
  have h : x ^ p ^ n = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx
  calc (x : E) ^ p ^ n = ((x ^ p ^ n : Eˣ) : E) := by rw [Units.val_pow_eq_pow_val]
    _ = ((x⁻¹ : Eˣ) : E) := by rw [h]

/-- Unit-free form: an element of the norm-one subgroup is inverted by the
`q`-power Frobenius.  This is the book's `x^{1+σ} = 1` for `x ∈ W₁` with `σ` the
bar operation. -/
theorem qFrobenius_mul_self_eq_one {x : E} (hx : x ^ (p ^ n + 1) = 1) :
    x * qFrobenius E p n x = 1 := by
  rw [qFrobenius_apply]
  calc x * x ^ p ^ n = x ^ p ^ n * x := mul_comm _ _
    _ = x ^ (p ^ n + 1) := (pow_succ x (p ^ n)).symm
    _ = 1 := hx

end NormOne

/-! ## `Aut` of a finite field is generated by the Frobenius

The input the book leaves implicit at the start of step (2) of the Ch. III §3
Proposition: `θ ∈ Aut(F)` extends to an automorphism of `E`.  Rather than going
through `AlgEquiv.restrictNormalHom`, note that *every* automorphism of a finite
field of order `pⁿ` is `x ↦ x^{p^j}` for some `j`; the same formula then defines an
automorphism of any larger field of characteristic `p`, and it restricts to the
given one. -/

section FrobeniusGenerates

variable {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- `(x ↦ x^p)^j = (x ↦ x^{p^j})`. -/
theorem qFrobenius_pow (j : ℕ) : qFrobenius K p 1 ^ j = qFrobenius K p j := by
  induction j with
  | zero =>
      refine RingEquiv.ext fun x => ?_
      rw [pow_zero, qFrobenius_apply, pow_zero, pow_one]
      rfl
  | succ k ih =>
      refine RingEquiv.ext fun x => ?_
      rw [pow_succ, RingAut.mul_apply, ih, qFrobenius_apply, qFrobenius_apply,
        qFrobenius_apply, ← pow_mul]
      congr 1
      rw [pow_one, ← pow_succ']

/-- **`x ↦ x^{p^j}` is the identity on a field of order `pⁿ` exactly when `n ∣ j`.**

If the map is trivial then every unit satisfies `x^{p^j - 1} = 1`, so the exponent
`pⁿ - 1` of the cyclic group `K^×` divides `p^j - 1`, which by
`OddOrder.Nat.pow_sub_one_dvd_pow_sub_one_iff` forces `n ∣ j`.  Conversely
`x^{(pⁿ)^k} = x` on a field of order `pⁿ`. -/
theorem qFrobenius_eq_one_iff {n j : ℕ} (hcard : Nat.card K = p ^ n) (hn : n ≠ 0) :
    qFrobenius K p j = 1 ↔ n ∣ j := by
  classical
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  constructor
  · intro hone
    have hall : ∀ x : Kˣ, orderOf x ∣ p ^ j - 1 := by
      intro x
      refine orderOf_dvd_of_pow_eq_one ?_
      have hxq : (x : K) ^ p ^ j = (x : K) := by
        have h := DFunLike.congr_fun hone (x : K)
        rwa [qFrobenius_apply] at h
      have hxu : x ^ p ^ j = x :=
        Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hxq)
      have hge : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
      have h1 : x ^ (p ^ j - 1) * x = 1 * x := by
        rw [one_mul, ← pow_succ, show p ^ j - 1 + 1 = p ^ j by omega, hxu]
      exact mul_right_cancel h1
    have hdvd : Nat.card Kˣ ∣ p ^ j - 1 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd.mpr hall
    rw [Nat.card_units, hcard] at hdvd
    exact (OddOrder.Nat.pow_sub_one_dvd_pow_sub_one_iff hp2 hn).mp hdvd
  · rintro ⟨k, rfl⟩
    haveI : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [qFrobenius_apply, pow_mul]
    have hc : Fintype.card K = p ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
    rw [← hc]
    exact (FiniteField.pow_card_pow k x).trans rfl

/-- The Frobenius `x ↦ x^p` of a field of order `pⁿ` has order exactly `n`. -/
theorem orderOf_frobenius {n : ℕ} (hcard : Nat.card K = p ^ n) (hn : n ≠ 0) :
    orderOf (qFrobenius K p 1) = n := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine orderOf_dvd_of_pow_eq_one ?_
    rw [qFrobenius_pow]
    exact (qFrobenius_eq_one_iff hcard hn).mpr dvd_rfl
  · refine (qFrobenius_eq_one_iff (j := orderOf (qFrobenius K p 1)) hcard hn).mp ?_
    rw [← qFrobenius_pow]
    exact pow_orderOf_eq_one _

/-- **Every automorphism of a finite field is a power of the Frobenius.**

`|Aut K| = [K : 𝐅_p] = n` while the Frobenius has order `n`, so it generates. -/
theorem exists_pow_eq_of_ringAut {n : ℕ} (hcard : Nat.card K = p ^ n) (hn : n ≠ 0)
    (θ : RingAut K) : ∃ j : ℕ, ∀ x : K, θ x = x ^ p ^ j := by
  classical
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Fintype K := Fintype.ofFinite K
  -- `[K : 𝐅_p] = n`
  have hfin : Module.finrank (ZMod p) K = n := by
    have hpow : Fintype.card K =
        Fintype.card (ZMod p) ^ Module.finrank (ZMod p) K :=
      Module.card_eq_pow_finrank
    rw [ZMod.card p, ← Nat.card_eq_fintype_card, hcard] at hpow
    exact (Nat.pow_right_injective (Fact.out (p := p.Prime)).two_le hpow).symm
  have hcardAut : Nat.card (RingAut K) = n := by
    rw [OddOrder.RepresentationTheory.natCard_ringAut_eq_finrank K p, hfin]
  -- the Frobenius generates, since its order equals the group order
  have hzp : Subgroup.zpowers (qFrobenius K p 1) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, orderOf_frobenius hcard hn, hcardAut]
  -- in a finite group the integer powers are already the natural powers
  obtain ⟨j, hj⟩ : θ ∈ Submonoid.powers (qFrobenius K p 1) := by
    rw [mem_powers_iff_mem_zpowers, hzp]
    exact Subgroup.mem_top _
  refine ⟨j, fun x => ?_⟩
  have hj' : qFrobenius K p 1 ^ j = θ := hj
  have hθ : θ = qFrobenius K p j := by rw [← hj', qFrobenius_pow]
  rw [hθ, qFrobenius_apply]

end FrobeniusGenerates

/-! ## Extending an automorphism of `F` to `E` -/

section Extension

variable {E : Type*} [Field E] [Finite E] {p n : ℕ} [Fact p.Prime] [CharP E p]

instance charP_frobFixedSubfield : CharP ↥(frobFixedSubfield E p n) p :=
  Subfield.charP (frobFixedSubfield E p n) p

/-- **Every automorphism of `F = 𝐅_q` extends to `E = 𝐅_{q²}`** (the input the book
leaves implicit at the start of step (2) of the Ch. III §3 Proposition, p. 120).

`θ` is `x ↦ x^{p^j}` for some `j` (`exists_pow_eq_of_ringAut`), and the same
formula on `E` is `qFrobenius E p j`. -/
theorem exists_ringAut_extending_frobFixedSubfield
    (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0)
    (θ : RingAut ↥(frobFixedSubfield E p n)) :
    ∃ σ : RingAut E,
      ∀ a : ↥(frobFixedSubfield E p n), σ (a : E) = ((θ a : ↥(frobFixedSubfield E p n)) : E) := by
  obtain ⟨j, hj⟩ := exists_pow_eq_of_ringAut
    (K := ↥(frobFixedSubfield E p n)) (p := p) (n := n)
    (natCard_frobFixedSubfield hcard hn) hn θ
  refine ⟨qFrobenius E p j, fun a => ?_⟩
  rw [qFrobenius_apply, hj a]
  push_cast
  rfl

/-- **An automorphism of `E` fixing `F` pointwise is `1` or the `q`-Frobenius.**

Galois correspondence (`OddOrder.RingAut.mem_of_fixes_fixedPoints`): such an
automorphism lies in `⟨σ₀⟩`, which has order `2`. -/
theorem eq_one_or_eq_qFrobenius_of_fixes
    (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0)
    {τ : RingAut E} (hτ : ∀ x : E, x ^ p ^ n = x → τ x = x) :
    τ = 1 ∨ τ = qFrobenius E p n := by
  have hmem : τ ∈ Subgroup.zpowers (qFrobenius E p n) := by
    refine OddOrder.RingAut.mem_of_fixes_fixedPoints ?_
    intro x hx
    rw [fixedSet_qFrobenius] at hx
    exact hτ x hx
  obtain ⟨j, hj⟩ : τ ∈ Submonoid.powers (qFrobenius E p n) :=
    mem_powers_iff_mem_zpowers.mpr hmem
  have hj' : qFrobenius E p n ^ j = τ := hj
  have hord : orderOf (qFrobenius E p n) = 2 := orderOf_qFrobenius hcard hn
  have hmod : qFrobenius E p n ^ (j % 2) = τ := by
    rw [← hord, pow_mod_orderOf]
    exact hj'
  have hlt : j % 2 < 2 := Nat.mod_lt j (by omega)
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · left
    rw [h, pow_zero] at hmod
    exact hmod.symm
  · right
    rw [h, pow_one] at hmod
    exact hmod.symm

/-- **The extensions of an automorphism of `F` to `E` come in pairs**: if `σ` and
`σ'` agree on `F`, then `σ' = σ` or `σ' = σ σ₀`.

This is the book's "possibly on replacing `σ` by `σ̄`" at the end of step (2) of the
Ch. III §3 Proposition (p. 121). -/
theorem eq_or_eq_mul_qFrobenius_of_eq_on_frobFixed
    (hcard : Nat.card E = (p ^ n) ^ 2) (hn : n ≠ 0) {σ σ' : RingAut E}
    (h : ∀ x : E, x ^ p ^ n = x → σ x = σ' x) :
    σ' = σ ∨ σ' = σ * qFrobenius E p n := by
  have hτ : ∀ x : E, x ^ p ^ n = x → (σ⁻¹ * σ') x = x := by
    intro x hx
    change σ.symm (σ' x) = x
    rw [← h x hx, σ.symm_apply_apply]
  rcases eq_one_or_eq_qFrobenius_of_fixes hcard hn hτ with h1 | h1
  · left
    have h2 : σ * (σ⁻¹ * σ') = σ * 1 := by rw [h1]
    rw [mul_inv_cancel_left, mul_one] at h2
    exact h2
  · right
    have h2 : σ * (σ⁻¹ * σ') = σ * qFrobenius E p n := by rw [h1]
    rw [mul_inv_cancel_left] at h2
    exact h2

end Extension

end OddOrder.FiniteField
