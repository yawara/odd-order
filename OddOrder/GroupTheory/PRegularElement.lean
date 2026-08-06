/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Factorization.Basic

/-!
# `p`-elements, `p`-regular elements, and the `p` / `p'` decomposition

Fix a prime `p`.  An element `g` of a group is

* a **`p`-element** if `orderOf g` is a power of `p` (`IsPElement`);
* **`p`-regular** if `p ∤ orderOf g` (`IsPRegular`).

Every element `g` of finite order factors **uniquely** as a commuting product

`g = pRegularPart p g * pPart p g`

with `pPart p g` a `p`-element and `pRegularPart p g` `p`-regular; both factors are powers
of `g`.  This decomposition is the indexing device of modular representation theory: Brauer
characters are class functions supported on the `p`-regular classes
(issue 9506, the bottom-up first stage of issue 0147).

mathlib has `CommMonoid.primaryComponent` for commutative monoids but no `p`/`p'` factorisation
of a single group element, so this leaf builds it from Bézout applied to the coprime pair
`ordProj[p] (orderOf g)`, `ordCompl[p] (orderOf g)`.

⚠ `ordProj[p] n` and `ordCompl[p] n` are *notation* for `p ^ n.factorization p` and
`n / p ^ n.factorization p`.  Writing `(ordCompl[p] n : ℤ)` therefore elaborates the division
**in `ℤ`**; every cast below goes through `((… : ℕ) : ℤ)` so that the natural-number division
is performed first.

## Main definitions

* `OddOrder.GroupTheory.IsPElement`
* `OddOrder.GroupTheory.IsPRegular`
* `OddOrder.GroupTheory.pPart` / `OddOrder.GroupTheory.pRegularPart`

## Main results

* `OddOrder.GroupTheory.pRegularPart_mul_pPart` — the factorisation `g = g_{p'} · g_p`
* `OddOrder.GroupTheory.isPElement_pPart` / `OddOrder.GroupTheory.isPRegular_pRegularPart`
* `OddOrder.GroupTheory.eq_pPart_of_commute` — uniqueness of the factorisation
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ### `p`-elements and `p`-regular elements -/

/-- `g` is a **`p`-element** if its order is a power of `p`. -/
def IsPElement (p : ℕ) (g : G) : Prop := ∃ k : ℕ, orderOf g = p ^ k

/-- `g` is **`p`-regular** if `p` does not divide its order.  (Elements of infinite order are
not `p`-regular, since `orderOf g = 0` is divisible by everything.) -/
def IsPRegular (p : ℕ) (g : G) : Prop := ¬ p ∣ orderOf g

theorem isPRegular_iff_coprime {p : ℕ} (hp : p.Prime) {g : G} :
    IsPRegular p g ↔ Nat.Coprime p (orderOf g) :=
  (Nat.Prime.coprime_iff_not_dvd hp).symm

theorem IsPRegular.isOfFinOrder {p : ℕ} {g : G} (h : IsPRegular p g) : IsOfFinOrder g := by
  rw [← orderOf_pos_iff]
  rcases Nat.eq_zero_or_pos (orderOf g) with h0 | h0
  · exact absurd (h0 ▸ dvd_zero p) h
  · exact h0

theorem isPElement_one (p : ℕ) : IsPElement p (1 : G) := ⟨0, by simp⟩

/-- **`⟨x⟩` is a `p`-group** when `x` is a `p`-element: every element of `⟨x⟩` has order dividing
that of `x`. -/
theorem isPGroup_zpowers_of_isPElement {p : ℕ} {x : G} (hx : IsPElement p x) :
    IsPGroup p ↥(Subgroup.zpowers x) := by
  obtain ⟨a, ha⟩ := hx
  refine fun g => ⟨a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← ha, ← orderOf_dvd_iff_pow_eq_one]
  exact orderOf_dvd_of_mem_zpowers g.2

theorem isPRegular_one {p : ℕ} (hp : p.Prime) : IsPRegular p (1 : G) := by
  rw [IsPRegular, orderOf_one]
  intro h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

/-- Conjugation preserves the order.  (mathlib has this only in the `SemiconjBy` form
`SemiconjBy.orderOf_eq`; this is the conjugation-form adaptation used throughout.) -/
theorem orderOf_conj (x g : G) : orderOf (x * g * x⁻¹) = orderOf g := by
  refine (SemiconjBy.orderOf_eq x ?_).symm
  change x * g = x * g * x⁻¹ * x
  simp [mul_assoc]

/-- Being a `p`-element only depends on the order, hence is conjugation invariant. -/
theorem IsPElement.conj {p : ℕ} {g : G} (h : IsPElement p g) (x : G) :
    IsPElement p (x * g * x⁻¹) := by
  rwa [IsPElement, orderOf_conj]

/-- Being `p`-regular only depends on the order, hence is conjugation invariant. -/
theorem IsPRegular.conj {p : ℕ} {g : G} (h : IsPRegular p g) (x : G) :
    IsPRegular p (x * g * x⁻¹) := by
  rwa [IsPRegular, orderOf_conj]

theorem IsPRegular.inv {p : ℕ} {g : G} (h : IsPRegular p g) : IsPRegular p g⁻¹ := by
  rwa [IsPRegular, orderOf_inv]

theorem IsPRegular.pow {p : ℕ} {g : G} (h : IsPRegular p g) (n : ℕ) : IsPRegular p (g ^ n) :=
  fun hdvd => h (hdvd.trans (orderOf_pow_dvd n))

/-- A `p`-element that is also `p`-regular is trivial. -/
theorem eq_one_of_isPElement_of_isPRegular {p : ℕ} {g : G}
    (hx : IsPElement p g) (hy : IsPRegular p g) : g = 1 := by
  obtain ⟨k, hk⟩ := hx
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd (hk ▸ dvd_pow_self p hk0.ne') hy

/-- **`p`-regularity does not see the ambient group.** -/
theorem isPRegular_coe_iff {p : ℕ} {H : Subgroup G} {y : ↥H} :
    IsPRegular p ((y : G)) ↔ IsPRegular p y := by
  rw [IsPRegular, IsPRegular, Subgroup.orderOf_coe]

/-- **A `p`-regular element of a subgroup is `p`-regular in the ambient group.** -/
theorem isPRegular_coe {p : ℕ} {H : Subgroup G} {y : ↥H} (hy : IsPRegular p y) :
    IsPRegular p ((y : G)) := isPRegular_coe_iff.mpr hy

/-- Being a `p`-element does not see the ambient group either. -/
theorem isPElement_coe_iff {p : ℕ} {H : Subgroup G} {y : ↥H} :
    IsPElement p ((y : G)) ↔ IsPElement p y := by
  rw [IsPElement, IsPElement, Subgroup.orderOf_coe]

/-- Every element of a `p`-subgroup is a `p`-element. -/
theorem isPElement_of_mem_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) {x : G} (hx : x ∈ H) : IsPElement p x :=
  isPElement_coe_iff.mpr (IsPGroup.iff_orderOf.mp hH ⟨x, hx⟩)

/-! ### The `p` / `p'` decomposition

Write `n = orderOf g`, `q = ordProj[p] n = p ^ (n.factorization p)` and `m = ordCompl[p] n = n / q`,
so `q * m = n` and `gcd q m = 1`.  Bézout gives integers `A = Nat.gcdA q m`, `B = Nat.gcdB q m`
with `q * A + m * B = 1`, and we set

`pRegularPart p g = g ^ (q * A)`,  `pPart p g = g ^ (m * B)`.

Then `g = g ^ (q * A + m * B)` is the required product, `(g ^ (m * B)) ^ q = (g ^ n) ^ B = 1`
makes the second factor a `p`-element, and `(g ^ (q * A)) ^ m = (g ^ n) ^ A = 1` makes the first
one `p`-regular. -/

section Decomposition

variable (p : ℕ)

/-- The **`p`-part** of an element of finite order: the unique `p`-element factor in the
commuting factorisation `g = pRegularPart p g * pPart p g`. -/
noncomputable def pPart (g : G) : G :=
  g ^ (((ordCompl[p] (orderOf g) : ℕ) : ℤ) *
    Nat.gcdB (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)))

/-- The **`p'`-part** (or `p`-regular part) of an element of finite order: the unique
`p`-regular factor in the commuting factorisation `g = pRegularPart p g * pPart p g`. -/
noncomputable def pRegularPart (g : G) : G :=
  g ^ (((ordProj[p] (orderOf g) : ℕ) : ℤ) *
    Nat.gcdA (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)))

variable {p}

theorem coprime_ordProj_ordCompl {n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    Nat.Coprime (ordProj[p] n) (ordCompl[p] n) :=
  Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn)

/-- The Bézout identity behind the decomposition. -/
theorem bezout_ordProj_ordCompl {n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ((ordProj[p] n : ℕ) : ℤ) * Nat.gcdA (ordProj[p] n) (ordCompl[p] n)
        + ((ordCompl[p] n : ℕ) : ℤ) * Nat.gcdB (ordProj[p] n) (ordCompl[p] n) = 1 := by
  have h := Nat.gcd_eq_gcd_ab (ordProj[p] n) (ordCompl[p] n)
  rw [coprime_ordProj_ordCompl hp hn] at h
  exact_mod_cast h.symm

/-- **The `p` / `p'` factorisation**: `g = g_{p'} · g_p`. -/
theorem pRegularPart_mul_pPart (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    pRegularPart p g * pPart p g = g := by
  rw [pRegularPart, pPart, ← zpow_add,
    bezout_ordProj_ordCompl hp (orderOf_pos_iff.mpr hg).ne', zpow_one]

/-- The two factors commute (both are powers of `g`). -/
theorem commute_pPart_of_commute {a g : G} (h : Commute a g) : Commute a (pPart p g) := by
  rw [pPart]; exact h.zpow_right _

theorem commute_pRegularPart_of_commute {a g : G} (h : Commute a g) :
    Commute a (pRegularPart p g) := by
  rw [pRegularPart]; exact h.zpow_right _

theorem commute_pRegularPart_pPart (g : G) : Commute (pRegularPart p g) (pPart p g) :=
  (Commute.refl g).zpow_zpow _ _

theorem pPart_mul_pRegularPart (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    pPart p g * pRegularPart p g = g :=
  (commute_pRegularPart_pPart g).symm.eq ▸ pRegularPart_mul_pPart hp hg

/-- `ordProj[p] n * ordCompl[p] n = n`, cast to `ℤ` with the natural-number division done
first (see the warning in the module docstring). -/
theorem cast_ordProj_mul_ordCompl (n : ℕ) :
    ((ordProj[p] n : ℕ) : ℤ) * ((ordCompl[p] n : ℕ) : ℤ) = (n : ℤ) := by
  rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]

theorem pPart_pow_ordProj (g : G) : pPart p g ^ ordProj[p] (orderOf g) = 1 := by
  rw [pPart, ← zpow_natCast (g ^ _) (ordProj[p] (orderOf g)), ← zpow_mul]
  have harith : ((ordCompl[p] (orderOf g) : ℕ) : ℤ) *
        Nat.gcdB (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)) *
        ((ordProj[p] (orderOf g) : ℕ) : ℤ)
      = ((orderOf g : ℕ) : ℤ) *
        Nat.gcdB (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)) := by
    rw [← cast_ordProj_mul_ordCompl (p := p) (orderOf g)]
    ring
  rw [harith, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem pRegularPart_pow_ordCompl (g : G) : pRegularPart p g ^ ordCompl[p] (orderOf g) = 1 := by
  rw [pRegularPart, ← zpow_natCast (g ^ _) (ordCompl[p] (orderOf g)), ← zpow_mul]
  have harith : ((ordProj[p] (orderOf g) : ℕ) : ℤ) *
        Nat.gcdA (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)) *
        ((ordCompl[p] (orderOf g) : ℕ) : ℤ)
      = ((orderOf g : ℕ) : ℤ) *
        Nat.gcdA (ordProj[p] (orderOf g)) (ordCompl[p] (orderOf g)) := by
    rw [← cast_ordProj_mul_ordCompl (p := p) (orderOf g)]
    ring
  rw [harith, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

/-- The `p`-part is a `p`-element. -/
theorem isPElement_pPart (hp : p.Prime) (g : G) : IsPElement p (pPart p g) := by
  have hdvd : orderOf (pPart p g) ∣ p ^ ((orderOf g).factorization p) :=
    orderOf_dvd_of_pow_eq_one (pPart_pow_ordProj g)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, hk⟩

/-- The `p'`-part is `p`-regular. -/
theorem isPRegular_pRegularPart (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    IsPRegular p (pRegularPart p g) := fun hdvd =>
  Nat.not_dvd_ordCompl hp (orderOf_pos_iff.mpr hg).ne'
    (hdvd.trans (orderOf_dvd_of_pow_eq_one (pRegularPart_pow_ordCompl g)))

end Decomposition

/-! ### Uniqueness, and behaviour on special elements -/

section Uniqueness

variable {p : ℕ}

/-- **Uniqueness of the `p` / `p'` factorisation.**  If `g = y * x` with `x` a `p`-element,
`y` `p`-regular and `x`, `y` commuting, then `x` and `y` are the two canonical parts.

The point is that `x` and `y` are automatically powers of `g`: with `orderOf x = p ^ a` and
`orderOf y` coprime to it, Bézout in `⟨g⟩` isolates each factor. -/
theorem eq_pPart_of_commute (hp : p.Prime) {g x y : G} (hcomm : Commute x y)
    (hx : IsPElement p x) (hy : IsPRegular p y) (hg : y * x = g) :
    x = pPart p g ∧ y = pRegularPart p g := by
  obtain ⟨a, ha⟩ := hx
  have hyfin : IsOfFinOrder y := hy.isOfFinOrder
  have hxpos : 0 < orderOf x := by rw [ha]; exact pow_pos hp.pos a
  have hypos : 0 < orderOf y := orderOf_pos_iff.mpr hyfin
  have hcop : Nat.Coprime (orderOf y) (orderOf x) := by
    rw [ha]
    exact Nat.Coprime.pow_right a ((isPRegular_iff_coprime hp).mp hy).symm
  have horder : orderOf g = orderOf y * orderOf x := by
    rw [← hg]
    exact hcomm.symm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hgpos : 0 < orderOf g := by rw [horder]; exact Nat.mul_pos hypos hxpos
  have hproj : ordProj[p] (orderOf g) = orderOf x := by
    rw [horder, Nat.factorization_mul hypos.ne' hxpos.ne']
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd hy, ha, Nat.Prime.factorization_pow hp]
    simp
  have hcompl : ordCompl[p] (orderOf g) = orderOf y := by
    rw [hproj, horder, Nat.mul_div_cancel _ hxpos]
  -- Bézout for the pair `(orderOf x, orderOf y)`
  have hbez : (orderOf x : ℤ) * Nat.gcdA (orderOf x) (orderOf y)
      + (orderOf y : ℤ) * Nat.gcdB (orderOf x) (orderOf y) = 1 := by
    have h := Nat.gcd_eq_gcd_ab (orderOf x) (orderOf y)
    rw [hcop.symm] at h
    exact_mod_cast h.symm
  have hx1 : x ^ ((orderOf x : ℤ) * Nat.gcdA (orderOf x) (orderOf y)) = 1 := by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hy1 : y ^ ((orderOf y : ℤ) * Nat.gcdB (orderOf x) (orderOf y)) = 1 := by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hzpow : ∀ n : ℤ, g ^ n = y ^ n * x ^ n := fun n => by
    rw [← hg]; exact hcomm.symm.mul_zpow n
  refine ⟨?_, ?_⟩
  · rw [pPart, hzpow, hcompl, hproj, hy1, one_mul]
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ ((orderOf x : ℤ) * Nat.gcdA (orderOf x) (orderOf y)
            + (orderOf y : ℤ) * Nat.gcdB (orderOf x) (orderOf y)) := by rw [hbez]
      _ = x ^ ((orderOf y : ℤ) * Nat.gcdB (orderOf x) (orderOf y)) := by
          rw [zpow_add, hx1, one_mul]
  · rw [pRegularPart, hzpow, hcompl, hproj, hx1, mul_one]
    calc y = y ^ (1 : ℤ) := (zpow_one y).symm
      _ = y ^ ((orderOf x : ℤ) * Nat.gcdA (orderOf x) (orderOf y)
            + (orderOf y : ℤ) * Nat.gcdB (orderOf x) (orderOf y)) := by rw [hbez]
      _ = y ^ ((orderOf x : ℤ) * Nat.gcdA (orderOf x) (orderOf y)) := by
          rw [zpow_add, hy1, mul_one]

theorem pPart_eq_one_of_isPRegular (hp : p.Prime) {g : G} (hg : IsPRegular p g) :
    pPart p g = 1 :=
  ((eq_pPart_of_commute hp (Commute.one_left g) (isPElement_one p) hg (mul_one g)).1).symm

theorem pRegularPart_eq_one_of_isPElement (hp : p.Prime) {g : G} (hg : IsPElement p g) :
    pRegularPart p g = 1 := by
  obtain ⟨k, hk⟩ := hg
  have hproj : ordProj[p] (orderOf g) = orderOf g := by
    rw [hk, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  rw [pRegularPart, hproj, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem pRegularPart_eq_self_of_isPRegular (hp : p.Prime) {g : G} (hg : IsPRegular p g) :
    pRegularPart p g = g :=
  ((eq_pPart_of_commute hp (Commute.one_left g) (isPElement_one p) hg (mul_one g)).2).symm

/-- A `p`-element is its own `p`-part. -/
theorem pPart_eq_self_of_isPElement (hp : p.Prime) {g : G} (hg : IsPElement p g) :
    pPart p g = g :=
  ((eq_pPart_of_commute hp (Commute.one_right g) hg (isPRegular_one hp) (one_mul g)).1).symm

/-- The converse of `pPart_eq_one_of_isPRegular`: a trivial `p`-part means `g` *is* its own
`p'`-part, hence is `p`-regular. -/
theorem isPRegular_of_pPart_eq_one (hp : p.Prime) {g : G} (hg : IsOfFinOrder g)
    (h : pPart p g = 1) : IsPRegular p g := by
  have hgeq : pRegularPart p g = g := by
    have hfac := pRegularPart_mul_pPart (p := p) hp hg
    rwa [h, mul_one] at hfac
  exact hgeq ▸ isPRegular_pRegularPart hp hg

/-- `p`-regularity is exactly the triviality of the `p`-part. -/
theorem isPRegular_iff_pPart_eq_one (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    IsPRegular p g ↔ pPart p g = 1 :=
  ⟨pPart_eq_one_of_isPRegular hp, isPRegular_of_pPart_eq_one hp hg⟩

/-- Both parts are conjugation equivariant (they are given by a formula in `g` alone). -/
theorem pPart_conj (g x : G) : pPart p (x * g * x⁻¹) = x * pPart p g * x⁻¹ := by
  rw [pPart, pPart, orderOf_conj, conj_zpow]

theorem pRegularPart_conj (g x : G) :
    pRegularPart p (x * g * x⁻¹) = x * pRegularPart p g * x⁻¹ := by
  rw [pRegularPart, pRegularPart, orderOf_conj, conj_zpow]

end Uniqueness

/-! ### The `p'`-part of the group order -/

section PRegularExponent

variable {p : ℕ} {G : Type*} [Group G]

/-- The **`p'`-part of the order of `G`**: the largest divisor of `|G|` prime to `p`.  This is
the exponent at which Brauer characters of `G` are taken, because every `p`-regular element of
`G` has order dividing it (`orderOf_dvd_pRegularExponent`). -/
noncomputable def pRegularExponent (p : ℕ) (G : Type*) [Group G] : ℕ :=
  ordCompl[p] (Nat.card G)

theorem not_dvd_pRegularExponent [Finite G] (hp : p.Prime) : ¬ p ∣ pRegularExponent p G :=
  Nat.not_dvd_ordCompl hp Nat.card_pos.ne'

theorem pRegularExponent_pos [Finite G] : 0 < pRegularExponent p G :=
  Nat.ordCompl_pos p Nat.card_pos.ne'

/-- **Every `p`-regular element has order dividing the `p'`-part of `|G|`.**  Lagrange gives
`orderOf g ∣ |G| = p ^ a * m`, and `p ∤ orderOf g` forces the `p`-power factor out. -/
theorem orderOf_dvd_pRegularExponent (hp : p.Prime) {g : G} (hg : IsPRegular p g) :
    orderOf g ∣ pRegularExponent p G := by
  have hcop : Nat.Coprime (orderOf g) (ordProj[p] (Nat.card G)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hg).symm
  refine hcop.dvd_of_dvd_mul_left ?_
  rw [pRegularExponent, Nat.ordProj_mul_ordCompl_eq_self]
  exact orderOf_dvd_natCard g

theorem pow_pRegularExponent_eq_one (hp : p.Prime) {g : G} (hg : IsPRegular p g) :
    g ^ pRegularExponent p G = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_pRegularExponent hp hg)

end PRegularExponent

/-! ### `p`-regular conjugacy classes -/

section PRegularClasses

variable {p : ℕ} {G : Type*} [Group G]

/-- Being `p`-regular is a conjugacy invariant, so it descends to conjugacy classes. -/
def IsPRegularClass (p : ℕ) (C : ConjClasses G) : Prop :=
  Quotient.liftOn C (fun g => IsPRegular p g) fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    have hord : orderOf b = orderOf a := by rw [← hc, orderOf_conj]
    exact propext (by rw [IsPRegular, IsPRegular, hord])

@[simp]
theorem isPRegularClass_mk {g : G} : IsPRegularClass p (ConjClasses.mk g) ↔ IsPRegular p g :=
  Iff.rfl

/-- The `p'`-part of a conjugacy class: well defined because taking `p'`-parts commutes with
conjugation (`pRegularPart_conj`). -/
noncomputable def pRegularPartClass (p : ℕ) (C : ConjClasses G) : ConjClasses G :=
  Quotient.liftOn C (fun g => ConjClasses.mk (pRegularPart p g)) fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc, pRegularPart_conj]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c, rfl⟩)

@[simp]
theorem pRegularPartClass_mk (g : G) :
    pRegularPartClass p (ConjClasses.mk g) = ConjClasses.mk (pRegularPart p g) := rfl

/-- The `p'`-part of a class is a `p`-regular class. -/
theorem isPRegularClass_pRegularPartClass (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    IsPRegularClass p (pRegularPartClass p (ConjClasses.mk g)) :=
  isPRegularClass_mk.mpr (isPRegular_pRegularPart hp hg)

/-- On `p`-regular classes the `p'`-part map is the identity. -/
theorem pRegularPartClass_of_isPRegularClass (hp : p.Prime) {C : ConjClasses G}
    (hC : IsPRegularClass p C) : pRegularPartClass p C = C := by
  induction C using Quotient.inductionOn with
  | h g => exact congrArg ConjClasses.mk (pRegularPart_eq_self_of_isPRegular hp hC)

/-- **The chosen representative of a `p`-regular class is `p`-regular.**  Needed whenever one
indexes a family by the `p`-regular classes and has to pick group elements. -/
theorem isPRegular_out {C : ConjClasses G} (hC : IsPRegularClass p C) : IsPRegular p C.out := by
  induction C using Quotient.inductionOn with
  | h g =>
    obtain ⟨b, hb⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      (Quotient.out_eq (ConjClasses.mk g)))
    have hord : orderOf (Quotient.out (ConjClasses.mk g)) = orderOf g := by
      conv_rhs => rw [← hb]
      rw [orderOf_conj]
    change ¬ p ∣ orderOf (Quotient.out (ConjClasses.mk g))
    rw [hord]
    exact hC

/-- `ConjClasses.mk` of a chosen representative is the class again.  Stated for
`ConjClasses.mk` rather than `Quotient.mk` so that it rewrites in the places where classes are
built by `ConjClasses.mk`. -/
theorem conjClasses_mk_out (C : ConjClasses G) : ConjClasses.mk (Quotient.out C) = C := by
  rw [← ConjClasses.quotient_mk_eq_mk]
  exact Quotient.out_eq _

/-- Being a `p`-element is a conjugacy invariant, so it descends to conjugacy classes. -/
def IsPElementClass (p : ℕ) (C : ConjClasses G) : Prop :=
  Quotient.liftOn C (fun g => IsPElement p g) fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    have hord : orderOf b = orderOf a := by rw [← hc, orderOf_conj]
    exact propext (by rw [IsPElement, IsPElement, hord])

@[simp]
theorem isPElementClass_mk {g : G} : IsPElementClass p (ConjClasses.mk g) ↔ IsPElement p g :=
  Iff.rfl

/-- The `p`-part of a conjugacy class: well defined because taking `p`-parts commutes with
conjugation (`pPart_conj`). -/
noncomputable def pPartClass (p : ℕ) (C : ConjClasses G) : ConjClasses G :=
  Quotient.liftOn C (fun g => ConjClasses.mk (pPart p g)) fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc, pPart_conj]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c, rfl⟩)

@[simp]
theorem pPartClass_mk (g : G) :
    pPartClass p (ConjClasses.mk g) = ConjClasses.mk (pPart p g) := rfl

/-- The `p`-part of a class is a `p`-element class. -/
theorem isPElementClass_pPartClass (hp : p.Prime) (C : ConjClasses G) :
    IsPElementClass p (pPartClass p C) := by
  induction C using Quotient.inductionOn with
  | h g => exact isPElementClass_mk.mpr (isPElement_pPart hp g)

/-- On `p`-element classes the `p`-part map is the identity. -/
theorem pPartClass_of_isPElementClass (hp : p.Prime) {C : ConjClasses G}
    (hC : IsPElementClass p C) : pPartClass p C = C := by
  induction C using Quotient.inductionOn with
  | h g => exact congrArg ConjClasses.mk (pPart_eq_self_of_isPElement hp hC)

end PRegularClasses

end OddOrder.GroupTheory
