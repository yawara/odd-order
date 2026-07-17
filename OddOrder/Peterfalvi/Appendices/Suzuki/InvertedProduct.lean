/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# Peterfalvi Part II, Ch. I §1: the `Y × Z → X` decomposition (the Lemma)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, p. 101.

The general group-theoretic **Lemma** used in the proof of Proposition 5.
Let `M` be a finite group, `t` an involution of `M`, `X` a subgroup of odd
order normalized by `t`, `Y = C_X(t)` and `Z = {x ∈ X | tˣt = x⁻¹}` the
elements of `X` inverted by `t`.

* (a) `(y, z) ↦ yz` is a bijection `Y × Z → X`; in particular `|X| = |Y||Z|`.
* (b) `⟨Z⟩ ◁ X`.

The bijection is exhibited with an explicit inverse: for `x ∈ X` set
`w = (t x⁻¹ t) x` (inverted by `t`), `z = w^{(|X|+1)/2}` its odd square root,
and `y = x z⁻¹`; then `x = yz` with `y ∈ Y`, `z ∈ Z`, and every decomposition
arises this way (`w(yz) = z²`).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise

variable {M : Type*} [Group M]

/-- `Z(X, t) = {x ∈ X | x is inverted by t}`, the elements of `X` sent to
their inverse by conjugation by the involution `t`. -/
def invertedBy (X : Subgroup M) (t : M) : Set M :=
  {x | x ∈ X ∧ t * x * t = x⁻¹}

namespace invertedBy

variable {t : M} {X : Subgroup M}

lemma mem_iff {x : M} : x ∈ invertedBy X t ↔ x ∈ X ∧ t * x * t = x⁻¹ := Iff.rfl

/-- Elements of a finite subgroup of odd order have odd order. -/
lemma odd_orderOf_of_mem [Finite M] (hodd : Odd (Nat.card X)) {a : M}
    (ha : a ∈ X) : Odd (orderOf a) := by
  have key : orderOf a = orderOf (⟨a, ha⟩ : X) :=
    orderOf_injective X.subtype X.subtype_injective ⟨a, ha⟩
  have hdvd : orderOf a ∣ Nat.card X := by rw [key]; exact orderOf_dvd_natCard _
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ orderOf a := Nat.dvd_of_mod_eq_zero (by omega)
  have hd2 : (2 : ℕ) ∣ Nat.card X := h2.trans hdvd
  have := Nat.odd_iff.mp hodd
  omega

/-- `a^{|X|} = 1` for `a ∈ X` (Lagrange). -/
lemma pow_card_eq_one_of_mem [Finite M] {a : M} (ha : a ∈ X) :
    a ^ Nat.card X = 1 := by
  have key : orderOf a = orderOf (⟨a, ha⟩ : X) :=
    orderOf_injective X.subtype X.subtype_injective ⟨a, ha⟩
  have hdvd : orderOf a ∣ Nat.card X := by rw [key]; exact orderOf_dvd_natCard _
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

/-- For `a ∈ X` (odd order), `(a^{(|X|+1)/2})² = a`. -/
lemma sq_pow_half [Finite M] (hodd : Odd (Nat.card X)) {a : M} (ha : a ∈ X) :
    (a ^ ((Nat.card X + 1) / 2)) ^ 2 = a := by
  rw [← pow_mul]
  obtain ⟨j, hj⟩ := hodd
  rw [show (Nat.card X + 1) / 2 * 2 = Nat.card X + 1 from by omega, pow_succ,
    pow_card_eq_one_of_mem ha, one_mul]

/-- For `a ∈ X` (odd order), `(a²)^{(|X|+1)/2} = a`. -/
lemma pow_half_sq [Finite M] (hodd : Odd (Nat.card X)) {a : M} (ha : a ∈ X) :
    (a ^ 2) ^ ((Nat.card X + 1) / 2) = a := by
  rw [← pow_mul]
  obtain ⟨j, hj⟩ := hodd
  rw [show 2 * ((Nat.card X + 1) / 2) = Nat.card X + 1 from by omega, pow_succ,
    pow_card_eq_one_of_mem ha, one_mul]

/-- If `t` inverts `a` then it inverts every power of `a`. -/
lemma t_conj_pow (ht : t * t = 1) {a : M} (hinv : t * a * t = a⁻¹) (n : ℕ) :
    t * a ^ n * t = (a ^ n)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * a ^ n * t = t * a ^ n * t⁻¹ := by rw [ht']
    _ = (t * a * t⁻¹) ^ n := by rw [conj_pow]
    _ = (a⁻¹) ^ n := by rw [show t * a * t⁻¹ = a⁻¹ from by rw [ht']; exact hinv]
    _ = (a ^ n)⁻¹ := inv_pow a n

/-- `w x = (t x⁻¹ t) x` lies in `X` (as `t` normalizes `X`). -/
lemma w_mem (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M} (hx : x ∈ X) :
    t * x⁻¹ * t * x ∈ X :=
  mul_mem (hnorm x⁻¹ (X.inv_mem hx)) hx

/-- `w x = (t x⁻¹ t) x` is inverted by `t`. -/
lemma w_inverted (ht : t * t = 1) (x : M) :
    t * (t * x⁻¹ * t * x) * t = (t * x⁻¹ * t * x)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hL : t * (t * x⁻¹ * t * x) * t = x⁻¹ * t * x * t := by
    calc t * (t * x⁻¹ * t * x) * t
        = (t * t) * x⁻¹ * t * x * t := by group
      _ = x⁻¹ * t * x * t := by rw [ht, one_mul]
  have hR : (t * x⁻¹ * t * x)⁻¹ = x⁻¹ * t * x * t := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, ht']; group
  rw [hL, hR]

/-- The distinguished odd square root `z = w^{(|X|+1)/2}` of `w = t x⁻¹ t x`. -/
noncomputable def sqrtRoot (X : Subgroup M) (t x : M) : M :=
  (t * x⁻¹ * t * x) ^ ((Nat.card X + 1) / 2)

lemma sqrtRoot_mem_X [Finite M] (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M}
    (hx : x ∈ X) : sqrtRoot X t x ∈ X :=
  X.pow_mem (w_mem hnorm hx) _

/-- `z = sqrtRoot X t x` is inverted by `t`. -/
lemma sqrtRoot_inverted (ht : t * t = 1) (x : M) :
    t * sqrtRoot X t x * t = (sqrtRoot X t x)⁻¹ :=
  t_conj_pow ht (w_inverted ht x) _

/-- `z² = w`, the defining property of the odd square root. -/
lemma sqrtRoot_sq [Finite M] (hodd : Odd (Nat.card X))
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M} (hx : x ∈ X) :
    (sqrtRoot X t x) ^ 2 = t * x⁻¹ * t * x :=
  sq_pow_half hodd (w_mem hnorm hx)

/-- `z ∈ Z`: the square root is inverted by `t` and lies in `X`. -/
lemma sqrtRoot_mem [Finite M] (ht : t * t = 1)
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M} (hx : x ∈ X) :
    sqrtRoot X t x ∈ invertedBy X t :=
  ⟨sqrtRoot_mem_X hnorm hx, sqrtRoot_inverted ht x⟩

/-- `y = x z⁻¹` commutes with `t` (using `z² = w` and `x w⁻¹ = t x t`). -/
lemma yRoot_commute [Finite M] (ht : t * t = 1) (hodd : Odd (Nat.card X))
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M} (hx : x ∈ X) :
    t * (x * (sqrtRoot X t x)⁻¹) * t = x * (sqrtRoot X t x)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set z := sqrtRoot X t x with hz
  have htzt : t * z * t = z⁻¹ := by rw [hz]; exact sqrtRoot_inverted ht x
  have htzi : t * z⁻¹ * t = z := by
    have h2 := congrArg Inv.inv htzt
    rwa [mul_inv_rev, mul_inv_rev, ht', inv_inv, ← mul_assoc] at h2
  have hsq : z ^ 2 = t * x⁻¹ * t * x := by rw [hz]; exact sqrtRoot_sq hodd hnorm hx
  have hzz : z⁻¹ * z⁻¹ = (t * x⁻¹ * t * x)⁻¹ := by rw [← hsq, sq, mul_inv_rev]
  have hwinv : (t * x⁻¹ * t * x)⁻¹ = x⁻¹ * t * x * t := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, ht']; group
  have htxt : t * x * t = x * (z⁻¹ * z⁻¹) := by rw [hzz, hwinv]; group
  have hmul : t * (x * z⁻¹) * t = (t * x * t) * (t * z⁻¹ * t) := by
    have h : (t * x * t) * (t * z⁻¹ * t) = t * x * (t * t) * z⁻¹ * t := by group
    rw [h, ht]; group
  rw [hmul, htxt, htzi]; group

/-- `y = x z⁻¹ ∈ Y = X ⊓ C_M(t)`. -/
lemma yRoot_mem [Finite M] (ht : t * t = 1) (hodd : Odd (Nat.card X))
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) {x : M} (hx : x ∈ X) :
    x * (sqrtRoot X t x)⁻¹ ∈ X ⊓ Subgroup.centralizer ({t} : Set M) := by
  refine Subgroup.mem_inf.mpr ⟨mul_mem hx (X.inv_mem (sqrtRoot_mem_X hnorm hx)), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := yRoot_commute ht hodd hnorm hx
  have e : (x * (sqrtRoot X t x)⁻¹) * t
      = (t * t) * ((x * (sqrtRoot X t x)⁻¹) * t) := by rw [ht, one_mul]
  have e2 : (t * t) * ((x * (sqrtRoot X t x)⁻¹) * t)
      = t * (t * (x * (sqrtRoot X t x)⁻¹) * t) := by group
  change (x * (sqrtRoot X t x)⁻¹) * t = t * (x * (sqrtRoot X t x)⁻¹)
  rw [e, e2, h]

/-- For `y ∈ Y`, `z ∈ Z`, the element `w(yz) = t (yz)⁻¹ t (yz)` equals `z²`. -/
lemma w_of_prod (ht : t * t = 1) {y z : M}
    (hy : y ∈ X ⊓ Subgroup.centralizer ({t} : Set M)) (hz : z ∈ invertedBy X t) :
    t * (y * z)⁻¹ * t * (y * z) = z * z := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hyc : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hyc' : y⁻¹ * t = t * y⁻¹ := by
    have h2 := congrArg Inv.inv hyc
    rw [mul_inv_rev, mul_inv_rev, ht'] at h2
    exact h2.symm
  have hzi : t * z⁻¹ * t = z := by
    have h2 := congrArg Inv.inv hz.2
    rwa [mul_inv_rev, mul_inv_rev, ht', inv_inv, ← mul_assoc] at h2
  have e1 : t * (y * z)⁻¹ * t * (y * z) = t * z⁻¹ * (y⁻¹ * t) * y * z := by
    rw [mul_inv_rev]; group
  have e2 : t * z⁻¹ * (t * y⁻¹) * y * z = (t * z⁻¹ * t) * (y⁻¹ * y) * z := by group
  rw [e1, hyc', e2, hzi, inv_mul_cancel, mul_one]

/-- `sqrtRoot X t (yz) = z` for `y ∈ Y`, `z ∈ Z` (the inverse map recovers `z`). -/
lemma sqrtRoot_prod [Finite M] (ht : t * t = 1) (hodd : Odd (Nat.card X))
    {y z : M} (hy : y ∈ X ⊓ Subgroup.centralizer ({t} : Set M))
    (hz : z ∈ invertedBy X t) : sqrtRoot X t (y * z) = z := by
  simp only [sqrtRoot]
  rw [w_of_prod ht hy hz, ← sq, pow_half_sq hodd hz.1]

end invertedBy

open invertedBy in
/-- **Peterfalvi Part II, Ch. I §1, the Lemma (a)** (p. 101) — for a finite
group `M`, an involution `t`, and a subgroup `X` of odd order normalized by
`t`, the multiplication map `(y, z) ↦ yz` is a bijection from `Y × Z` onto `X`,
where `Y = C_X(t)` and `Z = {x ∈ X | tˣt = x⁻¹}`. -/
noncomputable def invertedProdEquiv {M : Type*} [Group M] [Finite M] {t : M}
    {X : Subgroup M} (ht : t * t = 1) (hodd : Odd (Nat.card X))
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) :
    ↥(X ⊓ Subgroup.centralizer ({t} : Set M)) × ↥(invertedBy X t) ≃ ↥X where
  toFun p := ⟨(p.1 : M) * (p.2 : M),
    mul_mem (Subgroup.mem_inf.mp p.1.2).1 p.2.2.1⟩
  invFun x := (⟨(x : M) * (sqrtRoot X t x)⁻¹, yRoot_mem ht hodd hnorm x.2⟩,
    ⟨sqrtRoot X t x, sqrtRoot_mem ht hnorm x.2⟩)
  left_inv := by
    rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    have hzeq : sqrtRoot X t (y * z) = z := sqrtRoot_prod ht hodd hy hz
    have h1 : (y * z) * (sqrtRoot X t (y * z))⁻¹ = y := by rw [hzeq]; group
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨h1, hzeq⟩
  right_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    change (x * (sqrtRoot X t x)⁻¹) * sqrtRoot X t x = x
    group

/-- **Peterfalvi Part II, Ch. I §1, the Lemma (a)** (p. 101), cardinality —
`|X| = |Y||Z|` with `Y = C_X(t)`, `Z = {x ∈ X | tˣt = x⁻¹}`. -/
theorem card_eq_card_centralizer_mul_ncard_invertedBy {M : Type*} [Group M]
    [Finite M] {t : M} {X : Subgroup M} (ht : t * t = 1) (hodd : Odd (Nat.card X))
    (hnorm : ∀ x ∈ X, t * x * t ∈ X) :
    Nat.card X = Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set M)) *
      (invertedBy X t).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_prod,
    Nat.card_congr (invertedProdEquiv ht hodd hnorm)]

end OddOrder.Peterfalvi.Appendices.Suzuki
