/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Conjugacy of commuting coprime products

This module collects the elementary group-theoretic counting facts needed for
the **Dade isometry** (Peterfalvi §4, in particular the adjoint formula (2.7)).

The setting throughout is: an element `a : G` and a subgroup `H ≤ C_G(a)` whose
order is coprime to `orderOf a`.  For `x ∈ H` the product `a * x` then behaves
like a coprime decomposition into a "`π`-part" `a` and a "`π'`-part" `x`, even
though we never introduce a genuine prime-set decomposition: instead a single
exponent `k`, produced by the Chinese remainder theorem, simultaneously fixes
`a` and kills every element of `H`.

## Main results

* `OddOrder.GroupTheory.exists_pow_eq_self_and_forall_pow_eq_one` — the CRT
  exponent `k` with `a ^ k = a` and `x ^ k = 1` for all `x` of order dividing
  `n` (`n` coprime to `orderOf a`).
* `OddOrder.GroupTheory.conj_fixes_of_commute` — **conjugacy rigidity**: if
  `a * x` is conjugate to `a * x'` (with `x, x'` of order dividing such an `n`,
  both commuting with `a`), then the conjugator already centralizes `a`, and
  conjugates `x` to `x'`.

Reference note: `notes/peterfalvi/s04_dade_isometry.md`.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- The Chinese-remainder exponent: if `n` is coprime to `orderOf a`, there is a
single exponent `k` with `a ^ k = a` that simultaneously sends every element of
order dividing `n` to `1`.

This is the elementary substitute for "raising to the `π`-part" used throughout
Peterfalvi §4: with `H ≤ C_G(a)` of order coprime to `orderOf a`, taking `k`-th
powers extracts the `a`-component of `a * x` for `x ∈ H`. -/
theorem exists_pow_eq_self_and_forall_pow_eq_one (a : G) {n : ℕ}
    (hn : Nat.Coprime (orderOf a) n) :
    ∃ k : ℕ, a ^ k = a ∧ ∀ x : G, orderOf x ∣ n → x ^ k = 1 := by
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hn 1 0
  refine ⟨k, ?_, ?_⟩
  · have : a ^ k = a ^ 1 := pow_eq_pow_iff_modEq.mpr hk1
    simpa using this
  · intro x hx
    have hnk : n ∣ k := (Nat.modEq_zero_iff_dvd).mp hk0
    exact orderOf_dvd_iff_pow_eq_one.mp (hx.trans hnk)

/-- **Conjugacy rigidity** for commuting coprime products.

If `a * x` is conjugate (by `t`) to `a * x'`, where `x` and `x'` commute with `a`
and have orders dividing some `n` coprime to `orderOf a`, then `t` already
centralizes `a` and conjugates `x` to `x'`.

This is the formal content of Peterfalvi's "`a = (a x)_π` is conjugate to
`b = (b v)_π`" step. -/
theorem conj_fixes_of_commute {a x x' t : G} (hx : Commute a x) (hx' : Commute a x')
    {n : ℕ} (hn : Nat.Coprime (orderOf a) n)
    (hxn : orderOf x ∣ n) (hx'n : orderOf x' ∣ n)
    (hconj : t * (a * x) * t⁻¹ = a * x') :
    t * a * t⁻¹ = a ∧ t * x * t⁻¹ = x' := by
  obtain ⟨k, hak, hone⟩ := exists_pow_eq_self_and_forall_pow_eq_one a hn
  have hfix : t * a * t⁻¹ = a := by
    have hpow : (t * (a * x) * t⁻¹) ^ k = (a * x') ^ k := by rw [hconj]
    rw [conj_pow, hx.mul_pow, hx'.mul_pow, hak, hone x hxn, hone x' hx'n,
      mul_one] at hpow
    exact hpow
  refine ⟨hfix, mul_left_cancel (a := a) ?_⟩
  calc a * (t * x * t⁻¹)
      = (t * a * t⁻¹) * (t * x * t⁻¹) := by rw [hfix]
    _ = t * (a * x) * t⁻¹ := by group
    _ = a * x' := hconj

end OddOrder.GroupTheory
