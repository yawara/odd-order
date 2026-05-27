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

/-- The set of elements conjugating a fixed `g₀` to `g` is, when nonempty, a left
coset of the centralizer of `g₀`; hence has the same cardinality. -/
theorem card_conjugatorBy_eq_card_centralizer {g₀ g : G} (h : IsConj g₀ g) :
    Nat.card {t : G // t * g₀ * t⁻¹ = g}
      = Nat.card (Subgroup.centralizer ({g₀} : Set G)) := by
  obtain ⟨t₀, ht₀⟩ := isConj_iff.mp h
  apply Nat.card_congr
  refine
    { toFun := fun t => ⟨t₀⁻¹ * t.1, ?_⟩
      invFun := fun c => ⟨t₀ * c.1, ?_⟩
      left_inv := fun t => by simp
      right_inv := fun c => by simp }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : (t₀⁻¹ * t.1) * g₀ * (t₀⁻¹ * t.1)⁻¹ = g₀ := by
      have e : (t₀⁻¹ * t.1) * g₀ * (t₀⁻¹ * t.1)⁻¹
          = t₀⁻¹ * (t.1 * g₀ * t.1⁻¹) * t₀ := by group
      rw [e, t.2, ← ht₀]; group
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · have hmem := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    change (t₀ * c.1) * g₀ * (t₀ * c.1)⁻¹ = g
    calc (t₀ * c.1) * g₀ * (t₀ * c.1)⁻¹
        = t₀ * (c.1 * g₀ * c.1⁻¹) * t₀⁻¹ := by group
      _ = t₀ * g₀ * t₀⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hmem]
      _ = g := ht₀

/-- **Fiber count for the Dade-map computation.**

Fix `a : G` and a subgroup `H ≤ C_G(a)` of order coprime to `orderOf a`, with
`C_G(a)` normalizing `H`.  For `g` conjugate to some `a * x₀` (`x₀ ∈ H`), the set
of pairs `(x, t)` with `x ∈ H` and `t * (a * x) * t⁻¹ = g` is a single left coset
of `C_G(a)`, hence has cardinality `|C_G(a)|`.

This is the precise content of Peterfalvi's "`𝒜(g, H(a)a) = x C_G(a)`" remark in
the proof of (2.10.3); it drives the inner-product reduction (2.7). -/
theorem card_conj_fiber {a : G} {H : Subgroup G}
    (hcomm : ∀ x ∈ H, Commute a x)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ x ∈ H, c * x * c⁻¹ ∈ H)
    (hcop : Nat.Coprime (orderOf a) (Nat.card H))
    {g x₀ : G} (hx₀H : x₀ ∈ H) (hx₀ : IsConj (a * x₀) g) :
    Nat.card {p : G × G // p.1 ∈ H ∧ p.2 * (a * p.1) * p.2⁻¹ = g}
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  obtain ⟨t₀, ht₀⟩ := isConj_iff.mp hx₀
  have hx₀n : orderOf x₀ ∣ Nat.card H := H.orderOf_dvd_natCard hx₀H
  -- Conjugacy rigidity, packaged for the elements appearing below.
  have key : ∀ x ∈ H, ∀ k : G, k * (a * x) * k⁻¹ = a * x₀ →
      k * a * k⁻¹ = a ∧ k * x * k⁻¹ = x₀ := fun x hx k hk =>
    conj_fixes_of_commute (hcomm x hx) (hcomm x₀ hx₀H) hcop
      (H.orderOf_dvd_natCard hx) hx₀n hk
  have memK : ∀ k : G, k * a * k⁻¹ = a → k ∈ Subgroup.centralizer ({a} : Set G) :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hk)
  have ofK : ∀ k ∈ Subgroup.centralizer ({a} : Set G), k * a * k⁻¹ = a :=
    fun k hk => mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hk)
  refine Nat.card_congr ?_
  refine
    { toFun := fun p => ⟨t₀⁻¹ * p.1.2, memK _ ?_⟩
      invFun := fun k => ⟨(k.1⁻¹ * x₀ * k.1, t₀ * k.1), ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `t₀⁻¹ * t` conjugates `a*x` to `a*x₀`, so it centralizes `a`.
    have hconj : (t₀⁻¹ * p.1.2) * (a * p.1.1) * (t₀⁻¹ * p.1.2)⁻¹ = a * x₀ := by
      have e : (t₀⁻¹ * p.1.2) * (a * p.1.1) * (t₀⁻¹ * p.1.2)⁻¹
          = t₀⁻¹ * (p.1.2 * (a * p.1.1) * p.1.2⁻¹) * t₀ := by group
      rw [e, p.2.2, ← ht₀]; group
    exact (key p.1.1 p.2.1 _ hconj).1
  · -- `k⁻¹ * x₀ * k ∈ H`
    have h := hnorm k.1⁻¹ (Subgroup.inv_mem _ k.2) x₀ hx₀H
    rwa [inv_inv] at h
  · -- `(t₀ k) * (a * (k⁻¹ x₀ k)) * (t₀ k)⁻¹ = g`
    have hk := ofK k.1 k.2
    calc (t₀ * k.1) * (a * (k.1⁻¹ * x₀ * k.1)) * (t₀ * k.1)⁻¹
        = t₀ * ((k.1 * a * k.1⁻¹) * x₀) * t₀⁻¹ := by group
      _ = t₀ * (a * x₀) * t₀⁻¹ := by rw [hk]
      _ = g := ht₀
  · -- left inverse
    rintro ⟨⟨x, t⟩, hx, ht⟩
    have hconj : (t₀⁻¹ * t) * (a * x) * (t₀⁻¹ * t)⁻¹ = a * x₀ := by
      have e : (t₀⁻¹ * t) * (a * x) * (t₀⁻¹ * t)⁻¹
          = t₀⁻¹ * (t * (a * x) * t⁻¹) * t₀ := by group
      rw [e, ht, ← ht₀]; group
    have hx_eq : (t₀⁻¹ * t)⁻¹ * x₀ * (t₀⁻¹ * t) = x := by
      have h2 := (key x hx _ hconj).2
      rw [← h2]; group
    apply Subtype.ext
    apply Prod.ext
    · exact hx_eq
    · change t₀ * (t₀⁻¹ * t) = t; group
  · -- right inverse
    rintro ⟨k, hk⟩
    apply Subtype.ext
    change t₀⁻¹ * (t₀ * k) = k; group

end OddOrder.GroupTheory
