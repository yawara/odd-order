/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Algebraic-integer congruences in `ℂ`

This module formalizes the **congruence modulo an integer in the algebraic integers**, the relation
written `α ≡ β (mod n)` throughout **Peterfalvi, _Character Theory for the Odd Order Theorem_** (LMS
LNS 272, 2000), notably in the proof of **(6.7)** (pp. 31–32), where:

> The notation `α ≡ β (mod |P|)` means that `α`, `β` and `(α - β)/|P|` are algebraic integers.

We take as the basic relation the load-bearing component: `(α - β) / n` is an algebraic integer over
`ℤ` (the endpoints `α`, `β` being algebraic integers is, in the §6 applications, established
separately — e.g. character values are algebraic integers, `character_isIntegral`).  Concretely

  `AlgInt.Cong n α β  :=  IsIntegral ℤ ((α - β) / (n : ℂ))`.

This is an additive congruence: it is reflexive, symmetric, transitive, closed under addition of
congruences, and closed under multiplication of one side by *any* algebraic integer (in particular
by an integer or by another central-character / structure-constant value, which is exactly how
Peterfalvi (6.7.2)/(6.7.3) manipulate it: multiply through by `ψ(1)`, by `a_{ij}`, ...).

## Main definitions and results

* `OddOrder.AlgInt.Cong` — the congruence `α ≡ β (mod n)` on `ℂ`, parameterized by `n : ℤ`.
* `OddOrder.AlgInt.Cong.refl` / `.symm` / `.trans` — equivalence-relation laws.
* `OddOrder.AlgInt.Cong.add` — congruences add: `a ≡ b`, `c ≡ d` ⇒ `a + c ≡ b + d (mod n)`.
* `OddOrder.AlgInt.Cong.sub` — congruences subtract.
* `OddOrder.AlgInt.Cong.smul_left` — scale by an algebraic integer `k`: `a ≡ b` ⇒ `k·a ≡ k·b`.
* `OddOrder.AlgInt.Cong.intMul_left` — the special case `k ∈ ℤ`.
* `OddOrder.AlgInt.cong_of_sub_eq_intMul` / `cong_of_exists_isIntegral` — introduction forms: if
  `α - β = n · c` with `c` an algebraic integer (e.g. `α - β` is a `ℤ`-multiple of `n`), then
  `α ≡ β (mod n)`.
* `OddOrder.AlgInt.Cong.of_int` — for integers `j k : ℤ`, the algebraic-integer congruence is
  implied by the ordinary integer congruence `n ∣ j - k`.

## Notation

`α ≡ β [ALGMOD n]` (scoped in `OddOrder.AlgInt`) denotes `OddOrder.AlgInt.Cong n α β`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem*, LMS LNS 272 (2000), proof of (6.7),
  pp. 31–32.
-/

namespace OddOrder.AlgInt

/-- **Algebraic-integer congruence in `ℂ`** (Peterfalvi, proof of (6.7)): `α ≡ β (mod n)` means
`(α - β) / n` is an algebraic integer over `ℤ`.  (In Peterfalvi's full notation one additionally
requires `α` and `β` to be algebraic integers; in the §6 applications that part is supplied
separately, e.g. by `character_isIntegral`.) -/
def Cong (n : ℤ) (α β : ℂ) : Prop :=
  IsIntegral ℤ ((α - β) / (n : ℂ))

@[inherit_doc Cong] scoped notation3:50 α " ≡ " β " [ALGMOD " n "]" => Cong n α β

variable {n : ℤ} {a b c d : ℂ}

theorem cong_def (n : ℤ) (α β : ℂ) : (α ≡ β [ALGMOD n]) ↔ IsIntegral ℤ ((α - β) / (n : ℂ)) :=
  Iff.rfl

namespace Cong

/-- Reflexivity: `α ≡ α (mod n)`, since `(α - α)/n = 0` is integral. -/
@[refl] theorem refl (n : ℤ) (α : ℂ) : α ≡ α [ALGMOD n] := by
  unfold Cong
  rw [sub_self, zero_div]
  exact isIntegral_zero

/-- Symmetry: `α ≡ β (mod n)` ⇒ `β ≡ α (mod n)`, via `(β - α)/n = -((α - β)/n)`. -/
@[symm] theorem symm (h : a ≡ b [ALGMOD n]) : b ≡ a [ALGMOD n] := by
  unfold Cong at h ⊢
  rw [show (b - a) / (n : ℂ) = -((a - b) / (n : ℂ)) by ring]
  exact h.neg

theorem comm : (a ≡ b [ALGMOD n]) ↔ (b ≡ a [ALGMOD n]) :=
  ⟨Cong.symm, Cong.symm⟩

/-- Transitivity: `α ≡ β` and `β ≡ γ` ⇒ `α ≡ γ (mod n)`, via
`(α - γ)/n = (α - β)/n + (β - γ)/n`. -/
@[trans] theorem trans (hab : a ≡ b [ALGMOD n]) (hbc : b ≡ c [ALGMOD n]) :
    a ≡ c [ALGMOD n] := by
  unfold Cong at hab hbc ⊢
  rw [show (a - c) / (n : ℂ) = (a - b) / (n : ℂ) + (b - c) / (n : ℂ) by ring]
  exact hab.add hbc

/-- Congruences add: `a ≡ b` and `c ≡ d` ⇒ `a + c ≡ b + d (mod n)`. -/
theorem add (hab : a ≡ b [ALGMOD n]) (hcd : c ≡ d [ALGMOD n]) :
    a + c ≡ b + d [ALGMOD n] := by
  unfold Cong at hab hcd ⊢
  rw [show (a + c - (b + d)) / (n : ℂ) = (a - b) / (n : ℂ) + (c - d) / (n : ℂ) by ring]
  exact hab.add hcd

/-- Congruences subtract: `a ≡ b` and `c ≡ d` ⇒ `a - c ≡ b - d (mod n)`. -/
theorem sub (hab : a ≡ b [ALGMOD n]) (hcd : c ≡ d [ALGMOD n]) :
    a - c ≡ b - d [ALGMOD n] := by
  unfold Cong at hab hcd ⊢
  rw [show (a - c - (b - d)) / (n : ℂ) = (a - b) / (n : ℂ) - (c - d) / (n : ℂ) by ring]
  exact hab.sub hcd

/-- Negation: `a ≡ b (mod n)` ⇒ `-a ≡ -b (mod n)`. -/
theorem neg (h : a ≡ b [ALGMOD n]) : -a ≡ -b [ALGMOD n] := by
  unfold Cong at h ⊢
  rw [show (-a - -b) / (n : ℂ) = -((a - b) / (n : ℂ)) by ring]
  exact h.neg

/-- Scale by an algebraic integer on the left: if `k` is an algebraic integer and `a ≡ b (mod n)`,
then `k·a ≡ k·b (mod n)`, via `(k·a - k·b)/n = k·((a - b)/n)`.

This is the central multiplicative step in Peterfalvi (6.7.2)/(6.7.3): one multiplies a congruence
through by `ψ(1)`, by a structure constant `a_{ij}`, or by another integral central-character value,
all of which are algebraic integers. -/
theorem smul_left {k : ℂ} (hk : IsIntegral ℤ k) (h : a ≡ b [ALGMOD n]) :
    k * a ≡ k * b [ALGMOD n] := by
  unfold Cong at h ⊢
  rw [show (k * a - k * b) / (n : ℂ) = k * ((a - b) / (n : ℂ)) by ring]
  exact hk.mul h

/-- Scale by an algebraic integer on the right: `a ≡ b (mod n)` ⇒ `a·k ≡ b·k (mod n)`. -/
theorem smul_right {k : ℂ} (hk : IsIntegral ℤ k) (h : a ≡ b [ALGMOD n]) :
    a * k ≡ b * k [ALGMOD n] := by
  simpa [mul_comm] using h.smul_left hk

/-- Scale by an integer on the left: `a ≡ b (mod n)` ⇒ `(k : ℂ)·a ≡ (k : ℂ)·b (mod n)`. -/
theorem intMul_left (k : ℤ) (h : a ≡ b [ALGMOD n]) :
    (k : ℂ) * a ≡ (k : ℂ) * b [ALGMOD n] :=
  h.smul_left (isIntegral_algebraMap (x := k))

/-- Scale by an integer on the right: `a ≡ b (mod n)` ⇒ `a·(k : ℂ) ≡ b·(k : ℂ) (mod n)`. -/
theorem intMul_right (k : ℤ) (h : a ≡ b [ALGMOD n]) :
    a * (k : ℂ) ≡ b * (k : ℂ) [ALGMOD n] :=
  h.smul_right (isIntegral_algebraMap (x := k))

/-- Scale by a natural number on the left: `a ≡ b (mod n)` ⇒ `(k : ℂ)·a ≡ (k : ℂ)·b (mod n)`.
Used for the factorization-count coefficients `a_{ijs} ∈ ℕ` of Peterfalvi (6.7.2). -/
theorem natMul_left (k : ℕ) (h : a ≡ b [ALGMOD n]) :
    (k : ℂ) * a ≡ (k : ℂ) * b [ALGMOD n] := by
  have := h.intMul_left (k : ℤ)
  simpa using this

/-- **Cancel a coprime integer factor from a congruence.** If `(c : ℂ)·a ≡ (c : ℂ)·b (mod n)` with
`c` coprime to the modulus `n` (as integers), and the endpoints `a`, `b` are themselves algebraic
integers, then `a ≡ b (mod n)`.

This is the "divide by `|C₁|`" step of Peterfalvi (6.7.3): `|C₁|` is prime to `p` (hence coprime to
`n = |P| = p^k`), so it may be cancelled from a congruence modulo `|P|`.  The endpoint-integrality
hypotheses are essential and are supplied by `character_isIntegral` (`a = ψ(z)`, `b = ψ(1)`).
Bézout `u·c + v·n = 1` writes `(a-b)/n = u·(c·(a-b)/n) + v·(a-b)`, integral since both
`c·(a-b)/n = (c·a - c·b)/n` and `a - b` are integral. -/
theorem intMul_cancel_left {c : ℤ} (hcop : IsCoprime c n) (ha : IsIntegral ℤ a)
    (hb : IsIntegral ℤ b) (h : (c : ℂ) * a ≡ (c : ℂ) * b [ALGMOD n]) :
    a ≡ b [ALGMOD n] := by
  unfold Cong at h ⊢
  obtain ⟨u, v, huv⟩ := hcop
  -- `t := (a - b)/n`; the hypothesis gives `c·t` integral, and `a - b` is integral.
  set t : ℂ := (a - b) / (n : ℂ) with ht
  have hct : IsIntegral ℤ ((c : ℂ) * t) := by
    have : ((c : ℂ) * a - (c : ℂ) * b) / (n : ℂ) = (c : ℂ) * t := by rw [ht]; ring
    rwa [this] at h
  have hab : IsIntegral ℤ (a - b) := ha.sub hb
  -- `t = u·(c·t) + v·(a - b)` by Bézout `u·c + v·n = 1` (note `n·t = a - b` after clearing).
  by_cases hn0 : (n : ℂ) = 0
  · -- `n = 0`: then `t = (a-b)/0 = 0`, integral.
    rw [ht, hn0, div_zero]; exact isIntegral_zero
  · have hnt : (n : ℂ) * t = a - b := by
      rw [ht]; field_simp
    have hbez : (u : ℂ) * (c : ℂ) + (v : ℂ) * (n : ℂ) = 1 := by
      have hc : ((u * c + v * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [huv]
      push_cast at hc; linear_combination hc
    have hrw : t = (u : ℂ) * ((c : ℂ) * t) + (v : ℂ) * (a - b) := by
      have hcollect : (u : ℂ) * ((c : ℂ) * t) + (v : ℂ) * (a - b)
          = ((u : ℂ) * (c : ℂ) + (v : ℂ) * (n : ℂ)) * t := by rw [← hnt]; ring
      rw [hcollect, hbez, one_mul]
    rw [hrw]
    exact ((isIntegral_algebraMap (x := u)).mul hct).add
      ((isIntegral_algebraMap (x := v)).mul hab)

end Cong

/-- **Introduction form.** If `α - β = n · c` with `c` an algebraic integer, then `α ≡ β (mod n)`,
provided `n ≠ 0` (so that `(α - β)/n = c`).  This is how congruences are *produced* in the §6
arguments: one exhibits the difference as `n` times an integral element. -/
theorem cong_of_exists_isIntegral (hn : (n : ℂ) ≠ 0) {c : ℂ} (hc : IsIntegral ℤ c)
    (h : a - b = (n : ℂ) * c) : a ≡ b [ALGMOD n] := by
  unfold Cong
  rw [h, mul_div_cancel_left₀ _ hn]
  exact hc

/-- **Introduction form, integer multiple.** If `α - β = (n · k : ℤ)` (cast to `ℂ`) for some
`k : ℤ`, then `α ≡ β (mod n)` (`n ≠ 0`): the difference being a `ℤ`-multiple of `n` makes the
quotient the integer `k`, an algebraic integer.  (The multiple is passed as an integer `k` whose
cast is supplied through `h`, so no integer cast appears in the statement's right-hand product.) -/
theorem cong_of_sub_eq_intMul (hn : (n : ℂ) ≠ 0) {k : ℤ} (h : a - b = (n : ℂ) * (k : ℂ)) :
    a ≡ b [ALGMOD n] :=
  cong_of_exists_isIntegral hn (c := (k : ℂ)) (isIntegral_algebraMap (x := k)) h

/-- **From an ordinary integer congruence.** For integers `j k : ℤ` with `n ∣ j - k`, the cast
values satisfy the algebraic-integer congruence `(j : ℂ) ≡ (k : ℂ) (mod n)` (`n ≠ 0`). -/
theorem Cong.of_int (hn : (n : ℂ) ≠ 0) {j k : ℤ} (h : n ∣ j - k) :
    Cong n (j : ℂ) (k : ℂ) := by
  obtain ⟨m, hm⟩ := h
  refine cong_of_sub_eq_intMul hn (k := m) ?_
  have hc : ((j - k : ℤ) : ℂ) = ((n * m : ℤ) : ℂ) := by rw [hm]
  push_cast at hc ⊢
  linear_combination hc

end OddOrder.AlgInt
