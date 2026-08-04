/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A `p`-power-order operator in characteristic `p` has a nonzero fixed vector

**Navarro (2.32)** says that `O_p(G)` acts trivially on every simple `kG`-module when
`char k = p`.  The engine of that statement — and the only place characteristic `p` enters — is
the one-operator case recorded here:

if `T ^ (p ^ n) = 1` on a nonzero module over a ring of characteristic `p`, then `T` fixes a
nonzero vector.

The reason is the freshman's dream: `T` commutes with `1`, so `(T - 1) ^ (p ^ n) = T ^ (p ^ n) - 1
= 0`, and a nilpotent endomorphism of a nonzero module cannot be injective.

Applied to a central element of order `p` in a `p`-group, this starts the induction that proves
(2.32); the module of fixed vectors is then a module for the quotient by that element.

## Main results

* `OddOrder.charP_moduleEnd` — `End k M` has characteristic `p` when `k` does
* `OddOrder.exists_ne_zero_fixed_of_pow_eq_one`
-/

namespace OddOrder

variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

/-- If `p` kills `k` then it kills `End k M`, so — for `M` nontrivial and `p` prime — the
endomorphism ring has characteristic `p`. -/
theorem charP_moduleEnd {p : ℕ} [Fact p.Prime] [Nontrivial M] (hchar : (p : k) = 0) :
    CharP (Module.End k M) p := by
  have h0 : ((p : ℕ) : Module.End k M) = 0 := by
    rw [← map_natCast (algebraMap k (Module.End k M)) p, hchar, map_zero]
  obtain ⟨q, hq⟩ := CharP.exists (Module.End k M)
  haveI := hq
  have hdvd : q ∣ p := (CharP.cast_eq_zero_iff _ q p).mp h0
  have hq1 : q ≠ 1 := by
    rintro rfl
    have h1 : ((1 : ℕ) : Module.End k M) = 0 := (CharP.cast_eq_zero_iff _ 1 1).mpr dvd_rfl
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd q hdvd with h | h
  · exact absurd h hq1
  · rwa [h] at hq

/-- **An operator of `p`-power order on a nonzero module in characteristic `p` fixes a nonzero
vector.**  `(T - 1) ^ (p ^ n) = T ^ (p ^ n) - 1 = 0` by the freshman's dream, and a nilpotent
endomorphism of a nonzero module is not injective. -/
theorem exists_ne_zero_fixed_of_pow_eq_one {p : ℕ} [Fact p.Prime] [Nontrivial M]
    (hchar : (p : k) = 0) {T : Module.End k M} {n : ℕ} (hT : T ^ p ^ n = 1) :
    ∃ v : M, v ≠ 0 ∧ T v = v := by
  haveI := charP_moduleEnd (M := M) (p := p) hchar
  haveI : ExpChar (Module.End k M) p := ExpChar.prime Fact.out
  have hnil : (T - 1) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow_of_commute _ _ (Commute.one_right T), hT, one_pow, sub_self]
  set S : Module.End k M := T - 1 with hS
  have key : ∀ N : ℕ, ∀ v : M, v ≠ 0 → (S ^ N) v = 0 → ∃ w : M, w ≠ 0 ∧ S w = 0 := by
    intro N
    induction N with
    | zero => intro v hv h0; rw [pow_zero] at h0; exact absurd h0 hv
    | succ N ih =>
      intro v hv h0
      by_cases hSv : S v = 0
      · exact ⟨v, hv, hSv⟩
      · refine ih (S v) hSv ?_
        rw [← Module.End.mul_apply, ← pow_succ]
        exact h0
  obtain ⟨u, hu⟩ := exists_ne (0 : M)
  obtain ⟨w, hw, hSw⟩ := key (p ^ n) u hu (by rw [hS, hnil]; simp)
  refine ⟨w, hw, ?_⟩
  have : (T - 1) w = 0 := hSw
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

end OddOrder
