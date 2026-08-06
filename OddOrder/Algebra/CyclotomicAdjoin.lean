/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import OddOrder.Algebra.AdicCompletePi

/-!
# The cyclotomic extension `A[ζ_n] = A[X]/Φ_n`

The coefficient ring of the modular character theory has to satisfy two competing demands
(issue 9506): its residue field must be algebraically closed of characteristic `p` — which
`𝕎(𝔽̄_p)` provides — and its fraction field must contain `ζ_{exp G}`, which `𝕎(𝔽̄_p)` does *not*
when `p` divides `exp G`.  The fix is the ramified extension `A[ζ_{p^a}]`, presented here as
`A[X]/Φ_{p^a}`.

What this file supplies is the *module-theoretic* half, which is all that the completeness argument
needs: `Φ_n` is monic, so `A[X]/Φ_n` is free of rank `deg Φ_n` over `A`, and a finite free module
over an `I`-adically complete ring is `I`-adically complete (`isAdicComplete_of_basis`).

Combined with `isAdicComplete_of_le_of_pow_le` — and with `𝔪_B^{φ(p^a)} ⊆ 𝔪_A·B`, which comes from
`Φ_{p^a} ≡ (X-1)^{φ(p^a)}` in characteristic `p` — this gives `IsAdicComplete (maximalIdeal B) B`,
the hypothesis that the block idempotents are lifted along.

## Main results

* `OddOrder.Algebra.cyclotomicPowerBasis` — the power basis `1, ζ, …, ζ^{deg Φ_n - 1}`
* `OddOrder.Algebra.isAdicComplete_cyclotomicAdjoin` — `A[ζ_n]` inherits `I`-adic completeness
* `OddOrder.Algebra.cyclotomic_prime_pow_charP` — `Φ_{p^k} = (X-1)^{p^k - p^{k-1}}` in
  characteristic `p` (the exponent is `φ(p^k)`)
-/

namespace OddOrder.Algebra

open Polynomial

variable (n : ℕ) (A : Type*) [CommRing A]

/-- **The power basis `1, ζ, …, ζ^{deg Φ_n - 1}` of `A[X]/Φ_n`.**  The cyclotomic polynomial is
monic, so the quotient is free on the powers of the root. -/
noncomputable def cyclotomicPowerBasis : PowerBasis A (AdjoinRoot (cyclotomic n A)) :=
  AdjoinRoot.powerBasis' (cyclotomic.monic n A)

instance : Module.Free A (AdjoinRoot (cyclotomic n A)) :=
  Module.Free.of_basis (cyclotomicPowerBasis n A).basis

instance : Module.Finite A (AdjoinRoot (cyclotomic n A)) :=
  Module.Finite.of_basis (cyclotomicPowerBasis n A).basis

/-- **`A[ζ_n]` is `I`-adically complete when `A` is** — it is a finite free `A`-module. -/
theorem isAdicComplete_cyclotomicAdjoin (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete I (AdjoinRoot (cyclotomic n A)) :=
  isAdicComplete_of_basis I (Finite.of_fintype _) (cyclotomicPowerBasis n A).basis

/-- **`Φ_{p^k} = (X - 1)^{φ(p^k)}` in characteristic `p`.**  Specialisation of
`Polynomial.cyclotomic_mul_prime_pow_eq` at `m = 1`, where `Φ_1 = X - 1`.

This is what makes `A[ζ_{p^k}] ⧸ 𝔪_A` a local Artinian ring — hence `A[ζ_{p^k}]` local — and
`𝔪_B^{φ(p^k)} ⊆ 𝔪_A·B`, the totally ramified estimate that `isAdicComplete_of_le_of_pow_le`
consumes. -/
theorem cyclotomic_prime_pow_charP (R : Type*) [CommRing R] {q k : ℕ} [Fact (Nat.Prime q)]
    [CharP R q] (hk : 0 < k) :
    cyclotomic (q ^ k) R = (X - 1) ^ (q ^ k - q ^ (k - 1)) := by
  have h := cyclotomic_mul_prime_pow_eq R (p := q) (m := 1)
    (by simpa [Nat.dvd_one] using (Fact.out : Nat.Prime q).ne_one) hk
  rwa [mul_one, cyclotomic_one] at h

end OddOrder.Algebra
