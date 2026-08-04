/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Navarro (5.7): the trace vanishes

The endgame of Navarro's proof of (5.7).  On the module `M` affording `χ`, write `E` for the
action of the block idempotent `f_b`, `Φ` for the action of `h`, and `S` for the action of the
eigenvector `s` of `TwistedLayerSum`.  Then `Φ S = ζ S Φ`, and `χ(f_b h)` is the trace of `E Φ`.

Navarro argues that `α` and `ζα` occur with equal multiplicity as eigenvalues of `h` on
`V = M f_b` (multiplication by `s` injects one eigenspace into the next), so that the eigenvalues
fall into `⟨ζ⟩`-orbits summing to zero.  **That is exactly the statement that `H` and `ζ H` are
similar**, and traces are similarity invariants — so the eigenvalue bookkeeping can be replaced by

`trace H = trace (T⁻¹ (H T)) = trace (ζ H) = ζ · trace H`,

which forces `trace H = 0` because `ζ ≠ 1`.  No diagonalisation, no multiplicities, no orbit
counting.

Working with `H = E Φ` on all of `M` rather than with `Φ` restricted to `V = range E` also removes
the direct sum decomposition `M = V ⊕ M(1 - f_b)`: the intertwiner is `T = S + 1 - E`, which is
`S` on `V` and the identity off it, and `(EΦ) T = ζ · T (EΦ)` holds on the nose.

## Main results

* `OddOrder.trace_eq_zero_of_conj_smul` — `H T = ζ (T H)` with `T` injective forces `trace H = 0`
* `OddOrder.trace_idempotent_mul_eq_zero` — Navarro (5.7): `χ(f_b h) = 0`
-/

namespace OddOrder

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **A twisted intertwiner kills the trace.**  If `H T = ζ (T H)` with `T` injective, then `H` is
similar to `ζ H`, so `trace H = ζ · trace H`; as `ζ ≠ 1` the trace vanishes.

This is the content of Navarro's "`α` and `ωα` have equal multiplicities", packaged as a
similarity instead of an eigenvalue count. -/
theorem trace_eq_zero_of_conj_smul {ζ : K} (hζ : ζ ≠ 1) {H T : Module.End K M}
    (hT : Function.Injective T) (hcomm : H * T = ζ • (T * H)) :
    LinearMap.trace K M H = 0 := by
  obtain ⟨u, hu⟩ : IsUnit T :=
    (LinearMap.isUnit_iff_ker_eq_bot T).mpr (LinearMap.ker_eq_bot.mpr hT)
  have hUT : (↑u⁻¹ : Module.End K M) * T = 1 := by rw [← hu]; exact u.inv_mul
  have hTU : T * (↑u⁻¹ : Module.End K M) = 1 := by rw [← hu]; exact u.mul_inv
  have key : LinearMap.trace K M H = ζ * LinearMap.trace K M H := by
    calc LinearMap.trace K M H
        = LinearMap.trace K M (H * T * (↑u⁻¹ : Module.End K M)) := by
          rw [mul_assoc, hTU, mul_one]
      _ = LinearMap.trace K M ((↑u⁻¹ : Module.End K M) * (H * T)) :=
          LinearMap.trace_mul_comm K (H * T) _
      _ = LinearMap.trace K M (ζ • H) := by
          rw [hcomm, mul_smul_comm, ← mul_assoc, hUT, one_mul]
      _ = ζ * LinearMap.trace K M H := by rw [map_smul, smul_eq_mul]
  have hsub : (1 - ζ) * LinearMap.trace K M H = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h).symm hζ
  · exact h

/-- **Navarro (5.7).**  Let `E` be an idempotent commuting with `Φ`, let `S` satisfy `E S = S E = S`
and `Φ S = ζ S Φ`, and suppose `S` is injective on the image of `E`.  Then `trace (E Φ) = 0`.

With `E` the action of `f_b`, `Φ` that of `h` and `S` that of `s`, this is `χ(f_b h) = 0`. -/
theorem trace_idempotent_mul_eq_zero {ζ : K} (hζ : ζ ≠ 1) {E Φ S : Module.End K M}
    (hE : E * E = E) (hEΦ : E * Φ = Φ * E) (hES : E * S = S) (hSE : S * E = S)
    (hΦS : Φ * S = ζ • (S * Φ))
    (hinj : ∀ v : M, E v = v → S v = 0 → v = 0) :
    LinearMap.trace K M (E * Φ) = 0 := by
  set T : Module.End K M := S + 1 - E with hTdef
  -- `E T = S`, which is what makes `T` injective and the twisted relation hold
  have hET : E * T = S := by
    rw [hTdef, mul_sub, mul_add, hES, mul_one, hE, add_sub_cancel_right]
  have hTinj : Function.Injective (T : M → M) := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
    have h1 : E (T v) = S v := by
      have := congrArg (fun f : Module.End K M => f v) hET
      simpa [Module.End.mul_apply] using this
    have hSv : S v = 0 := by rw [← h1, hv, map_zero]
    have hTv : S v + v - E v = 0 := by
      have h2 := hv
      rw [hTdef] at h2
      simpa using h2
    refine hinj v ?_ hSv
    have h3 : v - E v = 0 := by rw [← hTv, hSv]; abel
    exact (sub_eq_zero.mp h3).symm
  refine trace_eq_zero_of_conj_smul hζ hTinj ?_
  have hEΦT : (E * Φ) * T = ζ • (S * Φ) := by
    rw [hTdef, mul_sub, mul_add, mul_one, mul_assoc, hΦS, mul_smul_comm, ← mul_assoc, hES,
      mul_assoc, ← hEΦ, ← mul_assoc, hE, add_sub_cancel_right]
  have hTEΦ : T * (E * Φ) = S * Φ := by
    rw [hTdef, sub_mul, add_mul, one_mul, ← mul_assoc, hSE, ← mul_assoc, hE,
      add_sub_cancel_right]
  rw [hEΦT, hTEΦ]

end OddOrder
