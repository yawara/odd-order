/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# The trace splits along a pair of complementary invariant subspaces

`LinearMap.trace_eq_sum_trace_restrict` splits a trace along an internal direct sum indexed by a
`Fintype`.  In characteristic zero Maschke supplies an *invariant complement* of any invariant
subspace, so the two-summand case is the one that matters for decomposing ordinary characters:
the induction on dimension takes a minimal invariant subspace and its complement, rather than a
subspace and a quotient (which is what the modular side is forced to do).

## Main results

* `OddOrder.trace_eq_add_trace_restrict_of_isCompl`
-/

namespace OddOrder

open LinearMap Set

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The trace splits along complementary invariant subspaces.** -/
theorem trace_eq_add_trace_restrict_of_isCompl {W W' : Submodule R M}
    [Module.Finite R W] [Module.Free R W] [Module.Finite R W'] [Module.Free R W']
    (h : IsCompl W W') {f : M →ₗ[R] M} (hW : MapsTo f W W) (hW' : MapsTo f W' W') :
    trace R M f = trace R W (f.restrict hW) + trace R W' (f.restrict hW') := by
  classical
  set N : Fin 2 → Submodule R M := ![W, W'] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; fin_cases i <;> simp
  have hint : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (by decide) huniv).mpr h
  have hmaps : ∀ i : Fin 2, MapsTo f (N i) (N i) := by
    intro i; fin_cases i
    · exact hW
    · exact hW'
  have : ∀ i : Fin 2, Module.Finite R (N i) := by
    intro i; fin_cases i
    · exact ‹Module.Finite R W›
    · exact ‹Module.Finite R W'›
  have : ∀ i : Fin 2, Module.Free R (N i) := by
    intro i; fin_cases i
    · exact ‹Module.Free R W›
    · exact ‹Module.Free R W'›
  rw [LinearMap.trace_eq_sum_trace_restrict hint hmaps, Fin.sum_univ_two]
  rfl

end OddOrder
