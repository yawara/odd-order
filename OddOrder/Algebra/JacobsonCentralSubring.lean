/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The radical of a central subring over which the ring is finite

**Navarro (5.3).**  Let `A` be a ring and `R` a subring of `Z(A)` containing `1`, and suppose `A`
is finitely generated as an `R`-module.  Then `J(R) ⊆ J(A)`.

Being a subring of the centre and containing `1` is exactly an `R`-algebra structure on `A`, so
the statement here is: the image of `Ring.jacobson R` under `algebraMap R A` lies in
`Ring.jacobson A`.

The textbook proof takes a simple `A`-module `M`, notes that `M` is finitely generated over `R`
because `A` is, and applies Nakayama to get `M · J(R) < M`; centrality makes `M · J(R)` an
`A`-submodule, so it is `0`.  The version below applies Nakayama to `A` itself instead of to a
simple module: for `r ∈ J(R)` and `y ∈ A`, put `u = y·r + 1`; then `A = A·u + r·A`, so Nakayama
gives `A·u = A`, i.e. `u` is left invertible.  That is exactly the elementwise description of
`Ring.jacobson A` (`Ideal.mem_jacobson_iff`), and it avoids having to quantify over simple
modules.

This is the first of the lemmas Navarro uses for Brauer's second main theorem: (5.3) feeds (5.4)
(inverting an element of `f(𝒪G)f` that reduces to `f` mod `p`), which feeds (5.5)–(5.7).

## Main results

* `OddOrder.algebraMap_mem_ringJacobson`
-/

namespace OddOrder

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Module.Finite R A]

/-- **Navarro (5.3).**  If `A` is finite as a module over a commutative ring `R` acting centrally,
then `algebraMap R A` carries `J(R)` into `J(A)`. -/
theorem algebraMap_mem_ringJacobson {r : R} (hr : r ∈ Ring.jacobson R) :
    algebraMap R A r ∈ Ring.jacobson A := by
  rw [← Ideal.jacobson_bot] at hr ⊢
  rw [Ideal.mem_jacobson_iff]
  intro y
  set u : A := y * algebraMap R A r + 1 with hu
  -- Nakayama, applied to `A` as an `R`-module: `A = A·u + r·A` forces `A·u = A`.
  have hNN : (⊤ : Submodule R A)
      ≤ Submodule.restrictScalars R (Ideal.span {u} : Ideal A)
        ⊔ Ideal.jacobson (⊥ : Ideal R) • (⊤ : Submodule R A) := by
    intro a _
    have h1 : a * u = a * y * algebraMap R A r + a := by
      rw [hu, mul_add, mul_one, ← mul_assoc]
    have h2 : r • (a * y) = a * y * algebraMap R A r := by
      rw [Algebra.smul_def, Algebra.commutes]
    have hdecomp : a = a * u - r • (a * y) := by rw [h1, h2]; abel
    rw [hdecomp]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)
    · exact Submodule.smul_mem_smul hr Submodule.mem_top
  have hsup := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson
    (I := Ideal.jacobson (⊥ : Ideal R)) (J := ⊥)
    (N := Submodule.restrictScalars R (Ideal.span {u} : Ideal A)) (N' := (⊤ : Submodule R A))
    Module.Finite.fg_top le_rfl hNN
  rw [Submodule.bot_smul, sup_bot_eq, sup_top_eq] at hsup
  -- `1 ∈ A·u`, i.e. `u` is left invertible
  have hone : (1 : A) ∈ (Ideal.span {u} : Ideal A) := by
    have : (1 : A) ∈ Submodule.restrictScalars R (Ideal.span {u} : Ideal A) := by
      rw [← hsup]; exact Submodule.mem_top
    exact this
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hone
  refine ⟨z, ?_⟩
  rw [Ideal.mem_bot]
  have hzu : z * u = 1 := by rw [← hz]; rfl
  rw [hu, mul_add, mul_one, ← mul_assoc] at hzu
  rw [← hzu]
  abel

end OddOrder
