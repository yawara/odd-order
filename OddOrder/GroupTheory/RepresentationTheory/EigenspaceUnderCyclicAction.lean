/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Eigenspaces under a Cyclic Action

`OddOrder.GroupTheory` shared module for Bender-Glauberman, Chapter I,
Proposition 2.4.

The proposition fixes an invertible linear transformation `g` of finite order
`h`, a primitive `h`-th root of unity `epsilon`, and writes
`V_i = {v | v * g = epsilon^i v}` and `n_i = dim V_i`.

This file starts the Lean package for that notation.  The first facts are the
periodicity facts needed before the direct-sum and block-matrix parts of Prop
2.4 can be stated cleanly.
-/

namespace OddOrder
namespace RepresentationTheory
namespace EigenspaceUnderCyclicAction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- BG Prop 2.4 notation `V_i`: the `epsilon^i` eigenspace of `g`.

BG writes the action on the right (`v g = epsilon^i v`).  In Lean this is the
left action of the endomorphism `g`, so the condition is `g v = epsilon^i • v`.
-/
abbrev cyclicEigenspace (epsilon : F) (g : Module.End F V) (i : ℕ) :
    Submodule F V :=
  g.eigenspace (epsilon ^ i)

/-- BG Prop 2.4 notation `n_i = dim V_i`. -/
noncomputable abbrev cyclicEigenspaceDim (epsilon : F) (g : Module.End F V)
    (i : ℕ) : ℕ :=
  Module.finrank F (cyclicEigenspace epsilon g i)

/-- Fin-indexed version of `cyclicEigenspace`, for the sum over
`0 ≤ i ≤ h - 1` in BG Prop 2.4(a). -/
abbrev cyclicEigenspaceFin (epsilon : F) (g : Module.End F V) {h : ℕ}
    (i : Fin h) : Submodule F V :=
  cyclicEigenspace epsilon g i.1

/-- Fin-indexed version of `cyclicEigenspaceDim`. -/
noncomputable abbrev cyclicEigenspaceFinDim (epsilon : F) (g : Module.End F V)
    {h : ℕ} (i : Fin h) : ℕ :=
  cyclicEigenspaceDim epsilon g i.1

@[simp]
theorem mem_cyclicEigenspace_iff {epsilon : F} {g : Module.End F V}
    {i : ℕ} {v : V} :
    v ∈ cyclicEigenspace epsilon g i ↔ g v = (epsilon ^ i) • v := by
  simp [cyclicEigenspace]

@[simp]
theorem mem_cyclicEigenspaceFin_iff {epsilon : F} {g : Module.End F V}
    {h : ℕ} {i : Fin h} {v : V} :
    v ∈ cyclicEigenspaceFin epsilon g i ↔ g v = (epsilon ^ i.1) • v := by
  simp [cyclicEigenspaceFin]

/-- If `epsilon^h = 1`, then the BG eigenspaces are periodic with period `h`.

This is Prop 2.4(b)'s structural reason, stated before taking dimensions. -/
theorem cyclicEigenspace_add_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i : ℕ) :
    cyclicEigenspace epsilon g (i + h) = cyclicEigenspace epsilon g i := by
  unfold cyclicEigenspace
  rw [pow_add, hepsilon, mul_one]

/-- Periodicity by any multiple of the period. -/
theorem cyclicEigenspace_add_mul_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1)
    (i k : ℕ) :
    cyclicEigenspace epsilon g (i + k * h) = cyclicEigenspace epsilon g i := by
  unfold cyclicEigenspace
  have hpow : epsilon ^ (k * h) = 1 := by
    rw [Nat.mul_comm, pow_mul, hepsilon, one_pow]
  rw [pow_add, hpow, mul_one]

/-- Primitive-root version of periodicity. -/
theorem cyclicEigenspace_add_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i : ℕ) :
    cyclicEigenspace epsilon g (i + h) = cyclicEigenspace epsilon g i :=
  cyclicEigenspace_add_period_of_pow_eq_one hepsilon.pow_eq_one i

/-- Primitive-root version of periodicity by a multiple of the period. -/
theorem cyclicEigenspace_add_mul_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i k : ℕ) :
    cyclicEigenspace epsilon g (i + k * h) = cyclicEigenspace epsilon g i :=
  cyclicEigenspace_add_mul_period_of_pow_eq_one hepsilon.pow_eq_one i k

/-- Dimension form of BG Prop 2.4(b): `n_{i+h} = n_i`. -/
theorem cyclicEigenspaceDim_add_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i : ℕ) :
    cyclicEigenspaceDim epsilon g (i + h) = cyclicEigenspaceDim epsilon g i := by
  unfold cyclicEigenspaceDim
  rw [cyclicEigenspace_add_period_of_pow_eq_one hepsilon i]

/-- Dimension form of periodicity by any multiple of the period. -/
theorem cyclicEigenspaceDim_add_mul_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i k : ℕ) :
    cyclicEigenspaceDim epsilon g (i + k * h) = cyclicEigenspaceDim epsilon g i := by
  unfold cyclicEigenspaceDim
  rw [cyclicEigenspace_add_mul_period_of_pow_eq_one hepsilon i k]

/-- Primitive-root dimension form of BG Prop 2.4(b). -/
theorem cyclicEigenspaceDim_add_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i : ℕ) :
    cyclicEigenspaceDim epsilon g (i + h) = cyclicEigenspaceDim epsilon g i :=
  cyclicEigenspaceDim_add_period_of_pow_eq_one hepsilon.pow_eq_one i

/-- Primitive-root dimension form of periodicity by any multiple of the period. -/
theorem cyclicEigenspaceDim_add_mul_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i k : ℕ) :
    cyclicEigenspaceDim epsilon g (i + k * h) = cyclicEigenspaceDim epsilon g i :=
  cyclicEigenspaceDim_add_mul_period_of_pow_eq_one hepsilon.pow_eq_one i k

end EigenspaceUnderCyclicAction
end RepresentationTheory
end OddOrder
