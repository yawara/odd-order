/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Scalar extension (base change) of group representations

Shared `OddOrder.GroupTheory.RepresentationTheory` module: extend a representation
`ρ : Representation F G V` along a field extension `K / F` to
`Representation K G (K ⊗[F] V)`.

This is the bridge used by Bender–Glauberman §2/§3 (and BG Thm 2.6(b)) to reduce a
representation over an arbitrary field `F` (with `char F ∤ |G|`) to one over the algebraic
closure `F* = AlgebraicClosure F`, where the representation theory of (extra)special groups is
available.  BG Thm 2.5's proof opens with exactly this step ("Let `F*` be the algebraic closure
of `F` and `V* = F* ⊗_F V`").

## Main definitions / results

* `baseChangeRepresentation K ρ` — the scalar extension `Representation K G (K ⊗[F] V)`.
* `baseChangeRepresentation_apply_tmul` — action on a simple tensor.
* `baseChangeRepresentation_faithful` — faithfulness survives a faithfully flat extension.

The fixed-space / `C_V(R)` transfer lemmas (`C_V(R) = 0 ⟹ C_{V*}(R) = 0`, dimension invariance)
build on this; see the `invariants` lemmas below.
-/

namespace OddOrder.RepresentationTheory

open scoped TensorProduct

/-- Scalar extension of a representation along a field extension.

The concrete base-change object `Representation K G (K ⊗[F] V)`: `g` acts by `id_K ⊗ ρ g`. -/
noncomputable def baseChangeRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) :
    Representation K G (TensorProduct F K V) where
  toFun g := TensorProduct.AlgebraTensorModule.map (R := F) (A := K)
    (M := K) (N := V) (P := K) (Q := V)
    (LinearMap.id : K →ₗ[K] K) (ρ g)
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp [map_mul]

/-- `baseChangeRepresentation` の単純テンソル上の作用: `a ⊗ₜ v ↦ a ⊗ₜ ρ g v`. -/
@[simp]
theorem baseChangeRepresentation_apply_tmul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (g : G) (a : K) (v : V) :
    baseChangeRepresentation K ρ g (a ⊗ₜ[F] v) = a ⊗ₜ[F] ρ g v := by
  simp [baseChangeRepresentation]

/-- Faithfulness survives scalar extension along a faithfully flat field extension.

For the algebraic-closure route, `K` will be `AlgebraicClosure F`.  The proof uses the canonical
injection `V → K ⊗[F] V`. -/
theorem baseChangeRepresentation_faithful
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K] [Module.FaithfullyFlat F K]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) :
    Function.Injective (baseChangeRepresentation K ρ) := by
  intro g h hgh
  apply hfaithful
  ext v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := K) V
  have hmap := congrArg
    (fun f : TensorProduct F K V →ₗ[K] TensorProduct F K V => f (1 ⊗ₜ[F] v)) hgh
  simpa [baseChangeRepresentation] using hmap

end OddOrder.RepresentationTheory
