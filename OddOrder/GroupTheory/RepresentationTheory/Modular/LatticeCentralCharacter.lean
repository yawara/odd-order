/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalars descend along base change on a free module

Navarro builds the block of an ordinary character `χ` from its central character
`ω_χ : Z(ℂG) → ℂ`, and has to prove separately that `ω_χ(K̂)` is an **algebraic integer** before
he can reduce it modulo a maximal ideal (Chapter 3, quoting Isaacs `Characters` (3.7)).

In the `𝒪`-lattice formulation that step is free.  If `ρ` is realised on an `𝒪`-lattice `L` and
`z ∈ Z(𝒪G)`, then `ρ(z)` is an `𝒪`-endomorphism of `L`; if it becomes a `K`-scalar after base
change — which is what Schur's lemma gives when `ρ_K` is absolutely irreducible — then the
scalar already lies in `𝒪`, simply because `L` is free and the matrix of `ρ(z)` has entries in
`𝒪`.  No integrality theorem is needed.

That is the content of this file: `eq_smul_of_baseChange_eq_smul`.  It is stated for a bare
`𝒪`-linear endomorphism, with no group in sight.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_smul_of_baseChange_eq_smul`
-/

namespace OddOrder.RepresentationTheory.Modular

open TensorProduct

variable {𝒪 K : Type*} [CommRing 𝒪] [CommRing K] [Algebra 𝒪 K] [FaithfulSMul 𝒪 K]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Nontrivial L]

/-- **A `K`-scalar endomorphism of a free `𝒪`-module is an `𝒪`-scalar.**

`L` free means the matrix of `f` has entries in `𝒪`; if base change turns `f` into `c • id` then
comparing the coordinate of `f (b i)` at `b i` exhibits `c` as coming from `𝒪`, and comparing the
remaining coordinates shows `f` was already that scalar.

This is what replaces the algebraic-integrality of `ω_χ(K̂)` in the lattice formulation. -/
theorem eq_smul_of_baseChange_eq_smul {f : L →ₗ[𝒪] L} {c : K}
    (h : LinearMap.baseChange K f = c • LinearMap.id) :
    ∃ c' : 𝒪, algebraMap 𝒪 K c' = c ∧ f = c' • LinearMap.id := by
  classical
  set b := Module.Free.chooseBasis 𝒪 L with hb
  haveI : Nonempty (Module.Free.ChooseBasisIndex 𝒪 L) := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex 𝒪 L)›
  -- coordinates of the base-changed equation, read in the lifted basis
  have key : ∀ i j, algebraMap 𝒪 K (b.repr (f (b i)) j)
      = c * algebraMap 𝒪 K (b.repr (b i) j) := by
    intro i j
    have := congrArg (fun F => (b.baseChange K).repr (F (1 ⊗ₜ[𝒪] b i)) j) h
    simpa [LinearMap.baseChange_tmul, Algebra.smul_def, mul_comm] using this
  -- the scalar is the diagonal coordinate at `i₀`
  refine ⟨b.repr (f (b i₀)) i₀, ?_, ?_⟩
  · have := key i₀ i₀
    simpa using this
  · -- with the scalar identified, every coordinate matches
    set c' := b.repr (f (b i₀)) i₀ with hc'
    have hc : algebraMap 𝒪 K c' = c := by have := key i₀ i₀; simpa using this
    refine b.ext fun i => ?_
    refine b.repr.injective (Finsupp.ext fun j => ?_)
    have hij := key i j
    rw [← hc] at hij
    have : algebraMap 𝒪 K (b.repr (f (b i)) j) = algebraMap 𝒪 K (c' * b.repr (b i) j) := by
      rw [hij, map_mul]
    have hval := FaithfulSMul.algebraMap_injective 𝒪 K this
    simp [hval, LinearMap.smul_apply, map_smul, Finsupp.single_apply, mul_ite]

/-- **The scalar is determined.**  On a nonzero free module distinct scalars give distinct
endomorphisms, so `eq_smul_of_baseChange_eq_smul` pins `c'` uniquely — which is what makes the
central character below well defined. -/
theorem smul_id_injective {c₁ c₂ : 𝒪}
    (h : (c₁ • LinearMap.id : L →ₗ[𝒪] L) = c₂ • LinearMap.id) : c₁ = c₂ := by
  classical
  set b := Module.Free.chooseBasis 𝒪 L with hb
  haveI : Nonempty (Module.Free.ChooseBasisIndex 𝒪 L) := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex 𝒪 L)›
  have := congrArg (fun F => b.repr (F (b i₀)) i₀) h
  simpa using this

/-! ### The central character of a lattice representation

`hscalar` below is what Schur's lemma supplies once `K` splits `A`: a central element acts on an
absolutely irreducible module by a scalar.  Everything *integral* — that the scalar lies in `𝒪`
and not merely in `K` — is `eq_smul_of_baseChange_eq_smul`.
-/

variable {A : Type*} [Ring A] [Algebra 𝒪 A]

/-- **A central element acts on an `𝒪`-lattice by an `𝒪`-scalar**, given that it acts by a
`K`-scalar after base change.

Combined with `smul_id_injective` (which makes `c'` unique) this is the central character
`ω : Z(A) → 𝒪` of the lattice, and reducing it modulo the maximal ideal of `𝒪` is what assigns
a block to an ordinary character — Navarro's Chapter 3, without the appeal to algebraic
integrality. -/
theorem exists_smul_id_of_mem_center (φ : A →ₐ[𝒪] Module.End 𝒪 L)
    (hscalar : ∀ z ∈ Subalgebra.center 𝒪 A,
      ∃ c : K, LinearMap.baseChange K (φ z) = c • LinearMap.id)
    {z : A} (hz : z ∈ Subalgebra.center 𝒪 A) :
    ∃ c' : 𝒪, φ z = c' • LinearMap.id := by
  obtain ⟨c, hc⟩ := hscalar z hz
  obtain ⟨c', -, hc'⟩ := eq_smul_of_baseChange_eq_smul (K := K) hc
  exact ⟨c', hc'⟩

end OddOrder.RepresentationTheory.Modular
