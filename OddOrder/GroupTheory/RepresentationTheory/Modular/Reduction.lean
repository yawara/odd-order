/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeEigenspaces

/-!
# Reduction of an `𝒪`-lattice modulo the maximal ideal

The decomposition map compares an `𝒪`-lattice `L` with its reduction `k ⊗[𝒪] L`, where
`k = ResidueField 𝒪`.  This file sets that comparison up:

* an endomorphism of finite order stays of finite order after reduction
  (`Module.End.baseChangeHom` is an algebra map);
* the reduction of a `ζ`-eigen-submodule lands inside the `ζ̄`-eigenspace of the reduced
  operator.

Together with `LatticeEigenspaces` — where the trace over `𝒪` is already written in
Brauer-character shape, and reduction is a bijection `μ_n(𝒪) → μ_n(k)` — what remains for the
decomposition-map identity is that these containments are equalities on dimensions.

## Main results

* `OddOrder.RepresentationTheory.Modular.baseChange_pow_eq_one`
* `OddOrder.RepresentationTheory.Modular.baseChange_eigenspace_le`
* `OddOrder.RepresentationTheory.Modular.finrank_baseChange_eigenspace`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing TensorProduct

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L]

/-- Reduction preserves the order of an endomorphism: base change is an algebra map. -/
theorem baseChange_pow_eq_one {A : Module.End 𝒪 L} {n : ℕ} (hA : A ^ n = 1) :
    (A.baseChange (ResidueField 𝒪)) ^ n = 1 := by
  have h := congrArg (Module.End.baseChangeHom 𝒪 (ResidueField 𝒪) L) hA
  rwa [map_pow, map_one] at h

/-- **The reduction of an eigen-submodule lands in the eigenspace of the reduced operator.**
An eigenvector for `ζ` upstairs reduces to an eigenvector for the residue of `ζ`. -/
theorem baseChange_eigenspace_le (A : Module.End 𝒪 L) (ζ : 𝒪) :
    (Module.End.eigenspace A ζ).baseChange (ResidueField 𝒪)
      ≤ Module.End.eigenspace (A.baseChange (ResidueField 𝒪)) (residue 𝒪 ζ) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  have hv' : A v = ζ • v := Module.End.mem_eigenspace_iff.mp hv
  change (A.baseChange (ResidueField 𝒪)) ((1 : ResidueField 𝒪) ⊗ₜ[𝒪] v)
    = residue 𝒪 ζ • ((1 : ResidueField 𝒪) ⊗ₜ[𝒪] v)
  rw [LinearMap.baseChange_tmul, hv', TensorProduct.tmul_smul,
    ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

/-- The reduction of a free eigen-submodule has the same dimension as its rank. -/
theorem finrank_baseChange_eigenspace (A : Module.End 𝒪 L) (ζ : 𝒪)
    [Module.Free 𝒪 (Module.End.eigenspace A ζ)] [Module.Finite 𝒪 (Module.End.eigenspace A ζ)] :
    Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] (Module.End.eigenspace A ζ))
      = Module.finrank 𝒪 (Module.End.eigenspace A ζ) :=
  Module.finrank_baseChange

end OddOrder.RepresentationTheory.Modular
