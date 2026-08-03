/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

/-! ### Two counting helpers -/

section Counting

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The dimension of a finite supremum of subspaces is at most the sum of the dimensions.  With
the reverse inequality supplied by a spanning argument this pins each summand down. -/
theorem finrank_biSup_le_sum {ι : Type*} (t : Finset ι) (q : ι → Submodule K W) :
    Module.finrank K ↥(⨆ i ∈ t, q i) ≤ ∑ i ∈ t, Module.finrank K (q i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hins : (⨆ i ∈ insert a t, q i) = q a ⊔ ⨆ i ∈ t, q i := by
      simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
    rw [Finset.sum_insert ha, hins]
    refine le_trans ?_ (Nat.add_le_add_left ih _)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (q a) (⨆ i ∈ t, q i)
    omega

end Counting

/-! ### Base change and suprema -/

section BaseChangeSup

variable (k : Type*) [Field k] [Algebra 𝒪 k]

omit [IsLocalRing 𝒪] in
/-- Base change of a supremum of submodules is contained in the supremum of the base changes. -/
theorem baseChange_iSup_le {ι : Sort*} (N : ι → Submodule 𝒪 L) :
    (⨆ i, N i).baseChange k ≤ ⨆ i, (N i).baseChange k := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  induction hv using Submodule.iSup_induction' with
  | mem i x hx =>
    exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  | zero => simp
  | add x y _ _ hx hy =>
    have : (TensorProduct.mk 𝒪 k L 1) (x + y)
        = (TensorProduct.mk 𝒪 k L 1) x + (TensorProduct.mk 𝒪 k L 1) y := map_add _ _ _
    rw [SetLike.mem_coe] at hx hy ⊢
    rw [this]
    exact Submodule.add_mem _ hx hy

omit [IsLocalRing 𝒪] in
/-- If a family of submodules spans, so do their base changes. -/
theorem iSup_baseChange_eq_top {ι : Sort*} {N : ι → Submodule 𝒪 L} (hN : ⨆ i, N i = ⊤) :
    ⨆ i, (N i).baseChange k = ⊤ :=
  eq_top_iff.mpr (by
    rw [← Submodule.baseChange_top (A := k) (M := L), ← hN]
    exact baseChange_iSup_le k N)

end BaseChangeSup

end OddOrder.RepresentationTheory.Modular
