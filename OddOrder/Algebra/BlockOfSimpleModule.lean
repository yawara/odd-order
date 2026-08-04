/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacter

/-!
# The block of a simple module, read off its central scalar

`exists_linearEquiv_blockModule` says every simple `A`-module is one of the blocks of a splitting
`π : A ↠ ∏_j M_{n_j}(k)`, and `eq_centralCharacterAlg_of_forall_smul_eq` says the scalar by which
the centre acts on a block is that block's central character.  Putting them together: **if the
centre acts on a simple module by a scalar, that scalar is the central character of some block**.

This is the connector that attaches a block to an ordinary character.  The reduction of an
absolutely irreducible `𝒪`-lattice has `Z(kG)` acting by `λ_χ`
(`Modular.baseChange_apply_center` composed with `Modular.asAlgebraHom_reduction_mapRingHom`), so
any simple constituent of that reduction names the block of `χ` — Navarro Chapter 3.

The hypothesis is phrased with `algebraMap k A c` rather than `c • m` on purpose: `M` carries no
`k`-structure of its own, and the transport along the `A`-linear equivalence only respects the
`A`-action.

## Main results

* `OddOrder.MatrixModule.exists_eq_centralCharacterAlg_of_forall_smul_eq`
-/

namespace OddOrder.MatrixModule

variable {k ι : Type*} [Field k] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)] [Finite ι]
variable {A : Type*} [Ring A] [Algebra k A]

/-- **A scalar action of the centre on a simple module is the central character of a block.**

`M` simple picks out a block `i` (`exists_linearEquiv_blockModule`); transporting the scalar
action along that equivalence and comparing with `centralScalar` identifies the scalar. -/
theorem exists_eq_centralCharacterAlg_of_forall_smul_eq
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    {π : A →+* ∀ j, Matrix (nn j) (nn j) k} (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)
    (hker : RingHom.ker π ≤ Module.annihilator A M)
    {z : Subalgebra.center k A} {c : k}
    (h : ∀ m : M, (z : A) • m = (algebraMap k A c) • m) :
    ∃ i : ι, c = centralCharacterAlg π i hπ hlin z := by
  obtain ⟨i, ⟨e⟩⟩ := exists_linearEquiv_blockModule (nn := nn) hπ hker
  letI := blockModule nn π i
  haveI := isScalarTower_blockModule (k := k) hlin i
  refine ⟨i, eq_centralCharacterAlg_of_forall_smul_eq π i hπ hlin fun v => ?_⟩
  have hv := congrArg e (h (e.symm v))
  rw [map_smul, map_smul, e.apply_symm_apply] at hv
  rw [hv, algebraMap_smul]

end OddOrder.MatrixModule
