/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Diagonalisability from a split squarefree annihilating polynomial

An endomorphism `A` of a vector space over a field `F` is diagonalisable as soon as it is
annihilated by a polynomial that splits into *distinct* linear factors over `F`:

`aeval A (∏ ζ ∈ s, (X - C ζ)) = 0  ⟹  ⨆ ζ ∈ s, A.eigenspace ζ = ⊤`.

The proof is Lagrange interpolation: the basis polynomials `L_ζ` of the node set `s` sum to `1`
(`Lagrange.sum_basis`), so `v = ∑_{ζ ∈ s} L_ζ(A) v`, while `(X - C ζ) * L_ζ` is a constant
multiple of `∏_{η ∈ s} (X - C η)` and therefore kills `V`; hence `L_ζ(A) v` is a `ζ`-eigenvector.
No algebraic closure is needed — mathlib's `Module.End.IsSemisimple.iSup_eigenspace_eq_top`
assumes `IsAlgClosed`, which is exactly what one cannot have in modular representation theory,
where the coefficient field is a finite field chosen just large enough.

The application is `p`-regular elements in characteristic `p`: an element of order `m` prime to
`p` acts with `A ^ m = 1`, and over a field containing a primitive `m`-th root of unity
`X ^ m - 1` is precisely such a split squarefree annihilator (`iSup_eigenspace_eq_top_of_pow`).
That is what makes Brauer characters well defined.

## Main results

* `OddOrder.iSup_eigenspace_eq_top_of_aeval_prod_eq_zero` — the general statement
* `OddOrder.iSup_eigenspace_eq_top_of_pow` — the finite-order case
* `OddOrder.isInternal_eigenspace_of_pow` — the eigenspace decomposition is a direct sum
* `OddOrder.sum_finrank_eigenspace_of_pow` — the eigenspace dimensions add up to `dim V`
-/

namespace OddOrder

open Polynomial Module.End

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The Lagrange basis polynomial at a node `ζ` is the normalised product of `X - η` over the
other nodes. -/
theorem lagrangeBasis_eq_C_mul_prod [DecidableEq F] (s : Finset F) (ζ : F) :
    Lagrange.basis s id ζ
      = C (∏ η ∈ s.erase ζ, (ζ - η)⁻¹) * ∏ η ∈ s.erase ζ, (X - C η) := by
  rw [Lagrange.basis, map_prod]
  simp only [id_eq, Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib]

/-- `(X - ζ) · L_ζ` is a constant multiple of `∏_{η ∈ s} (X - η)`: multiplying the Lagrange
basis polynomial by its missing factor restores the full product. -/
theorem X_sub_C_mul_lagrangeBasis [DecidableEq F] {s : Finset F} {ζ : F} (hζ : ζ ∈ s) :
    (X - C ζ) * Lagrange.basis s id ζ
      = C (∏ η ∈ s.erase ζ, (ζ - η)⁻¹) * ∏ η ∈ s, (X - C η) := by
  rw [lagrangeBasis_eq_C_mul_prod, ← Finset.mul_prod_erase s (fun η => X - C η) hζ]
  ring

/-- **Diagonalisability from a split squarefree annihilator.**  If `A` is killed by
`∏_{ζ ∈ s} (X - ζ)` for a finite set `s` of scalars, then `V` is spanned by the eigenspaces of
`A` at the members of `s`. -/
theorem iSup_eigenspace_eq_top_of_aeval_prod_eq_zero {A : Module.End F V} {s : Finset F}
    (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    ⨆ ζ ∈ s, A.eigenspace ζ = ⊤ := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · -- The empty product is `1`, so `A` lives on the zero space and every submodule is `⊤`.
    simp only [Finset.prod_empty, map_one] at hA
    have hsub : Subsingleton V := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : V, z = 0 := fun z => by
        simpa using congrArg (fun T : Module.End F V => T z) hA
      rw [hx x, hx y]
    exact Subsingleton.elim _ _
  refine eq_top_iff.mpr fun v _ => ?_
  -- `∑_{ζ ∈ s} L_ζ = 1`, so `v` is the sum of the vectors `L_ζ(A) v`.
  have hsum : ∑ ζ ∈ s, Lagrange.basis s id ζ = 1 :=
    Lagrange.sum_basis (Set.injOn_id _) hs
  have hv : v = ∑ ζ ∈ s, (aeval A (Lagrange.basis s id ζ)) v := by
    have h := congrArg (fun q : F[X] => (aeval A q) v) hsum
    simpa [map_sum, LinearMap.sum_apply] using h.symm
  -- Each summand is a `ζ`-eigenvector, because `(X - ζ) · L_ζ` is a multiple of the annihilator.
  have hmem : ∀ ζ ∈ s, (aeval A (Lagrange.basis s id ζ)) v ∈ ⨆ ζ ∈ s, A.eigenspace ζ := by
    intro ζ hζ
    refine Submodule.mem_iSup_of_mem ζ (Submodule.mem_iSup_of_mem hζ ?_)
    rw [mem_eigenspace_iff]
    have hkill : aeval A ((X - C ζ) * Lagrange.basis s id ζ) = 0 := by
      rw [X_sub_C_mul_lagrangeBasis hζ, map_mul, hA, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C] at hkill
    have happ := congrArg (fun T : Module.End F V => T v) hkill
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      Module.algebraMap_end_apply] at happ
    exact sub_eq_zero.mp happ
  rw [hv]
  exact Submodule.sum_mem _ hmem

/-- **The finite-order case.**  If `A ^ m = 1` and the base field contains a primitive `m`-th
root of unity, then `V` is spanned by the eigenspaces of `A` at the `m`-th roots of unity. -/
theorem iSup_eigenspace_eq_top_of_pow {A : Module.End F V} {m : ℕ} (hm : 0 < m)
    {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) :
    ⨆ ζ ∈ nthRootsFinset m (1 : F), A.eigenspace ζ = ⊤ := by
  refine iSup_eigenspace_eq_top_of_aeval_prod_eq_zero ?_
  rw [← X_pow_sub_one_eq_prod hm hω]
  simp [hA]

/-- Over any field the eigenspaces of an endomorphism are independent, so the decomposition of
`iSup_eigenspace_eq_top_of_pow` is an internal direct sum. -/
theorem isInternal_eigenspace_of_pow [DecidableEq F] {A : Module.End F V} {m : ℕ} (hm : 0 < m)
    {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) :
    DirectSum.IsInternal fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨A.eigenspaces_iSupIndep.comp Subtype.val_injective, eq_top_iff.mpr ?_⟩
  rw [← iSup_eigenspace_eq_top_of_pow hm hω hA]
  exact iSup₂_le fun ζ hζ =>
    le_iSup (fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F)) ⟨ζ, hζ⟩

/-- **The eigenspace dimensions add up.**  This is the counting form of
`isInternal_eigenspace_of_pow`, and it is what makes a Brauer character take the value `dim V`
at the identity and reduce to the ordinary trace modulo the maximal ideal. -/
theorem sum_finrank_eigenspace_of_pow [FiniteDimensional F V]
    {A : Module.End F V} {m : ℕ} (hm : 0 < m) {ω : F} (hω : IsPrimitiveRoot ω m)
    (hA : A ^ m = 1) :
    ∑ ζ ∈ nthRootsFinset m (1 : F), Module.finrank F (A.eigenspace ζ) = Module.finrank F V := by
  classical
  have hint := isInternal_eigenspace_of_pow hm hω hA
  have he := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F))) hint
  rw [← he.finrank_eq, Module.finrank_directSum, Finset.univ_eq_attach]
  exact (Finset.sum_attach (nthRootsFinset m (1 : F))
    (fun ζ => Module.finrank F (A.eigenspace ζ))).symm

end OddOrder
