/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.MatrixNaturalModule
import OddOrder.Algebra.ModuleAlongSurjection
import OddOrder.Algebra.PiSimpleModule

/-!
# The simple modules of a product of matrix algebras

Assembling the uniqueness half of Artin–Wedderburn for `R = ∏_{j ∈ ι} M_{n_j}(k)`:

* for each `i` the column vectors `n_i → k`, with `R` acting through the `i`-th projection, are a
  simple `R`-module on which the central idempotent `e_i` acts as the identity;
* conversely a simple `R`-module has a *unique* `e_i` acting as the identity
  (`PiModule.exists_unique_idem_smul_eq_self`), and over that factor it is the column vectors
  (`linearEquiv_natural_of_isSimpleModule`).

So the simple `R`-modules are indexed by `ι`, with no repetitions: exactly what is needed to
turn the block count of Brauer's theorem into a count of irreducible modules.

## Main results

* `OddOrder.MatrixModule.piNaturalModule` — the `R`-module structure on the `i`-th block
* `OddOrder.MatrixModule.isSimpleModule_piNatural`, `OddOrder.MatrixModule.idem_smul_piNatural`
* `OddOrder.MatrixModule.nonempty_linearEquiv_natural_of_idem`
* `OddOrder.MatrixModule.blockModule`, `OddOrder.MatrixModule.isSimpleModule_blockModule`
* `OddOrder.MatrixModule.exists_linearEquiv_blockModule`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]

variable (k nn) in
/-- The column vectors of the `i`-th block, as a module over the whole product. -/
@[reducible] noncomputable def piNaturalModule (i : ι) :
    Module (∀ j, Matrix (nn j) (nn j) k) (nn i → k) :=
  Module.compHom _
    ((toEndRingHom k (nn i)).comp (Pi.evalRingHom (fun j => Matrix (nn j) (nn j) k) i))

theorem piNaturalModule_smul (i : ι) (r : ∀ j, Matrix (nn j) (nn j) k) (v : nn i → k) :
    letI := piNaturalModule k nn i
    r • v = r i *ᵥ v := rfl

/-- **The `i`-th block of column vectors is a simple module over the whole product.** -/
theorem isSimpleModule_piNatural [∀ i, Nonempty (nn i)] (i : ι) :
    letI := piNaturalModule k nn i
    IsSimpleModule (∀ j, Matrix (nn j) (nn j) k) (nn i → k) := by
  letI := piNaturalModule k nn i
  haveI : RingHomSurjective (Pi.evalRingHom (fun j => Matrix (nn j) (nn j) k) i) :=
    ⟨PiModule.surjective_evalRingHom i⟩
  let l : (nn i → k) →ₛₗ[Pi.evalRingHom (fun j => Matrix (nn j) (nn j) k) i] (nn i → k) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

/-- On the `i`-th block the `i`-th central idempotent acts as the identity. -/
theorem idem_smul_piNatural [DecidableEq ι] (i : ι) (v : nn i → k) :
    letI := piNaturalModule k nn i
    PiModule.idem (fun j => Matrix (nn j) (nn j) k) i • v = v := by
  letI := piNaturalModule k nn i
  rw [piNaturalModule_smul]
  simp [PiModule.idem]

/-- **A simple module over a product of matrix algebras is the column vectors of the block it
lives on.**  Which block that is, is determined by `PiModule.exists_unique_idem_smul_eq_self`. -/
theorem nonempty_linearEquiv_natural_of_idem [DecidableEq ι] [∀ i, Nonempty (nn i)]
    {M : Type*} [AddCommGroup M] [Module (∀ j, Matrix (nn j) (nn j) k) M]
    [IsSimpleModule (∀ j, Matrix (nn j) (nn j) k) M] {i : ι}
    (hi : ∀ s : M, PiModule.idem (fun j => Matrix (nn j) (nn j) k) i • s = s) :
    letI := PiModule.factorModule M hi
    Nonempty (M ≃ₗ[Matrix (nn i) (nn i) k] (nn i → k)) := by
  letI := PiModule.factorModule M hi
  haveI : IsSimpleModule (Matrix (nn i) (nn i) k) M :=
    PiModule.isSimpleModule_factor hi fun _ _ => rfl
  exact linearEquiv_natural_of_isSimpleModule M

/-! ### Blocks as modules over a ring mapping onto the product

This is the form in which the classification is used for `A = kG`: the surjection is
`kG ↠ kG ⧸ J(kG) ≅ ∏_i M_{d_i}(k)`, whose kernel `J(kG)` annihilates every simple module.
-/

variable {A : Type*} [Ring A]

variable (nn) in
/-- The `i`-th block of the product, as a module over a ring mapping onto the product. -/
@[reducible] noncomputable def blockModule (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) :
    Module A (nn i → k) :=
  Module.compHom _ ((toEndRingHom k (nn i)).comp
    ((Pi.evalRingHom (fun j => Matrix (nn j) (nn j) k) i).comp π))

theorem blockModule_smul (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) (a : A)
    (v : nn i → k) :
    letI := blockModule nn π i
    a • v = π a i *ᵥ v := rfl

/-- **The block action is compatible with the scalars** when the surjection is `k`-linear.  This
is what lets a `A`-linear map between blocks be restricted to a `k`-linear one, and hence what
connects the module classification to Brauer characters. -/
theorem isScalarTower_blockModule [Algebra k A] {π : A →+* ∀ j, Matrix (nn j) (nn j) k}
    (hπ : ∀ (c : k) (a : A), π (c • a) = c • π a) (i : ι) :
    letI := blockModule nn π i
    IsScalarTower k A (nn i → k) := by
  letI := blockModule nn π i
  refine ⟨fun c a v => ?_⟩
  change π (c • a) i *ᵥ v = c • (π a i *ᵥ v)
  rw [hπ, Pi.smul_apply, Matrix.smul_mulVec]

/-- **Each block is a simple module over the source ring.** -/
theorem isSimpleModule_blockModule [∀ i, Nonempty (nn i)]
    {π : A →+* ∀ j, Matrix (nn j) (nn j) k} (hπ : Function.Surjective π) (i : ι) :
    letI := blockModule nn π i
    IsSimpleModule A (nn i → k) := by
  letI := piNaturalModule k nn i
  haveI := isSimpleModule_piNatural (k := k) (nn := nn) i
  exact isSimpleModule_compHom π hπ

/-- **Every simple module is a block.**  Combined with `isSimpleModule_blockModule` and the
uniqueness in `PiModule.exists_unique_idem_smul_eq_self`, the simple `A`-modules are indexed by
`ι` without repetition. -/
theorem exists_linearEquiv_blockModule [Finite ι] [∀ i, Nonempty (nn i)]
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    {π : A →+* ∀ j, Matrix (nn j) (nn j) k} (hπ : Function.Surjective π)
    (h : RingHom.ker π ≤ Module.annihilator A M) :
    ∃ i : ι, letI := blockModule nn π i
      Nonempty (M ≃ₗ[A] (nn i → k)) := by
  classical
  letI := moduleOfSurjective π hπ h
  haveI := isSimpleModule_of_surjective π hπ h
  obtain ⟨i, hi, -⟩ := PiModule.exists_unique_idem_smul_eq_self
    (R := fun j => Matrix (nn j) (nn j) k) (M := M)
  letI := PiModule.factorModule M hi
  haveI : IsSimpleModule (Matrix (nn i) (nn i) k) M :=
    PiModule.isSimpleModule_factor hi fun _ _ => rfl
  obtain ⟨e⟩ := linearEquiv_natural_of_isSimpleModule (k := k) (n := nn i) M
  letI := blockModule nn π i
  have hsmul : ∀ (a : A) (m : M), e (a • m) = a • e m := by
    intro a m
    have hfac : a • m = (π a i) • m := by
      rw [← moduleOfSurjective_smul π hπ h a m, PiModule.smul_eq_single_smul hi]
      rfl
    rw [hfac, e.map_smul]
    rfl
  exact ⟨i, ⟨LinearEquiv.ofBijective
    ({ toFun := e, map_add' := e.map_add, map_smul' := hsmul } : M →ₗ[A] (nn i → k))
    e.bijective⟩⟩

end OddOrder.MatrixModule
