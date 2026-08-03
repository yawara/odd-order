/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.MatrixNaturalModule
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

end OddOrder.MatrixModule
