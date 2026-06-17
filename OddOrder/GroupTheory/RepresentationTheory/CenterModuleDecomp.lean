/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.IdempotentDirectSum
import Mathlib.RepresentationTheory.Basic

/-!
# Isotypic decomposition of a representation via the central idempotents (Peterfalvi (9.1), I-2)

Given a splitting `φ : Z(k[U]) ≃ₐ[k] (Fin N → k)` (from `exists_center_algEquiv_pi` over an
algebraically closed field with `char ∤ |U|`), the standard idempotents `Pi.single i 1` pull back
to the **primitive central idempotents** `φ.symm (Pi.single i 1) ∈ Z(k[U])`.  Their images under the
algebra map `asAlgebraHom ρ : k[U] →ₐ[k] Module.End k W` of any representation `ρ` are the
**isotypic projections** of `W`, and they decompose `W` internally:

`isInternal_centerProj` — `W = ⊕_i range (π i)`, with `π i = asAlgebraHom ρ ε_i` (`ε_i` the
`i`-th primitive central idempotent).

This is the `DirectSum.IsInternal` input the free-orbit count (†) needs; the `E`-action then
permutes these summands by `simplesAction φ` (the 3d.3c bridge, to follow).
-/

namespace OddOrder.GroupTheory.CenterModuleDecomp

open Representation MonoidAlgebra

variable {k U : Type*} [Field k] [Group U] {N : ℕ}
  (φ : Subalgebra.center k (MonoidAlgebra k U) ≃ₐ[k] (Fin N → k))
  {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k U W)

/-- The isotypic projection of `W` onto the `i`-th simple, `π i = asAlgebraHom ρ ε_i` where
`ε_i = φ.symm (Pi.single i 1)` is the `i`-th primitive central idempotent of `Z(k[U])`. -/
noncomputable def centerProj (i : Fin N) : Module.End k W :=
  asAlgebraHom ρ ((Subalgebra.center k (MonoidAlgebra k U)).val (φ.symm (Pi.single i 1)))

/-- The isotypic projections form a complete orthogonal family of idempotent endomorphisms: they are
the image of the standard idempotents `Pi.single i 1` under the algebra (hence ring) homomorphism
`asAlgebraHom ρ ∘ val ∘ φ.symm`. -/
theorem completeOrthogonalIdempotents_centerProj :
    CompleteOrthogonalIdempotents (centerProj φ ρ) := by
  let g : (Fin N → k) →ₐ[k] Module.End k W :=
    (asAlgebraHom ρ).comp ((Subalgebra.center k (MonoidAlgebra k U)).val.comp
      (φ.symm : (Fin N → k) →ₐ[k] Subalgebra.center k (MonoidAlgebra k U)))
  have h := (CompleteOrthogonalIdempotents.single (fun _ : Fin N => k)).map (f := g.toRingHom)
  exact h

/-- **I-2: isotypic decomposition.**  Any representation `ρ : Representation k U W` is the
internal direct sum of the isotypic components `range (centerProj φ ρ i)`. -/
theorem isInternal_centerProj :
    DirectSum.IsInternal (fun i : Fin N => LinearMap.range (centerProj φ ρ i)) :=
  IdempotentDirectSum.isInternal_range_of_completeOrthogonalIdempotents
    (completeOrthogonalIdempotents_centerProj φ ρ)

end OddOrder.GroupTheory.CenterModuleDecomp
