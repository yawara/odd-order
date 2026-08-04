/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis

/-!
# Reducing the centre of a group algebra

The central character `ω_χ : Z(𝒪G) → 𝒪` of a lattice (`LatticeCentralCharacter`) has to be
pushed down to `λ_χ : Z(kG) → k` before it can name a block, since the block partition
(`Algebra.BlockIdempotent`) lives over the residue field.  For that one needs the reduction map
to carry `Z(𝒪G)` **onto** `Z(kG)`.

It does, and the reason is the class sums: `classSum C` has coefficients `0` and `1`, so it is
fixed by any coefficient map, and the class sums span the centre over *any* commutative ring
(`center_eq_sum_classSum`, generalised from fields for exactly this purpose).  So a central
element downstairs is a combination of class sums, and lifting its coefficients one at a time
lifts it.

## Main results

* `OddOrder.GroupTheory.CenterClassSum.mapRingHom_classSum`
* `OddOrder.GroupTheory.CenterClassSum.exists_mem_center_mapRingHom_eq`
-/

namespace OddOrder.GroupTheory.CenterClassSum

open scoped MonoidAlgebra

variable {k k' G : Type*} [CommRing k] [CommRing k'] [Group G]

/-- Coefficient reduction commutes with scalar multiplication, read off coefficientwise. -/
theorem mapRingHom_smul (f : k →+* k') (a : k) (x : MonoidAlgebra k G) :
    MonoidAlgebra.mapRingHom G f (a • x) = f a • MonoidAlgebra.mapRingHom G f x := by
  ext y
  simp [MonoidAlgebra.coeff_mapRingHom]

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- **Class sums are fixed by coefficient reduction**: their coefficients are `0` and `1`, which
every ring homomorphism preserves. -/
theorem mapRingHom_classSum (f : k →+* k') (C : ConjClasses G) :
    MonoidAlgebra.mapRingHom G f (classSum (k := k) C) = classSum (k := k') C := by
  ext x
  simp [MonoidAlgebra.coeff_mapRingHom, coeff_classSum, apply_ite f]

variable [Fintype (ConjClasses G)]

-- The finiteness and decidability instances are consumed by the class-sum expansion inside the
-- proof rather than by the statement.  Weakening them to `Finite` and rebuilding `Fintype`
-- locally would make the instances in `center_eq_sum_classSum` fail to match the ones the local
-- `classSum` elaborates with, so they are kept as hypotheses deliberately.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The centre reduces onto the centre.**  If the coefficient map is surjective then every
central element of `k'[G]` lifts to a central element of `k[G]`.

This is what lets `ω_χ : Z(𝒪G) → 𝒪` descend to `λ_χ : Z(kG) → k`: the value of `λ_χ` on a
central element downstairs may be computed on any lift. -/
theorem exists_mem_center_mapRingHom_eq {f : k →+* k'} (hf : Function.Surjective f)
    {z : MonoidAlgebra k' G} (hz : z ∈ Subalgebra.center k' (MonoidAlgebra k' G)) :
    ∃ w ∈ Subalgebra.center k (MonoidAlgebra k G), MonoidAlgebra.mapRingHom G f w = z := by
  classical
  -- lift each class-sum coefficient of `z`
  choose a ha using fun C : ConjClasses G => hf (z.coeff C.out)
  refine ⟨∑ C : ConjClasses G, a C • classSum (k := k) C, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun C _ =>
      Subalgebra.smul_mem _ (classSum_mem_center (k := k) C) (a C)
  · rw [map_sum, center_eq_sum_classSum hz]
    exact Finset.sum_congr rfl fun C _ => by
      rw [mapRingHom_smul, mapRingHom_classSum, ha C]

end OddOrder.GroupTheory.CenterClassSum
