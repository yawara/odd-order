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

The two halves this needs are *existence* of a lift and *independence* of the choice; together
they produce `λ` as a ring homomorphism.

## Main results

* `OddOrder.GroupTheory.CenterClassSum.mapRingHom_classSum` — class sums survive reduction
* `OddOrder.GroupTheory.CenterClassSum.exists_mem_center_mapRingHom_eq` — a lift exists
* `OddOrder.GroupTheory.CenterClassSum.apply_eq_of_mapRingHom_eq` — the value is lift-independent
* `OddOrder.GroupTheory.CenterClassSum.reducedCentralCharacter` — `λ : Z(k'G) →+* k'`
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

/-- The class-sum expansion, inside the centre subalgebra rather than in `k[G]`. -/
theorem eq_sum_classSumCenter (w : Subalgebra.center k (MonoidAlgebra k G)) :
    w = ∑ C : ConjClasses G, (w : MonoidAlgebra k G).coeff C.out • classSumCenter (k := k) C := by
  refine Subtype.ext ?_
  push_cast
  exact center_eq_sum_classSum w.2

-- Same as above: the instances are consumed by the class-sum expansion in the proof.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The well-definedness of the reduced central character.**  If a central element dies under
coefficient reduction then so does its central-character value.

This is what makes `λ_χ` well defined: two lifts of the same central element of `k'[G]` differ by
something killed by the reduction, so `f ∘ ω` takes the same value on both.  The proof is the
class-sum expansion — `ω` is `k`-linear, and each coefficient of `w` is killed by `f`. -/
theorem apply_eq_zero_of_mapRingHom_eq_zero (f : k →+* k')
    (ω : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    {w : Subalgebra.center k (MonoidAlgebra k G)}
    (hw : MonoidAlgebra.mapRingHom G f (w : MonoidAlgebra k G) = 0) :
    f (ω w) = 0 := by
  have hcoeff : ∀ C : ConjClasses G, f ((w : MonoidAlgebra k G).coeff C.out) = 0 := by
    intro C
    have := congrArg (fun x => MonoidAlgebra.coeff x C.out) hw
    simpa [MonoidAlgebra.coeff_mapRingHom] using this
  conv_lhs => rw [eq_sum_classSumCenter w]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, hcoeff C, zero_mul]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **`f ∘ ω` factors through the reduction.**  Central elements with the same image have the
same reduced central-character value, so `λ_χ` may be computed on *any* lift.

Together with `exists_mem_center_mapRingHom_eq` (which supplies a lift) this is exactly what is
needed to define `λ_χ : Z(kG) → k` from `ω_χ : Z(𝒪G) → 𝒪`. -/
theorem apply_eq_of_mapRingHom_eq (f : k →+* k')
    (ω : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    {w₁ w₂ : Subalgebra.center k (MonoidAlgebra k G)}
    (h : MonoidAlgebra.mapRingHom G f (w₁ : MonoidAlgebra k G)
       = MonoidAlgebra.mapRingHom G f (w₂ : MonoidAlgebra k G)) :
    f (ω w₁) = f (ω w₂) := by
  have hzero : f (ω (w₁ - w₂)) = 0 := by
    refine apply_eq_zero_of_mapRingHom_eq_zero f ω ?_
    rw [Subalgebra.coe_sub, map_sub, h, sub_self]
  rw [map_sub, map_sub, sub_eq_zero] at hzero
  exact hzero

/-! ### The reduced central character `λ` -/

section Reduced

variable {f : k →+* k'} (hf : Function.Surjective f)
  (ω : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)

/-- A lift of a central element along the coefficient reduction. -/
noncomputable def centerLift (z : Subalgebra.center k' (MonoidAlgebra k' G)) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨(exists_mem_center_mapRingHom_eq hf z.2).choose,
    (exists_mem_center_mapRingHom_eq hf z.2).choose_spec.1⟩

theorem mapRingHom_centerLift (z : Subalgebra.center k' (MonoidAlgebra k' G)) :
    MonoidAlgebra.mapRingHom G f (centerLift hf z : MonoidAlgebra k G) = z :=
  (exists_mem_center_mapRingHom_eq hf z.2).choose_spec.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The reduced central character `λ`.**  Navarro's `λ_χ(K̂) = ω_χ(K̂)^*`, obtained by lifting a
central element of `k'[G]`, applying `ω`, and reducing.

Well defined by `apply_eq_of_mapRingHom_eq`; the ring-homomorphism laws all follow from
`reducedCentralCharacter_eq` because a lift of a product/sum is the product/sum of lifts. -/
noncomputable def reducedCentralCharacter :
    Subalgebra.center k' (MonoidAlgebra k' G) →+* k' where
  toFun z := f (ω (centerLift hf z))
  map_one' := by
    rw [apply_eq_of_mapRingHom_eq f ω (w₂ := 1)
      (by rw [mapRingHom_centerLift]; simp)]
    simp
  map_mul' z₁ z₂ := by
    rw [apply_eq_of_mapRingHom_eq f ω (w₂ := centerLift hf z₁ * centerLift hf z₂)
      (by simp [mapRingHom_centerLift])]
    rw [map_mul, map_mul]
  map_zero' := by
    rw [apply_eq_of_mapRingHom_eq f ω (w₂ := 0)
      (by rw [mapRingHom_centerLift]; simp)]
    simp
  map_add' z₁ z₂ := by
    rw [apply_eq_of_mapRingHom_eq f ω (w₂ := centerLift hf z₁ + centerLift hf z₂)
      (by simp [mapRingHom_centerLift])]
    rw [map_add, map_add]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **`λ` may be computed on any lift.**  The form in which it gets used. -/
theorem reducedCentralCharacter_eq {z : Subalgebra.center k' (MonoidAlgebra k' G)}
    {w : Subalgebra.center k (MonoidAlgebra k G)}
    (hw : MonoidAlgebra.mapRingHom G f (w : MonoidAlgebra k G) = z) :
    reducedCentralCharacter hf ω z = f (ω w) :=
  apply_eq_of_mapRingHom_eq f ω (by rw [mapRingHom_centerLift, hw])

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **`λ` is `k'`-linear.**  A scalar `c ∈ k'` lifts to `c₀ ∈ k`, and `c₀ • w` is a lift of
`c • z`. -/
theorem reducedCentralCharacter_smul (c : k') (z : Subalgebra.center k' (MonoidAlgebra k' G)) :
    reducedCentralCharacter hf ω (c • z) = c * reducedCentralCharacter hf ω z := by
  obtain ⟨c₀, rfl⟩ := hf c
  rw [reducedCentralCharacter_eq hf ω (w := c₀ • centerLift hf z) ?_,
    reducedCentralCharacter_eq hf ω (w := centerLift hf z) (mapRingHom_centerLift hf z),
    map_smul, smul_eq_mul, map_mul]
  · rw [show ((c₀ • centerLift hf z : Subalgebra.center k (MonoidAlgebra k G)) :
        MonoidAlgebra k G) = c₀ • (centerLift hf z : MonoidAlgebra k G) from rfl,
      mapRingHom_smul, mapRingHom_centerLift]
    rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **`λ` as a `k'`-algebra homomorphism.**  This is the form `blockOfCentralCharacter` consumes,
so it is what attaches a block to an ordinary character. -/
noncomputable def reducedCentralCharacterAlg :
    Subalgebra.center k' (MonoidAlgebra k' G) →ₐ[k'] k' :=
  AlgHom.mk' (reducedCentralCharacter hf ω) fun c z => by
    rw [reducedCentralCharacter_smul, smul_eq_mul]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
@[simp]
theorem reducedCentralCharacterAlg_apply (z : Subalgebra.center k' (MonoidAlgebra k' G)) :
    reducedCentralCharacterAlg hf ω z = reducedCentralCharacter hf ω z := rfl

end Reduced

end OddOrder.GroupTheory.CenterClassSum
