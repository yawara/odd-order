/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CenterGroupAlgebraHenselian
import OddOrder.Algebra.GroupAlgebraConjugation
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction

/-!
# Lifting the block idempotents from `Z(FG)` to `Z(𝒪G)`

`CenterReduction` shows the reduction `Z(𝒪G) → Z(FG)` is onto; here its kernel is identified with
the extended ideal `I·Z(𝒪G)`, both inclusions being read off the class-sum basis.  Combined with
`existsUnique_isIdempotentElem_centerGroupAlgebra` this lifts every idempotent of `Z(FG)` — in
particular every block idempotent `e_B` — to a unique idempotent `f_B` of `Z(𝒪G)`.

These `f_B` are the elements Navarro's lemmas (5.4)–(5.7) manipulate, and hence what Brauer's
second main theorem (5.2) is proved with.

## Main results

* `OddOrder.mapRingHom_mem_center` — reduction keeps central elements central
* `OddOrder.centerReduce` — the reduction `Z(𝒪G) →+* Z(FG)`
* `OddOrder.mem_centerIdeal_iff_mapRingHom_eq_zero` — the kernel is `I·Z(𝒪G)`
* `OddOrder.existsUnique_isIdempotentElem_mapRingHom_eq` — idempotents lift uniquely
-/

namespace OddOrder

open OddOrder.GroupTheory.CenterClassSum

variable {𝒪 F G : Type*} [CommRing 𝒪] [CommRing F] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
variable (I : Ideal 𝒪) (φ : 𝒪 →+* F)

/-- The reduction of the centre, as a ring homomorphism into the reduced group algebra.  Its
image is central, but for the kernel computation only the ring structure is needed. -/
noncomputable def centerReduceHom :
    ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) →+* MonoidAlgebra F G :=
  (MonoidAlgebra.mapRingHom G φ).comp
    (Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)).val.toRingHom

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
@[simp]
theorem centerReduceHom_apply (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    centerReduceHom φ w
      = MonoidAlgebra.mapRingHom G φ (w : MonoidAlgebra 𝒪 G) := rfl

-- The finiteness instances are consumed by the class-sum expansion in the proof.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The kernel of the reduction of the centre is the extended ideal.**  One inclusion is that
`I` reduces to `0`; the other is the class-sum expansion, whose coefficients must land in `I`. -/
theorem mem_centerIdeal_iff_mapRingHom_eq_zero (hker : RingHom.ker φ = I)
    (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    w ∈ centerIdeal (G := G) I ↔ centerReduceHom φ w = 0 := by
  classical
  constructor
  · intro hw
    have hle : centerIdeal (G := G) I ≤ RingHom.ker (centerReduceHom (G := G) φ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker, centerReduceHom_apply]
      have hval : ((algebraMap 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) a :
          ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) : MonoidAlgebra 𝒪 G)
          = a • (1 : MonoidAlgebra 𝒪 G) := by
        rw [Algebra.algebraMap_eq_smul_one]; rfl
      have haz : φ a = 0 := RingHom.mem_ker.mp (by rw [hker]; exact ha)
      rw [hval, mapRingHom_smul, haz, zero_smul]
    exact hle hw
  · intro hw
    have hcoeff : ∀ C : ConjClasses G, (w : MonoidAlgebra 𝒪 G).coeff C.out ∈ I := by
      intro C
      rw [← hker, RingHom.mem_ker, ← MonoidAlgebra.coeff_mapRingHom]
      rw [centerReduceHom_apply] at hw
      rw [hw]
      rfl
    rw [eq_sum_classSumCenter w]
    refine Submodule.sum_mem _ fun C _ => ?_
    have hsmul : (w : MonoidAlgebra 𝒪 G).coeff C.out • classSumCenter (k := 𝒪) C
        = algebraMap 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))
            ((w : MonoidAlgebra 𝒪 G).coeff C.out) * classSumCenter (k := 𝒪) C := by
      rw [Algebra.smul_def]
    rw [hsmul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff C))

variable [IsAdicComplete I 𝒪]

-- Same: consumed through the kernel description.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Idempotents of `Z(FG)` lift uniquely to `Z(𝒪G)`.**  This is what produces Navarro's block
idempotents `f_B ∈ Z(𝒪G)` from the block idempotents `e_B ∈ Z(FG)`. -/
theorem existsUnique_isIdempotentElem_mapRingHom_eq (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = I) (hG : Finite G)
    {z : MonoidAlgebra F G} (hzc : z ∈ Subalgebra.center F (MonoidAlgebra F G))
    (hz : z * z = z) :
    ∃! e : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      IsIdempotentElem e ∧ centerReduceHom φ e = z := by
  classical
  obtain ⟨c, hcmem, hc⟩ := exists_mem_center_mapRingHom_eq (G := G) hφ hzc
  set cc : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) := ⟨c, hcmem⟩ with hcc
  have hccred : centerReduceHom φ cc = z := hc
  have happrox : cc * cc - cc ∈ centerIdeal (G := G) I := by
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero I φ hker, map_sub, map_mul, hccred, hz, sub_self]
  obtain ⟨e, ⟨he, hec⟩, huniq⟩ :=
    existsUnique_isIdempotentElem_centerGroupAlgebra (G := G) I hG happrox
  refine ⟨e, ⟨he, ?_⟩, fun e' he' => ?_⟩
  · have hzero : centerReduceHom φ (e - cc) = 0 :=
      (mem_centerIdeal_iff_mapRingHom_eq_zero I φ hker _).mp hec
    rw [map_sub, hccred, sub_eq_zero] at hzero
    exact hzero
  · refine huniq e' ⟨he'.1, ?_⟩
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero I φ hker, map_sub, he'.2, hccred, sub_self]

/-! ### The reduction as a map of centres

Navarro's (5.5)–(5.7) evaluate block characters on reductions of central elements, so the
reduction has to be available as a map `Z(𝒪G) → Z(FG)`.  Centrality is preserved because, by
`GroupAlgebra.forall_smul_eq_iff_mem_center`, being central means having coefficients constant on
conjugacy classes — a condition visibly preserved by a coefficient map.
-/

section Center

open scoped OddOrder.Conjugation

variable {k k' : Type*} [CommRing k] [CommRing k']

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Coefficient reduction preserves centrality.** -/
theorem mapRingHom_mem_center (f : k →+* k') {w : MonoidAlgebra k G}
    (hw : w ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    MonoidAlgebra.mapRingHom G f w ∈ Subalgebra.center k' (MonoidAlgebra k' G) := by
  have hfix : ∀ g : G, g • w = w :=
    OddOrder.GroupAlgebra.forall_smul_eq_iff_mem_center.mpr
      fun z => ((Subalgebra.mem_center_iff.mp hw) z).symm
  rw [Subalgebra.mem_center_iff]
  refine fun b => (OddOrder.GroupAlgebra.forall_smul_eq_iff_mem_center.mp (fun g => ?_) b).symm
  refine (OddOrder.GroupAlgebra.smul_eq_self_iff_coeff g _).mpr fun n => ?_
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]
  congr 1
  exact (OddOrder.GroupAlgebra.smul_eq_self_iff_coeff g w).mp (hfix g) n

/-- **The reduction of centres** `Z(𝒪G) →+* Z(FG)`. -/
noncomputable def centerReduce :
    ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) →+*
      ↥(Subalgebra.center F (MonoidAlgebra F G)) where
  toFun w := ⟨centerReduceHom φ w, mapRingHom_mem_center _ w.2⟩
  map_one' := Subtype.ext (map_one (centerReduceHom φ))
  map_mul' _ _ := Subtype.ext (map_mul (centerReduceHom φ) _ _)
  map_zero' := Subtype.ext (map_zero (centerReduceHom φ))
  map_add' _ _ := Subtype.ext (map_add (centerReduceHom φ) _ _)

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
  [IsAdicComplete I 𝒪] in
@[simp]
theorem coe_centerReduce (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    ((centerReduce φ w : ↥(Subalgebra.center F (MonoidAlgebra F G))) : MonoidAlgebra F G)
      = centerReduceHom φ w := rfl

-- The finiteness instances are consumed through the kernel description.
omit [IsAdicComplete I 𝒪] in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The kernel of `centerReduce` is again `I·Z(𝒪G)`. -/
theorem mem_centerIdeal_iff_centerReduce_eq_zero (hker : RingHom.ker φ = I)
    (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    w ∈ centerIdeal (G := G) I ↔ centerReduce φ w = 0 := by
  rw [mem_centerIdeal_iff_mapRingHom_eq_zero I φ hker]
  constructor
  · intro h; exact Subtype.ext (by rw [coe_centerReduce, h]; rfl)
  · intro h
    have hv := congrArg (fun z : ↥(Subalgebra.center F (MonoidAlgebra F G)) =>
      (z : MonoidAlgebra F G)) h
    rwa [coe_centerReduce] at hv

end Center

end OddOrder
