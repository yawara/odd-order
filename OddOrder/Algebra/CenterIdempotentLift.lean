/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CenterGroupAlgebraHenselian
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

* `OddOrder.mem_centerIdeal_iff_mapRingHom_eq_zero` — the kernel is `I·Z(𝒪G)`
* `OddOrder.existsUnique_isIdempotentElem_mapRingHom_eq` — idempotents lift uniquely
-/

namespace OddOrder

open OddOrder.GroupTheory.CenterClassSum

variable {𝒪 G : Type*} [CommRing 𝒪] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable (I : Ideal 𝒪)

/-- The reduction of the centre, as a ring homomorphism into the reduced group algebra.  Its
image is central, but for the kernel computation only the ring structure is needed. -/
noncomputable def centerReduceHom :
    ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) →+* MonoidAlgebra (𝒪 ⧸ I) G :=
  (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I)).comp
    (Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)).val.toRingHom

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
@[simp]
theorem centerReduceHom_apply (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    centerReduceHom I w
      = MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I) (w : MonoidAlgebra 𝒪 G) := rfl

-- The finiteness instances are consumed by the class-sum expansion in the proof.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The kernel of the reduction of the centre is the extended ideal.**  One inclusion is that
`I` reduces to `0`; the other is the class-sum expansion, whose coefficients must land in `I`. -/
theorem mem_centerIdeal_iff_mapRingHom_eq_zero
    (w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    w ∈ centerIdeal (G := G) I ↔ centerReduceHom I w = 0 := by
  classical
  constructor
  · intro hw
    have hle : centerIdeal (G := G) I ≤ RingHom.ker (centerReduceHom (G := G) I) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker, centerReduceHom_apply]
      have hval : ((algebraMap 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) a :
          ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) : MonoidAlgebra 𝒪 G)
          = a • (1 : MonoidAlgebra 𝒪 G) := by
        rw [Algebra.algebraMap_eq_smul_one]; rfl
      rw [hval, mapRingHom_smul, (Ideal.Quotient.eq_zero_iff_mem).mpr ha, zero_smul]
    exact hle hw
  · intro hw
    have hcoeff : ∀ C : ConjClasses G, (w : MonoidAlgebra 𝒪 G).coeff C.out ∈ I := by
      intro C
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← MonoidAlgebra.coeff_mapRingHom]
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
theorem existsUnique_isIdempotentElem_mapRingHom_eq (hG : Finite G)
    {z : MonoidAlgebra (𝒪 ⧸ I) G} (hzc : z ∈ Subalgebra.center (𝒪 ⧸ I) (MonoidAlgebra (𝒪 ⧸ I) G))
    (hz : z * z = z) :
    ∃! e : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      IsIdempotentElem e ∧ centerReduceHom I e = z := by
  classical
  obtain ⟨c, hcmem, hc⟩ :=
    exists_mem_center_mapRingHom_eq (G := G) Ideal.Quotient.mk_surjective hzc
  set cc : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) := ⟨c, hcmem⟩ with hcc
  have hccred : centerReduceHom I cc = z := hc
  have happrox : cc * cc - cc ∈ centerIdeal (G := G) I := by
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero, map_sub, map_mul, hccred, hz, sub_self]
  obtain ⟨e, ⟨he, hec⟩, huniq⟩ :=
    existsUnique_isIdempotentElem_centerGroupAlgebra (G := G) I hG happrox
  refine ⟨e, ⟨he, ?_⟩, fun e' he' => ?_⟩
  · have hzero : centerReduceHom I (e - cc) = 0 :=
      (mem_centerIdeal_iff_mapRingHom_eq_zero I _).mp hec
    rw [map_sub, hccred, sub_eq_zero] at hzero
    exact hzero
  · refine huniq e' ⟨he'.1, ?_⟩
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero, map_sub, he'.2, hccred, sub_self]

end OddOrder
