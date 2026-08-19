/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import OddOrder.GroupTheory.RepresentationTheory.Modular.CommutatorSubspace

/-!
# `kG ⧸ [kG, kG]` is graded by conjugacy classes

The commutator subspace `T = [kG, kG]` is spanned by the differences of conjugate group
elements (`CommutatorSubspace`), so the quotient `kG ⧸ T` is spanned by the classes of the
group elements, of which there are as many as conjugacy classes.  Conversely the
class-coefficient functionals separate them.  Hence

`dim_k (kG ⧸ [kG, kG]) = #(conjugacy classes of G)`.

This is the "ordinary" half of Brauer's count; the modular half replaces `T` by
`T' = {x : x ^ (p ^ m) ∈ T}` and conjugacy classes by `p`-regular classes.

## Main results

* `OddOrder.RepresentationTheory.Modular.finrank_quotient_commutatorSubmodule`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]

variable (k G) in
/-- The class-coefficient functionals assembled into a single map. -/
noncomputable def classCoeffPi : MonoidAlgebra k G →ₗ[k] (ConjClasses G → k) :=
  LinearMap.pi fun C => classCoeffSum C

@[simp]
theorem classCoeffPi_apply (x : MonoidAlgebra k G) (C : ConjClasses G) :
    classCoeffPi k G x C = classCoeffSum C x := rfl

theorem classCoeffPi_single (a : G) :
    classCoeffPi k G (single a (1 : k)) = Pi.single (ConjClasses.mk a) 1 := by
  funext C
  rw [classCoeffPi_apply, classCoeffSum_single]
  by_cases h : ConjClasses.mk a = C
  · subst h; simp
  · rw [if_neg h, Pi.single_eq_of_ne' h]

theorem surjective_classCoeffPi : Function.Surjective (classCoeffPi k G) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun k (ConjClasses G)).span_eq,
    Submodule.span_le]
  rintro _ ⟨C, rfl⟩
  refine ⟨single C.out (1 : k), ?_⟩
  have hout : ConjClasses.mk (Quotient.out C) = C := Quotient.out_eq C
  rw [classCoeffPi_single, hout]
  simp

theorem commutatorSubmodule_le_ker_classCoeffPi :
    commutatorSubmodule k G ≤ LinearMap.ker (classCoeffPi k G) := fun x hx => by
  rw [LinearMap.mem_ker]
  funext C
  simpa using classCoeffSum_eq_zero_of_mem_commutatorSubmodule C hx

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- A group element and the chosen representative of its class agree in the quotient. -/
theorem mkQ_single_eq_mkQ_single_out (a : G) :
    (commutatorSubmodule k G).mkQ (single a (1 : k))
      = (commutatorSubmodule k G).mkQ (single (ConjClasses.mk a).out 1) := by
  set c := (ConjClasses.mk a).out with hc
  obtain ⟨b, hb⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
    (Quotient.out_eq (ConjClasses.mk a)))
  refine ((Submodule.Quotient.eq _).mpr ?_).symm
  rw [← hb]
  exact conjDiff_mem_commutatorSubmodule (k := k) c b

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- Every element of the quotient lies in the span of the class representatives. -/
theorem mkQ_mem_span_range_out (x : MonoidAlgebra k G) :
    (commutatorSubmodule k G).mkQ x ∈ Submodule.span k (Set.range fun C : ConjClasses G =>
      (commutatorSubmodule k G).mkQ (single C.out (1 : k))) := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    rw [MonoidAlgebra.of_apply, mkQ_single_eq_mkQ_single_out]
    exact Submodule.subset_span ⟨ConjClasses.mk a, rfl⟩
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- The images of class representatives span the quotient. -/
theorem span_range_mkQ_out_eq_top :
    Submodule.span k (Set.range fun C : ConjClasses G =>
      (commutatorSubmodule k G).mkQ (single C.out (1 : k))) = ⊤ := by
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨x, rfl⟩ := (commutatorSubmodule k G).mkQ_surjective q
  exact mkQ_mem_span_range_out x

omit [DecidableEq (ConjClasses G)] in
-- `[Fintype G]` does not appear in the statement but the proof needs it: the class-coefficient
-- functionals that give the lower bound are sums over `G`.
set_option linter.unusedFintypeInType false in
/-- **`kG ⧸ [kG, kG]` has dimension the number of conjugacy classes of `G`.** -/
theorem finrank_quotient_commutatorSubmodule :
    Module.finrank k (MonoidAlgebra k G ⧸ commutatorSubmodule k G)
      = Nat.card (ConjClasses G) := by
  classical
  have _ : Fintype (ConjClasses G) := Fintype.ofFinite _
  refine le_antisymm ?_ ?_
  · have h := finrank_range_le_card (R := k)
      (fun C : ConjClasses G => (commutatorSubmodule k G).mkQ (single C.out (1 : k)))
    rw [Set.finrank, span_range_mkQ_out_eq_top, finrank_top] at h
    simpa [Nat.card_eq_fintype_card] using h
  · have hsurj : Function.Surjective
        ((commutatorSubmodule k G).liftQ (classCoeffPi k G)
          commutatorSubmodule_le_ker_classCoeffPi) := by
      intro y
      obtain ⟨x, hx⟩ := surjective_classCoeffPi (k := k) (G := G) y
      exact ⟨(commutatorSubmodule k G).mkQ x, hx⟩
    have := LinearMap.finrank_le_finrank_of_surjective hsurj
    simpa [Nat.card_eq_fintype_card, Module.finrank_pi] using this

omit [DecidableEq (ConjClasses G)] in
-- `[Fintype G]` is used through `finrank_quotient_commutatorSubmodule`.
set_option linter.unusedFintypeInType false in
/-- **The class representatives are a basis of `kG ⧸ [kG, kG]`.**  They span
(`span_range_mkQ_out_eq_top`) and there are `dim` of them
(`finrank_quotient_commutatorSubmodule`), so they are independent. -/
theorem linearIndependent_mkQ_out :
    LinearIndependent k fun C : ConjClasses G =>
      (commutatorSubmodule k G).mkQ (single C.out (1 : k)) := by
  classical
  have _ : Fintype (ConjClasses G) := Fintype.ofFinite _
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [span_range_mkQ_out_eq_top]
  · rw [finrank_quotient_commutatorSubmodule (k := k) (G := G), Nat.card_eq_fintype_card]

end OddOrder.RepresentationTheory.Modular
