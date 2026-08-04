/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSum
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# The class sum of `W · L̂` in terms of a single Sylow subgroup

Write `W = ∑_{P ∈ Syl_p(G)} P̂` — the integral lift of `Ĝ_p`, central over any base ring
(`sum_sylow_subgroupSum_mem_center`).  Then for classes `K`, `L`

`∑_{u ∈ K} (W · L̂)(u) = |Syl_p(G)| · ∑_{x ∈ S} (K̂' · L̂)(x)`

for any single Sylow `p`-subgroup `S`, where `K'` is the class of the inverses.

Both sides are coefficients at `1` (`coeff_classSum_inv_mul_one`, `coeff_subgroupSum_mul_one`),
and the identity is then pure algebra: expand `W`, conjugate each `P̂` back to `Ŝ` — the
coefficient at `1` is conjugation invariant and `K̂'`, `L̂` are central, so nothing else moves.

This is the step that lets Navarro (4.23) compare `π(Ĝ_p L̂)` with the `|Ω_{K,L}|` side of
(4.19) **without dividing by `|K|`**: the `|K|` is cancelled while still in the domain `𝒪`.

## Main results

* `OddOrder.RepresentationTheory.sum_class_coeff_sylowSum_mul`
* `OddOrder.RepresentationTheory.sum_class_coeff_of_mem_center` — summing a central element's
  coefficients over a class multiplies by the class size
* `OddOrder.RepresentationTheory.conjugacyClassSize_mk_inv`
-/

namespace OddOrder.RepresentationTheory

open MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory.CenterClassSum

open scoped OddOrder.Conjugation Pointwise

variable {k G : Type*} [CommRing k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {p : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **`∑_{u ∈ K}(W · L̂)(u) = |Syl_p| · ∑_{x ∈ S}(K̂' · L̂)(x)`.** -/
theorem sum_class_coeff_sylowSum_mul (S : Sylow p G) [Fintype ↥(S : Subgroup G)]
    (K L : ConjClasses G) :
    ∑ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = K),
        ((∑ P : Sylow p G, subgroupSum k (P : Subgroup G)) * classSum L).coeff u
      = (Nat.card (Sylow p G) : k)
        * ∑ x : ↥(S : Subgroup G),
            (classSum (k := k) (ConjClasses.mk K.out⁻¹) * classSum (k := k) L).coeff (x : G) := by
  classical
  set Kinv : MonoidAlgebra k G := classSum (ConjClasses.mk K.out⁻¹) with hKinv
  have hKc : Kinv ∈ Subalgebra.center k (MonoidAlgebra k G) := classSum_mem_center _
  have hLc : (classSum (k := k) L) ∈ Subalgebra.center k (MonoidAlgebra k G) :=
    classSum_mem_center _
  -- both sides are coefficients at `1`
  rw [← coeff_classSum_inv_mul_one K ((∑ P : Sylow p G, subgroupSum k (P : Subgroup G))
    * classSum L), ← coeff_subgroupSum_mul_one (S : Subgroup G) (Kinv * classSum L)]
  -- expand `W`
  rw [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  -- each Sylow contributes the same
  have hterm : ∀ P : Sylow p G,
      (Kinv * (subgroupSum k (P : Subgroup G) * classSum L)).coeff 1
        = (subgroupSum k (S : Subgroup G) * (Kinv * classSum L)).coeff 1 := by
    intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
    have hSP : (MulAut.conj g) • (S : Subgroup G) = (P : Subgroup G) := by
      rw [← hg]; rfl
    have hconj : g • (Kinv * (subgroupSum k (S : Subgroup G) * classSum L))
        = Kinv * (subgroupSum k (P : Subgroup G) * classSum L) := by
      rw [smul_mul', smul_mul', conj_smul_subgroupSum_pointwise, hSP,
        (forall_smul_eq_iff_mem_center (x := Kinv)).mpr
          (fun y => ((Subalgebra.mem_center_iff.mp hKc) y).symm) g,
        (forall_smul_eq_iff_mem_center (x := classSum (k := k) L)).mpr
          (fun y => ((Subalgebra.mem_center_iff.mp hLc) y).symm) g]
    rw [← hconj, coeff_conj_smul_one]
    congr 1
    have hcomm := (Subalgebra.mem_center_iff.mp hKc) (subgroupSum k (S : Subgroup G))
    rw [← mul_assoc, ← mul_assoc, hcomm]
  rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) => hterm P, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

open scoped Classical in
/-- **The coefficients of a central element are constant on a class**, so summing over the class
multiplies by its size. -/
theorem sum_class_coeff_of_mem_center {w : MonoidAlgebra k G}
    (hw : w ∈ Subalgebra.center k (MonoidAlgebra k G)) (C : ConjClasses G) :
    ∑ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = C), w.coeff u
      = (OddOrder.RepresentationTheory.conjugacyClassSize C : k) * w.coeff C.out := by
  classical
  have hmk : ConjClasses.mk C.out = C := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hterm : ∀ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = C),
      w.coeff u = w.coeff C.out := fun u hu =>
    coeff_center_of_mk_eq hw (((Finset.mem_filter.mp hu).2).trans hmk.symm)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [OddOrder.RepresentationTheory.conjugacyClassSize, Nat.card_eq_fintype_card,
    ← Set.toFinset_card]
  refine congrArg Nat.cast (congrArg Finset.card (Finset.ext fun g => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
    ConjClasses.mem_carrier_iff_mk_eq]

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- **Inversion preserves class sizes.** -/
theorem conjugacyClassSize_mk_inv (g : G) :
    OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk g⁻¹)
      = OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk g) := by
  classical
  have hiff : ∀ a : G, a ∈ (ConjClasses.mk g⁻¹).carrier ↔ a⁻¹ ∈ (ConjClasses.mk g).carrier := by
    intro a
    simp only [ConjClasses.mem_carrier_iff_mk_eq]
    constructor
    · intro h; have := mk_inv_of_mk_eq h; rwa [inv_inv] at this
    · intro h; have := mk_inv_of_mk_eq h; rwa [inv_inv] at this
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv G) hiff)

end OddOrder.RepresentationTheory
