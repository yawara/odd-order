/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSum
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCore

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
-/

namespace OddOrder.RepresentationTheory

open MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory.CenterClassSum

open scoped OddOrder.Conjugation Pointwise

variable {k G : Type*} [CommRing k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {p : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **`∑_{u ∈ K}(W · L̂)(u) = |Syl_p| · ∑_{x ∈ S}(K̂' · L̂)(x)`.** -/
theorem sum_class_coeff_sylowSum_mul (S : Sylow p G) (K L : ConjClasses G) :
    ∑ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = K),
        ((∑ P : Sylow p G, subgroupSum k (P : Subgroup G)) * classSum L).coeff u
      = (Nat.card (Sylow p G) : k)
        * letI := Fintype.ofFinite ↥(S : Subgroup G)
          ∑ x : ↥(S : Subgroup G),
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

end OddOrder.RepresentationTheory
