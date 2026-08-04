/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCorrespondence
import OddOrder.GroupTheory.RepresentationTheory.Modular.ClassCentralizerCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockDefined
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock

/-!
# Brauer's third main theorem: the principal block induces the principal block

`b_0^G = B_0` for `P C_G(P) ≤ H ≤ N_G(P)`.  Both sides are blocks of `kG`, so it is enough to
compare their central characters on the class-sum basis of `Z(kG)`:

* `λ_{B_0}(K̂) = |K|·1` (`aug_classSumCenter`);
* `λ_{b_0}^G(K̂) = λ_{b_0}(Br_P(K̂)) = |K ∩ C_G(P)|·1` (Navarro (4.14) plus
  `aug_centralizerTruncClassSumCenter`);

and `|K| ≡ |K ∩ C_G(P)| (mod p)` (`card_conjClass_modEq_card_centralizer`), which in
characteristic `p` says the two agree.

⚠ This is only the *easy* half of the third main theorem.  The converse — a block of `H` inducing
`B_0` must be `b_0` — needs Okuyama's argument and with it the theory of heights.

## Main results

* `OddOrder.RepresentationTheory.Modular.aug_centralizerTruncClassSumCenter` — `λ_{b_0}(Br_P(K̂))`
* `OddOrder.RepresentationTheory.Modular.card_filter_centralizer_eq` — counting `K ∩ C_G(P)`
  inside `H` or inside `G` gives the same number

⚠ The assembly `b_0^G = B_0` itself is not here yet; these are the two evaluations it compares.
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum
open OddOrder.GroupTheory.CenterSimplesOrbit (aug aug_apply)

variable {k G : Type*} [Field k] [Group G] [DecidableEq (ConjClasses G)]
variable {P H : Subgroup G} [Fintype ↥H]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (P : Set G)]

open scoped Classical in
/-- **The augmentation of `Br_P(K̂)` is `|K ∩ H ∩ C_G(P)|·1`.**  Same computation as
`aug_classSumCenter`, on the truncated class sum. -/
theorem aug_centralizerTruncClassSumCenter (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (C : ConjClasses G) :
    aug (centralizerTruncClassSumCenter (k := k) hHN C)
      = ((Finset.univ.filter fun h : ↥H =>
          ConjClasses.mk (h : G) = C ∧ (h : G) ∈ Subgroup.centralizer (P : Set G)).card : k) := by
  classical
  rw [aug_apply, show ((centralizerTruncClassSumCenter (k := k) hHN C :
      Subalgebra.center k (MonoidAlgebra k ↥H)) : MonoidAlgebra k ↥H)
      = centralizerTruncClassSum P H C from rfl, centralizerTruncClassSum, map_sum]
  rw [Finset.sum_congr rfl fun (h : ↥H) _ => show
      OddOrder.Algebra.augmentation k ↥H
          (if ConjClasses.mk (h : G) = C ∧ (h : G) ∈ Subgroup.centralizer (P : Set G)
            then MonoidAlgebra.of k ↥H h else 0)
        = if ConjClasses.mk (h : G) = C ∧ (h : G) ∈ Subgroup.centralizer (P : Set G)
            then (1 : k) else 0 from by
    split
    · rw [MonoidAlgebra.of_apply, OddOrder.Algebra.augmentation_single]
    · rw [map_zero]]
  rw [Finset.sum_boole]

open scoped Classical in
/-- **The elements of a class that centralise `P` all lie in `H`**, when `C_G(P) ≤ H`; so counting
them inside `H` or inside `G` gives the same number. -/
theorem card_filter_centralizer_eq [Finite G] (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (C : ConjClasses G) :
    (Finset.univ.filter fun h : ↥H =>
        ConjClasses.mk (h : G) = C ∧ (h : G) ∈ Subgroup.centralizer (P : Set G)).card
      = Nat.card {g : G // ConjClasses.mk g = C ∧ g ∈ Subgroup.centralizer (P : Set G)} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_bij
    (i := fun (h : ↥H) _ => (h : G)) ?_ ?_ ?_]
  · intro h hh
    simpa using (Finset.mem_filter.mp hh).2
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    exact ⟨⟨g, hCH hg'.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg'⟩, rfl⟩

end OddOrder.RepresentationTheory.Modular
