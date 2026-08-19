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

* `OddOrder.RepresentationTheory.Modular.inducedBlockOfNormalizer_principalBlock` — `b_0^G = B_0`
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
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_bij
    (i := fun (h : ↥H) _ => (h : G)) ?_ ?_ ?_]
  · intro h hh
    simpa using (Finset.mem_filter.mp hh).2
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    exact ⟨⟨g, hCH hg'.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg'⟩, rfl⟩

open scoped Classical in
/-- Counting the elements of a class as a `Finset` or as a subtype gives the same number. -/
theorem card_filter_conjClass_eq [Fintype G] (C : ConjClasses G) :
    (Finset.univ.filter fun g : G => ConjClasses.mk g = C).card
      = Nat.card {g : G // ConjClasses.mk g = C} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

section ThirdMain

variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable {πH : MonoidAlgebra k ↥H →+* ∀ j, Matrix (nn j) (nn j) k} (hπH : Function.Surjective πH)
  (hlinH : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
  (hnilH : ∀ z : Subalgebra.center k (MonoidAlgebra k ↥H),
    blockCharacterPi πH hπH hlinH z = 0 → IsNilpotent z)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable {πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k} (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

variable [Fintype G] [Fintype (ConjClasses G)] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Brauer's third main theorem, the easy half.**  For `P C_G(P) ≤ H ≤ N_G(P)` the principal
block of `H` induces the principal block of `G`.

Both blocks are named by their central characters, so it is enough to compare those on the
class-sum basis: `λ_{B_0}(K̂) = |K|·1` while `λ_{b_0}^G(K̂) = λ_{b_0}(Br_P(K̂)) = |K ∩ C_G(P)|·1`,
and `|K| ≡ |K ∩ C_G(P)| (mod p)` because `P` acts on `K` with fixed points `K ∩ C_G(P)`. -/
theorem inducedBlockOfNormalizer_principalBlock (hP : IsPGroup p ↥P) (hPH : P ≤ H)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) :
    inducedBlockOfNormalizer πH hπH hlinH πG hπG hlinG hnilG hP hPH hCH hHN
        (principalBlock πH hπH hlinH hnilH)
      = principalBlock πG hπG hlinG hnilG := by
  classical
  -- the two central characters agree on the class-sum basis
  have hL : ∀ C : ConjClasses G, inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN
      (principalBlock πH hπH hlinH hnilH) (classSumCenter (k := k) C)
      = ((Finset.univ.filter fun h : ↥H => ConjClasses.mk (h : G) = C ∧
          (h : G) ∈ Subgroup.centralizer (P : Set G)).card : k) := by
    intro C
    change blockCharacter πH hπH hlinH (principalBlock πH hπH hlinH hnilH)
      (brauerCenterHom P H hP hCH hHN (classSumCenter (k := k) C)) = _
    rw [show brauerCenterHom P H hP hCH hHN (classSumCenter (k := k) C)
        = centralizerTruncClassSumCenter hHN C from Subtype.ext (brauerTrunc_classSum C),
      blockCharacter_principalBlock, aug_centralizerTruncClassSumCenter]
  have hlam : inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN
      (principalBlock πH hπH hlinH hnilH) = aug := by
    refine AlgHom.toLinearMap_injective ((centerBasis (k := k) (G := G)).ext fun C => ?_)
    rw [centerBasis_apply]
    change inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN
      (principalBlock πH hπH hlinH hnilH) (classSumCenter (k := k) C)
      = aug (classSumCenter (k := k) C)
    rw [hL C, aug_classSumCenter C, card_filter_centralizer_eq hCH C, card_filter_conjClass_eq C]
    exact (CharP.natCast_eq_natCast' k p
      (card_conjClass_modEq_card_centralizer P C Fact.out hP)).symm
  have hdef : inducedBlockOfNormalizer πH hπH hlinH πG hπG hlinG hnilG hP hPH hCH hHN
      (principalBlock πH hπH hlinH hnilH)
      = blockOfCentralCharacter πG hπG hlinG hnilG
        (inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN
          (principalBlock πH hπH hlinH hnilH)) := rfl
  rw [hdef, hlam]
  rfl

end ThirdMain

end OddOrder.RepresentationTheory.Modular
