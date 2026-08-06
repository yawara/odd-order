/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockDefined

/-!
# The block induced from the centraliser of a `p`-element

Brauer's theorem (Navarro (4.14), `inducedBlockOfNormalizer`) makes `b^G` defined whenever
`P C_G(P) ≤ H ≤ N_G(P)` for a `p`-subgroup `P`.  The case Navarro's second main theorem lives in
is `H = C_G(x)` for a `p`-element `x`, and there the hypothesis holds for `P = ⟨x⟩`:

* `⟨x⟩` is a `p`-group because `x` is a `p`-element;
* `⟨x⟩ ≤ C_G(x)` because `x` commutes with its own powers;
* `C_G(⟨x⟩) ≤ C_G(x)` because `{x} ⊆ ⟨x⟩`;
* `C_G(x) ≤ N_G(⟨x⟩)` because centralising `x` centralises — hence normalises — `⟨x⟩`.

So *every* block of `C_G(x)` induces a block of `G`, with no side condition.  That is what turns
the pointwise second main theorem into Navarro (5.8): a statement about all blocks of `C_G(x)` at
once.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.centralizer_zpowers_eq_centralizerOf`
* `OddOrder.RepresentationTheory.Modular.inducedBlockOfCentralizer` — `b^G` for
  `b ∈ Bl(C_G(x))`

## Main results

* `OddOrder.RepresentationTheory.Modular.centralizerOf_le_normalizer_zpowers`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_toLinearMap_inducedBlockOfCentralizer` —
  the defining property `λ_{b^G} = λ_b^G`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix OddOrder.MatrixModule OddOrder.GroupTheory
open OddOrder.GroupTheory.CenterClassSum (inducedCentralCharacter)

/-! ### `⟨x⟩` and the centraliser of `x` -/

section Zpowers

variable {p : ℕ} {G : Type*} [Group G] (x : G)

/-- `x` centralises itself. -/
theorem mem_centralizerOf_self : x ∈ centralizerOf x :=
  Subgroup.mem_centralizer_iff.mpr (by rintro y rfl; rfl)

/-- `⟨x⟩ ≤ C_G(x)`: the powers of `x` commute with `x`. -/
theorem zpowers_le_centralizerOf : Subgroup.zpowers x ≤ centralizerOf x :=
  Subgroup.zpowers_le.mpr (mem_centralizerOf_self x)

/-- `C_G(⟨x⟩) ≤ C_G(x)`, since `{x} ⊆ ⟨x⟩`. -/
theorem centralizer_zpowers_le_centralizerOf :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ centralizerOf x :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x))

/-- **`C_G(⟨x⟩) = C_G(x)`**: commuting with `x` is the same as commuting with all its powers.

The inclusion `≤` is `centralizer_zpowers_le_centralizerOf`; the reverse spreads a single
commutation over the powers.  The *equality* is what reconciles the two readings of the third main
theorem — Külshammer's route states it for `C_G(Q)` with `Q = ⟨x⟩`, while the Brauer–Suzuki chain
carries `C_G(x)` (`centralizerOf`). -/
theorem centralizer_zpowers_eq_centralizerOf :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = centralizerOf x := by
  refine le_antisymm (centralizer_zpowers_le_centralizerOf x) fun c hc => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hcomm : Commute x c := (Subgroup.mem_centralizer_iff.mp hc) x rfl
  exact hcomm.zpow_left n

/-- `C_G(x) ≤ N_G(⟨x⟩)`: an element commuting with `x` commutes with all its powers, hence
normalises `⟨x⟩`. -/
theorem centralizerOf_le_normalizer_zpowers :
    centralizerOf x ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro g hg
  have hcomm : Commute x g := (Subgroup.mem_centralizer_iff.mp hg) x rfl
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hcomm.zpow_left n)

end Zpowers

/-! ### The induced block -/

section InducedBlock

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {p : ℕ} [CharP k p] (x : G) [Fintype ↥(centralizerOf x)]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k ↥(centralizerOf x) →+* ∀ j, Matrix (nn j) (nn j) k)
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥(centralizerOf x)), π (c • a) = c • π a)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k) (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
variable (hnilG : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
variable (hp : p.Prime) (hx : IsPElement p x)

open scoped Classical in
/-- **The block of `G` induced by a block of `C_G(x)`**, for `x` a `p`-element.  Brauer's theorem
applies with `P = ⟨x⟩`, so this needs no side condition. -/
noncomputable def inducedBlockOfCentralizer (b : Block π hπ hlin) : Block πG hπG hlinG :=
  haveI : Fact p.Prime := ⟨hp⟩
  inducedBlockOfNormalizer π hπ hlin πG hπG hlinG hnilG
    (OddOrder.GroupTheory.isPGroup_zpowers_of_isPElement hx) (zpowers_le_centralizerOf x)
    (centralizer_zpowers_le_centralizerOf x) (centralizerOf_le_normalizer_zpowers x) b

open scoped Classical in
/-- **The defining property of `b^G`**: its central character is Navarro's `λ_b^G`. -/
theorem blockCharacter_toLinearMap_inducedBlockOfCentralizer (b : Block π hπ hlin) :
    (blockCharacter πG hπG hlinG
        (inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b)).toLinearMap
      = inducedCentralCharacter (centralizerOf x) (blockCharacter π hπ hlin b).toLinearMap := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [inducedBlockOfCentralizer, inducedBlockOfNormalizer, inducedBlock,
    blockCharacter_blockOfCentralCharacter]
  exact inducedCentralCharacterAlgHom_toLinearMap π hπ hlin
    (OddOrder.GroupTheory.isPGroup_zpowers_of_isPElement hx) (zpowers_le_centralizerOf x)
    (centralizer_zpowers_le_centralizerOf x) (centralizerOf_le_normalizer_zpowers x) b

end InducedBlock

end OddOrder.RepresentationTheory.Modular
