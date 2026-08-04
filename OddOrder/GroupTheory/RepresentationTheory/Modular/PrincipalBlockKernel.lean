/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.NormalPSubgroupTrivialAction
import OddOrder.Algebra.SubgroupSumBlockAction
import OddOrder.GroupTheory.ThreeStepGroup
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock

/-!
# The kernel of the principal block

For the principal block everything about `ker(B_0)` is elementary, because its central character
*is* the augmentation (`blockCharacter_principalBlock`): `λ_{B_0}(N̂) = |N|` holds for **every**
normal subgroup `N`, with no reference to ordinary characters, lattices or `𝒪` at all.

So the two mechanisms of Navarro (6.10)/(6.12) become, for `B_0`:

* a normal subgroup `N` with `|N|` invertible in `k` is killed by every irreducible Brauer
  character of `B_0` (`pi_single_eq_one_principalBlock`);
* if in addition `G = N·P` for a `p`-subgroup `P`, *everything* is killed
  (`pi_single_eq_one_principalBlock_of_sup_eq_top`), so the simple modules of `B_0` are trivial.

The second is the direction of Navarro (6.13) that the Brauer–Suzuki argument uses: a group with a
normal `p`-complement `N` satisfies `G = N·P` for `P` a Sylow `p`-subgroup, so `IBr(B_0)` consists
of trivial Brauer characters.

## Main results

* `OddOrder.RepresentationTheory.Modular.blockCharacter_principalBlock_subgroupSum` —
  `λ_{B_0}(N̂) = |N|`
* `OddOrder.RepresentationTheory.Modular.pi_single_eq_one_principalBlock`
* `OddOrder.RepresentationTheory.Modular.pi_single_eq_one_principalBlock_of_sup_eq_top`
* `OddOrder.RepresentationTheory.Modular.pi_single_eq_one_principalBlock_of_normalPComplement` —
  Navarro (6.13) in the form Brauer–Suzuki cites it
* `OddOrder.RepresentationTheory.Modular.eq_of_principalBlock_of_normalPComplement`,
  `OddOrder.RepresentationTheory.Modular.subsingleton_of_principalBlock_of_normalPComplement` —
  `IBr(B_0) = {1_{G^0}}`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.MatrixModule

variable {k G : Type*} [Field k] [Group G] [Finite G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)]
  [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)

/-- **`λ_{B_0}(N̂) = |N|`.**  The central character of the principal block is the augmentation, and
the augmentation of `N̂ = ∑_{n ∈ N} n` counts `N`. -/
theorem blockCharacter_principalBlock_subgroupSum {N : Subgroup G} (hN : N.Normal) :
    blockCharacter π hπ hlin (principalBlock π hπ hlin hnil)
        ⟨subgroupSum k N, subgroupSum_mem_center hN⟩ = ((Nat.card ↥N : ℕ) : k) := by
  rw [blockCharacter_principalBlock, OddOrder.GroupTheory.CenterSimplesOrbit.aug_apply]
  rw [map_subgroupSum_of_forall_map_single_eq_one (OddOrder.Algebra.augmentation k G)
    fun n _ => OddOrder.Algebra.augmentation_single k G n 1]
  simp

/-- **A normal subgroup of order prime to `p` is killed by the principal block.**  The
`p'`-half of Navarro (6.10)/(6.12), for `B_0` and without any ordinary-character input. -/
theorem pi_single_eq_one_principalBlock {N : Subgroup G} (hN : N.Normal)
    (hNk : ((Nat.card ↥N : ℕ) : k) ≠ 0) {i : ι}
    (hiB : Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil)
    {u : G} (hu : u ∈ N) : π (single u (1 : k)) i = 1 := by
  refine pi_single_eq_one_of_isUnit_centralScalar π i hπ hN ?_ hu
  have hscal : centralScalar π i (subgroupSum k N) = ((Nat.card ↥N : ℕ) : k) := by
    have hcc : centralScalar π i (subgroupSum k N)
        = centralCharacterAlg π i hπ hlin ⟨subgroupSum k N, subgroupSum_mem_center hN⟩ := rfl
    rw [hcc, ← blockCharacter_mk π hπ hlin i, hiB,
      blockCharacter_principalBlock_subgroupSum π hπ hlin hnil hN]
  rw [hscal, isUnit_iff_ne_zero]
  exact hNk

/-- **Navarro (6.13), the direction used by Brauer–Suzuki**: if `G = N·P` with `N ⊴ G` of order
prime to `p` and `P` a `p`-subgroup, then the simple modules of the principal block are trivial.

A group with a normal `p`-complement `N` is of this shape with `P` a Sylow `p`-subgroup, so its
principal block has only the trivial Brauer character. -/
theorem pi_single_eq_one_principalBlock_of_sup_eq_top {p : ℕ} [Fact p.Prime] [CharP k p]
    {N P : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hP : IsPGroup p ↥P)
    (hsup : N ⊔ P = ⊤) {i : ι}
    (hiB : Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil) (g : G) :
    π (single g (1 : k)) i = 1 := by
  have hNk : ((Nat.card ↥N : ℕ) : k) ≠ 0 := fun h => hNp ((CharP.cast_eq_zero_iff k p _).mp h)
  have hker : ∀ u ∈ N, blockRepresentation π i u = 1 := by
    intro u hu
    have h1 : π (single u (1 : k)) i = 1 :=
      pi_single_eq_one_principalBlock π hπ hlin hnil ‹N.Normal› hNk hiB hu
    change Matrix.toLinAlgEquiv' (π (single u (1 : k)) i) = 1
    rw [h1, map_one]
  apply (Matrix.toLinAlgEquiv' (R := k) (n := nn i)).injective
  rw [map_one]
  exact blockRepresentation_eq_one_of_sup_eq_top π hπ hlin hP hsup i hker g

/-- **Navarro (6.13), as Brauer–Suzuki cites it.**  If `G` has a normal `p`-complement `N` — a
normal subgroup of order prime to `p` with `G/N` a `p`-group — then every simple module of the
principal block is trivial, so `IBr(B_0) = {1_{G^0}}`.

`G = N·S` for `S` a Sylow `p`-subgroup because `S` covers the `p`-quotient `G/N`. -/
theorem pi_single_eq_one_principalBlock_of_normalPComplement {p : ℕ} [Fact p.Prime] [CharP k p]
    {N : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N))
    (S : Sylow p G) {i : ι}
    (hiB : Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil) (g : G) :
    π (single g (1 : k)) i = 1 := by
  haveI := Fintype.ofFinite G
  refine pi_single_eq_one_principalBlock_of_sup_eq_top π hπ hlin hnil hNp S.isPGroup' ?_ hiB g
  rw [sup_comm]
  exact OddOrder.GroupTheory.sylow_sup_eq_top_of_isPGroup_quotient hquot S

/-- **Navarro (6.13): `IBr(B_0) = {1_{G^0}}`.**  If `G` has a normal `p`-complement, the principal
block has exactly one irreducible Brauer character.

Both statements come out of the trivial action: a block killing `G` is the augmentation, so it has
degree one and there is at most one of it. -/
theorem eq_of_principalBlock_of_normalPComplement {p : ℕ} [Fact p.Prime] [CharP k p]
    {N : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N))
    (S : Sylow p G) {i j : ι}
    (hiB : Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil)
    (hjB : Quotient.mk (blockSetoid π hπ hlin) j = principalBlock π hπ hlin hnil) : i = j :=
  eq_of_forall_pi_single_eq_one π hπ hlin
    (pi_single_eq_one_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hiB)
    (pi_single_eq_one_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hjB)

/-- **Navarro (6.13): the unique Brauer character of `B_0` has degree one.** -/
theorem subsingleton_of_principalBlock_of_normalPComplement {p : ℕ} [Fact p.Prime] [CharP k p]
    {N : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N))
    (S : Sylow p G) {i : ι}
    (hiB : Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil) :
    Subsingleton (nn i) :=
  subsingleton_of_forall_pi_single_eq_one π hπ hlin
    (pi_single_eq_one_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hiB)

end OddOrder.RepresentationTheory.Modular
