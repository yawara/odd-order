/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralScalarBridge
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockNonvanishing

/-!
# The trivial character lies in the principal block

`principalBlock` is *defined* by its central character being the augmentation, which avoids having
to locate the trivial character inside a Wedderburn splitting.  What Navarro's arguments then use
is the converse reading: the trivial character `1_G` really is one of the `χ ∈ Irr(B_0)`, and its
value is `1` everywhere — "these are columns of integers having a `1` as the first entry"
(p. 140).

`exists_trivial_wedderburn_index` produces the index; what is proved here is that its block is
`B_0`.  Both blocks are pinned by their central characters, and the class sums are a basis of the
centre (`centerBasis`), so it is enough to compare them on `K̂`:

* on the trivial block, `ω(K̂) · χ(1) = ∑_{g ∈ K} χ(g) = |K|` with `χ(1) = χ(g) = 1`;
* the lattice central character agrees with it under `𝒪 → K` (`algebraMap_centralScalar_eq`), and
  `𝒪 → K` is injective, so the lattice value is `|K| ∈ 𝒪`;
* its residue is `|K|*`, which is `aug(K̂)` (`aug_classSumCenter`).

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_classSum_of_trivial` — `ω(K̂) = |K|`
* `OddOrder.RepresentationTheory.Modular.blockOfIrr_eq_principalBlock_of_trivial` — the block of
  the trivial character is `B_0`
* `OddOrder.RepresentationTheory.Modular.exists_blockOfIrr_eq_principalBlock_character_eq_one` —
  there is `χ ∈ Irr(B_0)` with `χ(g) = 1` for every `g`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra MatrixModule OddOrder.GroupTheory.CenterClassSum
open OddOrder.GroupTheory.CenterSimplesOrbit (aug)

section Character

variable {K G : Type*} [Field K] [Group G]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

/-- **A trivial Wedderburn block has character `1`.**  Every `ρ(g)` is the identity of a
one-dimensional space. -/
theorem character_eq_one_of_trivial [Subsingleton (m i)] [Nonempty (m i)]
    (htriv : ∀ (g : G) (w : m i → K), wedderburnRepresentation e i g w = w) (g : G) :
    (wedderburnRepresentation e i).character g = 1 := by
  have hid : (wedderburnRepresentation e i) g = LinearMap.id := LinearMap.ext (htriv g)
  rw [Representation.character, hid, LinearMap.trace_id, Module.finrank_fintype_fun_eq_card,
    Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨uniqueOfSubsingleton (Classical.arbitrary (m i))⟩,
    Nat.cast_one]

end Character

section CentralScalar

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

/-- **The central character of a trivial Wedderburn block is the augmentation**, read on a class
sum: `ω(K̂) = |K|`. -/
theorem centralScalar_classSum_of_trivial [Subsingleton (m i)]
    (htriv : ∀ (g : G) (w : m i → K), wedderburnRepresentation e i g w = w)
    (C : ConjClasses G) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
      = ((Finset.univ.filter fun g : G => ConjClasses.mk g = C).card : K) := by
  classical
  have h := centralScalar_classSum_mul_character_one e i C
  rw [character_eq_one_of_trivial e i htriv 1, mul_one] at h
  rw [h, Finset.sum_congr rfl fun g _ => by
    rw [character_eq_one_of_trivial e i htriv g], Finset.sum_boole]

end CentralScalar

section PrincipalBlock

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

set_option maxHeartbeats 800000 in
-- `Fintype G` is what makes the invariant lattice (and hence `centralScalar`) elaborate.
set_option linter.unusedFintypeInType false in
omit [HenselianLocalRing 𝒪] [Fintype (ConjClasses G)] in
/-- **The lattice central character of the trivial block on a class sum** is `|K| ∈ 𝒪`.  Apply the
injection `𝒪 → K` and use `algebraMap_centralScalar_eq`. -/
theorem centralScalar_lattice_classSum_of_trivial (i : ι') [Subsingleton (m i)]
    (htriv : ∀ (g : G) (w : m i → K), wedderburnRepresentation e i g w = w)
    (C : ConjClasses G) :
    centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i) (classSumCenter C)
      = ((Finset.univ.filter fun g : G => ConjClasses.mk g = C).card : 𝒪) := by
  classical
  refine IsFractionRing.injective 𝒪 K ?_
  rw [algebraMap_centralScalar_eq e i (classSumCenter C), classSumCenter_coe,
    mapRingHom_classSum (algebraMap 𝒪 K) C, centralScalar_classSum_of_trivial e i htriv C,
    map_natCast]

set_option maxHeartbeats 1600000 in
-- The block characters carry the full modular-datum chain.
set_option linter.unusedFintypeInType false in
/-- **The block of the trivial character is the principal block.**  Both are pinned by their
central characters, and on the class-sum basis of the centre both give `|K|*`. -/
theorem blockOfIrr_eq_principalBlock_of_trivial (i : ι') [Subsingleton (m i)]
    (htriv : ∀ (g : G) (w : m i → K), wedderburnRepresentation e i g w = w) :
    blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG := by
  classical
  refine MatrixModule.eq_blockOfCentralCharacter πG hπG hlinG hnilG ?_
  have hlin : (MatrixModule.blockCharacter πG hπG hlinG
        (blockOfIrr e hπG hlinG hnilG i)).toLinearMap
      = (aug (k := ResidueField 𝒪) (G := G)).toLinearMap := by
    refine Module.Basis.ext (OddOrder.GroupTheory.CenterClassSum.centerBasis) fun C => ?_
    change MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
        (OddOrder.GroupTheory.CenterClassSum.centerBasis C)
      = aug (OddOrder.GroupTheory.CenterClassSum.centerBasis C)
    rw [OddOrder.GroupTheory.CenterClassSum.centerBasis_apply,
      show blockOfIrr e hπG hlinG hnilG i
          = blockOfLattice K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
            (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        from rfl,
      blockCharacter_blockOfLattice_mapRingHom K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        (classSumCenter C) (z' := classSumCenter C)
        (by rw [classSumCenter_coe, classSumCenter_coe, mapRingHom_classSum]),
      centralScalar_lattice_classSum_of_trivial e i htriv C, map_natCast, aug_classSumCenter]
  exact AlgHom.ext fun z => LinearMap.congr_fun hlin z

set_option maxHeartbeats 800000 in
-- Same modular-datum chain as the block-character comparison it packages.
set_option linter.unusedFintypeInType false in
/-- **There is a character of `Irr(B_0)` that is identically `1`** — the trivial character.  This
is Navarro's "`1` as the first entry" of the columns of the principal block (p. 140). -/
theorem exists_blockOfIrr_eq_principalBlock_character_eq_one :
    ∃ i : ι', blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG
      ∧ ∀ g : G, (wedderburnRepresentation e i).character g = 1 := by
  classical
  obtain ⟨i, hsub, htriv⟩ := exists_trivial_wedderburn_index e
  have := hsub
  exact ⟨i, blockOfIrr_eq_principalBlock_of_trivial e hπG hlinG hnilG i htriv,
    fun g => character_eq_one_of_trivial e i htriv g⟩

end PrincipalBlock

end OddOrder.RepresentationTheory.Modular
