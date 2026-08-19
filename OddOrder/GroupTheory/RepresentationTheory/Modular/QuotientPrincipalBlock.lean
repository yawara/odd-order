/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientSplitting

/-!
# Blocks under `G ↠ G/N`: the central characters correspond

For `N` a normal `p`-subgroup, `quotientPi` splits `k[G/N]` through the *same* index set `ι` as
`π` splits `k[G]` — that is Navarro's `IBr(Ḡ) = IBr(G)` (7.6).  The block partitions of `ι` on the
two sides are therefore two partitions of one set, and this file relates them.

Everything here is the *easy* half.  `π = π̄ ∘ f` for `f = quotientMap : k[G] ↠ k[G/N]`
(`quotientPi_mapDomain`), and the central character is literally a matrix entry
(`centralScalar`), so

`ω^G_μ(z) = ω^{Ḡ}_μ(f z)`   for `z` central,

and the augmentations match the same way.  Consequently the `Ḡ`-block partition **refines** the
`G`-block partition, and `μ ∈ IBr(B_0(Ḡ)) ⟹ μ ∈ IBr(B_0(G))`.

The converse — that the two partitions are *equal*, which is what Navarro's (7.6) asserts — needs
Problem (3.4) (the Cartan matrix of a block is indecomposable) and is **not** proved here; see
issue 9506, 段 352.  The obstruction is real: `f` is not surjective on centres, because a class
sum `K̂_g` maps to `[C_{Ḡ}(ḡ) : im C_G(g)] · K̂_ḡ` and that index can be `p`.

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_quotientMap`
* `OddOrder.RepresentationTheory.Modular.centralCharacterAlg_quotientMap`
* `OddOrder.RepresentationTheory.Modular.aug_quotientMap`
* `OddOrder.RepresentationTheory.Modular.blockSetoid_quotientPi_le` — the `Ḡ`-partition refines
  the `G`-partition
* `OddOrder.RepresentationTheory.Modular.mk_eq_principalBlock_of_quotientPi` — `B_0(Ḡ) ⊆ B_0(G)`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.6).
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.MatrixModule
open OddOrder.GroupTheory.CenterSimplesOrbit (aug aug_apply)

variable {k ι G : Type*} [Field k] [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable {N : Subgroup G} [N.Normal]
variable {π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k} (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  {p : ℕ} [Fact p.Prime] [CharP k p] (hN : IsPGroup p ↥N)

/-! ### The centre maps to the centre -/

omit [Finite G] in
/-- **A surjective algebra map sends the centre into the centre.**  Here `quotientMap` is
surjective, so `f z` commutes with everything in `k[G/N]`. -/
theorem quotientMap_mem_center {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    (quotientMap (k := k) (G := G) (N := N)) z
      ∈ Subalgebra.center k (MonoidAlgebra k (G ⧸ N)) := by
  refine Subalgebra.mem_center_iff.mpr fun b => ?_
  obtain ⟨a, rfl⟩ := quotientMap_surjective (k := k) (G := G) (N := N) b
  rw [← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp hz) a]

/-! ### The central characters agree -/

include hπ hlin hN in
/-- **`ω^G_μ(z) = ω^{Ḡ}_μ(f z)`.**  The central scalar is the `(0,0)` entry of the matrix, and
`π̄ (f z) = π z` by `quotientPi_mapDomain`; the two matrices are literally equal. -/
theorem centralScalar_quotientMap (i : ι) (z : MonoidAlgebra k G) :
    centralScalar (quotientPi π hπ hlin hN).toRingHom i
        ((quotientMap (k := k) (G := G) (N := N)) z)
      = centralScalar π i z := by
  simp only [centralScalar]
  rw [show ((quotientPi π hπ hlin hN).toRingHom (quotientMap z)) = π z from
    quotientPi_mapDomain π hπ hlin hN z]

include hπ hlin hN in
/-- The `AlgHom` form of `centralScalar_quotientMap`. -/
theorem centralCharacterAlg_quotientMap (i : ι)
    (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centralCharacterAlg (quotientPi π hπ hlin hN).toRingHom i
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
        ⟨(quotientMap (k := k) (G := G) (N := N)) z, quotientMap_mem_center z.2⟩
      = centralCharacterAlg π i hπ hlin z :=
  centralScalar_quotientMap hπ hlin hN i (z : MonoidAlgebra k G)

/-! ### The augmentations agree -/

omit [Finite G] in
/-- **`ε_{Ḡ} ∘ f = ε_G`**: both are algebra maps `k[G] →ₐ[k] k` sending every `single g 1` to `1`.
-/
theorem augmentation_quotientMap (x : MonoidAlgebra k G) :
    OddOrder.Algebra.augmentation k (G ⧸ N) ((quotientMap (k := k) (G := G) (N := N)) x)
      = OddOrder.Algebra.augmentation k G x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      rw [show (MonoidAlgebra.of k G g : MonoidAlgebra k G) = single g (1 : k) from rfl,
        show (quotientMap (k := k) (G := G) (N := N)) (single g (1 : k))
          = single (QuotientGroup.mk g : G ⧸ N) (1 : k) from MonoidAlgebra.mapDomain_single,
        OddOrder.Algebra.augmentation_single, OddOrder.Algebra.augmentation_single]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

omit [Finite G] in
/-- The restriction of `augmentation_quotientMap` to the centre. -/
theorem aug_quotientMap (z : Subalgebra.center k (MonoidAlgebra k G)) :
    aug (k := k) ⟨(quotientMap (k := k) (G := G) (N := N)) z, quotientMap_mem_center z.2⟩
      = aug (k := k) z := by
  rw [aug_apply, aug_apply]
  exact augmentation_quotientMap (z : MonoidAlgebra k G)

/-! ### The block partitions -/

include hπ hlin hN in
/-- **The `Ḡ`-block partition refines the `G`-block partition.**  Two Brauer characters in the
same block of `k[G/N]` are in the same block of `k[G]`, because the `G`-central characters factor
through the `Ḡ`-ones.

The converse is Navarro (7.6) and needs Problem (3.4); see issue 9506. -/
theorem blockSetoid_quotientPi_le {μ τ : ι}
    (h : centralCharacterAlg (quotientPi π hπ hlin hN).toRingHom μ
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
      = centralCharacterAlg (quotientPi π hπ hlin hN).toRingHom τ
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) :
    centralCharacterAlg π μ hπ hlin = centralCharacterAlg π τ hπ hlin := by
  refine AlgHom.ext fun z => ?_
  rw [← centralCharacterAlg_quotientMap hπ hlin hN μ z,
    ← centralCharacterAlg_quotientMap hπ hlin hN τ z, h]

variable [Finite ι]
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilQ : ∀ z : Subalgebra.center k (MonoidAlgebra k (G ⧸ N)),
    blockCharacterPi (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) z = 0 → IsNilpotent z)

include hπ hlin hN hnil hnilQ in
/-- **`IBr(B_0(Ḡ)) ⊆ IBr(B_0(G))`.**  If `ω^{Ḡ}_μ` is the augmentation of `k[G/N]`, then
`ω^G_μ = ω^{Ḡ}_μ ∘ f = ε_{Ḡ} ∘ f = ε_G`.

This is the direction of Navarro (7.6) that comes for free.  The other inclusion is what makes
`IBr(B̄) = IBr(B)` an equality, and is not available here. -/
theorem mk_eq_principalBlock_of_quotientPi {μ : ι}
    (h : Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) μ
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ) :
    Quotient.mk (blockSetoid π hπ hlin) μ = principalBlock π hπ hlin hnil := by
  refine mk_eq_principalBlock_of_centralCharacterAlg_eq π hπ hlin hnil μ (AlgHom.ext fun z => ?_)
  have hQ : centralCharacterAlg (quotientPi π hπ hlin hN).toRingHom μ
      (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) = aug := by
    rw [← blockCharacter_mk, h]
    exact blockCharacter_principalBlock _ _ _ hnilQ
  rw [← centralCharacterAlg_quotientMap hπ hlin hN μ z, hQ, aug_quotientMap z]

end OddOrder.RepresentationTheory.Modular
