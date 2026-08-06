/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockCornerLift
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlock

/-!
# Navarro (5.6)

**Navarro (5.6).**  Let `H ≤ G` and let `b` be a block of `H` whose induced block `b^G` is the
block `B` of `G`.  Then there is a `w ∈ 𝒪G` with

* (a) `(1 - f_B) f_b = (1 - f_B) w`,
* (b) `w f_b = w`,
* (c) `H` centralises `w`, and
* (d) `w` is supported on `G ∖ H`.

This is the last step before Navarro's proof (due to Isaacs) of (5.7), where the `⟨h⟩`-orbits on
`supp w` are counted; from (5.7) the Second Main Theorem (5.2) follows.

The proof is the textbook one.  Split the block idempotent as `f_B = a - c`, with
`a = ι(subgroupTrunc H f_B)` the part supported on `H` and `c = a - f_B` the part supported on
`G ∖ H` (`OddOrder.Algebra.SubgroupTruncation`).  The hypothesis `b^G = B` says exactly that
`λ_b(a*) = λ_B(e_B) = 1`, so (5.5) (`exists_corner_inverse_blockCharacter`) produces a
`y ∈ f_b Z(𝒪H)` with `a y = f_b`, and `w = c · ι y` works: (b), (c), (d) are immediate from
`y ∈ f_b Z(𝒪H)`, `H` centralising `c`, and `(G ∖ H)·H ⊆ G ∖ H`, while (a) comes from
`f_B ι(y) = ι(a y) - w = ι(f_b) - w` and `(1 - f_B) f_B = 0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_inducedBlock_witness` — Navarro (5.6)
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum
open OddOrder.GroupAlgebra (inclusionHom subgroupTrunc)

variable {𝒪 F G : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [Field F] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
variable (H : Subgroup G) [Fintype ↥H] [DecidableEq (ConjClasses ↥H)] [Fintype (ConjClasses ↥H)]
variable (φ : 𝒪 →+* F)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
  (πG : MonoidAlgebra F G →+* ∀ j, Matrix (nnG j) (nnG j) F) (hπG : Function.Surjective πG)
  (hlinG : ∀ (r : F) (x : MonoidAlgebra F G), πG (r • x) = r • πG x)
variable {ιH : Type*} [Finite ιH] {nnH : ιH → Type*} [∀ j, Fintype (nnH j)]
  [∀ j, DecidableEq (nnH j)] [∀ j, Nonempty (nnH j)]
  (πH : MonoidAlgebra F ↥H →+* ∀ j, Matrix (nnH j) (nnH j) F) (hπH : Function.Surjective πH)
  (hlinH : ∀ (r : F) (x : MonoidAlgebra F ↥H), πH (r • x) = r • πH x)

omit [IsLocalRing 𝒪] [DecidableEq (ConjClasses ↥H)] [Fintype (ConjClasses ↥H)] in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The `H`-part of a central element reduces to its truncation.**  Coefficient truncation and
coefficient reduction obviously commute; the content is that `centerTrunc`, which is defined on
the class-sum basis, *is* coefficient truncation. -/
theorem centerReduce_subgroupTrunc
    (z : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))) :
    centerReduce φ ⟨subgroupTrunc H (z : MonoidAlgebra 𝒪 G),
        OddOrder.GroupAlgebra.subgroupTrunc_mem_center z.2⟩
      = centerTrunc H (centerReduce φ z) :=
  Subtype.ext <| by
    rw [coe_centerTrunc, coe_centerReduce, coe_centerReduce, centerReduceHom_apply,
      centerReduceHom_apply, OddOrder.GroupAlgebra.mapRingHom_subgroupTrunc]

omit [Finite ιG] [Finite ιH] in
-- The finiteness instances for `H` are consumed by (5.5), applied to the group `H`.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Navarro (5.6).**  If `b` is a block of `H ≤ G` with `b^G = B`, then there is a `w ∈ 𝒪G`
supported off `H`, centralised by `H`, with `w f_b = w` and `(1 - f_B) f_b = (1 - f_B) w`. -/
theorem exists_inducedBlock_witness
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal 𝒪)
    (hnilH : ∀ z : Subalgebra.center F (MonoidAlgebra F ↥H),
      blockCharacterPi πH hπH hlinH z = 0 → IsNilpotent z)
    [DecidableEq (Block πG hπG hlinG)] [DecidableEq (Block πH hπH hlinH)]
    {B : Block πG hπG hlinG} {b : Block πH hπH hlinH}
    {fB : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))} (hfB : IsIdempotentElem fB)
    (hfBc : blockCharacterPi πG hπG hlinG (centerReduce φ fB) = Pi.single B 1)
    {fb : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥H))} (hfb : IsIdempotentElem fb)
    (hfbc : blockCharacterPi πH hπH hlinH (centerReduce φ fb) = Pi.single b 1)
    (hbG : (blockCharacter πG hπG hlinG B).toLinearMap
      = inducedCentralCharacter H (blockCharacter πH hπH hlinH b).toLinearMap) :
    ∃ w : MonoidAlgebra 𝒪 G,
      (1 - (fB : MonoidAlgebra 𝒪 G)) * inclusionHom H (fb : MonoidAlgebra 𝒪 ↥H)
          = (1 - (fB : MonoidAlgebra 𝒪 G)) * w ∧
        w * inclusionHom H (fb : MonoidAlgebra 𝒪 ↥H) = w ∧
        (∀ h : ↥H, MonoidAlgebra.single (h : G) (1 : 𝒪) * w
          = w * MonoidAlgebra.single (h : G) (1 : 𝒪)) ∧
        ∀ g ∈ H, w.coeff g = 0 := by
  classical
  -- multiplication in a centre is commutative
  have hcomm : ∀ u v : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥H)), u * v = v * u :=
    fun u v => Subtype.ext (Subalgebra.mem_center_iff.mp u.2 (v : MonoidAlgebra 𝒪 ↥H)).symm
  -- the `H`-part `a` of `f_B` and the off-`H` part `c`
  have hAmem : subgroupTrunc H (fB : MonoidAlgebra 𝒪 G)
      ∈ Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥H) :=
    OddOrder.GroupAlgebra.subgroupTrunc_mem_center fB.2
  set a : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥H)) :=
    ⟨subgroupTrunc H (fB : MonoidAlgebra 𝒪 G), hAmem⟩ with hadef
  set c : MonoidAlgebra 𝒪 G :=
    inclusionHom H (a : MonoidAlgebra 𝒪 ↥H) - (fB : MonoidAlgebra 𝒪 G) with hcdef
  have hcoff : ∀ g ∈ H, c.coeff g = 0 := fun g hg =>
    OddOrder.GroupAlgebra.coeff_inclusionHom_subgroupTrunc_sub _ hg
  have hccomm : ∀ h : ↥H, MonoidAlgebra.single (h : G) (1 : 𝒪) * c
      = c * MonoidAlgebra.single (h : G) (1 : 𝒪) := by
    intro h
    rw [hcdef, mul_sub, sub_mul, OddOrder.GroupAlgebra.commute_single_inclusionHom hAmem h 1,
      Subalgebra.mem_center_iff.mp fB.2 (MonoidAlgebra.single (h : G) (1 : 𝒪))]
  -- `λ_b(a*) = λ_B(e_B) = 1`
  have hBone : blockCharacter πG hπG hlinG B (centerReduce φ fB) = 1 := by
    have h := congrFun hfBc B
    rwa [blockCharacterPi_apply, Pi.single_eq_same] at h
  have hone : blockCharacter πH hπH hlinH b (centerReduce φ a) = 1 := by
    have hlm := LinearMap.congr_fun hbG (centerReduce φ fB)
    rw [inducedCentralCharacter, LinearMap.comp_apply] at hlm
    simp only [AlgHom.toLinearMap_apply] at hlm
    rw [hadef, centerReduce_subgroupTrunc H φ fB, ← hlm]
    exact hBone
  -- (5.5) in `H`
  obtain ⟨y, hy1, hy2, -⟩ :=
    exists_corner_inverse_blockCharacter φ πH hπH hlinH hφ hker hnilH hfb hfbc hone
  have hay : a * y = fb := by
    calc a * y = a * (fb * y) := by rw [← hy1]
      _ = (fb * a) * y := by rw [← mul_assoc, hcomm a fb]
      _ = fb := hy2
  have hyfb : (y : MonoidAlgebra 𝒪 ↥H) * (fb : MonoidAlgebra 𝒪 ↥H) = (y : MonoidAlgebra 𝒪 ↥H) := by
    have : y * fb = y := by rw [hcomm y fb, ← hy1]
    exact congrArg Subtype.val this
  refine ⟨c * inclusionHom H (y : MonoidAlgebra 𝒪 ↥H), ?_, ?_, ?_, ?_⟩
  · -- (a)
    have hkey : (fB : MonoidAlgebra 𝒪 G) * inclusionHom H (y : MonoidAlgebra 𝒪 ↥H)
        = inclusionHom H (fb : MonoidAlgebra 𝒪 ↥H)
          - c * inclusionHom H (y : MonoidAlgebra 𝒪 ↥H) := by
      rw [hcdef, sub_mul, ← map_mul,
        show (a : MonoidAlgebra 𝒪 ↥H) * (y : MonoidAlgebra 𝒪 ↥H) = (fb : MonoidAlgebra 𝒪 ↥H) from
          congrArg Subtype.val hay]
      rw [sub_sub_cancel]
    have hzero : (1 - (fB : MonoidAlgebra 𝒪 G))
        * (inclusionHom H (fb : MonoidAlgebra 𝒪 ↥H) - c * inclusionHom H (y : MonoidAlgebra 𝒪 ↥H))
        = 0 := by
      rw [← hkey, ← mul_assoc, sub_mul, one_mul,
        show (fB : MonoidAlgebra 𝒪 G) * (fB : MonoidAlgebra 𝒪 G) = (fB : MonoidAlgebra 𝒪 G) from
          congrArg Subtype.val hfB,
        sub_self, zero_mul]
    have hfin : (1 - (fB : MonoidAlgebra 𝒪 G)) * inclusionHom H (fb : MonoidAlgebra 𝒪 ↥H)
        - (1 - (fB : MonoidAlgebra 𝒪 G)) * (c * inclusionHom H (y : MonoidAlgebra 𝒪 ↥H)) = 0 := by
      rw [← mul_sub]; exact hzero
    exact sub_eq_zero.mp hfin
  · -- (b)
    rw [mul_assoc, ← map_mul, hyfb]
  · -- (c)
    intro h
    rw [← mul_assoc, hccomm h, mul_assoc, mul_assoc,
      ← OddOrder.GroupAlgebra.commute_single_inclusionHom y.2 h 1]
  · -- (d)
    intro g hg
    exact OddOrder.GroupAlgebra.coeff_mul_inclusionHom_eq_zero hcoff _ hg

end OddOrder.RepresentationTheory.Modular
