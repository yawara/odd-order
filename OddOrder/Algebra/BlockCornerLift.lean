/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockCornerInverse
import OddOrder.Algebra.CenterIdempotentLift

/-!
# Navarro (5.5)

**Navarro (5.5).**  Let `B` be a block of `G` with idempotent `f_B ∈ Z(𝒪G)`, and let
`x ∈ Z(𝒪G)` satisfy `λ_B(x*) = 1`.  Then `f_B x` has an inverse in the corner `f_B Z(𝒪G)`.

The three ingredients are already in place:

* over the residue field, `e_B x*` is corner-invertible because every block character kills
  `e_B x* - e_B` (`exists_corner_inverse_of_blockCharacter_eq_one`);
* that inverse lifts to `Z(𝒪G)`, where it is only an *approximate* corner inverse — the error
  lies in the kernel of the reduction, which is `𝔪·Z(𝒪G)`
  (`mem_centerIdeal_iff_centerReduce_eq_zero`);
* an approximate corner inverse can be corrected (`exists_corner_inverse_of_approx`, which is
  (5.4)).

## Main results

* `OddOrder.exists_corner_inverse_blockCharacter` — Navarro (5.5)
-/

namespace OddOrder

open OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum

variable {𝒪 F G : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [Field F] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
variable {ι : Type*} [Finite ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (φ : 𝒪 →+* F)
variable (π : MonoidAlgebra F G →+* ∀ j, Matrix (nn j) (nn j) F) (hπ : Function.Surjective π)
  (hlin : ∀ (c : F) (a : MonoidAlgebra F G), π (c • a) = c • π a)

-- The finiteness instances are consumed by the class-sum basis and the kernel description.
omit [Finite ι] in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Navarro (5.5).**  If `f` is the idempotent of the block `c` and `x ∈ Z(𝒪G)` has
`λ_c(x*) = 1`, then `f x` is invertible in the corner `f Z(𝒪G)`. -/
theorem exists_corner_inverse_blockCharacter
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal 𝒪)
    (hnil : ∀ z : Subalgebra.center F (MonoidAlgebra F G),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    [DecidableEq (Block π hπ hlin)] {c : Block π hπ hlin}
    {f : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))} (hf : IsIdempotentElem f)
    (hfc : blockCharacterPi π hπ hlin (centerReduce φ f) = Pi.single c 1)
    {x : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))}
    (hx : blockCharacter π hπ hlin c (centerReduce φ x) = 1) :
    ∃ y : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      y = f * y ∧ (f * x) * y = f ∧ y * (f * x) = f := by
  classical
  haveI : Module.Finite 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
    Module.Finite.of_basis (centerBasis (k := 𝒪) (G := G))
  haveI : Nontrivial ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
    ⟨0, 1, fun h => one_ne_zero (congrArg Subtype.val h).symm⟩
  -- the residue-field corner inverse
  have hef : IsIdempotentElem (centerReduce φ f) := by
    have h : centerReduce φ f * centerReduce φ f = centerReduce φ f := by rw [← map_mul, hf]
    exact h
  obtain ⟨ybar, hybc, hyb1, -⟩ :=
    exists_corner_inverse_of_blockCharacter_eq_one π hπ hlin hnil hef hfc hx
  -- lift it
  obtain ⟨w0, hw0mem, hw0⟩ := exists_mem_center_mapRingHom_eq (G := G) hφ ybar.2
  set w : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) := ⟨w0, hw0mem⟩ with hwdef
  have hwred : centerReduce φ w = ybar := Subtype.ext hw0
  -- the lift is an approximate corner inverse
  have hey : centerReduce φ f * ybar = ybar := by
    calc centerReduce φ f * ybar
        = centerReduce φ f * (centerReduce φ f * ybar * centerReduce φ f) := by
          conv_lhs => rw [hybc]
      _ = centerReduce φ f * centerReduce φ f * ybar * centerReduce φ f := by ring
      _ = centerReduce φ f * ybar * centerReduce φ f := by rw [hef]
      _ = ybar := hybc.symm
  have happrox : f - (f * x) * (f * w) ∈ centerIdeal (G := G) (IsLocalRing.maximalIdeal 𝒪) := by
    rw [mem_centerIdeal_iff_centerReduce_eq_zero _ φ hker, map_sub, map_mul, map_mul, map_mul,
      hwred, hey, hyb1, sub_self]
  -- correct it
  refine exists_corner_inverse_of_approx (𝒪 := 𝒪) hf ?_ ?_ happrox
  · rw [← mul_assoc, hf]
  · rw [← mul_assoc, hf]

end OddOrder
