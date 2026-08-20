/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.CharacterCore
import OddOrder.GroupTheory.GlaubermanZStar.CharacterIdentity
import OddOrder.GroupTheory.RepresentationTheory.CharacterInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishing
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockTrivial

/-!
# Glauberman's `Z*`-theorem: Step 9 and the final contradiction

Navarro (7.9), Step 9 and the closing paragraph.  With `v ∈ P` a second involution:

* **Step 9.**  For `χ ∈ Irr(B_0)`, `χ(u) χ(v) = χ(u v) χ(1)`
  (`character_mul_eq_of_const_on_class_product` fed by Step 8).  Applying the same to the
  involution `u v` gives `χ(u)² χ(v) = χ(v) χ(1)²`, so either `χ(v) = 0` or `χ(u) = ± χ(1)`.
* **The final contradiction.**  Block orthogonality (Navarro (5.11),
  `sum_character_blockOfIrr_eq_zero`) applied to the non-conjugate pairs `(v, u)` and `(v, 1)`
  gives
  `∑_{χ ∈ Irr(B_0)} χ(v) (χ(u) + χ(1)) = 0`.  Every summand vanishes except those `χ` with
  `χ(u) = χ(1)`; for those, `u` lies in `ker χ`, which is normal, so Step 3 forces `ker χ = G`,
  `χ` is the constant `χ(1)`, and the summand is `2 χ(1)²`.  At least one such `χ` exists — the
  trivial character lies in `B_0` — so the sum is a nonzero natural number in a characteristic
  zero field.

## Main results

* `OddOrder.GroupTheory.MinimalConfig.false_of_exists_involution`
-/

open OddOrder.Isaacs.Ch03 OddOrder.RepresentationTheory.Modular
open OddOrder.RepresentationTheory OddOrder.MatrixModule

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

namespace MinimalConfig

variable {G : Type v} [Group G] [Finite G] (cfg : MinimalConfig G)

section Final

variable [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
  {ι'G : Type} [Fintype ι'G] {mG : ι'G → Type} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [∀ i, Nonempty (mG i)]
  {ιG : Type} [Fintype ιG] {nnG : ιG → Type} [∀ j, Fintype (nnG j)] [∀ j, DecidableEq (nnG j)]
  [∀ j, Nonempty (nnG j)]
  (eG : MonoidAlgebra ℂ_[2] G ≃ₐ[ℂ_[2]] ∀ i, Matrix (mG i) (mG i) ℂ_[2])
  {πG : MonoidAlgebra (IsLocalRing.ResidueField 𝓞_ℂ_[2]) G →+*
    ∀ j, Matrix (nnG j) (nnG j) (IsLocalRing.ResidueField 𝓞_ℂ_[2])}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : IsLocalRing.ResidueField 𝓞_ℂ_[2])
    (a : MonoidAlgebra (IsLocalRing.ResidueField 𝓞_ℂ_[2]) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (IsLocalRing.ResidueField 𝓞_ℂ_[2])
      (MonoidAlgebra (IsLocalRing.ResidueField 𝓞_ℂ_[2]) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  (hkerJG : RingHom.ker πG
    = Ring.jacobson (MonoidAlgebra (IsLocalRing.ResidueField 𝓞_ℂ_[2]) G))

set_option maxHeartbeats 1600000 in
-- Step 8 is invoked twice (at `v` and at `u v`), each time through the `C_G(z)` datum.
set_option linter.unusedFintypeInType false in
include hkerJG in
/-- **Navarro (7.9), Step 9.**  For `χ ∈ Irr(B_0)` either `χ(v) = 0` or `χ(u)² = χ(1)²`. -/
theorem character_sq_eq_of_character_ne_zero {v : G} (hv : v ∈ (cfg.P : Subgroup G))
    (hv2 : orderOf v = 2) (hvne : v ≠ cfg.u)
    {i : ι'G} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) :
    (wedderburnRepresentation eG i).character v
        * ((wedderburnRepresentation eG i).character cfg.u
          * (wedderburnRepresentation eG i).character cfg.u)
      = (wedderburnRepresentation eG i).character v
        * ((wedderburnRepresentation eG i).character 1
          * (wedderburnRepresentation eG i).character 1) := by
  classical
  have huv : cfg.u * v = v * cfg.u := by
    have h := cfg.conj_eq_of_mem_sylow hv
    have h2 := congrArg (fun a => a * v) h
    simp only [inv_mul_cancel_right] at h2
    exact h2.symm
  have hv2' : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, sq] at this
  have hvne1 : v ≠ 1 := fun h => by
    have hord := hv2
    rw [h, orderOf_one] at hord
    omega
  -- `u v` is another involution of `P` different from `u`
  have huvP : cfg.u * v ∈ (cfg.P : Subgroup G) := mul_mem cfg.mem_sylow hv
  have huv2 : (cfg.u * v) * (cfg.u * v) = 1 := by
    calc cfg.u * v * (cfg.u * v) = cfg.u * (v * cfg.u) * v := by group
      _ = cfg.u * (cfg.u * v) * v := by rw [← huv]
      _ = (cfg.u * cfg.u) * (v * v) := by group
      _ = 1 := by rw [cfg.mul_self, hv2', mul_one]
  have huvne : cfg.u * v ≠ cfg.u := by
    intro h
    refine hvne1 ?_
    calc v = cfg.u * (cfg.u * v) := by rw [← mul_assoc, cfg.mul_self, one_mul]
      _ = cfg.u * cfg.u := by rw [h]
      _ = 1 := cfg.mul_self
  have huvne1 : cfg.u * v ≠ 1 := by
    intro h
    refine hvne ?_
    calc v = cfg.u * (cfg.u * v) := by rw [← mul_assoc, cfg.mul_self, one_mul]
      _ = cfg.u * 1 := by rw [h]
      _ = cfg.u := mul_one _
  have huvord : orderOf (cfg.u * v) = 2 := orderOf_eq_prime (by rw [sq]; exact huv2) huvne1
  -- Step 9 at `v` and at `u v`
  have h1 := character_mul_eq_of_const_on_class_product eG i v cfg.u
    ((wedderburnRepresentation eG i).character (v * cfg.u))
    (cfg.character_const_on_class_product eG hπG hlinG hnilG hkerJG hv hv2 hvne hi)
  have h2 := character_mul_eq_of_const_on_class_product eG i (cfg.u * v) cfg.u
    ((wedderburnRepresentation eG i).character (cfg.u * v * cfg.u))
    (cfg.character_const_on_class_product eG hπG hlinG hnilG hkerJG huvP huvord huvne hi)
  -- `(u v) u = v`
  have huvu : cfg.u * v * cfg.u = v := by
    calc cfg.u * v * cfg.u = cfg.u * (v * cfg.u) := by group
      _ = cfg.u * (cfg.u * v) := by rw [← huv]
      _ = (cfg.u * cfg.u) * v := by group
      _ = v := by rw [cfg.mul_self, one_mul]
  have hcvu : (wedderburnRepresentation eG i).character (cfg.u * v)
      = (wedderburnRepresentation eG i).character (v * cfg.u) := by rw [huv]
  rw [huvu, hcvu] at h2
  linear_combination (wedderburnRepresentation eG i).character cfg.u * h1
    + (wedderburnRepresentation eG i).character 1 * h2

end Final

end MinimalConfig

end OddOrder.GroupTheory
