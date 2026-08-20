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

section Contradiction

set_option maxHeartbeats 3200000 in
-- The `2`-modular data of `G` and of `C_G(v)` are instantiated here, and block orthogonality is
-- invoked twice against them.
/-- **Navarro (7.9), the final contradiction.**  A `MinimalConfig` has no second involution in
`P`.

Block orthogonality (Navarro (5.11)) kills `∑_{χ ∈ Irr(B_0)} χ(u⁻¹) χ(v)` and
`∑_{χ ∈ Irr(B_0)} χ(1) χ(v)` — the `2`-parts of `v` and `u` are not conjugate (`v` is an
involution of `P` other than `u`, and `u` is isolated), and neither are those of `v` and `1`.  So
the combined sum `∑_{χ ∈ Irr(B_0)} χ(v) (χ(u) + χ(1))` vanishes; but Step 9 makes every summand
`0` except at those `χ` with `χ(u) = χ(1)`, and there `u ∈ ker χ`, so Step 3 (`u` lies in no
proper normal subgroup) forces `ker χ = G` and the summand is `2 χ(1)²`.  The trivial character
contributes such a summand, so the total is a nonzero natural number. -/
theorem false_of_exists_involution {v : G} (hv : v ∈ (cfg.P : Subgroup G))
    (hv2 : orderOf v = 2) (hvne : v ≠ cfg.u) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hvconj : ¬ IsConj cfg.u v := cfg.not_isConj_of_mem_sylow hv hvne
  have hvne1 : v ≠ 1 := fun h => by
    have hord := hv2
    rw [h, orderOf_one] at hord
    omega
  have hvp : IsPElement 2 v := ⟨1, by rw [hv2, pow_one]⟩
  have hup : IsPElement 2 cfg.u := ⟨1, by rw [cfg.orderOf_eq_two, pow_one]⟩
  have hpv : pPart 2 v = v := pPart_eq_self_of_isPElement Nat.prime_two hvp
  have hpu : pPart 2 cfg.u = cfg.u := pPart_eq_self_of_isPElement Nat.prime_two hup
  have hp1 : pPart 2 (1 : G) = 1 :=
    pPart_eq_self_of_isPElement Nat.prime_two ⟨0, by rw [orderOf_one, pow_zero]⟩
  -- the two non-conjugacy inputs of block orthogonality
  have hnc : ¬ IsConj (pPart 2 v) (pPart 2 cfg.u) := by
    rw [hpv, hpu]
    exact fun h => hvconj h.symm
  have hnc1 : ¬ IsConj (pPart 2 v) (pPart 2 (1 : G)) := by
    rw [hpv, hp1]
    exact fun h => hvne1 (isConj_one_right.mp h.symm)
  -- the `2`-modular datum of `G`
  obtain ⟨ι'G, _, mG, _, _, _, eG, ιG, _, nnG, _, _, _, πG, hπG, hlinG, ωG, ω'G,
    hkerJG, hnilG, hωG, hω'G⟩ := exists_datum_padicComplex 2 G
  -- and that of `C_G(v)`, which block orthogonality consumes
  have : Finite ↥(centralizerOf (pPart 2 v)) := Subtype.finite
  have : Fintype ↥(centralizerOf (pPart 2 v)) := Fintype.ofFinite _
  obtain ⟨ι'V, _, mV, _, _, _, eV, ιV, _, nnV, _, _, _, πV, hπV, hlinV, ωV, ω'V,
    hkerJV, hnilV, hωV, hω'V⟩ :=
    exists_datum_padicComplex 2 ↥(centralizerOf (pPart 2 v))
  obtain ⟨ζ, hζ, hζk, hζK⟩ := exists_pow_eq_one_residue_eq_one_padicComplexInt 2
  set S : Finset ι'G := Finset.univ.filter
    (fun i => blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) with hS
  have hA : ∑ i ∈ S, (wedderburnRepresentation eG i).character cfg.u⁻¹
      * (wedderburnRepresentation eG i).character v = 0 :=
    sum_character_blockOfIrr_eq_zero Nat.prime_two hnc eG eV hπG hlinG hnilG hπV hlinV hkerJV
      hnilV hωV hω'V hζ hζk hζK (principalBlock πG hπG hlinG hnilG)
  have hB : ∑ i ∈ S, (wedderburnRepresentation eG i).character (1 : G)⁻¹
      * (wedderburnRepresentation eG i).character v = 0 :=
    sum_character_blockOfIrr_eq_zero Nat.prime_two hnc1 eG eV hπG hlinG hnilG hπV hlinV hkerJV
      hnilV hωV hω'V hζ hζk hζK (principalBlock πG hπG hlinG hnilG)
  rw [cfg.inv_eq] at hA
  rw [inv_one] at hB
  -- the combined sum vanishes
  have hsum : ∑ i ∈ S, (wedderburnRepresentation eG i).character v
      * ((wedderburnRepresentation eG i).character cfg.u
        + (wedderburnRepresentation eG i).character 1) = 0 := by
    have hsplit : ∑ i ∈ S, (wedderburnRepresentation eG i).character v
        * ((wedderburnRepresentation eG i).character cfg.u
          + (wedderburnRepresentation eG i).character 1)
        = (∑ i ∈ S, (wedderburnRepresentation eG i).character cfg.u
            * (wedderburnRepresentation eG i).character v)
          + ∑ i ∈ S, (wedderburnRepresentation eG i).character (1 : G)
            * (wedderburnRepresentation eG i).character v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hA, hB, add_zero]
  -- every summand vanishes except where `χ(u) = χ(1)`, and there it is `2 χ(1)²`
  have hterm : ∀ i ∈ S, (wedderburnRepresentation eG i).character v
      * ((wedderburnRepresentation eG i).character cfg.u
        + (wedderburnRepresentation eG i).character 1)
      = if (wedderburnRepresentation eG i).character cfg.u
          = (wedderburnRepresentation eG i).character 1
        then ((2 * (Fintype.card (mG i)) ^ 2 : ℕ) : ℂ_[2]) else 0 := by
    intro i hiS
    have hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG :=
      (Finset.mem_filter.mp hiS).2
    by_cases hcase : (wedderburnRepresentation eG i).character cfg.u
        = (wedderburnRepresentation eG i).character 1
    · rw [if_pos hcase]
      -- `u` acts trivially, so by Step 3 all of `G` does
      have hu1 : (wedderburnRepresentation eG i) cfg.u = 1 :=
        rep_eq_one_of_character_eq_of_mul_self_eq_one _ cfg.mul_self hcase
      have hker : (wedderburnRepresentation eG i).ker = ⊤ := by
        by_contra hne
        exact cfg.notMem_of_normal_ne_top hne (MonoidHom.mem_ker.mpr hu1)
      have htriv : ∀ g : G, (wedderburnRepresentation eG i).character g
          = (Module.finrank ℂ_[2] (mG i → ℂ_[2]) : ℂ_[2]) := by
        intro g
        have hg : g ∈ (wedderburnRepresentation eG i).ker := by rw [hker]; trivial
        rw [Representation.character, MonoidHom.mem_ker.mp hg, LinearMap.trace_one]
      rw [htriv v, htriv cfg.u, htriv 1, Module.finrank_fintype_fun_eq_card]
      push_cast
      ring
    · rw [if_neg hcase]
      have hstep9 := cfg.character_sq_eq_of_character_ne_zero eG hπG hlinG hnilG hkerJG hv hv2
        hvne hi
      have hfac : ((wedderburnRepresentation eG i).character cfg.u
            - (wedderburnRepresentation eG i).character 1)
          * ((wedderburnRepresentation eG i).character v
            * ((wedderburnRepresentation eG i).character cfg.u
              + (wedderburnRepresentation eG i).character 1)) = 0 := by
        linear_combination hstep9
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hcase
      · exact h
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    ← Nat.cast_sum] at hsum
  have hzero := Nat.cast_eq_zero.mp hsum
  -- the trivial character is one of the survivors
  obtain ⟨i₀, hi₀B, hi₀one⟩ :=
    exists_blockOfIrr_eq_principalBlock_character_eq_one eG hπG hlinG hnilG
  have hi₀ : i₀ ∈ S.filter (fun i => (wedderburnRepresentation eG i).character cfg.u
      = (wedderburnRepresentation eG i).character 1) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀B⟩
    · rw [hi₀one, hi₀one]
  have hpos : 0 < 2 * (Fintype.card (mG i₀)) ^ 2 := by
    have : 0 < Fintype.card (mG i₀) := Fintype.card_pos
    positivity
  have hi₀zero := Finset.sum_eq_zero_iff.mp hzero i₀ hi₀
  omega

end Contradiction

end MinimalConfig

end OddOrder.GroupTheory
