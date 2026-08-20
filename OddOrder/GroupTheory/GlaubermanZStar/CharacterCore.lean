/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.Fusion
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockPPrimeCore
import OddOrder.GroupTheory.RepresentationTheory.Modular.PadicComplexDatum
import OddOrder.GroupTheory.RepresentationTheory.Modular.ThirdMainConverseSupply

/-!
# Glauberman's `Z*`-theorem: Step 8 — the character is constant on `cl(v)·cl(u)`

Navarro (7.9), Step 8: for `χ ∈ Irr(B_0)` and any involution `v ∈ P` with `v ≠ u`,

`χ(v^g u^h) = χ(v u)` for every `g, h ∈ G`.

Conjugating by `h⁻¹` reduces to `h = 1`, and then the fusion analysis of Steps 6 and 7 writes
`v^g u = z x` with `z` a `2`-element `G`-conjugate to `v u` and `x ∈ O_{2'}(C_G(z))`.  Navarro
(7.7) — `character_mul_eq_character_of_mem_normal_of_not_dvd` — says `χ(z x) = χ(z)`, and `χ` is
a class function, so `χ(z) = χ(v u)`.

The `2`-modular datum of `C_G(z)` is produced on the spot (`exists_datum_padicComplex`), together
with the converse of the third main theorem for it
(`eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots`), exactly as in the `Q₈` branch of
Brauer–Suzuki.

## Main results

* `OddOrder.GroupTheory.MinimalConfig.character_conj_mul_eq` — Step 8 at `h = 1`
* `OddOrder.GroupTheory.MinimalConfig.character_const_on_class_product` — Step 8
-/

open OddOrder.Isaacs.Ch03 OddOrder.RepresentationTheory.Modular
open OddOrder.RepresentationTheory OddOrder.MatrixModule

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

namespace MinimalConfig

variable {G : Type v} [Group G] [Finite G] (cfg : MinimalConfig G)

section StepEight

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
    OddOrder.MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  (hkerJG : RingHom.ker πG
    = Ring.jacobson (MonoidAlgebra (IsLocalRing.ResidueField 𝓞_ℂ_[2]) G))

set_option maxHeartbeats 3200000 in
-- The whole `2`-modular datum of `C_G(z)` plus the converse third main theorem is instantiated
-- in one term, as in `q8_exists_proper_normal`.
set_option linter.unusedFintypeInType false in
include hkerJG in
/-- **Navarro (7.9), Step 8 at `h = 1`.**  `χ(v^g u) = χ(v u)` for `χ ∈ Irr(B_0)`. -/
theorem character_conj_mul_eq {w : G} (hw2 : w * w = 1) (hwne : w ≠ 1)
    (hwconj : ¬ IsConj cfg.u w) {v : G} (hv : v ∈ (cfg.P : Subgroup G))
    (hzu : IsConj v (pPart 2 (w * cfg.u) * cfg.u))
    {i : ι'G} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) :
    (wedderburnRepresentation eG i).character (w * cfg.u)
      = (wedderburnRepresentation eG i).character (v * cfg.u) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z : G := pPart 2 (w * cfg.u) with hz
  have hzp : IsPElement 2 z := isPElement_pPart Nat.prime_two (w * cfg.u)
  -- the `2`-modular datum of `C_G(z)`
  have : Finite ↥(centralizerOf z) := Subtype.finite
  have : Fintype ↥(centralizerOf z) := Fintype.ofFinite _
  obtain ⟨ι'C, _, mC, _, _, _, eC, ιC, _, nnC, _, _, _, πC, hπC, hlinC, ωC, ω'C,
    hkerJC, hnilC, hωC, hω'C⟩ :=
    exists_datum_padicComplex 2 ↥(centralizerOf z)
  obtain ⟨ζ, hζ, hζk, hζK⟩ := exists_pow_eq_one_residue_eq_one_padicComplexInt 2
  have hroot : ∀ n : ℕ, ¬ 2 ∣ n → n ≠ 0 → ∃ ζ' : 𝓞_ℂ_[2], IsPrimitiveRoot ζ' n :=
    fun n hn hn0 => exists_isPrimitiveRoot_padicComplexInt 2 hn hn0
  have hroot' : ∀ n : ℕ, ¬ 2 ∣ n → n ≠ 0 →
      ∃ ζ' : IsLocalRing.ResidueField 𝓞_ℂ_[2], IsPrimitiveRoot ζ' n :=
    fun n hn hn0 => exists_isPrimitiveRoot_residueField_padicComplexInt 2 hn hn0
  have hconv : ∀ b : Block πC hπC hlinC,
      inducedBlockOfCentralizer z πC hπC hlinC πG hπG hlinG hnilG Nat.prime_two hzp b
        = principalBlock πG hπG hlinG hnilG → b = principalBlock πC hπC hlinC hnilC :=
    fun b hind => eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots Nat.prime_two hzp
      hroot hroot' hζ hζk hζK eG eC hπG hlinG hnilG hkerJG hπC hlinC hnilC hkerJC b hind
  -- Navarro (7.7) applied to `x ∈ O_{2'}(C_G(z))`
  obtain ⟨hxC, hxK⟩ := cfg.pRegularPart_mem_oPiCore hw2 hwne hwconj
  have hNodd : ¬ (2 : ℕ) ∣ Nat.card ↥(oPiCore {q | q ≠ 2} ↥(centralizerOf z)) := fun hdvd =>
    (oPiCore.isPiGroup (G := ↥(centralizerOf z)) {q | q ≠ 2}) 2
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, Nat.card_pos.ne'⟩) rfl
  have hsplit : z * (pRegularPart 2 (w * cfg.u)) = w * cfg.u :=
    pPart_mul_pRegularPart Nat.prime_two (isOfFinOrder_of_finite _)
  have h77 := character_mul_eq_character_of_mem_normal_of_not_dvd Nat.prime_two hzp hωC eC eG
    hπG hlinG hπC hlinC hkerJC hnilC hnilG hω'C hζ hζk hζK hconv hi
    (N := oPiCore {q | q ≠ 2} ↥(centralizerOf z)) inferInstance hNodd hxK
  rw [hsplit] at h77
  -- `z` is conjugate to `v u`
  rw [h77]
  exact character_eq_of_isConj _ (cfg.isConj_pPart_of_isConj hv hw2 hzu)

set_option maxHeartbeats 3200000 in
-- as `character_conj_mul_eq`, which it wraps.
set_option linter.unusedFintypeInType false in
include hkerJG in
/-- **Navarro (7.9), Step 8.**  `χ` is constant on the product set `cl(v) · cl(u)`, with value
`χ(v u)`.  Conjugating by `b⁻¹` (where `y = u^b`) reduces to `character_conj_mul_eq`. -/
theorem character_const_on_class_product {v : G} (hv : v ∈ (cfg.P : Subgroup G))
    (hv2 : orderOf v = 2) (hvne : v ≠ cfg.u)
    {i : ι'G} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    (x y : G) (hx : ConjClasses.mk x = ConjClasses.mk v)
    (hy : ConjClasses.mk y = ConjClasses.mk cfg.u) :
    (wedderburnRepresentation eG i).character (x * y)
      = (wedderburnRepresentation eG i).character (v * cfg.u) := by
  classical
  have hv2' : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, sq] at this
  have hvne1 : v ≠ 1 := fun h => by
    have hord := hv2
    rw [h, orderOf_one] at hord
    omega
  have hvconj : ¬ IsConj cfg.u v := cfg.not_isConj_of_mem_sylow hv hvne
  -- write `y = u^b` and conjugate the whole product back
  obtain ⟨b, hb⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hy).symm
  set w : G := b⁻¹ * x * b with hw
  have hvw : IsConj v w := by
    refine ((ConjClasses.mk_eq_mk_iff_isConj.mp hx).symm.trans ?_)
    exact isConj_iff.mpr ⟨b⁻¹, by rw [hw]; group⟩
  have hw2 : w * w = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hvw
    rw [← hc]
    calc c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
      _ = 1 := by rw [hv2', mul_one, mul_inv_cancel]
  have hwne : w ≠ 1 := by
    intro h
    refine hvne1 ?_
    obtain ⟨c, hc⟩ := isConj_iff.mp hvw
    rw [h] at hc
    have : c * v = c := by
      calc c * v = c * v * c⁻¹ * c := by group
        _ = 1 * c := by rw [hc]
        _ = c := one_mul c
    exact mul_left_cancel (this.trans (mul_one c).symm)
  have hwconj : ¬ IsConj cfg.u w := fun h => hvconj (h.trans hvw.symm)
  obtain ⟨-, -, hzu⟩ := cfg.isConj_mul_pPart hw2 hwne hwconj
  -- `x y` is conjugate to `w u`
  have hxy : (wedderburnRepresentation eG i).character (x * y)
      = (wedderburnRepresentation eG i).character (w * cfg.u) := by
    refine character_eq_of_isConj _ (isConj_iff.mpr ⟨b⁻¹, ?_⟩)
    rw [hw, ← hb]
    group
  rw [hxy]
  exact cfg.character_conj_mul_eq eG hπG hlinG hnilG hkerJG hw2 hwne hwconj hv
    (hvw.trans hzu) hi

end StepEight

end MinimalConfig

end OddOrder.GroupTheory
