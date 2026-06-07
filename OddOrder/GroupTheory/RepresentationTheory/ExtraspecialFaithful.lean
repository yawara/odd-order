/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible
import OddOrder.GroupTheory.IsExtraspecial

/-!
# Faithful representations of extraspecial `p`-groups (BG §2 Thm 2.5 / Gor 5.5.5)

`OddOrder.GroupTheory.RepresentationTheory` shared module towards
**Gorenstein 5.5.5**: a faithful irreducible representation of an extraspecial
`q`-group `P` of order `q^{1+2n}` over an algebraically closed field of
characteristic not dividing `|P|` has dimension `q^n`.

## Strategy

The proof is the character mass formula plus a trace-form basis count, carried
out over a *general* algebraically closed field (no `ℂ`/`star`): mathlib's
`Representation.char_orthonormal` is field-valued.

* **`character_eq_zero_of_notMem_center`** (this file): the character vanishes
  off the center.  This is the geometric input.
* The mass formula `(dim V)² · |Z| = |P|` (in `F`) then comes from
  `Representation.char_orthonormal` + the per-`Z`-element computation.
* `(dim V : F) ≠ 0` follows from `(dim V : F)² = (|P/Z| : F) ≠ 0`, which lets the
  trace-form Gram matrix `[χ(gᵢgⱼ⁻¹)] = (dim V) · I` of `Z`-coset representatives
  be nonsingular, giving the *integer* equation `(dim V)² = |P/Z|` (the `E(P)`
  basis of BG (2.11)).  Combined with `|P/Z| = q^{2n}` (extraspecial), `dim V = qⁿ`.

## BG ↔ mathlib mapping

* **BG Thm 2.5** uses Gor 5.5.5 as `dim M = dim V = pⁿ`, then `dim E(P) = q²`
  (BG (2.11)).  See `notes/bg/s03_extraspecial_blocker.md` for the full chain.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped commutatorElement

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- **The character of a faithful irreducible vanishes off the center** (Gor 5.5.5, geometric step).

If `ρ` is a faithful irreducible representation over an algebraically closed field `F`, `P` has
nilpotency class `≤ 2` (`commutator P ≤ Z(P)`), and `g ∉ Z(P)`, then `χ(g) = 0`.

For `g ∉ Z(P)` there is `x` with `z₀ := ⁅x, g⁆ ≠ 1`; as `[P,P] ⊆ Z(P)`, `z₀` is central and
`x g x⁻¹ = z₀ g`, so `χ(g) = χ(z₀ g) = c · χ(g)` where `ρ z₀ = c • id` and `c ≠ 1` (faithfulness),
forcing `χ(g) = 0`. -/
theorem character_eq_zero_of_notMem_center [FiniteDimensional F V]
    (ρ : Representation F P V) [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P) {g : P} (hg : g ∉ Subgroup.center P) :
    ρ.character g = 0 := by
  -- a non-commuting partner of `g`
  obtain ⟨x, hx⟩ : ∃ x : P, x * g ≠ g * x := by
    by_contra h
    exact hg (Subgroup.mem_center_iff.mpr fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  -- `z₀ := ⁅x, g⁆` is a nontrivial central element
  have hz₀ne : ⁅x, g⁆ ≠ 1 := by rw [Ne, commutatorElement_eq_one_iff_mul_comm]; exact hx
  have hz₀mem : ⁅x, g⁆ ∈ Subgroup.center P := by
    apply hcl
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top g)
  -- it acts as a scalar `c`, with `c ≠ 1` by faithfulness
  obtain ⟨c, hc⟩ := center_isScalar ρ hz₀mem
  have hcne : c ≠ 1 := by
    intro hc1
    apply hz₀ne
    apply hf
    rw [map_one, hc, hc1, one_smul, Module.End.one_eq_id]
  -- `x g x⁻¹ = ⁅x, g⁆ * g`
  have hconj : x * g * x⁻¹ = ⁅x, g⁆ * g := by rw [commutatorElement_def]; group
  -- `χ(g) = χ(x g x⁻¹) = χ(z₀ g) = c · χ(g)`
  have key : ρ.character g = c * ρ.character g :=
    calc ρ.character g = ρ.character (x * g * x⁻¹) := (Representation.char_conj ρ g x).symm
      _ = ρ.character (⁅x, g⁆ * g) := by rw [hconj]
      _ = c * ρ.character g := by
          rw [Representation.character, Representation.character, map_mul, hc,
            ← Module.End.one_eq_id, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  -- conclude `χ(g) = 0`
  have h1c : (1 : F) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcne)
  have hzero : (1 - c) * ρ.character g = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left h1c

end OddOrder.RepresentationTheory
