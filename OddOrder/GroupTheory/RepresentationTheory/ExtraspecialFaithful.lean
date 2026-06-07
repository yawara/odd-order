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

/-- **On the center, `χ(g) · χ(g⁻¹) = (dim V)²`** (Gor 5.5.5 step). A central element acts as a
scalar `c` (with `g⁻¹` acting as `c'` and `c·c'·(dim V) = dim V` from `ρ g · ρ g⁻¹ = 1`), so
`χ(g) = c·(dim V)`, `χ(g⁻¹) = c'·(dim V)`, and the product collapses to `(dim V)²`. -/
theorem char_mul_char_inv_of_mem_center [FiniteDimensional F V]
    (ρ : Representation F P V) [ρ.IsIrreducible] {g : P} (hg : g ∈ Subgroup.center P) :
    ρ.character g * ρ.character g⁻¹ = (Module.finrank F V : F) ^ 2 := by
  obtain ⟨c, hc⟩ := center_isScalar ρ hg
  obtain ⟨c', hc'⟩ := center_isScalar ρ (Subgroup.inv_mem _ hg)
  rw [← Module.End.one_eq_id] at hc hc'
  have hchar : ρ.character g = c * (Module.finrank F V : F) := by
    change LinearMap.trace F V (ρ g) = _
    rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hchar' : ρ.character g⁻¹ = c' * (Module.finrank F V : F) := by
    change LinearMap.trace F V (ρ g⁻¹) = _
    rw [hc', map_smul, LinearMap.trace_one, smul_eq_mul]
  -- `(c·c') • 1 = ρ g · ρ g⁻¹ = ρ 1 = 1`, hence `c·c'·(dim V) = dim V`.
  have hone : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hprod : (c * c') • (1 : Module.End F V) = 1 := by
    have hmul : (c • (1 : Module.End F V)) * (c' • 1) = (c * c') • 1 := by
      rw [smul_mul_smul_comm, one_mul]
    rw [← hmul, ← hc, ← hc']; exact hone
  have hcc : c * c' * (Module.finrank F V : F) = (Module.finrank F V : F) := by
    have h := congrArg (LinearMap.trace F V) hprod
    rwa [map_smul, LinearMap.trace_one, smul_eq_mul] at h
  rw [hchar, hchar']
  have hrearrange : c * (Module.finrank F V : F) * (c' * (Module.finrank F V : F))
      = c * c' * (Module.finrank F V : F) * (Module.finrank F V : F) := by ring
  rw [hrearrange, hcc, ← pow_two]

/-- **Character mass formula** (Gor 5.5.5a-ii): for a faithful irreducible representation `ρ` of a
finite group `P` of nilpotency class `≤ 2` (`commutator P ≤ Z(P)`) over an algebraically closed
field with `char ∤ |P|`, `(dim V)² · |Z(P)| = |P|` (an equation in `F`).

By `char_orthonormal` the sum `∑_g χ(g)χ(g⁻¹)` is `|P|`; the character vanishes off `Z(P)`
(`character_eq_zero_of_notMem_center`) and equals `(dim V)²` on each central element
(`char_mul_char_inv_of_mem_center`), so the sum is `|Z(P)| · (dim V)²`. -/
theorem sq_finrank_mul_card_center [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    (Module.finrank F V : F) ^ 2 * (Nat.card (Subgroup.center P) : F) = (Nat.card P : F) := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have hne : (Nat.card P : F) ≠ 0 := (isUnit_of_invertible _).ne_zero
  -- orthonormality `⟹ ∑ χ(g) χ(g⁻¹) = |P|`
  have hortho := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
  have hsum : ∑ g : P, ρ.character g * ρ.character g⁻¹ = (Nat.card P : F) := by
    have h := congrArg (fun x => (Nat.card P : F) * x) hortho
    simp only [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h
    exact h
  -- each term is `(dim V)²` on the center and `0` off it
  have hterm : ∀ g : P, ρ.character g * ρ.character g⁻¹
      = if g ∈ Subgroup.center P then (Module.finrank F V : F) ^ 2 else 0 := by
    intro g
    by_cases hg : g ∈ Subgroup.center P
    · rw [if_pos hg, char_mul_char_inv_of_mem_center ρ hg]
    · rw [if_neg hg, character_eq_zero_of_notMem_center ρ hf hcl hg, zero_mul]
  -- count: `|{g : g ∈ Z}| = |Z|`
  have hcard : (Finset.univ.filter (· ∈ Subgroup.center P)).card
      = Nat.card (Subgroup.center P) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- assemble the split sum
  have hsplit : ∑ g : P, ρ.character g * ρ.character g⁻¹
      = (Nat.card (Subgroup.center P) : F) * (Module.finrank F V : F) ^ 2 :=
    calc ∑ g : P, ρ.character g * ρ.character g⁻¹
        = ∑ g : P, if g ∈ Subgroup.center P then (Module.finrank F V : F) ^ 2 else 0 :=
          Finset.sum_congr rfl (fun g _ => hterm g)
      _ = ∑ _g ∈ Finset.univ.filter (· ∈ Subgroup.center P), (Module.finrank F V : F) ^ 2 :=
          (Finset.sum_filter _ _).symm
      _ = (Finset.univ.filter (· ∈ Subgroup.center P)).card • (Module.finrank F V : F) ^ 2 :=
          Finset.sum_const _
      _ = (Nat.card (Subgroup.center P) : F) * (Module.finrank F V : F) ^ 2 := by
          rw [nsmul_eq_mul, hcard]
  rw [mul_comm, ← hsplit]
  exact hsum

/-- **`(dim V : F) ≠ 0`** (Gor 5.5.5a-iii). Bootstrapped from the mass formula: if `(dim V : F) = 0`
then `(dim V)² · |Z| = 0 ≠ |P|`, contradicting `char ∤ |P|`. This is what makes the trace-form Gram
matrix nonsingular in the integer step. -/
theorem finrank_cast_ne_zero [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    (Module.finrank F V : F) ≠ 0 := by
  intro h
  apply (isUnit_of_invertible (Nat.card P : F)).ne_zero
  have hmass := sq_finrank_mul_card_center ρ hf hcl
  rw [h] at hmass
  rw [← hmass]; ring

end OddOrder.RepresentationTheory
