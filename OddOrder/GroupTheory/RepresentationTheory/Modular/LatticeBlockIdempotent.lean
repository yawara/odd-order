/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeCentralCharacter

/-!
# Navarro (3.13.a): a block idempotent acts as `0` or `1`

**Navarro (3.13.a).**  Let `V` be a simple `ℂG`-module affording `χ ∈ Irr(G)` and let `B` be a
`p`-block.  Then `V f_B = V` if `χ ∈ B`, and `V f_B = 0` otherwise.

In the `𝒪`-lattice formulation this needs no appeal to `f_B = ∑_{χ ∈ Irr(B)} e_χ`.  An absolutely
irreducible lattice has a central character `ω : Z(𝒪G) →ₐ[𝒪] 𝒪`
(`LatticeCentralCharacter.centralCharacter`), so `ω(f_B)` is an idempotent **of `𝒪`**; since `𝒪`
is local it is `0` or `1`, and which one is decided by its residue — that is, by the value of the
block character `λ_χ = ω mod 𝔪` on the block idempotent `e_B`, which is `1` for `χ ∈ B` and `0`
otherwise.  Since `f_B` acts as `ω(f_B) • id`, the lattice is either fixed or killed.

The two-valuedness is the whole content: it upgrades `λ_χ(e_B) = 0` (a statement modulo `𝔪`) to
"`f_B` annihilates the module" (a statement over `𝒪`, hence over `K` after base change).  That
upgrade is what Navarro (5.7) uses to know `M f_B = 0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_zero_or_one_of_isIdempotentElem` — a local ring has
  only the trivial idempotents
* `OddOrder.RepresentationTheory.Modular.centralScalar_eq_zero_or_one`
* `OddOrder.RepresentationTheory.Modular.apply_eq_zero_of_reduce_centralScalar_eq_zero` —
  (3.13.a), the `χ ∉ B` half
* `OddOrder.RepresentationTheory.Modular.apply_eq_id_of_reduce_centralScalar_ne_zero` —
  (3.13.a), the `χ ∈ B` half
-/

namespace OddOrder.RepresentationTheory.Modular

open TensorProduct

/-! ### Idempotents of a local ring -/

section LocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]

/-- **A local ring has no idempotents other than `0` and `1`.**  One of `c` and `1 - c` is a unit,
and `c (1 - c) = 0` then forces the other factor to vanish. -/
theorem eq_zero_or_one_of_isIdempotentElem {c : 𝒪} (hc : IsIdempotentElem c) :
    c = 0 ∨ c = 1 := by
  have hmul : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [mul_one]; exact hc))
  · exact Or.inl (hu.mul_left_cancel (by rw [mul_zero, mul_comm]; exact hmul))

end LocalRing

/-! ### The block idempotent on an absolutely irreducible lattice -/

section Lattice

variable {𝒪 K : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing K] [Algebra 𝒪 K]
  [FaithfulSMul 𝒪 K]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Nontrivial L]
variable {A : Type*} [Ring A] [Algebra 𝒪 A]
variable (K)
variable (φ : A →ₐ[𝒪] Module.End 𝒪 L)
  (hEnd : ∀ F : Module.End K (K ⊗[𝒪] L),
    (∀ a : A, F * LinearMap.baseChange K (φ a) = LinearMap.baseChange K (φ a) * F) →
    ∃ c : K, F = c • LinearMap.id)

omit [IsLocalRing 𝒪] in
/-- The central character of an idempotent is an idempotent of `𝒪`. -/
theorem isIdempotentElem_centralScalar {z : Subalgebra.center 𝒪 A} (hz : IsIdempotentElem z) :
    IsIdempotentElem (centralScalar K φ hEnd z) := by
  have h := congrArg (centralCharacter K φ hEnd) hz
  rw [map_mul] at h
  exact h

/-- **A block idempotent acts by `0` or by `1`.**  Its central character is an idempotent of the
local ring `𝒪`. -/
theorem centralScalar_eq_zero_or_one {z : Subalgebra.center 𝒪 A} (hz : IsIdempotentElem z) :
    centralScalar K φ hEnd z = 0 ∨ centralScalar K φ hEnd z = 1 :=
  eq_zero_or_one_of_isIdempotentElem (isIdempotentElem_centralScalar K φ hEnd hz)

/-- The value is `0` as soon as it is not a unit. -/
theorem centralScalar_eq_zero_of_mem_maximalIdeal {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : centralScalar K φ hEnd z ∈ IsLocalRing.maximalIdeal 𝒪) :
    centralScalar K φ hEnd z = 0 := by
  rcases centralScalar_eq_zero_or_one K φ hEnd hz with h0 | h1
  · exact h0
  · exact absurd (h1 ▸ h) (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one)

/-- The value is `1` as soon as it is a unit. -/
theorem centralScalar_eq_one_of_notMem_maximalIdeal {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : centralScalar K φ hEnd z ∉ IsLocalRing.maximalIdeal 𝒪) :
    centralScalar K φ hEnd z = 1 := by
  rcases centralScalar_eq_zero_or_one K φ hEnd hz with h0 | h1
  · exact absurd (h0 ▸ Submodule.zero_mem _) h
  · exact h1

/-- **Navarro (3.13.a), the `χ ∉ B` half, over `𝒪`.** -/
theorem apply_eq_zero_of_mem_maximalIdeal {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : centralScalar K φ hEnd z ∈ IsLocalRing.maximalIdeal 𝒪) :
    φ (z : A) = 0 := by
  rw [apply_center_eq_centralScalar_smul K φ hEnd z,
    centralScalar_eq_zero_of_mem_maximalIdeal K φ hEnd hz h, zero_smul]

/-- **Navarro (3.13.a), the `χ ∈ B` half, over `𝒪`.** -/
theorem apply_eq_id_of_notMem_maximalIdeal {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : centralScalar K φ hEnd z ∉ IsLocalRing.maximalIdeal 𝒪) :
    φ (z : A) = LinearMap.id := by
  rw [apply_center_eq_centralScalar_smul K φ hEnd z,
    centralScalar_eq_one_of_notMem_maximalIdeal K φ hEnd hz h, one_smul]

/-! ### In terms of the reduction

The block characters are maps out of `Z(FG)`, so this is the form in which (3.13.a) is used:
`λ_χ(e_B) = 0` versus `≠ 0`. -/

variable {F : Type*} [CommRing F] (ψ : 𝒪 →+* F)
  (hker : RingHom.ker ψ = IsLocalRing.maximalIdeal 𝒪)

include hker

/-- **Navarro (3.13.a), the `χ ∉ B` half.**  `λ_χ(e_B) = 0` forces `f_B` to annihilate the
lattice — not merely modulo `𝔪`. -/
theorem apply_eq_zero_of_reduce_centralScalar_eq_zero {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : ψ (centralScalar K φ hEnd z) = 0) :
    φ (z : A) = 0 :=
  apply_eq_zero_of_mem_maximalIdeal K φ hEnd hz (hker ▸ RingHom.mem_ker.mpr h)

/-- **Navarro (3.13.a), the `χ ∈ B` half.**  `λ_χ(e_B) ≠ 0` forces `f_B` to act as the
identity. -/
theorem apply_eq_id_of_reduce_centralScalar_ne_zero {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : ψ (centralScalar K φ hEnd z) ≠ 0) :
    φ (z : A) = LinearMap.id :=
  apply_eq_id_of_notMem_maximalIdeal K φ hEnd hz fun hmem =>
    h (RingHom.mem_ker.mp (hker ▸ hmem))

/-- The base-changed form: `K ⊗ L` is annihilated too.  This is the shape `M f_B = 0` in which
Navarro (5.7) cites (3.13.a). -/
theorem baseChange_apply_eq_zero_of_reduce_centralScalar_eq_zero {z : Subalgebra.center 𝒪 A}
    (hz : IsIdempotentElem z) (h : ψ (centralScalar K φ hEnd z) = 0) :
    LinearMap.baseChange K (φ (z : A)) = 0 := by
  rw [apply_eq_zero_of_reduce_centralScalar_eq_zero K φ hEnd ψ hker hz h,
    LinearMap.baseChange_zero]

end Lattice

end OddOrder.RepresentationTheory.Modular
