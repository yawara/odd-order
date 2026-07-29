/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.LinearCharacter
import OddOrder.GroupTheory.WielandtFixedPoint
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Corollary132

/-!
# `|N| = |C_N(X)|^{|X|}` for `K`-invariant `2`-subgroups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §1, Proposition, p. 117:

> But `[K, P] ⋊ P` is a Frobenius group acting on `S/Q₀` and `[K, P]` acts
> without fixed points on `S/Q₀` …

This file assembles `⁅K, X⁆` for `X ≤ V`, the kernel of that Frobenius group.
The plan is to feed `Q` and `Q₀` themselves to Wielandt's formula rather than the
quotient `S/Q₀`, which is shorter: the fixed-point-freeness of the kernel comes
straight from Ch. I §2 Proposition 1(a) (`K` acts fixed-point-freely on `Q`),
whereas the corresponding statement for `S/Q₀` would need extra work.

The Frobenius structure needs `W = 1` only through `⁅K, X⁆ ≠ 1`: if `X`
centralized `K` it would lie in `W = C_V(K)`.

## Main results

* `Hypothesis.commutator_K_le_K` — `⁅K, X⁆ ≤ K` for `X ≤ D`.
* `Hypothesis.commutator_K_ne_bot` — `⁅K, X⁆ ≠ 1` for `1 ≠ X ≤ V` when `W = 1`.
* `Hypothesis.conj_mem_commutator_K_of_mem` — `X` normalizes `⁅K, X⁆`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise
open scoped commutatorElement

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## `⁅K, X⁆` -/

/-- `⁅K, X⁆ ≤ K` for any `X ≤ D`. -/
theorem commutator_K_le_K {X : Subgroup G} (hXD : X ≤ hyp.D) : ⁅hyp.K, X⁆ ≤ hyp.K := by
  rw [Subgroup.commutator_le]
  intro k hk x hx
  have : k * (x * k⁻¹ * x⁻¹) ∈ hyp.K :=
    hyp.K.mul_mem hk (hyp.conj_mem_K_of_mem_D (hXD hx) (hyp.K.inv_mem hk))
  simpa [commutatorElement_def, mul_assoc] using this

/-- **`⁅K, X⁆ ≠ 1`** for `1 ≠ X ≤ V` when `W = 1`: otherwise `X` would
centralize `K`, so `X ≤ C_V(K) = W = 1`. -/
theorem commutator_K_ne_bot (hW : hyp.W = ⊥) {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hXne : X ≠ ⊥) : ⁅hyp.K, X⁆ ≠ ⊥ := by
  intro hbot
  refine hXne (le_bot_iff.mp ?_)
  rw [← hW]
  intro x hx
  refine ⟨hXV hx, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
  have hmem : ⁅k, x⁆ ∈ ⁅hyp.K, X⁆ := Subgroup.commutator_mem_commutator hkK hx
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
  exact hmem.eq

/-- `X ≤ D` normalizes `⁅K, X⁆`: conjugation by `x ∈ X` carries `K` to `K` and
`X` to `X`, hence the commutator subgroup to itself (`Subgroup.map_commutator`). -/
theorem conj_mem_commutator_K_of_mem {X : Subgroup G} (hXD : X ≤ hyp.D) {x : G}
    (hx : x ∈ X) {z : G} (hz : z ∈ ⁅hyp.K, X⁆) : x * z * x⁻¹ ∈ ⁅hyp.K, X⁆ := by
  have hmap : (⁅hyp.K, X⁆).map (MulAut.conj x).toMonoidHom ≤ ⁅hyp.K, X⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hyp.conj_mem_K_of_mem_D (hXD hx) hk
    · rintro _ ⟨y, hy, rfl⟩
      exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  exact hmap ⟨z, hz, rfl⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
