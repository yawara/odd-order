/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_FurtherResults

/-!
# BG Appendix E, Theorem E.3: the regular-operator eigenvalue count

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 159--161 — the `(E.9)`--`(E.12)` part of Step 2 and
the conclusion `|S| ≤ p^q` of Theorem E.3(c).

This is a sibling leaf of `OddOrder/BG/AppE_FurtherResults.lean`, which carries `(E.1)`
through `(E.9)`.  The split is deliberate: that file reached the repo's 2000-line hard limit
(issue 0134), so further Appendix E work lands here instead of growing it.

## BG's elision, and the route taken

BG picks `w ∈ H₀ − H₁`, sets `wᵢ = [wᵢ₋₁, v]`, and later writes *"So `⟨w̄ᵢ⟩ = H̄ᵢ`"*.  That
silently requires `wᵢ ∉ Hᵢ₊₁`, for which BG gives no argument.

The route here is to observe that `x ↦ ⁅v, x⁆` is a **homomorphism modulo the next chain
term** (`commutator_mul_mem_chain`), so `{x ∈ Hᵢ | ⁅v,x⁆ ∈ Hᵢ₊₂}` is the kernel of a map
`Hᵢ → Hᵢ₊₁/Hᵢ₊₂`.  It contains `Hᵢ₊₁`, and cannot be all of `Hᵢ` (that would collapse
`Hᵢ₊₁ ≤ Hᵢ₊₂`), so by `|Hᵢ : Hᵢ₊₁| = p` it *is* `Hᵢ₊₁` — giving
`⁅v, x⁆ ∈ Hᵢ₊₂ ↔ x ∈ Hᵢ₊₁` and hence `wᵢ ∉ Hᵢ₊₁` by induction from `w ∉ H₁`.

⚠ This supersedes the bijection/fibre argument recorded earlier in issue 3021, which routed
through the tightness of the counting; the kernel argument needs no counting at all.  (The
sharpened `Ch1.S05.index_centralizer_le_card_of_commutator_mem` remains a genuine
improvement to that lemma, but is not needed here.)
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open scoped commutatorElement

/-! ### `x ↦ ⁅v, x⁆` is multiplicative modulo the next chain term -/

/-- **The multiplicativity behind (E.12)**: for `y ∈ Hᵢ`,
`(⁅v,x⁆ * ⁅v,y⁆)⁻¹ * ⁅v, x*y⁆ ∈ Hᵢ₊₂`.

That is, `x ↦ ⁅v, x⁆` becomes a homomorphism `Hᵢ → Hᵢ₊₁/Hᵢ₊₂` after passing to the
quotient.  The computation is the standard expansion
`⁅v, xy⁆ = ⁅v,x⁆ · (x ⁅v,y⁆ x⁻¹)`, together with
`x ⁅v,y⁆ x⁻¹ ⁅v,y⁆⁻¹ = ⁅x, ⁅v,y⁆⁆ ∈ ⁅S, Hᵢ₊₁⁆ = Hᵢ₊₂`.

⚠ Only `y ∈ Hᵢ` is needed — `v` and `x` are unconstrained, because the chain brackets
against all of `S`. -/
theorem commutator_mul_mem_chain {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {i : ℕ} {v x y : G}
    (hy : y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) :
    (⁅v, x⁆ * ⁅v, y⁆)⁻¹ * ⁅v, x * y⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  -- `⁅v,y⁆ ∈ Hᵢ₊₁`
  have hvy : ⁅v, y⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hy
  -- `c := ⁅x, ⁅v,y⁆⁆ ∈ Hᵢ₊₂`
  have hc : ⁅x, ⁅v, y⁆⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hvy
  -- the identity: the difference is a conjugate of `c`
  have hrw : (⁅v, x⁆ * ⁅v, y⁆)⁻¹ * ⁅v, x * y⁆ = ⁅v, y⁆⁻¹ * ⁅x, ⁅v, y⁆⁆ * ⁅v, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hrw]
  exact Subgroup.Normal.conj_mem' inferInstance _ hc _

end OddOrder.BG.AppE
