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

/-- **The homomorphism behind (E.12)**: `x ↦ ⁅v, x⁆ mod Hᵢ₊₂`, as a map `Hᵢ →* G/Hᵢ₊₂`.

Multiplicativity is `commutator_mul_mem_chain`.  Taking the *ambient* quotient `G/Hᵢ₊₂` as
codomain (rather than `Hᵢ₊₁/Hᵢ₊₂`) keeps the construction light — the image automatically
lands in the image of `Hᵢ₊₁`, but nothing here needs to say so.

Its kernel is `{x ∈ Hᵢ | ⁅v,x⁆ ∈ Hᵢ₊₂}`, the set BG needs to identify with `Hᵢ₊₁`. -/
def chainStepHom {G : Type*} [Group G] (T : Subgroup G) [T.Characteristic] (v : G) (i : ℕ) :
    ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) →*
      (G ⧸ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) where
  toFun x := QuotientGroup.mk ⁅v, (x : G)⁆
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.coe_mul]
    have h := Subgroup.inv_mem _ (commutator_mul_mem_chain (v := v) (x := (x : G)) y.2)
    simpa [mul_inv_rev] using h

@[simp]
theorem chainStepHom_apply {G : Type*} [Group G] (T : Subgroup G) [T.Characteristic] (v : G)
    (i : ℕ) (x : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i)) :
    chainStepHom T v i x = QuotientGroup.mk ⁅v, (x : G)⁆ := rfl

/-- `Hᵢ₊₁` lies in the kernel: `⁅v, x⁆ ∈ ⁅S, Hᵢ₊₁⁆ = Hᵢ₊₂` already for `x ∈ Hᵢ₊₁`.

This is the easy half of BG's identification; the hard half is that the kernel is no
*bigger* than `Hᵢ₊₁`, which follows because it is a proper subgroup of `Hᵢ` and
`|Hᵢ : Hᵢ₊₁| = p` is prime. -/
theorem chainStepHom_ker_ge {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {v : G} {i : ℕ}
    {x : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i)}
    (hx : (x : G) ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1)) :
    chainStepHom T v i x = 1 := by
  rw [chainStepHom_apply, QuotientGroup.eq_one_iff,
    OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hx

/-- If `⁅v, x⁆ ∈ Hᵢ₊₂` then so is `⁅vᵏ, x⁆`.

In `G/Hᵢ₊₂` the element `⁅v, x⁆` becomes trivial, hence central, so BG Lemma 4.2(a)
(`Ch1.S04.commutatorElement_pow_left_of_central`) gives `⁅vᵏ, x⁆ ≡ ⁅v,x⁆ᵏ = 1`.

This is what upgrades "the kernel contains `x` for the single element `v`" to "… for the
whole of `R₀ = ⟨v⟩`", which is what BG's `Hᵢ₊₁ = ⁅R₀, Hᵢ⁆` needs.  ⚠ No hypothesis on `x` is
required — centrality comes from `⁅v,x⁆` being trivial in the quotient, not from
`chain_map_le_center`. -/
theorem commutator_pow_mem_of_commutator_mem {G : Type*} [Group G] {T : Subgroup G}
    [T.Characteristic] {i : ℕ} {v x : G}
    (h : ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) (k : ℕ) :
    ⁅v ^ k, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  set N := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) with hN
  have h1 : (QuotientGroup.mk' N) ⁅v, x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h
  have h2 : ⁅(QuotientGroup.mk' N) v, (QuotientGroup.mk' N) x⁆ = 1 := by
    rw [← map_commutatorElement]; exact h1
  have hcent : ⁅(QuotientGroup.mk' N) v, (QuotientGroup.mk' N) x⁆ ∈
      Subgroup.center (G ⧸ N) := by rw [h2]; exact Subgroup.one_mem _
  have h3 := OddOrder.BG.Ch1.S04.commutatorElement_pow_left_of_central hcent k
  rw [h2, one_pow] at h3
  have h4 : (QuotientGroup.mk' N) ⁅v ^ k, x⁆ = 1 := by
    rw [map_commutatorElement, map_pow]; exact h3
  exact (QuotientGroup.eq_one_iff _).mp h4

/-- If `⁅v, x⁆ ∈ Hᵢ₊₂` for **every** `x ∈ Hᵢ` — i.e. the kernel of `chainStepHom` is all of
`Hᵢ` — then `⁅⟨v⟩, Hᵢ⁆ ≤ Hᵢ₊₂`.

`⁅⟨v⟩, Hᵢ⁆` is generated by brackets `⁅vᵏ, x⁆`, and
`commutator_pow_mem_of_commutator_mem` lifts the hypothesis from `v` to each `vᵏ`.
Finiteness lets the integer exponents of `zpowers` be taken natural.

Combined with BG's `Hᵢ₊₁ = ⁅R₀, Hᵢ⁆` (`commutator_R₀_eq_commutator_top`), this says a full
kernel would force `Hᵢ₊₁ ≤ Hᵢ₊₂` — impossible while the chain is still descending.  That is
the *hard* half of BG's unargued `⟨w̄ᵢ⟩ = H̄ᵢ`. -/
theorem commutator_zpowers_le_of_forall {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    [T.Characteristic] {i : ℕ} {v : G}
    (h : ∀ x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i,
      ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) :
    ⁅Subgroup.zpowers v, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff a v).mp (mem_powers_iff_mem_zpowers.mpr ha)
  exact commutator_pow_mem_of_commutator_mem (h b hb) k

end OddOrder.BG.AppE
