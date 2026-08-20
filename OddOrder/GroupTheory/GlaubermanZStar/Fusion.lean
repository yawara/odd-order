/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.SecondInvolution
import OddOrder.GroupTheory.PRegularElement

/-!
# Glauberman's `Z*`-theorem: Steps 6 and 7 — the fusion analysis

Navarro (7.9), Steps 6 and 7.  Let `v ∈ P` be an involution other than `u`, and `w = v^g` any
conjugate of it.  Splitting `w u = z x` into `2`-part and `2'`-part, the content is

* `z` commutes with `u` and is an involution;
* `z u` is `G`-conjugate to `v` (Step 6), and in fact `z` is `G`-conjugate to `v u` (Step 7);
* `x ∈ O_{2'}(C_G(z))`.

## Note on the proof

Navarro runs this through the dihedral group `D = ⟨w, u⟩`: `P₀ = ⟨z, u⟩` is a Sylow `2`-subgroup
of `D`, `w` is `D`-conjugate to one of `z`, `u`, `z u`, and the first two are excluded.  Step 7
then produces the conjugating element by another dihedral argument inside `C_G(zu)`.

Both are replaced here by one lemma — **two involutions whose product has odd order are
conjugate, by an explicit power of that product** (`conj_zpow_eq_of_odd_orderOf_mul`) — applied
twice:

* `(z u) · w = x⁻¹` has odd order, so `z u` and `w` are conjugate.  Taking `z = 1` would make `w`
  conjugate to `u`, which the isolation hypothesis forbids; so `z ≠ 1`.
* For Step 7 the conjugator must fix `u`.  Pick `t` with `t (zu) t⁻¹ = v`; then `u` and `t u t⁻¹`
  both centralise `v`, and `u · t u t⁻¹ = ⁅u, t⁆` has odd order, so they are conjugate *by an
  element `s` of `⟨u, t u t⁻¹⟩ ≤ C_G(v)`*.  Then `r = s⁻¹ t` fixes `u` and carries `z u` to `v`,
  hence `z = (z u) u` to `v u`.

The membership `x ∈ O_{2'}(C_G(z))` also simplifies: `u` inverts `x`, so `⁅u, x⁆ = x⁻²`, and
Step 2 (`zStar_proper`) puts that in `O_{2'}(C_G(z))`; `x` of odd order is a power of `x²`.

## Main results

* `OddOrder.GroupTheory.MinimalConfig` — the configuration Steps 1–5 leave behind
* `OddOrder.GroupTheory.MinimalConfig.fusion` — Steps 6 and 7
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

/-- **The configuration Navarro's (7.9) reduces to after Steps 1–5.**  `zStar_proper` is what the
induction supplies: the theorem, in its working form, for every proper subgroup containing `u`. -/
structure MinimalConfig (G : Type v) [Group G] [Finite G] where
  /-- a Sylow `2`-subgroup -/
  P : Sylow 2 G
  /-- the isolated involution -/
  u : G
  mem_sylow : u ∈ (P : Subgroup G)
  orderOf_eq_two : orderOf u = 2
  /-- `u` is the only `G`-conjugate of itself inside `P` -/
  isolated : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u
  oPiCore_eq_bot : oPiCore {q | q ≠ 2} G = ⊥
  center_eq_bot : Subgroup.center G = ⊥
  /-- Step 2: the theorem for proper subgroups, supplied by the induction -/
  zStar_proper : ∀ (H : Subgroup G), H ≠ ⊤ → ∀ (huH : u ∈ H) (h : ↥H),
    ⁅(⟨u, huH⟩ : ↥H), h⁆ ∈ oPiCore {q | q ≠ 2} ↥H

namespace MinimalConfig

variable {G : Type v} [Group G] [Finite G] (cfg : MinimalConfig G)

theorem mul_self : cfg.u * cfg.u = 1 := by
  have := pow_orderOf_eq_one cfg.u
  rwa [cfg.orderOf_eq_two, sq] at this

theorem inv_eq : cfg.u⁻¹ = cfg.u := inv_eq_of_mul_eq_one_right cfg.mul_self

theorem ne_one : cfg.u ≠ 1 := fun h => by
  have hord := cfg.orderOf_eq_two
  rw [h, orderOf_one] at hord
  omega

/-- Navarro (7.8) applied to the configuration. -/
theorem odd_commutator (g : G) : Odd (orderOf ⁅cfg.u, g⁆) :=
  odd_orderOf_commutator_of_forall_conj_eq cfg.P cfg.orderOf_eq_two cfg.isolated g

/-- `⁅u, g⁆ = u · u^g`, since `u` is an involution. -/
theorem commutator_eq (g : G) : ⁅cfg.u, g⁆ = cfg.u * (g * cfg.u * g⁻¹) := by
  rw [commutatorElement_def, cfg.inv_eq]; group

/-- The product of `u` with any of its conjugates has odd order. -/
theorem odd_mul_conj (g : G) : Odd (orderOf (cfg.u * (g * cfg.u * g⁻¹))) := by
  rw [← cfg.commutator_eq g]; exact cfg.odd_commutator g

/-- `u` is central in every `2`-subgroup containing it (Step 5). -/
theorem commute_of_isPGroup {D : Subgroup G} (hD : IsPGroup 2 D) (huD : cfg.u ∈ D) {d : G}
    (hd : d ∈ D) : d * cfg.u * d⁻¹ = cfg.u :=
  mem_center_of_isPGroup cfg.P cfg.isolated hD huD d hd

/-- An involution of `P` other than `u` is not `G`-conjugate to `u`. -/
theorem not_isConj_of_mem_sylow {w : G} (hw : w ∈ (cfg.P : Subgroup G)) (hne : w ≠ cfg.u) :
    ¬ IsConj cfg.u w := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact hne (hc ▸ cfg.isolated c (hc ▸ hw))

section Inversion

omit [Finite G] in
/-- If `a` inverts `y` then it inverts every power of `y`. -/
theorem conj_zpow_eq_inv_of_conj_eq_inv {a y : G} (h : a * y * a⁻¹ = y⁻¹) (i : ℤ) :
    a * y ^ i * a⁻¹ = (y ^ i)⁻¹ := by
  have hz := map_zpow (MulAut.conj a) y i
  simpa [MulAut.conj_apply, h, inv_zpow] using hz

omit [Finite G] in
/-- If `a` inverts `y` then it inverts every element of `⟨y⟩`. -/
theorem conj_eq_inv_of_mem_zpowers {a y t : G} (h : a * y * a⁻¹ = y⁻¹)
    (ht : t ∈ Subgroup.zpowers y) : a * t * a⁻¹ = t⁻¹ := by
  obtain ⟨i, rfl⟩ := ht
  exact conj_zpow_eq_inv_of_conj_eq_inv h i

omit [Finite G] in
/-- The `p`-part is a power of the element. -/
theorem pPart_mem_zpowers (p : ℕ) (y : G) : pPart p y ∈ Subgroup.zpowers y := ⟨_, rfl⟩

omit [Finite G] in
/-- The `p'`-part is a power of the element. -/
theorem pRegularPart_mem_zpowers (p : ℕ) (y : G) :
    pRegularPart p y ∈ Subgroup.zpowers y := ⟨_, rfl⟩

end Inversion

section Fusion

variable {w : G}

/-- `u` inverts `w u`: this is what makes both its `2`-part and its `2'`-part inverted by `u`. -/
theorem conj_mul_eq_inv (hw2 : w * w = 1) :
    cfg.u * (w * cfg.u) * cfg.u⁻¹ = (w * cfg.u)⁻¹ := by
  rw [cfg.inv_eq, mul_inv_rev, cfg.inv_eq, inv_eq_of_mul_eq_one_right hw2]
  calc cfg.u * (w * cfg.u) * cfg.u = cfg.u * w * (cfg.u * cfg.u) := by group
    _ = cfg.u * w := by rw [cfg.mul_self, mul_one]

set_option maxHeartbeats 1000000 in
-- `pPart` is a `zpow` with a Bézout exponent, so every `isDefEq` against it unfolds
-- `Nat.gcdA`/`Nat.gcdB`; the `2`-group construction below hits that repeatedly.
/-- **The `2`-part `z` of `w u` is an involution or trivial, and commutes with `u`.**  `u` inverts
`z` (a power of `w u`), and `⟨z⟩ ⊔ ⟨u⟩` is a `2`-group in which `u` is central by Step 5; so
`z⁻¹ = z`. -/
theorem commute_pPart (hw2 : w * w = 1) :
    cfg.u * pPart 2 (w * cfg.u) * cfg.u⁻¹ = pPart 2 (w * cfg.u) ∧
      pPart 2 (w * cfg.u) * pPart 2 (w * cfg.u) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPElement 2 (pPart 2 (w * cfg.u)) :=
    isPElement_pPart Nat.prime_two (w * cfg.u)
  have hinvz : cfg.u * pPart 2 (w * cfg.u) * cfg.u⁻¹ = (pPart 2 (w * cfg.u))⁻¹ :=
    conj_eq_inv_of_mem_zpowers (cfg.conj_mul_eq_inv hw2) (pPart_mem_zpowers 2 _)
  set z : G := pPart 2 (w * cfg.u) with hz
  have hconjzpow : ∀ j : ℤ, cfg.u * z ^ j * cfg.u⁻¹ = z ^ (-j) := by
    intro j
    rw [zpow_neg]
    exact conj_zpow_eq_inv_of_conj_eq_inv hinvz j
  -- `⟨z⟩ ⊔ ⟨u⟩` is a `2`-group containing `u`
  have hupg : IsPGroup 2 (Subgroup.zpowers cfg.u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, cfg.orderOf_eq_two, pow_one]
  have hzpg : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_isPElement hzp
  have hnorm : Subgroup.zpowers cfg.u ≤ Subgroup.normalizer (Subgroup.zpowers z) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨-j, (hconjzpow j).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨-j, ?_⟩
      have hh := hconjzpow (-j)
      rw [neg_neg] at hh
      exact mul_left_cancel (mul_right_cancel (hh.trans hj))
  have hQ : IsPGroup 2 (Subgroup.zpowers z ⊔ Subgroup.zpowers cfg.u : Subgroup G) :=
    hzpg.to_sup_of_normal_left' hupg hnorm
  have huQ : cfg.u ∈ (Subgroup.zpowers z ⊔ Subgroup.zpowers cfg.u : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hzQ : z ∈ (Subgroup.zpowers z ⊔ Subgroup.zpowers cfg.u : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  -- `u` is central there, so it commutes with `z`
  have hcz : z * cfg.u * z⁻¹ = cfg.u := cfg.commute_of_isPGroup hQ huQ hzQ
  have hcomm : cfg.u * z = z * cfg.u := by
    have h := congrArg (fun t => t * z) hcz
    simp only [inv_mul_cancel_right] at h
    exact h.symm
  have hfix : cfg.u * z * cfg.u⁻¹ = z := by
    rw [hcomm, cfg.inv_eq]
    calc z * cfg.u * cfg.u = z * (cfg.u * cfg.u) := by group
      _ = z := by rw [cfg.mul_self, mul_one]
  refine ⟨hfix, ?_⟩
  have hzinv : z⁻¹ = z := by rw [← hinvz, hfix]
  calc z * z = z * z⁻¹ := by rw [hzinv]
    _ = 1 := mul_inv_cancel z

end Fusion

end MinimalConfig

end OddOrder.GroupTheory
