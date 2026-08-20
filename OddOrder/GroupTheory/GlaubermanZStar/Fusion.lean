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

/-- `w = (w u) u`, since `u` is an involution. -/
theorem eq_mul_self : w * cfg.u * cfg.u = w := by
  calc w * cfg.u * cfg.u = w * (cfg.u * cfg.u) := by group
    _ = w := by rw [cfg.mul_self, mul_one]

set_option maxHeartbeats 1000000 in
-- as in `commute_pPart`: unification against `pPart`/`pRegularPart` unfolds Bézout coefficients.
/-- **`(z u) · w = x⁻¹`**, where `w u = z x` splits into `2`-part and `2'`-part.  This is the
identity that makes `z u` and `w` conjugate: the right-hand side has odd order. -/
theorem mul_conj_eq_inv_pRegularPart (hw2 : w * w = 1) :
    (pPart 2 (w * cfg.u) * cfg.u) * w = (pRegularPart 2 (w * cfg.u))⁻¹ := by
  obtain ⟨hfix, hzz⟩ := cfg.commute_pPart hw2
  set z : G := pPart 2 (w * cfg.u) with hz
  set x : G := pRegularPart 2 (w * cfg.u) with hx
  have hcomm : cfg.u * z = z * cfg.u := by
    have h := congrArg (fun t => t * cfg.u) hfix
    simp only [inv_mul_cancel_right] at h
    exact h
  have hinvx : cfg.u * x * cfg.u⁻¹ = x⁻¹ :=
    conj_eq_inv_of_mem_zpowers (cfg.conj_mul_eq_inv hw2) (pRegularPart_mem_zpowers 2 _)
  have hsplit : z * x = w * cfg.u :=
    pPart_mul_pRegularPart Nat.prime_two (isOfFinOrder_of_finite _)
  have hwval : w = z * x * cfg.u := by rw [hsplit, cfg.eq_mul_self]
  calc z * cfg.u * w = z * cfg.u * (z * x * cfg.u) := by rw [← hwval]
    _ = z * (cfg.u * z) * x * cfg.u := by group
    _ = z * (z * cfg.u) * x * cfg.u := by rw [hcomm]
    _ = (z * z) * (cfg.u * x * cfg.u⁻¹) := by rw [cfg.inv_eq]; group
    _ = x⁻¹ := by rw [hzz, hinvx, one_mul]

set_option maxHeartbeats 1000000 in
-- same reason as `commute_pPart`.
/-- **Navarro (7.9), Step 6 (first half).**  `z u` is an involution `G`-conjugate to `w`, and
`z ≠ 1`.

`(z u) · w = x⁻¹` has odd order, so `conj_zpow_eq_of_odd_orderOf_mul` conjugates `w` to `z u`
provided both are involutions; `z u = 1` would make `w = x⁻¹` of odd order, impossible for an
involution, and `z = 1` would make `w` conjugate to `u`, which the hypothesis forbids. -/
theorem isConj_mul_pPart (hw2 : w * w = 1) (hwne : w ≠ 1) (hwconj : ¬ IsConj cfg.u w) :
    pPart 2 (w * cfg.u) ≠ 1 ∧
      (pPart 2 (w * cfg.u) * cfg.u) * (pPart 2 (w * cfg.u) * cfg.u) = 1 ∧
      IsConj w (pPart 2 (w * cfg.u) * cfg.u) := by
  obtain ⟨hfix, hzz⟩ := cfg.commute_pPart hw2
  have hkey := cfg.mul_conj_eq_inv_pRegularPart hw2
  set z : G := pPart 2 (w * cfg.u) with hz
  set x : G := pRegularPart 2 (w * cfg.u) with hx
  have hcomm : cfg.u * z = z * cfg.u := by
    have h := congrArg (fun t => t * cfg.u) hfix
    simp only [inv_mul_cancel_right] at h
    exact h
  -- `z u` squares to `1`
  have hzu2 : (z * cfg.u) * (z * cfg.u) = 1 := by
    calc z * cfg.u * (z * cfg.u) = z * (cfg.u * z) * cfg.u := by group
      _ = z * (z * cfg.u) * cfg.u := by rw [hcomm]
      _ = (z * z) * (cfg.u * cfg.u) := by group
      _ = 1 := by rw [hzz, cfg.mul_self, mul_one]
  -- `x⁻¹` has odd order
  have hxodd : Odd (orderOf ((z * cfg.u) * w)) := by
    rw [hkey, orderOf_inv, Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    exact isPRegular_pRegularPart Nat.prime_two (isOfFinOrder_of_finite _)
  -- `z u ≠ 1`
  have hzune : z * cfg.u ≠ 1 := by
    intro h
    rw [h, one_mul] at hxodd
    have hword : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hwne
    rw [hword] at hxodd
    exact absurd hxodd (by decide)
  refine ⟨?_, hzu2, ?_⟩
  · intro hzone
    refine hwconj ?_
    have hconj := conj_zpow_eq_of_odd_orderOf_mul hw2 hzu2 hxodd
    rw [hzone, one_mul] at hconj
    exact (isConj_iff.mpr ⟨_, hconj⟩).symm
  · exact isConj_iff.mpr ⟨_, conj_zpow_eq_of_odd_orderOf_mul hw2 hzu2 hxodd⟩

/-- **Navarro (7.9), Step 3**, read off the configuration: `u` lies in no proper normal
subgroup.  If it did, Step 2 (`zStar_proper`) plus `O_{2'}(H) = 1` would make `u` central in `H`,
hence commuting with each of its conjugates — and `⁅u, g⁆`, a product of two commuting
involutions of odd order, would be trivial, putting `u` in `Z(G) = 1`. -/
theorem notMem_of_normal_ne_top {H : Subgroup G} [H.Normal] (hHtop : H ≠ ⊤) : cfg.u ∉ H := by
  intro huH
  have hOH : oPiCore {q | q ≠ 2} ↥H = ⊥ := oPiCore_subgroup_eq_bot cfg.oPiCore_eq_bot
  have hcen : ∀ h : ↥H, ⁅(⟨cfg.u, huH⟩ : ↥H), h⁆ = 1 := fun h => by
    have hmem := cfg.zStar_proper H hHtop huH h
    rwa [hOH, Subgroup.mem_bot] at hmem
  have hone : ∀ g : G, ⁅cfg.u, g⁆ = 1 := by
    intro g
    have hvH : g * cfg.u * g⁻¹ ∈ H := ‹H.Normal›.conj_mem cfg.u huH g
    have hcomm : cfg.u * (g * cfg.u * g⁻¹) = (g * cfg.u * g⁻¹) * cfg.u :=
      congrArg Subtype.val
        (commutatorElement_eq_one_iff_commute.mp (hcen ⟨g * cfg.u * g⁻¹, hvH⟩))
    exact eq_one_of_mul_self_eq_one_of_odd
      (mul_self_commutator_eq_one_of_commute cfg.mul_self hcomm) (cfg.odd_commutator g)
  have hz : cfg.u ∈ Subgroup.center G :=
    Subgroup.mem_center_iff.mpr fun g =>
      (commutatorElement_eq_one_iff_commute.mp (hone g)).symm
  rw [cfg.center_eq_bot, Subgroup.mem_bot] at hz
  exact cfg.ne_one hz

/-- `u` commutes with every element of `P` (Step 5 applied to `P` itself). -/
theorem conj_eq_of_mem_sylow {a : G} (ha : a ∈ (cfg.P : Subgroup G)) :
    a * cfg.u * a⁻¹ = cfg.u :=
  cfg.commute_of_isPGroup cfg.P.isPGroup' cfg.mem_sylow ha

set_option maxHeartbeats 1000000 in
-- same reason as `commute_pPart`.
/-- **Navarro (7.9), Step 7.**  `z` is `G`-conjugate to `v u`.

Pick `t` with `t (z u) t⁻¹ = v`.  Then `u` and `t u t⁻¹` both centralise `v` — the first because
`u ∈ Z(P)`, the second because `u` centralises `z u` — and `u · t u t⁻¹ = ⁅u, t⁆` has odd order,
so they are conjugate by an element `s` of `⟨u, t u t⁻¹⟩ ≤ C_G(v)`.  Then `r = s⁻¹ t` fixes `u`
and carries `z u` to `v`, hence carries `z = (z u) u` to `v u`. -/
theorem isConj_pPart_of_isConj {v : G} (hv : v ∈ (cfg.P : Subgroup G)) (hw2 : w * w = 1)
    (hzu : IsConj v (pPart 2 (w * cfg.u) * cfg.u)) :
    IsConj (pPart 2 (w * cfg.u)) (v * cfg.u) := by
  obtain ⟨hfix, hzz⟩ := cfg.commute_pPart hw2
  set z : G := pPart 2 (w * cfg.u) with hz
  have hcomm : cfg.u * z = z * cfg.u := by
    have h := congrArg (fun t => t * cfg.u) hfix
    simp only [inv_mul_cancel_right] at h
    exact h
  obtain ⟨t, ht⟩ := isConj_iff.mp hzu.symm
  -- `u` centralises `z u`, hence `t u t⁻¹` centralises `v`
  have huzu : cfg.u * (z * cfg.u) = (z * cfg.u) * cfg.u := by
    calc cfg.u * (z * cfg.u) = (cfg.u * z) * cfg.u := by group
      _ = (z * cfg.u) * cfg.u := by rw [hcomm]
  have htu : (t * cfg.u * t⁻¹) * v = v * (t * cfg.u * t⁻¹) := by
    rw [← ht]
    calc t * cfg.u * t⁻¹ * (t * (z * cfg.u) * t⁻¹)
        = t * (cfg.u * (z * cfg.u)) * t⁻¹ := by group
      _ = t * ((z * cfg.u) * cfg.u) * t⁻¹ := by rw [huzu]
      _ = t * (z * cfg.u) * t⁻¹ * (t * cfg.u * t⁻¹) := by group
  -- `u` centralises `v`
  have huv : cfg.u * v = v * cfg.u := by
    have h := cfg.conj_eq_of_mem_sylow hv
    have h2 := congrArg (fun a => a * v) h
    simp only [inv_mul_cancel_right] at h2
    exact h2.symm
  -- `u` and `t u t⁻¹` are conjugate by an element of `C_G(v)`
  have hoddc : Odd (orderOf ((t * cfg.u * t⁻¹) * cfg.u)) := by
    have h := cfg.odd_mul_conj t
    have heq : orderOf ((t * cfg.u * t⁻¹) * cfg.u)
        = orderOf (cfg.u * (t * cfg.u * t⁻¹)) := by
      have hc : cfg.u⁻¹ * (cfg.u * (t * cfg.u * t⁻¹)) * cfg.u⁻¹⁻¹
          = (t * cfg.u * t⁻¹) * cfg.u := by group
      rw [← hc]
      exact orderOf_injective (MulAut.conj cfg.u⁻¹).toMonoidHom
        (MulAut.conj cfg.u⁻¹).injective _
    rw [heq]
    exact h
  set s : G := ((t * cfg.u * t⁻¹) * cfg.u) ^
    ((orderOf ((t * cfg.u * t⁻¹) * cfg.u) + 1) / 2) with hs
  have hconj2 : s * cfg.u * s⁻¹ = t * cfg.u * t⁻¹ :=
    conj_zpow_eq_of_odd_orderOf_mul cfg.mul_self
      (by calc t * cfg.u * t⁻¹ * (t * cfg.u * t⁻¹) = t * (cfg.u * cfg.u) * t⁻¹ := by group
            _ = 1 := by rw [cfg.mul_self, mul_one, mul_inv_cancel]) hoddc
  -- `s` centralises `v`
  have hsv : s * v = v * s := by
    have hbase : ((t * cfg.u * t⁻¹) * cfg.u) * v = v * ((t * cfg.u * t⁻¹) * cfg.u) := by
      calc (t * cfg.u * t⁻¹) * cfg.u * v = (t * cfg.u * t⁻¹) * (cfg.u * v) := by group
        _ = (t * cfg.u * t⁻¹) * (v * cfg.u) := by rw [huv]
        _ = ((t * cfg.u * t⁻¹) * v) * cfg.u := by group
        _ = (v * (t * cfg.u * t⁻¹)) * cfg.u := by rw [htu]
        _ = v * ((t * cfg.u * t⁻¹) * cfg.u) := by group
    rw [hs]
    exact (Commute.pow_left (hbase : Commute _ v) _)
  -- `r = s⁻¹ t` fixes `u` and carries `z u` to `v`
  refine isConj_iff.mpr ⟨s⁻¹ * t, ?_⟩
  have hru : (s⁻¹ * t) * cfg.u * (s⁻¹ * t)⁻¹ = cfg.u := by
    calc (s⁻¹ * t) * cfg.u * (s⁻¹ * t)⁻¹ = s⁻¹ * (t * cfg.u * t⁻¹) * s := by group
      _ = s⁻¹ * (s * cfg.u * s⁻¹) * s := by rw [hconj2]
      _ = cfg.u := by group
  have hrzu : (s⁻¹ * t) * (z * cfg.u) * (s⁻¹ * t)⁻¹ = v := by
    calc (s⁻¹ * t) * (z * cfg.u) * (s⁻¹ * t)⁻¹
        = s⁻¹ * (t * (z * cfg.u) * t⁻¹) * s := by group
      _ = s⁻¹ * v * s := by rw [ht]
      _ = v := by
          calc s⁻¹ * v * s = s⁻¹ * (v * s) := by group
            _ = s⁻¹ * (s * v) := by rw [← hsv]
            _ = v := by group
  have hzuu : z * cfg.u * cfg.u = z := by
    calc z * cfg.u * cfg.u = z * (cfg.u * cfg.u) := by group
      _ = z := by rw [cfg.mul_self, mul_one]
  calc (s⁻¹ * t) * z * (s⁻¹ * t)⁻¹
      = (s⁻¹ * t) * (z * cfg.u * cfg.u) * (s⁻¹ * t)⁻¹ := by rw [hzuu]
    _ = ((s⁻¹ * t) * (z * cfg.u) * (s⁻¹ * t)⁻¹) * ((s⁻¹ * t) * cfg.u * (s⁻¹ * t)⁻¹) := by group
    _ = v * cfg.u := by rw [hrzu, hru]

set_option maxHeartbeats 1000000 in
-- same reason as `commute_pPart`.
/-- **Navarro (7.9), Step 6 (second half).**  The `2'`-part `x` of `w u` lies in
`O_{2'}(C_G(z))`.

`C_G(z)` is proper (`z ≠ 1` and `Z(G) = 1`), so Step 2 applies inside it and gives
`⁅u, x⁆ ∈ O_{2'}(C_G(z))`.  But `u` inverts `x`, so `⁅u, x⁆ = x⁻²`; and `x` of odd order is a
power of `x²`. -/
theorem pRegularPart_mem_oPiCore (hw2 : w * w = 1) (hwne : w ≠ 1)
    (hwconj : ¬ IsConj cfg.u w) :
    ∃ hx : pRegularPart 2 (w * cfg.u) ∈
        Subgroup.centralizer ({pPart 2 (w * cfg.u)} : Set G),
      (⟨pRegularPart 2 (w * cfg.u), hx⟩ :
          ↥(Subgroup.centralizer ({pPart 2 (w * cfg.u)} : Set G)))
        ∈ oPiCore {q | q ≠ 2} ↥(Subgroup.centralizer ({pPart 2 (w * cfg.u)} : Set G)) := by
  obtain ⟨hfix, hzz⟩ := cfg.commute_pPart hw2
  obtain ⟨hzne, -, -⟩ := cfg.isConj_mul_pPart hw2 hwne hwconj
  have hinvx : cfg.u * pRegularPart 2 (w * cfg.u) * cfg.u⁻¹ = (pRegularPart 2 (w * cfg.u))⁻¹ :=
    conj_eq_inv_of_mem_zpowers (cfg.conj_mul_eq_inv hw2) (pRegularPart_mem_zpowers 2 _)
  have hxodd : Odd (orderOf (pRegularPart 2 (w * cfg.u))) := by
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    exact isPRegular_pRegularPart Nat.prime_two (isOfFinOrder_of_finite _)
  set z : G := pPart 2 (w * cfg.u) with hz
  set x : G := pRegularPart 2 (w * cfg.u) with hx
  have hcomm : cfg.u * z = z * cfg.u := by
    have h := congrArg (fun t => t * cfg.u) hfix
    simp only [inv_mul_cancel_right] at h
    exact h
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have huC : cfg.u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hxC : x ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_pRegularPart_pPart (w * cfg.u)).eq
  refine ⟨hxC, ?_⟩
  -- `C` is proper, because `Z(G) = 1` and `z ≠ 1`
  have hCne : C ≠ ⊤ := by
    intro hCtop
    refine hzne ?_
    have hzc : z ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun a => ?_
      have ha : a ∈ C := by rw [hCtop]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.mp ha
    rw [cfg.center_eq_bot, Subgroup.mem_bot] at hzc
    exact hzc
  -- Step 2 inside `C`
  have hstep := cfg.zStar_proper C hCne huC ⟨x, hxC⟩
  set K : Subgroup ↥C := oPiCore {q | q ≠ 2} ↥C with hK
  -- `⁅u, x⁆ = x⁻¹ x⁻¹`
  have hcommval : ⁅cfg.u, x⁆ = x⁻¹ * x⁻¹ := by
    rw [commutatorElement_def, cfg.inv_eq]
    calc cfg.u * x * cfg.u * x⁻¹ = (cfg.u * x * cfg.u⁻¹) * x⁻¹ := by rw [cfg.inv_eq]
      _ = x⁻¹ * x⁻¹ := by rw [hinvx]
  have hsq : (⟨x, hxC⟩ : ↥C) * (⟨x, hxC⟩ : ↥C) ∈ K := by
    have hcomm2 : ⁅(⟨cfg.u, huC⟩ : ↥C), (⟨x, hxC⟩ : ↥C)⁆
        = ((⟨x, hxC⟩ : ↥C) * (⟨x, hxC⟩ : ↥C))⁻¹ := by
      refine Subtype.ext ?_
      have h := hcommval
      rw [commutatorElement_def] at h
      simp only [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
      exact h
    rw [hcomm2] at hstep
    exact inv_mem_iff.mp hstep
  -- `x` is a power of `x²`, being of odd order
  obtain ⟨j, hj⟩ := hxodd
  have hord : orderOf (⟨x, hxC⟩ : ↥C) = orderOf x := Subgroup.orderOf_mk x hxC
  have hpow : ((⟨x, hxC⟩ : ↥C) * (⟨x, hxC⟩ : ↥C)) ^ (j + 1) = (⟨x, hxC⟩ : ↥C) := by
    rw [← sq, ← pow_mul]
    have : 2 * (j + 1) = orderOf (⟨x, hxC⟩ : ↥C) + 1 := by rw [hord, hj]; omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [← hpow]
  exact pow_mem hsq _

end Fusion

end MinimalConfig

end OddOrder.GroupTheory
