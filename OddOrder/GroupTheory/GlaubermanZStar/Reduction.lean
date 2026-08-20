/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.Basic
import OddOrder.GroupTheory.BrauerSuzukiQ8.Reduction
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3D

/-!
# Glauberman's `Z*`-theorem: the inductive reduction (Navarro (7.9), Steps 1–4)

Navarro's proof of (7.9) is an induction on `|G|`.  This file carries the steps that consume the
inductive hypothesis, packaged as `ZStarUpTo n` — the statement of the theorem for every group of
order at most `n` in a fixed universe.

* **Step 1** (`commutator_mem_of_quotient`): the hypothesis passes to `G ⧸ N`, so the theorem for
  `G ⧸ N` gives `⁅u, g⁆ N ∈ O_{2'}(G/N)`.  With `N = O_{2'}(G)` this *is* the theorem for `G`,
  which is why one may assume `O_{2'}(G) = 1`.
* **Step 2** (`mem_center_of_subgroup`): the hypothesis restricts to any subgroup containing `u`,
  so a proper subgroup `H ∋ u` has `u ∈ Z*(H) = Z(H)` (using `O_{2'}(H) = 1`).
* **Step 3** (`notMem_of_isProper_normal`): with `O_{2'}(G) = 1` and `u ∉ Z(G)`, the involution
  `u` lies in no proper normal subgroup.
* **Step 4** (`center_eq_bot`): consequently `Z(G) = 1`.

## Main results

* `OddOrder.GroupTheory.ZStarUpTo`
* `OddOrder.GroupTheory.commutator_mem_of_quotient`
* `OddOrder.GroupTheory.mem_center_of_subgroup`
* `OddOrder.GroupTheory.notMem_of_isProper_normal`
* `OddOrder.GroupTheory.center_eq_bot`
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

/-- **The `Z*`-theorem for all groups of order at most `n`.**  `Navarro (7.9)` is proved by
induction on `|G|`, and this is the shape of the inductive hypothesis: it is stated in the
working form `⁅u, g⁆ ∈ O_{2'}(H)` of `u ∈ Z*(H)`
(`mk_mem_center_iff_forall_commutator_mem`). -/
def ZStarUpTo (n : ℕ) : Prop :=
  ∀ (H : Type v) [Group H] [Finite H], Nat.card H ≤ n → ∀ (P : Sylow 2 H) (u : H),
    u ∈ (P : Subgroup H) → orderOf u = 2 →
    (∀ g : H, g * u * g⁻¹ ∈ (P : Subgroup H) → g * u * g⁻¹ = u) →
    ∀ g : H, ⁅u, g⁆ ∈ oPiCore {q | q ≠ 2} H

variable {G : Type v} [Group G] [Finite G] (P : Sylow 2 G) {u : G}

section Step1

/-- **Navarro (7.9), Step 1.**  If `N ⊴ G` does not contain `u`, the image of `u` in `G ⧸ N` is
again an involution of a Sylow `2`-subgroup satisfying the hypothesis, so the theorem for the
smaller group `G ⧸ N` applies.

The hypothesis travels through its odd-order form (Navarro (7.8)): the order of `⁅u, g⁆ N`
divides the order of `⁅u, g⁆`. -/
theorem commutator_mem_of_quotient {n : ℕ} (hIH : ZStarUpTo.{v} n) (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
    {N : Subgroup G} [N.Normal] (huN : u ∉ N) (hcard : Nat.card (G ⧸ N) ≤ n) (g : G) :
    ⁅QuotientGroup.mk' N u, QuotientGroup.mk' N g⁆ ∈ oPiCore {q | q ≠ 2} (G ⧸ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  -- the image of `u` is again an involution
  have hmk2 : orderOf (QuotientGroup.mk' N u) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, hu2', map_one]
    · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact huN
  -- the image of `P` is a Sylow `2`-subgroup of `G ⧸ N` containing it
  set Pbar : Sylow 2 (G ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N) with hPbar
  have hmkP : QuotientGroup.mk' N u ∈ (Pbar : Subgroup (G ⧸ N)) := by
    rw [hPbar, Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ hu
  -- the hypothesis, in its odd-order form, passes to the quotient
  have hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆) :=
    odd_orderOf_commutator_of_forall_conj_eq P hu2 hiso
  have hisobar : ∀ gg : G ⧸ N, gg * QuotientGroup.mk' N u * gg⁻¹ ∈ (Pbar : Subgroup (G ⧸ N)) →
      gg * QuotientGroup.mk' N u * gg⁻¹ = QuotientGroup.mk' N u := fun gg =>
    forall_conj_eq_of_odd_orderOf_commutator Pbar hmkP hmk2
      (odd_orderOf_commutator_quotient hodd) gg
  exact hIH (G ⧸ N) hcard Pbar _ hmkP hmk2 hisobar _

end Step1

section Involutions

variable {g : G}

omit [Finite G] in
/-- An element that squares to `1` and has odd order is trivial. -/
theorem eq_one_of_mul_self_eq_one_of_odd {w : G} (hw : w * w = 1) (hodd : Odd (orderOf w)) :
    w = 1 := by
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hw)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
/-- If `u` is an involution commuting with its conjugate `u^g`, then `⁅u, g⁆` squares to `1`:
it is the product of two commuting involutions. -/
theorem mul_self_commutator_eq_one_of_commute (hu2 : u * u = 1)
    (hcomm : u * (g * u * g⁻¹) = (g * u * g⁻¹) * u) : ⁅u, g⁆ * ⁅u, g⁆ = 1 := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hval : ⁅u, g⁆ = u * (g * u * g⁻¹) := by
    rw [commutatorElement_def, huinv]; group
  have hv2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2, mul_one, mul_inv_cancel]
  rw [hval]
  calc u * (g * u * g⁻¹) * (u * (g * u * g⁻¹))
      = u * ((g * u * g⁻¹) * u) * (g * u * g⁻¹) := by group
    _ = u * (u * (g * u * g⁻¹)) * (g * u * g⁻¹) := by rw [hcomm]
    _ = (u * u) * ((g * u * g⁻¹) * (g * u * g⁻¹)) := by group
    _ = 1 := by rw [hu2, hv2, mul_one]

omit [Finite G] in
/-- If `u` is an involution and `⁅u, g⁆` is central, then `⁅u, g⁆` squares to `1`. -/
theorem mul_self_commutator_eq_one_of_mem_center (hu2 : u * u = 1)
    (hz : ⁅u, g⁆ ∈ Subgroup.center G) : ⁅u, g⁆ * ⁅u, g⁆ = 1 := by
  refine mul_self_commutator_eq_one_of_commute hu2 ?_
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hval : ⁅u, g⁆ = u * (g * u * g⁻¹) := by
    rw [commutatorElement_def, huinv]; group
  have hcen := Subgroup.mem_center_iff.mp hz u
  rw [hval] at hcen
  calc u * (g * u * g⁻¹) = u * (u * (u * (g * u * g⁻¹))) := by
        rw [← mul_assoc u u, hu2, one_mul]
    _ = u * ((u * (g * u * g⁻¹)) * u) := by rw [hcen]
    _ = (u * u) * (g * u * g⁻¹) * u := by group
    _ = (g * u * g⁻¹) * u := by rw [hu2, one_mul]

end Involutions

section Steps

variable {n : ℕ}

/-- **Navarro (7.9), Step 2.**  The hypothesis restricts to any subgroup containing `u`, so the
theorem for the smaller group `H` gives `u ∈ Z*(H)`. -/
theorem commutator_mem_of_subgroup (hIH : ZStarUpTo.{v} n) (hu2 : orderOf u = 2)
    (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆))
    {H : Subgroup G} (huH : u ∈ H) (hcard : Nat.card ↥H ≤ n) (h : ↥H) :
    ⁅(⟨u, huH⟩ : ↥H), h⁆ ∈ oPiCore {q | q ≠ 2} ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (⟨u, huH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  -- a Sylow `2`-subgroup of `H` containing `u`
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers (⟨u, huH⟩ : ↥H)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨PH, hPH⟩ := hpg.exists_le_sylow
  have huPH : (⟨u, huH⟩ : ↥H) ∈ (PH : Subgroup ↥H) :=
    hPH (Subgroup.mem_zpowers _)
  exact hIH ↥H hcard PH _ huPH hord
    (fun a => forall_conj_eq_of_odd_orderOf_commutator PH huPH hord
      (odd_orderOf_commutator_subgroup huH hodd) a) h

/-- **Navarro (7.9), Step 3.**  With `O_{2'}(G) = 1`, if `u` lay in a proper normal subgroup `H`
then `u` would be central in `H` (Step 2 plus `O_{2'}(H) = 1`), hence would commute with each of
its `G`-conjugates — but then `⁅u, g⁆`, a product of two commuting involutions of odd order,
would be trivial for every `g`, i.e. `u ∈ Z(G)`. -/
theorem commutator_eq_one_of_mem_normal (hIH : ZStarUpTo.{v} n)
    (hO : oPiCore {q | q ≠ 2} G = ⊥) (hu2 : orderOf u = 2)
    (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆))
    {H : Subgroup G} [H.Normal] (huH : u ∈ H) (hcard : Nat.card ↥H ≤ n) (g : G) :
    ⁅u, g⁆ = 1 := by
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  -- `u` is central in `H`
  have hOH : oPiCore {q | q ≠ 2} ↥H = ⊥ := oPiCore_subgroup_eq_bot hO
  have hcen : ∀ h : ↥H, ⁅(⟨u, huH⟩ : ↥H), h⁆ = 1 := fun h => by
    have := commutator_mem_of_subgroup hIH hu2 hodd huH hcard h
    rwa [hOH, Subgroup.mem_bot] at this
  -- `u^g ∈ H`, so `u` commutes with it
  have hvH : g * u * g⁻¹ ∈ H := ‹H.Normal›.conj_mem u huH g
  have hcomm : u * (g * u * g⁻¹) = (g * u * g⁻¹) * u := by
    have h := commutatorElement_eq_one_iff_commute.mp (hcen ⟨g * u * g⁻¹, hvH⟩)
    exact congrArg Subtype.val h
  exact eq_one_of_mul_self_eq_one_of_odd
    (mul_self_commutator_eq_one_of_commute hu2' hcomm) (hodd g)

/-- **Navarro (7.9), Step 4.**  With `O_{2'}(G) = 1`, if `Z(G) ≠ 1` then Step 1 applied to
`G ⧸ Z(G)` puts every `⁅u, g⁆` inside `Z(G)` — because `O_{2'}(G/Z(G))` is the image of
`O_{2'}(G) = 1` (Isaacs Problem 3D.2) — and a central `⁅u, g⁆` of odd order is trivial. -/
theorem commutator_eq_one_of_center_ne_bot (hIH : ZStarUpTo.{v} n) (P : Sylow 2 G)
    (hO : oPiCore {q | q ≠ 2} G = ⊥) (hu : u ∈ (P : Subgroup G)) (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
    (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆))
    (huZ : u ∉ Subgroup.center G)
    (hcard : Nat.card (G ⧸ Subgroup.center G) ≤ n) (g : G) :
    ⁅u, g⁆ = 1 := by
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  -- `O_{2'}(G / Z(G))` is the image of `O_{2'}(G) = 1`
  have hOquot : oPiCore {q | q ≠ 2} (G ⧸ Subgroup.center G) = ⊥ := by
    rw [oPiCore_quotient_center_eq_map le_rfl, hO, Subgroup.map_bot]
  have hmem := commutator_mem_of_quotient P hIH hu hu2 hiso huZ hcard g
  rw [hOquot, Subgroup.mem_bot] at hmem
  -- so `⁅u, g⁆` lies in `Z(G)`
  have hmemZ : ⁅u, g⁆ ∈ Subgroup.center G := by
    have hmap : ⁅QuotientGroup.mk' (Subgroup.center G) u,
        QuotientGroup.mk' (Subgroup.center G) g⁆
        = QuotientGroup.mk' (Subgroup.center G) ⁅u, g⁆ := by
      rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul,
        map_inv, map_inv]
    rw [hmap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  exact eq_one_of_mul_self_eq_one_of_odd
    (mul_self_commutator_eq_one_of_mem_center hu2' hmemZ) (hodd g)

end Steps

end OddOrder.GroupTheory
