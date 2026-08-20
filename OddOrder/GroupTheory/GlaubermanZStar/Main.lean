/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.FinalContradiction
import OddOrder.GroupTheory.BrauerSuzukiEndgame

/-!
# Glauberman's `Z*`-theorem

Navarro (7.9): if `u` is an involution of a Sylow `2`-subgroup `P` of the finite group `G` and
`u` is the only `G`-conjugate of itself inside `P`, then `u ∈ Z*(G)` — the image of `u` in
`G / O_{2'}(G)` is central.

This file runs the induction on `|G|` that the previous files feed:

* if `O_{2'}(G) ≠ 1`, Step 1 (`commutator_mem_of_quotient`) applied to `N = O_{2'}(G)` gives the
  conclusion for `G ⧸ N`, and `O_{2'}(G/O_{2'}(G)) = 1` (`oPiCore_quotient_self_eq_bot`) turns it
  into the conclusion for `G`;
* so assume `O_{2'}(G) = 1`; if `u` is already central there is nothing to prove, and if
  `Z(G) ≠ 1` then Step 4 (`commutator_eq_one_of_center_ne_bot`) finishes;
* what is left — `O_{2'}(G) = 1`, `Z(G) = 1`, `u ∉ Z(G)` — is exactly a `MinimalConfig`, whose
  `zStar_proper` field is Step 2 (`commutator_mem_of_subgroup`) for the proper subgroups.  Step 5
  (`exists_involution_ne_of_notMem_center`) produces a second involution of `P`, and
  `false_of_exists_involution` kills it.

## Main results

* `OddOrder.GroupTheory.zStarUpTo_all` — the inductive statement, for every bound
* `OddOrder.GroupTheory.commutator_mem_oPiCore_of_isolated` — `⁅u, g⁆ ∈ O_{2'}(G)`
* `OddOrder.GroupTheory.glauberman_zStar` — `u ∈ Z*(G)`, in the quotient form
* `OddOrder.GroupTheory.glauberman_zStar_oddCore` — the same with the classical odd core `O(G)`
* `OddOrder.GroupTheory.glauberman_zStar_sup_centralizer_eq_top` — the product form
  `G = O_{2'}(G) · C_G(u)`
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

/-- **Navarro (7.9), the induction.**  The `Z*`-theorem holds for every group of order at most
`n`, for every `n`. -/
theorem zStarUpTo_all (n : ℕ) : ZStarUpTo.{v} n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro H _ _ hcard P u hu hu2 hiso g
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hHpos : 0 < Nat.card H := Nat.card_pos
    -- the inductive hypothesis, available for every proper section of `H`
    have hIH : ZStarUpTo.{v} (Nat.card H - 1) := IH _ (by omega)
    have hodd : ∀ g : H, Odd (orderOf ⁅u, g⁆) :=
      odd_orderOf_commutator_of_forall_conj_eq P hu2 hiso
    have hu2' : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu2, sq] at this
    by_cases hO : oPiCore {q | q ≠ 2} H = ⊥
    · -- `O_{2'}(H) = 1`: the conclusion is `⁅u, g⁆ = 1`
      rw [hO, Subgroup.mem_bot]
      by_cases huZ : u ∈ Subgroup.center H
      · exact commutatorElement_eq_one_iff_commute.mpr
          (Subgroup.mem_center_iff.mp huZ g).symm
      by_cases hZ : Subgroup.center H = ⊥
      · -- the minimal configuration: Steps 5–9 and block orthogonality contradict it
        exfalso
        obtain ⟨w, hwP, hw2, hwne, -⟩ :=
          exists_involution_ne_of_notMem_center P hO hu hu2 hiso huZ
        exact MinimalConfig.false_of_exists_involution
          { P := P
            u := u
            mem_sylow := hu
            orderOf_eq_two := hu2
            isolated := hiso
            oPiCore_eq_bot := hO
            center_eq_bot := hZ
            zStar_proper := fun K hK huK h =>
              commutator_mem_of_subgroup hIH hu2 hodd huK
                (by
                  have := Subgroup.card_lt_card_of_ne_top hK
                  omega) h }
          hwP hw2 hwne
      · -- `Z(H) ≠ 1`: Step 4
        exact commutator_eq_one_of_center_ne_bot hIH P hO hu hu2 hiso hodd huZ
          (by
            have := Subgroup.card_quotient_lt_of_ne_bot (K := Subgroup.center H) hZ
            omega) g
    · -- `O_{2'}(H) ≠ 1`: Step 1, then `O_{2'}(H/O_{2'}(H)) = 1`
      have huN : u ∉ oPiCore {q | q ≠ 2} H := fun hmem => by
        have hord : orderOf (⟨u, hmem⟩ : ↥(oPiCore {q | q ≠ 2} H)) = 2 := by
          rw [Subgroup.orderOf_mk]; exact hu2
        have hdvd : (2 : ℕ) ∣ Nat.card ↥(oPiCore {q | q ≠ 2} H) := by
          have h := orderOf_dvd_natCard (⟨u, hmem⟩ : ↥(oPiCore {q | q ≠ 2} H))
          rwa [hord] at h
        exact (oPiCore.isPiGroup (G := H) {q | q ≠ 2}) 2
          (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, Nat.card_pos.ne'⟩) rfl
      have hmem := commutator_mem_of_quotient P hIH hu hu2 hiso huN
        (by
          have := Subgroup.card_quotient_lt_of_ne_bot (K := oPiCore {q | q ≠ 2} H) hO
          omega) g
      rw [oPiCore_quotient_self_eq_bot (G := H) {q | q ≠ 2}, Subgroup.mem_bot] at hmem
      have hmap : ⁅QuotientGroup.mk' (oPiCore {q | q ≠ 2} H) u,
            QuotientGroup.mk' (oPiCore {q | q ≠ 2} H) g⁆
          = QuotientGroup.mk' (oPiCore {q | q ≠ 2} H) ⁅u, g⁆ := by
        rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul,
          map_inv, map_inv]
      rw [hmap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem

variable {G : Type v} [Group G] [Finite G]

/-- **Glauberman's `Z*`-theorem, working form** (Navarro (7.9)): every commutator `⁅u, g⁆` of an
isolated involution lies in `O_{2'}(G)`. -/
theorem commutator_mem_oPiCore_of_isolated (P : Sylow 2 G) {u : G} (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u) (g : G) :
    ⁅u, g⁆ ∈ oPiCore {q | q ≠ 2} G :=
  zStarUpTo_all (Nat.card G) G le_rfl P u hu hu2 hiso g

/-- **Glauberman's `Z*`-theorem** (G. Glauberman, *Central elements in core-free groups*,
J. Algebra **4** (1966), 403–420; Navarro (7.9)): if `u` is an involution of a Sylow
`2`-subgroup `P` of the finite group `G` and `u` is the only `G`-conjugate of itself inside `P`,
then `u ∈ Z*(G)` — the image of `u` in `G/O_{2'}(G)` is central.

Brauer–Suzuki (`brauerSuzuki_mk_mem_center`) is the special case in which `P` is generalized
quaternion, where the isolation hypothesis is automatic; here it is used the other way round, as
one of the two branches of Step 5. -/
theorem glauberman_zStar (P : Sylow 2 G) {u : G} (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u) :
    QuotientGroup.mk' (oPiCore {q | q ≠ 2} G) u
      ∈ Subgroup.center (G ⧸ oPiCore {q | q ≠ 2} G) :=
  mk_mem_center_iff_forall_commutator_mem.mpr
    (commutator_mem_oPiCore_of_isolated P hu hu2 hiso)

/-- **Glauberman's `Z*`-theorem, product form**: `G = O_{2'}(G) · C_G(u)`. -/
theorem glauberman_zStar_sup_centralizer_eq_top (P : Sylow 2 G) {u : G}
    (hu : u ∈ (P : Subgroup G)) (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u) :
    oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {u} = ⊤ :=
  oPiCore_sup_centralizer_eq_top_of_mk_mem_center hu2 (glauberman_zStar P hu hu2 hiso)

/-- **Glauberman's `Z*`-theorem in the classical `O(G)` notation**, where `O(G)` is the largest
normal subgroup of odd order. -/
theorem glauberman_zStar_oddCore (P : Sylow 2 G) {u : G} (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u) :
    (QuotientGroup.mk u : G ⧸ sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)})
      ∈ Subgroup.center (G ⧸ sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}) := by
  refine mk_mem_center_of_sup_centralizer_eq_top ?_
  rw [← oPiCore_ne_two_eq_sSup_normal_odd G]
  exact glauberman_zStar_sup_centralizer_eq_top P hu hu2 hiso

/-- **Glauberman's `Z*`-theorem, stated with the commutator form of the hypothesis**
(Navarro (7.8) turns one into the other): if every `⁅u, g⁆` has odd order then `u ∈ Z*(G)`. -/
theorem glauberman_zStar_of_odd_commutator (P : Sylow 2 G) {u : G} (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2) (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆)) :
    QuotientGroup.mk' (oPiCore {q | q ≠ 2} G) u
      ∈ Subgroup.center (G ⧸ oPiCore {q | q ≠ 2} G) :=
  glauberman_zStar P hu hu2
    ((forall_conj_eq_iff_forall_odd_orderOf_commutator P hu hu2).mpr hodd)

end OddOrder.GroupTheory
