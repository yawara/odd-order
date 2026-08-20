/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanZStar.Reduction
import OddOrder.GroupTheory.BrauerSuzukiGeneral
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main

/-!
# Glauberman's `Z*`-theorem: Step 5 — a second involution in `P`

Navarro (7.9), Step 5.  In the minimal configuration (`O_{2'}(G) = 1`, `u ∉ Z(G)`, `P ≠ G`) the
Sylow `2`-subgroup `P` cannot have a unique involution:

* if `P` were cyclic, Burnside's normal `2`-complement (the cyclic branch of Brauer–Suzuki,
  `brauerSuzuki_of_isCyclic_sylowTwo`) would give `G = O_{2'}(G)·C_G(u) = C_G(u)`, i.e.
  `u ∈ Z(G)`;
* if `P` were generalized quaternion, `brauerSuzuki_of_quaternionSylowTwo` would give the same.

Since a `2`-group with a unique subgroup of order `2` is cyclic or generalized quaternion
(**Isaacs Thm 6.11**, `isCyclic_or_two_quaternion_of_subgroups_card_prime_unique`), `P` contains
an involution `v ≠ u`.  That `v` is not `G`-conjugate to `u` is immediate from the hypothesis:
both lie in `P`.

The "in particular" of Step 5 — `u ∈ Z(D)` for every `2`-subgroup `D` containing `u` — is
`conj_eq_of_mem_pGroup` from `IsolatedInvolution.lean`.

## Main results

* `OddOrder.GroupTheory.mem_center_of_isPGroup` — `u` is central in every `2`-subgroup it meets
* `OddOrder.GroupTheory.exists_involution_ne_of_notMem_center` — Step 5
-/

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch06

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

universe v

variable {G : Type v} [Group G] [Finite G] (P : Sylow 2 G) {u : G}

/-- **Navarro (7.9), Step 5, "in particular"**: `u` lies in the centre of every `2`-subgroup
containing it.  Every `d ∈ D` conjugates `u` inside `D`, and `conj_eq_of_mem_pGroup` says that a
`2`-subgroup cannot separate `u` from its conjugates. -/
theorem mem_center_of_isPGroup
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
    {D : Subgroup G} (hD : IsPGroup 2 D) (huD : u ∈ D) (d : G) (hd : d ∈ D) :
    d * u * d⁻¹ = u :=
  conj_eq_of_mem_pGroup P hiso hD (mul_mem (mul_mem hd huD) (inv_mem hd)) huD

/-- **Navarro (7.9), Step 5.**  In the minimal configuration `P` carries an involution `v ≠ u`,
necessarily not `G`-conjugate to `u`. -/
theorem exists_involution_ne_of_notMem_center (hO : oPiCore {q | q ≠ 2} G = ⊥)
    (hu : u ∈ (P : Subgroup G)) (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
    (huZ : u ∉ Subgroup.center G) :
    ∃ v : G, v ∈ (P : Subgroup G) ∧ orderOf v = 2 ∧ v ≠ u ∧ ¬ IsConj u v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2' : u ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
  have hune : u ≠ 1 := fun h => by simp [h] at hu2
  -- both Brauer–Suzuki branches would put `u` in the centre
  have hcentral : ∀ {S : Sylow 2 G}, u ∈ (S : Subgroup G) →
      oPiCore {q | q ≠ 2} G ⊔ Subgroup.centralizer {u} = ⊤ → False := by
    intro S _ hsup
    refine huZ ?_
    rw [hO, bot_sup_eq] at hsup
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have hg : g ∈ Subgroup.centralizer ({u} : Set G) := by rw [hsup]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  -- an involution of `P` other than `u` must exist
  have hexists : ∃ v : G, v ∈ (P : Subgroup G) ∧ orderOf v = 2 ∧ v ≠ u := by
    by_contra hno
    push Not at hno
    -- otherwise every subgroup of order `2` of `P` is `⟨u⟩`, and Isaacs Thm 6.11 applies
    have hUnique : ∀ K L : Subgroup ↥(P : Subgroup G),
        Nat.card K = 2 → Nat.card L = 2 → K = L := by
      have hkey : ∀ K : Subgroup ↥(P : Subgroup G), Nat.card K = 2 →
          K = Subgroup.zpowers (⟨u, hu⟩ : ↥(P : Subgroup G)) := by
        intro K hK
        have hord : orderOf (⟨u, hu⟩ : ↥(P : Subgroup G)) = 2 := by
          rw [Subgroup.orderOf_mk]; exact hu2
        refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
        · rw [Subgroup.zpowers_le]
          -- the nontrivial element of `K` is an involution of `P`, hence equals `u`
          obtain ⟨x, hxK, hx1⟩ : ∃ x : ↥(P : Subgroup G), x ∈ K ∧ x ≠ 1 := by
            by_contra hcon
            push Not at hcon
            have hbot : K = ⊥ := (Subgroup.eq_bot_iff_forall K).mpr fun y hy => hcon y hy
            rw [hbot] at hK
            simp at hK
          have hxord : orderOf x = 2 := by
            have hdvd : orderOf x ∣ 2 := by
              have h := orderOf_dvd_natCard (⟨x, hxK⟩ : ↥K)
              rwa [Subgroup.orderOf_mk, hK] at h
            rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) hx1
            · exact h
          have hxG : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hxord
          have : (x : G) = u := hno _ x.2 hxG
          have hxu : x = (⟨u, hu⟩ : ↥(P : Subgroup G)) := Subtype.ext this
          rwa [← hxu]
        · rw [hK, Nat.card_zpowers, hord]
      intro K L hK hL
      rw [hkey K hK, hkey L hL]
    rcases isCyclic_or_two_quaternion_of_subgroups_card_prime_unique P.isPGroup' hUnique with
      hcyc | ⟨-, m, ⟨e⟩⟩
    · exact hcentral hu (brauerSuzuki_of_isCyclic_sylowTwo P hcyc u hu2' hune)
    · exact hcentral hu (brauerSuzuki_of_quaternionSylowTwo P ⟨e⟩ hu hu2)
  obtain ⟨v, hvP, hv2, hvu⟩ := hexists
  refine ⟨v, hvP, hv2, hvu, fun hconj => ?_⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact hvu (hc ▸ hiso c (hc ▸ hvP))

end OddOrder.GroupTheory
