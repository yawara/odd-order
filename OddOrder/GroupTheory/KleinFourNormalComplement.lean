/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.KleinFourSylowFusion
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# Klein four Sylow `2`-subgroups: two non-conjugate involutions force a normal `2`-complement

Navarro (7.2) says a group with a Klein four Sylow `2`-subgroup has one or three classes of
involutions, three exactly when it has a normal `2`-complement.  The direction used in the proof
of the Brauer–Suzuki theorem is the contrapositive of the "one class" half:

if two involutions are **not** conjugate then `N_G(P) ≤ C_G(P)`, and Burnside's normal
`p`-complement theorem applies.

In (7.2) this is used for `C = C_G(t)`: the involution `t` is central in `C`, so its `C`-class is
`{t}` while the Klein four Sylow `2`-subgroup of `C` has three involutions — hence `C` cannot have
a single class, and `C` has a normal `2`-complement.

## Main results

* `OddOrder.GroupTheory.hasNormalPComplement_of_not_isConj`
* `OddOrder.GroupTheory.exists_not_isConj_of_mem_center` — a central involution keeps a Klein four
  Sylow `2`-subgroup from having a single class
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **Two non-conjugate involutions force a normal `2`-complement**, for a Klein four Sylow
`2`-subgroup.  Contrapositive of `isConj_of_klein_sylow_of_not_centralizes`, followed by
Burnside's normal `p`-complement theorem. -/
theorem hasNormalPComplement_of_not_isConj (P : Sylow 2 G)
    (hcard : Nat.card ↥(P : Subgroup G) = 4) (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {u v : G} (hu : u ≠ 1) (hu2 : u * u = 1) (hv : v ≠ 1) (hv2 : v * v = 1)
    (hnc : ¬ IsConj u v) : Isaacs.Ch05.HasNormalPComplement 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P fun g hg => ?_
  by_contra hgc
  refine hnc (isConj_of_klein_sylow_of_not_centralizes P hcard hexp hg ?_ hu hu2 hv hv2)
  by_contra hall
  refine hgc (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
  have hxg : g * x * g⁻¹ = x := by
    by_contra hne
    exact hall ⟨x, hx, hne⟩
  calc x * g = (g * x * g⁻¹) * g := by rw [hxg]
    _ = g * x := by group

omit [Finite G] in
/-- **A central involution keeps a Klein four Sylow `2`-subgroup from having a single class.**
Its class is the singleton `{t}`, while `P` contains an involution different from `t`. -/
theorem exists_not_isConj_of_mem_center (P : Sylow 2 G)
    (hcard : Nat.card ↥(P : Subgroup G) = 4) (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {t : G} (ht : t ≠ 1) (ht2 : t * t = 1) (htc : ∀ y : G, y * t = t * y) :
    ∃ u : G, u ≠ 1 ∧ u * u = 1 ∧ ¬ IsConj t u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht
    · exact h
  have hfix : ∀ y : G, y * t * y⁻¹ = t := fun y => by rw [htc y]; group
  have hfix' : ∀ y : G, t * y * t⁻¹ = y := fun y => by rw [← htc y]; group
  have htP : t ∈ (P : Subgroup G) :=
    mem_of_isPElement_of_mem_normalizer P ⟨1, by rw [hord, pow_one]⟩
      (Subgroup.mem_normalizer_iff.mpr fun h => by rw [hfix' h])
  obtain ⟨u, hu1, hut⟩ := exists_ne_ne_one_of_klein (P := ↥(P : Subgroup G)) hcard
    (a := (⟨t, htP⟩ : ↥(P : Subgroup G))) fun h => ht (congrArg Subtype.val h)
  refine ⟨(u : G), fun h => hu1 (Subtype.ext h), congrArg Subtype.val (hexp u), fun hconj => ?_⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact hut (Subtype.ext (by rw [← hc, hfix c]))

end OddOrder.GroupTheory
